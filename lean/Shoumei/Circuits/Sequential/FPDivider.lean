/-
Circuits/Sequential/FPDivider.lean - 23-Cycle Iterative FP Divider

An iterative floating-point divider for IEEE 754 binary32.
Uses a busy/done state machine protocol identical to the integer Divider32.

Algorithm:
  Restoring division of mantissas. On start, performs a pre-comparison of
  dividend and divisor mantissas to determine the first quotient bit (1 if
  dividend >= divisor, 0 otherwise), with the initial remainder set to the
  subtraction result or the original dividend accordingly. Then 23 cycles of
  shift-subtract produce the remaining quotient bits. On done, normalizes
  the quotient (left-shift + exp decrement if leading bit is 0) and packs
  the result.

Architecture:
- Sequential circuit (DFF registers, clock, reset)
- 23 cycles to complete one division (+ combinational pre-compare on start)
- Busy/done handshake protocol

State registers:
- src1_q[31:0]: Latched dividend (32 DFFs)
- src2_q[31:0]: Latched divisor (32 DFFs)
- rm_q[2:0]: Latched rounding mode (3 DFFs)
- tag_q[5:0]: Latched destination tag (6 DFFs)
- cnt_q[4:0]: 5-bit cycle counter 0..23 (5 DFFs)
- busy_q: Busy flag (1 DFF)
- sign_q: Result sign (1 DFF)
- exp_q[7:0]: Result exponent (8 DFFs)
- div_mant_q[23:0]: Divisor mantissa with implicit 1 (24 DFFs)
- rem_q[24:0]: Remainder (25 DFFs)
- quot_q[23:0]: Quotient (24 DFFs)
Total: 161 DFFs

Interface:
- Inputs: src1[31:0], src2[31:0], rm[2:0], dest_tag[5:0], start,
          clock, reset, zero, one
- Outputs: result[31:0], tag_out[5:0], exc[4:0], valid_out, busy
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.KoggeStoneAdder
import Shoumei.Circuits.Sequential.FPNormalize

namespace Shoumei.Circuits.Sequential

open Shoumei
open Shoumei.Circuits.Combinational

/-! ## Helper: Indexed Wire Generation -/

private def makeIndexedWires (pfx : String) (n : Nat) : List Wire :=
  (List.range n).map fun i => Wire.mk (pfx ++ "_" ++ toString i)

/-- AND-reduce a wire list. -/
private def mkAndTree (pfx : String) (wires : List Wire) : Wire × List Gate :=
  match wires with
  | [] => (Wire.mk s!"{pfx}_gnd", [])
  | w0 :: rest =>
    let (last, gates) := rest.foldl (fun (acc, gs) w =>
      let o := Wire.mk s!"{pfx}_{gs.length}"
      (o, gs ++ [Gate.mkAND acc w o])) (w0, [])
    (last, gates)

/-- OR-reduce a wire list. -/
private def mkOrTree (pfx : String) (wires : List Wire) : Wire × List Gate :=
  match wires with
  | [] => (Wire.mk s!"{pfx}_gnd", [])
  | w0 :: rest =>
    let (last, gates) := rest.foldl (fun (acc, gs) w =>
      let o := Wire.mk s!"{pfx}_{gs.length}"
      (o, gs ++ [Gate.mkOR acc w o])) (w0, [])
    (last, gates)

/-- Right barrel shifter that accumulates every bit shifted below position 0
    into `sticky_out`, so a subnormal result keeps its guard/round window and the
    remainder below it stays visible. -/
private def mkBarrelShiftRightSticky (input : List Wire) (shift_amt : List Wire)
    (output : List Wire) (sticky_out : Wire) (zero_wire : Wire) (pfx : String) : List Gate :=
  let w := input.length
  let levels : List (List Wire) := (List.range 7).map fun level =>
    if level == 0 then input
    else (List.range w).map fun i => Wire.mk (pfx ++ "_l" ++ toString level ++ "_" ++ toString i)
  let stickies : List Wire := (List.range 7).map fun level => Wire.mk (pfx ++ "_stk_" ++ toString level)
  let init_stk_gate := Gate.mkBUF zero_wire stickies[0]!
  let (mux_gates, stk_gates) := (List.range 6).foldl (fun (acc : List Gate × List Gate) level =>
    let shift_by := 1 <<< level
    let prev := levels[level]!
    let curr := levels[level + 1]!
    let sel := shift_amt[level]!
    let prev_stk := stickies[level]!
    let curr_stk := stickies[level + 1]!
    let m_gates := (List.range w).map fun i =>
      let shifted := if i + shift_by < w then prev[i + shift_by]! else zero_wire
      Gate.mkMUX prev[i]! shifted sel curr[i]!
    let lost_bits := (List.range (min shift_by w)).map fun i => prev[i]!
    let (lost_or, lost_or_gates) := mkOrTree (pfx ++ "_lost_" ++ toString level) lost_bits
    let stk_c := Wire.mk (pfx ++ "_stkc_" ++ toString level)
    let s_gates := lost_or_gates ++ [
      Gate.mkAND sel lost_or stk_c,
      Gate.mkOR prev_stk stk_c curr_stk
    ]
    (acc.1 ++ m_gates, acc.2 ++ s_gates)
  ) ([], [init_stk_gate])
  let copy_gates := (List.range w).map fun i => Gate.mkBUF (levels[6]!)[i]! output[i]!
  mux_gates ++ stk_gates ++ copy_gates ++ [Gate.mkBUF stickies[6]! sticky_out]

/-! ## Structural Circuit -/

/-- Build the 24-cycle iterative FP divider structural circuit. -/
def mkFPDivider : Circuit :=
  -- ══════════════════════════════════════════════
  -- Input wires
  -- ══════════════════════════════════════════════
  let src1_in := makeIndexedWires "src1" 32
  let src2_in := makeIndexedWires "src2" 32
  let rm_in := makeIndexedWires "rm" 3
  let dest_tag := makeIndexedWires "dest_tag" 6
  let start := Wire.mk "start"
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- ══════════════════════════════════════════════
  -- Output wires
  -- ══════════════════════════════════════════════
  let result := makeIndexedWires "result" 32
  let tag_out := makeIndexedWires "tag_out" 6
  let exc := makeIndexedWires "exc" 5
  let valid_out := Wire.mk "valid_out"
  let busy_out := Wire.mk "busy"

  -- ══════════════════════════════════════════════
  -- State register wires (DFF outputs = current state)
  -- ══════════════════════════════════════════════
  let src1_q := makeIndexedWires "src1_q" 32
  let src2_q := makeIndexedWires "src2_q" 32
  let rm_q := makeIndexedWires "rm_q" 3
  let tag_q := makeIndexedWires "tag_q" 6
  let cnt_q := makeIndexedWires "cnt_q" 5
  let busy_q := Wire.mk "busy_q"

  -- Division datapath state
  let sign_q := Wire.mk "sign_q"
  let exp_q := makeIndexedWires "exp_q" 10
  let div_mant_q := makeIndexedWires "div_mant_q" 24
  let rem_q := makeIndexedWires "rem_q" 25
  let quot_q := makeIndexedWires "quot_q" 24

  -- Next-state wires (DFF inputs)
  let src1_d := makeIndexedWires "src1_d" 32
  let src2_d := makeIndexedWires "src2_d" 32
  let rm_d := makeIndexedWires "rm_d" 3
  let tag_d := makeIndexedWires "tag_d" 6
  let cnt_d := makeIndexedWires "cnt_d" 5
  let busy_d := Wire.mk "busy_d"

  let sign_d := Wire.mk "sign_d"
  let exp_d := makeIndexedWires "exp_d" 10
  let div_mant_d := makeIndexedWires "div_mant_d" 24
  let rem_d := makeIndexedWires "rem_d" 25
  let quot_d := makeIndexedWires "quot_d" 24

  -- ══════════════════════════════════════════════
  -- Control signals (combinational)
  -- ══════════════════════════════════════════════
  let not_busy := Wire.mk "not_busy"
  let start_new := Wire.mk "start_new"
  let cnt_is_23 := Wire.mk "cnt_is_23"
  let done := Wire.mk "done"
  let not_done := Wire.mk "not_done"
  let busy_and_not_done := Wire.mk "busy_and_not_done"

  let cnt3_inv := Wire.mk "cnt3_inv"

  -- cnt_is_23: 23 = 10111 → cnt[0] AND cnt[1] AND cnt[2] AND NOT(cnt[3]) AND cnt[4]
  let ctrl_gates := [
    Gate.mkNOT busy_q not_busy,
    Gate.mkAND start not_busy start_new,
    Gate.mkNOT (cnt_q[3]!) cnt3_inv,
    Gate.mkAND (cnt_q[0]!) (cnt_q[1]!) (Wire.mk "cnt_01"),
    Gate.mkAND (cnt_q[2]!) cnt3_inv (Wire.mk "cnt_2n3"),
    Gate.mkAND (Wire.mk "cnt_01") (Wire.mk "cnt_2n3") (Wire.mk "cnt_0123"),
    Gate.mkAND (Wire.mk "cnt_0123") (cnt_q[4]!) cnt_is_23,
    Gate.mkAND busy_q cnt_is_23 done,
    Gate.mkNOT done not_done,
    Gate.mkAND busy_q not_done busy_and_not_done
  ]

  -- ══════════════════════════════════════════════
  -- Busy flag next state
  -- ══════════════════════════════════════════════
  let busy_gates := [
    Gate.mkOR start_new busy_and_not_done busy_d
  ]

  -- ══════════════════════════════════════════════
  -- Counter increment logic (5-bit ripple incrementer)
  -- ══════════════════════════════════════════════
  let cnt_next := makeIndexedWires "cnt_next" 5
  let inc_carry := makeIndexedWires "inc_carry" 6

  let cnt_inc_gates :=
    [Gate.mkBUF one (inc_carry[0]!)] ++
    (List.range 5).flatMap (fun i =>
      [
        Gate.mkXOR (cnt_q[i]!) (inc_carry[i]!) (cnt_next[i]!),
        Gate.mkAND (cnt_q[i]!) (inc_carry[i]!) (inc_carry[i + 1]!)
      ]
    )

  -- ══════════════════════════════════════════════
  -- Counter next-state MUX (two-level)
  -- ══════════════════════════════════════════════
  let cnt_m1 := makeIndexedWires "cnt_m1" 5
  let cnt_mux_gates := (List.range 5).flatMap (fun i => [
    Gate.mkMUX (cnt_q[i]!) (cnt_next[i]!) busy_and_not_done (cnt_m1[i]!),
    Gate.mkMUX (cnt_m1[i]!) zero start_new (cnt_d[i]!)
  ])

  -- ══════════════════════════════════════════════
  -- Data latch MUXes: latch on start_new, hold otherwise
  -- ══════════════════════════════════════════════
  let src1_mux_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (src1_q[i]!) (src1_in[i]!) start_new (src1_d[i]!)
  )

  let src2_mux_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (src2_q[i]!) (src2_in[i]!) start_new (src2_d[i]!)
  )

  let rm_mux_gates := (List.range 3).map (fun i =>
    Gate.mkMUX (rm_q[i]!) (rm_in[i]!) start_new (rm_d[i]!)
  )

  let tag_mux_gates := (List.range 6).map (fun i =>
    Gate.mkMUX (tag_q[i]!) (dest_tag[i]!) start_new (tag_d[i]!)
  )

  -- ══════════════════════════════════════════════
  -- Sign computation: res_sign = src1[31] XOR src2[31]
  -- ══════════════════════════════════════════════
  let init_sign := Wire.mk "init_sign"
  let sign_gates := [
    Gate.mkXOR (src1_in[31]!) (src2_in[31]!) init_sign,
    -- sign_d = MUX(sign_q, init_sign, start_new)
    Gate.mkMUX sign_q init_sign start_new sign_d
  ]

  -- ══════════════════════════════════════════════
  -- Operand normalization
  -- ══════════════════════════════════════════════
  -- A nonzero subnormal operand has no implicit bit: its leading one sits below
  -- position 23 and its exponent field is zero.  Shifting the fraction up until
  -- that one reaches position 23 puts the mantissa in [1, 2), which is what the
  -- restoring division needs -- it compares and subtracts the two mantissas
  -- directly, so an unscaled small dividend would produce a quotient off by a
  -- power of two and a first remainder that never restores.  The exponent field
  -- drops by the same shift to keep the value.  A normal operand shifts by
  -- nothing and its raw field passes through unchanged.
  let frac1_bits := (List.range 23).map fun i => src1_in[i]!
  let frac2_bits := (List.range 23).map fun i => src2_in[i]!
  let exp1_bits := (List.range 8).map fun i => src1_in[23 + i]!
  let exp2_bits := (List.range 8).map fun i => src2_in[23 + i]!
  let (f1_nz, f1_nz_gates) := mkOrTree "div_f1nz" frac1_bits
  let (f2_nz, f2_nz_gates) := mkOrTree "div_f2nz" frac2_bits
  let (exp1_or, exp1_or_gates) := mkOrTree "div_e1or" exp1_bits
  let (exp2_or, exp2_or_gates) := mkOrTree "div_e2or" exp2_bits

  let not_exp1_or := Wire.mk "div_ne1or"
  let not_exp2_or := Wire.mk "div_ne2or"
  let sub1 := Wire.mk "div_sub1"
  let sub2 := Wire.mk "div_sub2"
  let sub_op_gates := [
    Gate.mkNOT exp1_or not_exp1_or,
    Gate.mkNOT exp2_or not_exp2_or,
    Gate.mkAND not_exp1_or f1_nz sub1,
    Gate.mkAND not_exp2_or f2_nz sub2
  ]

  -- Shift that brings the leading one to position 23: 23 - position.
  let pos1 := makeIndexedWires "div_pos1" 5
  let pos2 := makeIndexedWires "div_pos2" 5
  let (pos1_w, lead1_gates) := mkLeadPos "div_lz1" frac1_bits zero 5
  let (pos2_w, lead2_gates) := mkLeadPos "div_lz2" frac2_bits zero 5
  let pos1_gates := (List.range 5).map fun i => Gate.mkBUF (pos1_w[i]!) (pos1[i]!)
  let pos2_gates := (List.range 5).map fun i => Gate.mkBUF (pos2_w[i]!) (pos2[i]!)
  let const23 := (List.range 6).map fun i =>
    if i == 0 || i == 1 || i == 2 || i == 4 then one else zero
  let pos1_ext := (List.range 6).map fun i => if i < 5 then pos1[i]! else zero
  let pos2_ext := (List.range 6).map fun i => if i < 5 then pos2[i]! else zero
  let sh1 := makeIndexedWires "div_sh1" 6
  let sh2 := makeIndexedWires "div_sh2" 6
  let (sh1_gates, _sh1_borrow) := mkKoggeStoneSub const23 pos1_ext sh1 "div_sh1sub" one
  let (sh2_gates, _sh2_borrow) := mkKoggeStoneSub const23 pos2_ext sh2 "div_sh2sub" one

  let norm1 := makeIndexedWires "div_norm1" 24
  let norm2 := makeIndexedWires "div_norm2" 24
  let norm1_gates := mkBarrelShiftLeft (frac1_bits ++ [zero]) sh1 norm1 zero "div_bsl1"
  let norm2_gates := mkBarrelShiftLeft (frac2_bits ++ [zero]) sh2 norm2 zero "div_bsl2"

  -- Mantissa in [1, 2): the raw {1, fraction} for a normal operand, the shifted
  -- fraction for a subnormal.
  let mant1 := makeIndexedWires "div_mant1" 24
  let mant2 := makeIndexedWires "div_mant2" 24
  let mant_gates := (List.range 24).flatMap fun i =>
    let raw1 := if i == 23 then one else src1_in[i]!
    let raw2 := if i == 23 then one else src2_in[i]!
    [Gate.mkMUX raw1 (norm1[i]!) sub1 (mant1[i]!),
     Gate.mkMUX raw2 (norm2[i]!) sub2 (mant2[i]!)]

  -- Effective exponent field at 10 bits: 1 - shift for a subnormal (a signed
  -- value, hence the full width), the raw field otherwise.
  let one10 := (List.range 10).map fun i => if i == 0 then one else zero
  let sh1_10 := (List.range 10).map fun i => if i < 6 then sh1[i]! else zero
  let sh2_10 := (List.range 10).map fun i => if i < 6 then sh2[i]! else zero
  let eff1 := makeIndexedWires "div_eff1" 10
  let eff2 := makeIndexedWires "div_eff2" 10
  let (eff1_gates, _eff1_borrow) := mkKoggeStoneSub one10 sh1_10 eff1 "div_eff1s" one
  let (eff2_gates, _eff2_borrow) := mkKoggeStoneSub one10 sh2_10 eff2 "div_eff2s" one
  let exp1_n := makeIndexedWires "div_exp1_n" 10
  let exp2_n := makeIndexedWires "div_exp2_n" 10
  let exp_norm_gates := (List.range 10).flatMap fun i =>
    let raw1 := if i < 8 then exp1_bits[i]! else zero
    let raw2 := if i < 8 then exp2_bits[i]! else zero
    [Gate.mkMUX raw1 (eff1[i]!) sub1 (exp1_n[i]!),
     Gate.mkMUX raw2 (eff2[i]!) sub2 (exp2_n[i]!)]

  -- ══════════════════════════════════════════════
  -- Exponent computation: res_exp = exp1 - exp2 + 127
  -- ══════════════════════════════════════════════
  -- Step 1: 10-bit subtraction diff = exp1 - exp2.  The field must hold the whole
  -- range: a single-precision quotient exponent spans -254..381, and at 8 bits a
  -- subnormal result (exponent 0 or less) is indistinguishable from an ordinary
  -- large exponent.
  let exp_diff := makeIndexedWires "exp_diff" 10
  let (exp_sub_gates, _exp_diff_borrow) :=
    mkKoggeStoneSub exp1_n exp2_n exp_diff "div_esub" one

  -- Step 2: 10-bit addition init_exp = diff + 127
  let init_exp := makeIndexedWires "init_exp" 10
  let bias_bits : List Wire := (List.range 10).map (fun i => if i < 7 then one else zero)
  let (exp_add_gates, _exp_add_carry) :=
    mkKoggeStoneAdd exp_diff bias_bits zero init_exp "div_eadd"

  -- exp_d MUX: hold or load init on start_new
  let exp_mux_gates := (List.range 10).map (fun i =>
    Gate.mkMUX (exp_q[i]!) (init_exp[i]!) start_new (exp_d[i]!)
  )

  -- ══════════════════════════════════════════════
  -- Divisor mantissa: init = {1, src2[22:0]}
  -- Hold after start (only loaded once on start_new)
  -- ══════════════════════════════════════════════
  let div_mant_mux_gates := (List.range 24).map (fun i =>
    Gate.mkMUX (div_mant_q[i]!) (mant2[i]!) start_new (div_mant_d[i]!)
  )

  -- ══════════════════════════════════════════════
  -- Pre-comparison: dividend_mant - divisor_mant (on start_new)
  -- Determines first quotient bit and initial remainder
  -- ══════════════════════════════════════════════
  let pre_trial := makeIndexedWires "pre_trial" 25

  -- dividend_mant = mant1, divisor_mant = mant2, each extended to 25 bits
  -- (bit 24 = 0)
  let pre_a := (List.range 25).map (fun i =>
    if i == 24 then zero else mant1[i]!)
  let pre_b := (List.range 25).map (fun i =>
    if i == 24 then zero else mant2[i]!)
  let pre_one := Wire.mk "pre_sub_one"
  let (pre_sub_gates_ks, pre_borrow_out) := mkKoggeStoneSub
    pre_a pre_b (pre_trial.toArray.toList) "pre_sub" pre_one
  let pre_sub_gates := [Gate.mkBUF one pre_one] ++ pre_sub_gates_ks

  -- pre_q = NOT borrow = 1 if dividend >= divisor
  let pre_q := Wire.mk "pre_q"
  let pre_q_gate := [Gate.mkNOT pre_borrow_out pre_q]

  -- ══════════════════════════════════════════════
  -- Division step: executed every cycle while busy_q=1
  -- ══════════════════════════════════════════════

  -- Shift remainder left by 1: rem_shifted[0]=0, rem_shifted[i+1]=rem_q[i]
  let rem_shifted := makeIndexedWires "rem_shifted" 25

  let rem_shift_gates :=
    [Gate.mkBUF zero (rem_shifted[0]!)] ++
    (List.range 24).map (fun i =>
      Gate.mkBUF (rem_q[i]!) (rem_shifted[i + 1]!)
    )

  -- 25-bit Kogge-Stone subtractor: trial = rem_shifted - {0, div_mant_q}
  -- divisor_ext[23:0] = div_mant_q, divisor_ext[24] = 0
  let trial := makeIndexedWires "trial" 25
  let div_ext := (List.range 25).map (fun i =>
    if i < 24 then div_mant_q[i]! else zero)
  let trial_one := Wire.mk "trial_sub_one"
  let (trial_sub_gates_ks, trial_borrow_out) := mkKoggeStoneSub
    (rem_shifted.toArray.toList) div_ext (trial.toArray.toList) "trial_sub" trial_one
  let trial_sub_gates := [Gate.mkBUF one trial_one] ++ trial_sub_gates_ks

  -- q_bit = NOT borrow (no borrow means positive, quotient bit = 1)
  let q_bit := Wire.mk "q_bit"
  let q_bit_gate := [Gate.mkNOT trial_borrow_out q_bit]

  -- new_rem[i] = MUX(rem_shifted[i], trial[i], q_bit)
  -- if q_bit=1 (no borrow): use trial; if q_bit=0 (borrow): use rem_shifted (restore)
  let new_rem := makeIndexedWires "new_rem" 25
  let new_rem_gates := (List.range 25).map (fun i =>
    Gate.mkMUX (rem_shifted[i]!) (trial[i]!) q_bit (new_rem[i]!)
  )

  -- new_quot: shift left and insert q_bit
  -- new_quot[0] = q_bit, new_quot[i] = quot_q[i-1] for i=1..23
  let new_quot := makeIndexedWires "new_quot" 24
  let new_quot_gates :=
    [Gate.mkBUF q_bit (new_quot[0]!)] ++
    (List.range 23).map (fun i =>
      Gate.mkBUF (quot_q[i]!) (new_quot[i + 1]!)
    )

  -- ══════════════════════════════════════════════
  -- Remainder next-state MUX (two-level)
  -- Level 1: MUX(rem_q, new_rem, busy_q)  -- step when busy
  -- Level 2: MUX(m1, init_rem, start_new) -- load on start
  -- init_rem: if pre_q=1 (dividend>=divisor): pre_trial[24:0]
  --           if pre_q=0 (dividend<divisor):  {0, mant1}
  -- ══════════════════════════════════════════════
  let init_rem := makeIndexedWires "init_rem" 25
  let init_rem_gates := (List.range 25).map (fun i =>
    let orig_bit :=
      if i == 24 then zero
      else mant1[i]!
    Gate.mkMUX orig_bit (pre_trial[i]!) pre_q (init_rem[i]!)
  )

  let rem_m1 := makeIndexedWires "rem_m1" 25
  let rem_mux_gates := (List.range 25).flatMap (fun i =>
    [
      Gate.mkMUX (rem_q[i]!) (new_rem[i]!) busy_q (rem_m1[i]!),
      Gate.mkMUX (rem_m1[i]!) (init_rem[i]!) start_new (rem_d[i]!)
    ]
  )

  -- ══════════════════════════════════════════════
  -- Quotient next-state MUX (two-level)
  -- init_quot[0] = pre_q (first quotient bit from pre-comparison)
  -- init_quot[23:1] = 0
  -- ══════════════════════════════════════════════
  let quot_m1 := makeIndexedWires "quot_m1" 24
  let quot_mux_gates := (List.range 24).flatMap (fun i =>
    let init_bit := if i == 0 then pre_q else zero
    [
      Gate.mkMUX (quot_q[i]!) (new_quot[i]!) busy_q (quot_m1[i]!),
      Gate.mkMUX (quot_m1[i]!) init_bit start_new (quot_d[i]!)
    ]
  )

  -- ══════════════════════════════════════════════
  -- DFF registers (all state elements)
  -- ══════════════════════════════════════════════
  let src1_dffs := (List.range 32).map (fun i =>
    Gate.mkDFF (src1_d[i]!) clock reset (src1_q[i]!)
  )
  let src2_dffs := (List.range 32).map (fun i =>
    Gate.mkDFF (src2_d[i]!) clock reset (src2_q[i]!)
  )
  let rm_dffs := (List.range 3).map (fun i =>
    Gate.mkDFF (rm_d[i]!) clock reset (rm_q[i]!)
  )
  let tag_dffs := (List.range 6).map (fun i =>
    Gate.mkDFF (tag_d[i]!) clock reset (tag_q[i]!)
  )
  let cnt_dffs := (List.range 5).map (fun i =>
    Gate.mkDFF (cnt_d[i]!) clock reset (cnt_q[i]!)
  )
  let busy_dff := [Gate.mkDFF busy_d clock reset busy_q]

  let sign_dff := [Gate.mkDFF sign_d clock reset sign_q]
  let exp_dffs := (List.range 10).map (fun i =>
    Gate.mkDFF (exp_d[i]!) clock reset (exp_q[i]!)
  )
  let div_mant_dffs := (List.range 24).map (fun i =>
    Gate.mkDFF (div_mant_d[i]!) clock reset (div_mant_q[i]!)
  )
  let rem_dffs := (List.range 25).map (fun i =>
    Gate.mkDFF (rem_d[i]!) clock reset (rem_q[i]!)
  )
  let quot_dffs := (List.range 24).map (fun i =>
    Gate.mkDFF (quot_d[i]!) clock reset (quot_q[i]!)
  )

  -- ══════════════════════════════════════════════
  -- Output packing: normalize quotient and assemble result
  -- ══════════════════════════════════════════════

  -- Check if normalization needed: norm_needed = NOT quot_q[23]
  let norm_needed := Wire.mk "norm_needed"
  let norm_gate := [Gate.mkNOT (quot_q[23]!) norm_needed]

  -- Normalized mantissa:
  -- If norm_needed=0: mant[i] = quot_q[i] for i=0..22
  -- If norm_needed=1: mant[i] = quot_q[i-1] for i=1..22, mant[0] = 0
  -- norm_mant[i] = MUX(quot_q[i], shifted, norm_needed)
  let norm_mant := makeIndexedWires "norm_mant" 23
  let norm_mant_gates := (List.range 23).map (fun i =>
    let shifted := if i == 0 then zero else quot_q[i - 1]!
    Gate.mkMUX (quot_q[i]!) shifted norm_needed (norm_mant[i]!)
  )

  -- Normalized exponent: exp_q or exp_q - 1
  -- 8-bit decrement: dec[0] = NOT exp[0], borrow[0] = NOT exp[0]
  -- dec[i] = exp[i] XOR borrow[i-1], borrow[i] = NOT exp[i] AND borrow[i-1]
  let dec_exp := makeIndexedWires "dec_exp" 10
  let dec_borrow := makeIndexedWires "dec_borrow" 10
  let dec_gates :=
    -- bit 0
    [
      Gate.mkNOT (exp_q[0]!) (dec_exp[0]!),
      Gate.mkNOT (exp_q[0]!) (dec_borrow[0]!)
    ] ++
    -- bits 1..9
    (List.range 9).flatMap (fun j =>
      let i := j + 1
      let not_exp := Wire.mk s!"dec_nexp_{i}"
      [
        Gate.mkXOR (exp_q[i]!) (dec_borrow[i - 1]!) (dec_exp[i]!),
        Gate.mkNOT (exp_q[i]!) not_exp,
        Gate.mkAND not_exp (dec_borrow[i - 1]!) (dec_borrow[i]!)
      ]
    )

  -- final_exp[i] = MUX(exp_q[i], dec_exp[i], norm_needed)
  let final_exp := makeIndexedWires "final_exp" 10
  let final_exp_gates := (List.range 10).map (fun i =>
    Gate.mkMUX (exp_q[i]!) (dec_exp[i]!) norm_needed (final_exp[i]!)
  )

  -- ══════════════════════════════════════════════
  -- Rounding
  -- ══════════════════════════════════════════════
  -- The quotient is exact to its last bit and the remainder holds everything
  -- below it, so "above half an ulp" is 2*rem > divisor and an exact tie is
  -- 2*rem == divisor.  This unit truncated and did not consult rm at all.
  -- The remainder is scaled to the *unnormalized* quotient, so when the
  -- normalizing shift fires the mantissa LSB halves and the remainder's weight
  -- relative to it doubles: the half-ulp test becomes 4*rem > divisor, not
  -- 2*rem > divisor.
  -- 2*rem and 4*rem, both aligned to 27 bits.  rem_q is 25 bits, so the doubled
  -- form is 26 and gains a zero on top.
  let twice_rem := (List.range 26).map fun i =>
    if i == 0 then zero else rem_q[i - 1]!
  let four_rem := (List.range 27).map fun i =>
    if i < 2 then zero else rem_q[i - 2]!
  let twice_rem := twice_rem ++ [zero]
  let scaled_rem := (List.range 27).map fun i => Wire.mk s!"div_srem_{i}"
  let scale_gates := (List.range 27).map fun i =>
    Gate.mkMUX (twice_rem[i]!) (four_rem[i]!) norm_needed (scaled_rem[i]!)
  let div27 := div_mant_q ++ [zero, zero, zero]

  let cmp_out := makeIndexedWires "div_cmp_out" 27
  let (cmp_sub_gates, cmp_borrow) :=
    mkKoggeStoneSub div27 scaled_rem cmp_out "div_half" one
  let gt_half := cmp_borrow            -- divisor < 2*rem: strictly above half

  let cmp_ne_bits := (List.range 27).map fun i => Wire.mk s!"div_ne_{i}"
  let cmp_eq_bits := (List.range 27).map fun i => Wire.mk s!"div_eq_{i}"
  let cmp_eq_pre_gates := (List.range 27).flatMap fun i =>
    [Gate.mkXOR (div27[i]!) (scaled_rem[i]!) (cmp_ne_bits[i]!),
     Gate.mkNOT (cmp_ne_bits[i]!) (cmp_eq_bits[i]!)]
  let (eq_half, cmp_eq_tree) := mkAndTree "div_eqtree" cmp_eq_bits

  let (any_rem, any_rem_tree) := mkOrTree "div_anyrem" ((List.range 25).map fun i => rem_q[i]!)

  -- Mode decode: 000 RNE, 001 RTZ, 010 RDN, 011 RUP, 100 RMM, 101..111 as RNE.
  -- gt_half is the guard bit; round and sticky are "the remainder is not exactly
  -- half", which is ~eq_half -- eq_half itself is the tie case.
  let not_eq_half := Wire.mk "div_not_eqhalf"
  let rs_or := Wire.mk "div_rs_or"
  let rne_up := Wire.mk "div_rne_up"
  let rmm_cand := Wire.mk "div_rmm_cand"
  let rmm_up := Wire.mk "div_rmm_up"
  let rdn_up := Wire.mk "div_rdn_up"
  let rup_up := Wire.mk "div_rup_up"
  let not_sign := Wire.mk "div_not_sign"
  let not_rm0 := Wire.mk "div_not_rm0"
  let not_rm1 := Wire.mk "div_not_rm1"
  let not_rm2 := Wire.mk "div_not_rm2"
  let is_rtz := Wire.mk "div_is_rtz"
  let is_rdn := Wire.mk "div_is_rdn"
  let is_rup := Wire.mk "div_is_rup"
  let is_rmm := Wire.mk "div_is_rmm"
  let grp_n2n1 := Wire.mk "div_grp_n2n1"
  let grp_n2p1 := Wire.mk "div_grp_n2p1"
  let grp_p2n1 := Wire.mk "div_grp_p2n1"
  let up_rdn := Wire.mk "div_up_rdn"
  let up_rup := Wire.mk "div_up_rup"
  let up_rmm := Wire.mk "div_up_rmm"
  let round_up := Wire.mk "div_round_up"
  let rnd_cond_gates := [
    Gate.mkNOT eq_half not_eq_half,
    Gate.mkOR not_eq_half (norm_mant[0]!) rs_or,
    Gate.mkAND gt_half rs_or rne_up,
    Gate.mkOR gt_half eq_half rmm_cand,
    Gate.mkBUF rmm_cand rmm_up,
    Gate.mkNOT sign_q not_sign,
    Gate.mkAND any_rem sign_q rdn_up,
    Gate.mkAND any_rem not_sign rup_up,
    Gate.mkNOT (rm_q[0]!) not_rm0,
    Gate.mkNOT (rm_q[1]!) not_rm1,
    Gate.mkNOT (rm_q[2]!) not_rm2,
    Gate.mkAND not_rm2 not_rm1 grp_n2n1,
    Gate.mkAND grp_n2n1 (rm_q[0]!) is_rtz,
    Gate.mkAND not_rm2 (rm_q[1]!) grp_n2p1,
    Gate.mkAND grp_n2p1 not_rm0 is_rdn,
    Gate.mkAND grp_n2p1 (rm_q[0]!) is_rup,
    Gate.mkAND (rm_q[2]!) not_rm1 grp_p2n1,
    Gate.mkAND grp_p2n1 not_rm0 is_rmm,
    Gate.mkMUX rne_up rdn_up is_rdn up_rdn,
    Gate.mkMUX up_rdn rup_up is_rup up_rup,
    Gate.mkMUX up_rup rmm_up is_rmm up_rmm,
    Gate.mkMUX up_rmm zero is_rtz round_up
  ]

  let rnd_mant_inc := makeIndexedWires "div_m_inc" 23
  let rnd_mant_c := makeIndexedWires "div_m_c" 24
  let rnd_inc_gates := [Gate.mkBUF round_up (rnd_mant_c[0]!)] ++
    (List.range 23).flatMap fun i =>
      [Gate.mkXOR (norm_mant[i]!) (rnd_mant_c[i]!) (rnd_mant_inc[i]!),
       Gate.mkAND (norm_mant[i]!) (rnd_mant_c[i]!) (rnd_mant_c[i + 1]!)]
  let rnd_rollover := rnd_mant_c[23]!
  let rnd_not_roll := Wire.mk "div_not_roll"
  let rounded_mant := makeIndexedWires "div_rmant" 23
  let rnd_mant_gates := [Gate.mkNOT rnd_rollover rnd_not_roll] ++
    (List.range 23).map fun i =>
      Gate.mkAND (rnd_mant_inc[i]!) rnd_not_roll (rounded_mant[i]!)

  let roll_inc := (List.range 10).map fun i =>
    if i == 0 then rnd_rollover else zero
  let exp_rnd := makeIndexedWires "div_ernd" 10
  let (exp_rnd_gates, _) := mkKoggeStoneAdd final_exp roll_inc zero exp_rnd "div_erndadd"

  -- exc[4:0]: NX (inexact) = remainder non-zero after division
  -- Build OR-tree over rem_q[24:0] to detect non-zero remainder
  let rem_or_l0 := (List.range 12).map fun i =>
    let o := Wire.mk s!"rem_or_l0_{i}"
    (Gate.mkOR (rem_q[2*i]!) (rem_q[2*i+1]!) o, o)
  let rem_or_l0_extra := Wire.mk "rem_or_l0_12"
  let rem_or_l0_extra_gate := Gate.mkBUF (rem_q[24]!) rem_or_l0_extra
  let l0_outs := rem_or_l0.map Prod.snd ++ [rem_or_l0_extra]  -- 13 values
  let rem_or_l1 := (List.range 6).map fun i =>
    let o := Wire.mk s!"rem_or_l1_{i}"
    (Gate.mkOR l0_outs[2*i]! l0_outs[2*i+1]! o, o)
  let rem_or_l1_extra := Wire.mk "rem_or_l1_6"
  let rem_or_l1_extra_gate := Gate.mkBUF l0_outs[12]! rem_or_l1_extra
  let l1_outs := rem_or_l1.map Prod.snd ++ [rem_or_l1_extra]  -- 7 values
  let rem_or_l2_0 := Wire.mk "rem_or_l2_0"
  let rem_or_l2_1 := Wire.mk "rem_or_l2_1"
  let rem_or_l2_2 := Wire.mk "rem_or_l2_2"
  let rem_or_l3_0 := Wire.mk "rem_or_l3_0"
  let rem_nonzero := Wire.mk "rem_nonzero"
  let rem_or_tree :=
    rem_or_l0.map Prod.fst ++ [rem_or_l0_extra_gate] ++
    rem_or_l1.map Prod.fst ++ [rem_or_l1_extra_gate] ++
    [Gate.mkOR l1_outs[0]! l1_outs[1]! rem_or_l2_0,
     Gate.mkOR l1_outs[2]! l1_outs[3]! rem_or_l2_1,
     Gate.mkOR l1_outs[4]! l1_outs[5]! rem_or_l2_2,
     Gate.mkOR rem_or_l2_0 rem_or_l2_1 rem_or_l3_0,
     Gate.mkOR rem_or_l3_0 rem_or_l2_2 rem_nonzero]
  -- ── Subnormal and overflowing results ──────────────────────────────────────
  -- A quotient below the minimum normal is emitted with exponent field 0 and a
  -- mantissa counted in multiples of 2^-149: the normalized quotient is shifted
  -- down by (4 - final_exp), and the division remainder below its last bit joins
  -- the shifted-out bits in the sticky.  A quotient at or above 2^128 is
  -- infinity with OF.
  let sub_neg := final_exp[9]!
  let (final_exp_any, final_exp_any_gates) := mkOrTree "div_fexp_or" final_exp
  let final_exp_zero := Wire.mk "div_fexp_zero"
  let final_exp_le0 := Wire.mk "div_fexp_le0"
  let subnormal_res := Wire.mk "div_subres"
  -- Overflow: the exponent saturated at 255.  A negative exponent (a subnormal
  -- result) also has the high bits set, so only a non-negative one can overflow.
  let (exp_rnd_low8, exp_rnd_low8_gates) := mkAndTree "div_ernd_l8" ((List.range 8).map fun i => exp_rnd[i]!)
  let exp_rnd_n9 := Wire.mk "div_ernd_n9"
  let ovf_cand := Wire.mk "div_ovf_cand"
  let ovf_pre := Wire.mk "div_ovf_pre"
  let ovf_res := Wire.mk "div_ovf"
  let ovf_to_inf := Wire.mk "div_ovftoinf"
  let ovf_not_to_inf := Wire.mk "div_ovfnti"
  let ovf_inf := Wire.mk "div_ovfinf"
  let ovf_max := Wire.mk "div_ovfmax"
  let subres_gates := [
    Gate.mkNOT final_exp_any final_exp_zero,
    Gate.mkOR final_exp_zero sub_neg final_exp_le0,
    Gate.mkBUF final_exp_le0 subnormal_res,
    -- Overflow is exponent 255 or more: bit 9 must be clear (that would be a
    -- negative exponent) and the low nine bits must reach 255.
    Gate.mkNOT (exp_rnd[9]!) exp_rnd_n9,
    Gate.mkOR (exp_rnd[8]!) exp_rnd_low8 ovf_cand,
    Gate.mkAND exp_rnd_n9 ovf_cand ovf_pre,
    Gate.mkBUF ovf_pre ovf_res,
    -- IEEE 754 section 7.4: an overflowing quotient is an infinity only when
    -- the rounding direction points away from zero for this sign.  Toward zero
    -- is rtz always, rdn for a positive quotient and rup for a negative one;
    -- round to nearest counts as away.  The other modes saturate to the
    -- largest finite magnitude.
    Gate.mkAND is_rdn not_sign (Wire.mk "div_ovf_tzrdn"),
    Gate.mkAND is_rup sign_q (Wire.mk "div_ovf_tzrup"),
    Gate.mkOR is_rtz (Wire.mk "div_ovf_tzrdn") (Wire.mk "div_ovf_tza"),
    Gate.mkOR (Wire.mk "div_ovf_tza") (Wire.mk "div_ovf_tzrup") (Wire.mk "div_ovf_tzany"),
    Gate.mkNOT (Wire.mk "div_ovf_tzany") ovf_to_inf,
    Gate.mkNOT ovf_to_inf ovf_not_to_inf,
    Gate.mkAND ovf_res ovf_to_inf ovf_inf,
    Gate.mkAND ovf_res ovf_not_to_inf ovf_max
  ]

  -- shift = 4 - final_exp, saturated past the width of the window
  let four_10 := (List.range 10).map fun i => if i == 2 then one else zero
  let sub_shift10 := makeIndexedWires "div_subsh10" 10
  let (sub_shift10_gates, _sub_shift10_borrow) :=
    mkKoggeStoneSub four_10 final_exp sub_shift10 "div_subsh10" one
  let (sub_over, sub_over_gates) := mkOrTree "div_subover" ((List.range 5).map fun i => sub_shift10[5 + i]!)
  let sub_shift := makeIndexedWires "div_subsh" 6
  let sub_shift_gates := (List.range 6).map fun i =>
    Gate.mkMUX (sub_shift10[i]!) one sub_over (sub_shift[i]!)

  -- Window: the implicit bit at 26, the fraction at [25:3], the guard/round field
  -- at [2:0].  Two zeros are prepended so the shifter output carries guard at 1,
  -- round at 0 and the mantissa from 2.
  let sub_window := makeIndexedWires "div_subwin" 27
  let sub_window_gates := [
    Gate.mkBUF zero (sub_window[0]!), Gate.mkBUF zero (sub_window[1]!),
    Gate.mkBUF zero (sub_window[2]!), Gate.mkBUF one (sub_window[26]!)
  ] ++ (List.range 23).map fun i => Gate.mkBUF (norm_mant[i]!) (sub_window[3 + i]!)
  let sub_in := [zero, zero] ++ sub_window
  let sub_shifted := makeIndexedWires "div_subshifted" 29
  let sub_sticky_shift := Wire.mk "div_substk"
  let sub_barrel_gates :=
    mkBarrelShiftRightSticky sub_in sub_shift sub_shifted sub_sticky_shift zero "div_sbr"
  let sub_R := sub_shifted[0]!
  let sub_G := sub_shifted[1]!
  let sub_mant := makeIndexedWires "div_submant" 23
  let sub_mant_gates := (List.range 23).map fun i =>
    Gate.mkBUF (sub_shifted[2 + i]!) (sub_mant[i]!)

  let sub_sticky := Wire.mk "div_substk_all"
  let sub_sticky_gate := Gate.mkOR sub_sticky_shift rem_nonzero sub_sticky
  let sub_rs_or := Wire.mk "div_subrs"
  let sub_rne := Wire.mk "div_subrne"
  let sub_rne_up := Wire.mk "div_subrneup"
  let sub_any_rem := Wire.mk "div_subany"
  let sub_rdn := Wire.mk "div_subrdn"
  let sub_rup := Wire.mk "div_subrup"
  let sub_t0 := Wire.mk "div_subt0"
  let sub_t1 := Wire.mk "div_subt1"
  let sub_round_pre := Wire.mk "div_subrpre"
  let sub_round := Wire.mk "div_subround"
  let sub_rnd_gates := [
    Gate.mkOR sub_R sub_sticky sub_rs_or,
    Gate.mkOR sub_rs_or (sub_mant[0]!) sub_rne,
    Gate.mkAND sub_G sub_rne sub_rne_up,
    Gate.mkOR sub_G sub_rs_or sub_any_rem,
    Gate.mkAND sub_any_rem sign_q sub_rdn,
    Gate.mkAND sub_any_rem not_sign sub_rup,
    Gate.mkMUX sub_rne_up sub_rdn is_rdn sub_t0,
    Gate.mkMUX sub_t0 sub_rup is_rup sub_t1,
    Gate.mkMUX sub_t1 sub_G is_rmm sub_round_pre,
    Gate.mkMUX sub_round_pre zero is_rtz sub_round
  ]

  let sub_inc := makeIndexedWires "div_subinc" 23
  let sub_c := makeIndexedWires "div_subc" 24
  let sub_inc_gates := [Gate.mkBUF sub_round (sub_c[0]!)] ++ (List.range 23).flatMap fun i =>
    [Gate.mkXOR (sub_mant[i]!) (sub_c[i]!) (sub_inc[i]!),
     Gate.mkAND (sub_mant[i]!) (sub_c[i]!) (sub_c[i + 1]!)]
  let sub_carry := sub_c[23]!
  let sub_not_carry := Wire.mk "div_subncarry"
  let sub_final_mant := makeIndexedWires "div_subfm" 23
  let sub_final_mant_gates := [Gate.mkNOT sub_carry sub_not_carry] ++
    (List.range 23).map fun i =>
      Gate.mkAND (sub_inc[i]!) sub_not_carry (sub_final_mant[i]!)

  -- The iterative result, before the special-case override below.
  let packed_result := makeIndexedWires "div_packed_res" 32

  -- A rounded-to-zero subnormal is zero; a carry out of the mantissa reaches the
  -- smallest normal, so the exponent field becomes 1.
  let (sub_mant_any, sub_mant_any_gates) := mkOrTree "div_submany" sub_final_mant
  let sub_mant_nz := Wire.mk "div_submnz"
  let sub_zero_pre := Wire.mk "div_subzpre"
  let sub_zero := Wire.mk "div_subzero"
  let sub_zero_gates := [
    Gate.mkNOT sub_mant_any sub_mant_nz,
    Gate.mkAND subnormal_res sub_not_carry sub_zero_pre,
    Gate.mkAND sub_zero_pre sub_mant_nz sub_zero
  ]

  let pre_pack := makeIndexedWires "div_prepack" 32
  -- Exponent+mantissa: normal, else subnormal, else the overflowing infinity,
  -- and a subnormal that rounded to zero becomes zero.
  let mkPackBit (i : Nat) : List Gate :=
    let normal_bit := if i < 23 then rounded_mant[i]! else exp_rnd[i - 23]!
    let sub_bit := if i < 23 then sub_final_mant[i]!
                   else if i == 23 then sub_carry else zero
    -- An infinity is exponent all ones with a zero fraction; the largest
    -- finite magnitude is the exponent field all ones minus one, so only its
    -- low bit (bit 23) differs, with an all-ones fraction.
    let ovf_inf_bit := if i < 23 then zero else one
    let ovf_max_bit := if i == 23 then zero else one
    let m1 := Wire.mk s!"div_pp1_{i}"
    let m2 := Wire.mk s!"div_pp2_{i}"
    let m3 := Wire.mk s!"div_pp3_{i}"
    [Gate.mkMUX normal_bit sub_bit subnormal_res m1,
     Gate.mkMUX m1 ovf_max_bit ovf_max m2,
     Gate.mkMUX m2 ovf_inf_bit ovf_inf m3,
     Gate.mkMUX m3 zero sub_zero (pre_pack[i]!)]
  let pre_pack_gates := (List.range 31).flatMap mkPackBit ++
    [Gate.mkBUF sign_q (pre_pack[31]!)]

  let result_mant_gates := (List.range 23).map (fun i => Gate.mkBUF (pre_pack[i]!) (packed_result[i]!))
  let result_exp_gates := (List.range 8).map (fun i => Gate.mkBUF (pre_pack[23 + i]!) (packed_result[23 + i]!))
  let result_sign_gate := [Gate.mkBUF (pre_pack[31]!) (packed_result[31]!)]


  -- tag_out[5:0] = BUF from tag_q
  let tag_out_gates := (List.range 6).map (fun i =>
    Gate.mkBUF (tag_q[i]!) (tag_out[i]!)
  )

  -- ══════════════════════════════════════════════
  -- Special cases: NaN, infinity, zero, divide-by-zero
  -- ══════════════════════════════════════════════
  -- Classified from the latched operands, so the selection needs no new state and
  -- the 23-cycle protocol is unchanged.  None of this existed before: the unit
  -- packed the iterative result whatever the operands were, so 1.0/0.0 came out as
  -- 0x7F000000 and 0.0/0.0 as 0x3F800000 -- which is one.
  let (e1_all1, e1_all1_gates) := mkAndTree "div_e1o" ((List.range 8).map fun i => src1_q[23 + i]!)
  let (e2_all1, e2_all1_gates) := mkAndTree "div_e2o" ((List.range 8).map fun i => src2_q[23 + i]!)
  let e1_nz_bits := (List.range 8).map fun i => Wire.mk s!"div_e1n_{i}"
  let e2_nz_bits := (List.range 8).map fun i => Wire.mk s!"div_e2n_{i}"
  let (e1_all0, e1_all0_gates) := mkAndTree "div_e1z" e1_nz_bits
  let (e2_all0, e2_all0_gates) := mkAndTree "div_e2z" e2_nz_bits
  let exp_zero_gates :=
    (List.range 8).flatMap (fun i =>
      [Gate.mkNOT (src1_q[23 + i]!) (e1_nz_bits[i]!),
       Gate.mkNOT (src2_q[23 + i]!) (e2_nz_bits[i]!)])
  let (m1_nz, m1_nz_gates) := mkOrTree "div_m1nz" ((List.range 23).map fun i => src1_q[i]!)
  let (m2_nz, m2_nz_gates) := mkOrTree "div_m2nz" ((List.range 23).map fun i => src2_q[i]!)
  let not_m1_nz := Wire.mk "div_nm1nz"
  let not_m2_nz := Wire.mk "div_nm2nz"
  let is_nan_a := Wire.mk "div_nan_a"
  let is_nan_b := Wire.mk "div_nan_b"
  let is_inf_a := Wire.mk "div_inf_a"
  let is_inf_b := Wire.mk "div_inf_b"
  let is_zero_a := Wire.mk "div_zero_a"
  let is_zero_b := Wire.mk "div_zero_b"
  let classify_gates := [
    Gate.mkNOT m1_nz not_m1_nz,
    Gate.mkNOT m2_nz not_m2_nz,
    Gate.mkAND e1_all1 m1_nz is_nan_a,
    Gate.mkAND e2_all1 m2_nz is_nan_b,
    Gate.mkAND e1_all1 not_m1_nz is_inf_a,
    Gate.mkAND e2_all1 not_m2_nz is_inf_b,
    Gate.mkAND e1_all0 not_m1_nz is_zero_a,
    Gate.mkAND e2_all0 not_m2_nz is_zero_b
  ]

  let any_nan := Wire.mk "div_any_nan"
  let both_inf := Wire.mk "div_both_inf"
  let both_zero := Wire.mk "div_both_zero"
  let nan_res := Wire.mk "div_nan_res"
  let not_any_nan := Wire.mk "div_not_any_nan"
  let dz_cond := Wire.mk "div_dz"
  let inf_res_a := Wire.mk "div_inf_res_a"
  let inf_res := Wire.mk "div_inf_res"
  let zero_res_a := Wire.mk "div_zero_res_a"
  let zero_res_b := Wire.mk "div_zero_res_b"
  let zero_res := Wire.mk "div_zero_res"
  -- NV comes from a signalling NaN operand or from an invalid operation
  -- (0/0, inf/inf).  A quiet NaN propagates without a flag.
  let a_is_snan := Wire.mk "div_snan_a"
  let b_is_snan := Wire.mk "div_snan_b"
  let any_snan := Wire.mk "div_any_snan"
  let not_a_quiet := Wire.mk "div_naq"
  let not_b_quiet := Wire.mk "div_nbq"
  let nv_pre1 := Wire.mk "div_nvp1"
  let nv_all := Wire.mk "div_nv_all"
  let snan_gates := [
    Gate.mkNOT (src1_q[22]!) not_a_quiet,
    Gate.mkAND is_nan_a not_a_quiet a_is_snan,
    Gate.mkNOT (src2_q[22]!) not_b_quiet,
    Gate.mkAND is_nan_b not_b_quiet b_is_snan,
    Gate.mkOR a_is_snan b_is_snan any_snan,
    Gate.mkOR both_zero both_inf nv_pre1,
    Gate.mkOR any_snan nv_pre1 nv_all
  ]
  let is_special := Wire.mk "div_is_special"
  let nza := Wire.mk "div_nza"
  let nia := Wire.mk "div_nia"
  let nib := Wire.mk "div_nib"
  let nzb := Wire.mk "div_nzb"
  let special_gates := [
    Gate.mkOR is_nan_a is_nan_b any_nan,
    Gate.mkAND is_inf_a is_inf_b both_inf,
    Gate.mkAND is_zero_a is_zero_b both_zero,
    Gate.mkOR any_nan both_zero (Wire.mk "div_nr_t0"),
    Gate.mkOR (Wire.mk "div_nr_t0") both_inf nan_res,
    Gate.mkNOT any_nan not_any_nan,
    Gate.mkNOT is_zero_a nza,
    Gate.mkNOT is_inf_a nia,
    Gate.mkAND is_zero_b nza (Wire.mk "div_dz_t0"),
    Gate.mkAND (Wire.mk "div_dz_t0") not_any_nan (Wire.mk "div_dz_t1"),
    Gate.mkAND (Wire.mk "div_dz_t1") nia dz_cond,
    Gate.mkNOT is_inf_b nib,
    Gate.mkAND is_inf_a nib (Wire.mk "div_ir_t0"),
    Gate.mkAND (Wire.mk "div_ir_t0") not_any_nan inf_res_a,
    Gate.mkOR inf_res_a dz_cond inf_res,
    Gate.mkNOT is_zero_b nzb,
    Gate.mkAND is_zero_a nzb (Wire.mk "div_zr_t0"),
    Gate.mkAND (Wire.mk "div_zr_t0") not_any_nan zero_res_a,
    Gate.mkAND is_inf_b nia (Wire.mk "div_zr_t1"),
    Gate.mkAND (Wire.mk "div_zr_t1") not_any_nan zero_res_b,
    Gate.mkOR zero_res_a zero_res_b zero_res,
    Gate.mkOR nan_res inf_res (Wire.mk "div_sp_t0"),
    Gate.mkOR (Wire.mk "div_sp_t0") zero_res is_special
  ]

  -- The special result: canonical NaN (0x7FC00000), signed infinity, signed zero.
  -- Infinity and zero keep the computed sign; the NaN is canonical, sign zero.
  let sp_res := makeIndexedWires "div_spres" 32
  let sp_res_gates := (List.range 32).flatMap fun i =>
    let nan_bit := if i == 22 || (i >= 23 && i <= 30) then one else zero
    let inf_bit := if i == 31 then sign_q else if i >= 23 && i <= 30 then one else zero
    let zero_bit := if i == 31 then sign_q else zero
    let t0 := Wire.mk s!"div_spb_{i}"
    [Gate.mkMUX zero_bit nan_bit nan_res (t0),
     Gate.mkMUX t0 inf_bit inf_res (sp_res[i]!)]

  let final_result_gates := (List.range 32).map fun i =>
    Gate.mkMUX (packed_result[i]!) (sp_res[i]!) is_special (result[i]!)

  -- Also OR in the guard bit (quotient bit that gets shifted out during normalization)
  -- For now, just use remainder non-zero as NX
  -- The bit the normalizing shift drops is part of the remainder too.
  let nx_guard := Wire.mk "div_nx_guard"
  let nx_all := Wire.mk "div_nx_all"
  let nx_guard_gate := Gate.mkAND norm_needed (quot_q[0]!) nx_guard
  let nx_all_gate := Gate.mkOR rem_nonzero nx_guard nx_all

  -- fflags: bit0=NX bit1=UF bit2=OF bit3=DZ bit4=NV.
  -- The subnormal path measures its own remainder, and a saturated result is
  -- inexact too.  UF needs a tiny *and* inexact result: a carry out of the
  -- subnormal mantissa reaches the smallest normal, which is not tiny.
  let not_special_nx := Wire.mk "div_not_special_nx"
  let nx_final := Wire.mk "div_nx_final"
  let nx_sel := Wire.mk "div_nx_sel"
  let nx_of := Wire.mk "div_nx_of"
  let uf_pre := Wire.mk "div_uf_pre"
  let is_underflow := Wire.mk "div_uf"
  let exc_gates := rem_or_tree ++ [
    Gate.mkBUF nx_final (exc[0]!),
    Gate.mkAND is_underflow not_special_nx (exc[1]!),
    Gate.mkAND ovf_res not_special_nx (exc[2]!),
    Gate.mkBUF dz_cond (exc[3]!),
    Gate.mkBUF nv_all (exc[4]!),
    Gate.mkNOT is_special not_special_nx,
    Gate.mkMUX nx_all sub_any_rem subnormal_res nx_sel,
    Gate.mkOR nx_sel ovf_res nx_of,
    Gate.mkAND nx_of not_special_nx nx_final,
    Gate.mkAND subnormal_res sub_not_carry uf_pre,
    Gate.mkAND uf_pre sub_any_rem is_underflow
  ]

  -- valid_out = done
  let valid_gate := [Gate.mkBUF done valid_out]

  -- busy output = busy_q
  let busy_gate := [Gate.mkBUF busy_q busy_out]

  -- ══════════════════════════════════════════════
  -- Assemble all gates
  -- ══════════════════════════════════════════════
  let all_gates :=
    ctrl_gates ++
    busy_gates ++
    cnt_inc_gates ++
    cnt_mux_gates ++
    src1_mux_gates ++
    src2_mux_gates ++
    rm_mux_gates ++
    tag_mux_gates ++
    -- Division datapath: initialization
    sign_gates ++
    snan_gates ++
    exp_sub_gates ++
    exp_add_gates ++
    exp_mux_gates ++
    div_mant_mux_gates ++
    -- Pre-comparison (first quotient bit)
    pre_sub_gates ++
    pre_q_gate ++
    init_rem_gates ++
    f1_nz_gates ++ f2_nz_gates ++ exp1_or_gates ++ exp2_or_gates ++ sub_op_gates ++
    lead1_gates ++ lead2_gates ++ pos1_gates ++ pos2_gates ++
    sh1_gates ++ sh2_gates ++ norm1_gates ++ norm2_gates ++ mant_gates ++
    eff1_gates ++ eff2_gates ++ exp_norm_gates ++
    -- Division datapath: per-cycle step
    rem_shift_gates ++
    trial_sub_gates ++
    q_bit_gate ++
    new_rem_gates ++
    new_quot_gates ++
    rem_mux_gates ++
    quot_mux_gates ++
    -- DFFs
    src1_dffs ++
    src2_dffs ++
    rm_dffs ++
    tag_dffs ++
    cnt_dffs ++
    busy_dff ++
    sign_dff ++
    exp_dffs ++
    div_mant_dffs ++
    rem_dffs ++
    quot_dffs ++
    -- Output normalization and packing
    norm_gate ++
    norm_mant_gates ++
    dec_gates ++
    final_exp_gates ++
    -- Subnormal and overflowing results
    final_exp_any_gates ++ subres_gates ++ exp_rnd_low8_gates ++
    sub_shift10_gates ++ sub_over_gates ++ sub_shift_gates ++
    sub_window_gates ++ sub_barrel_gates ++ sub_mant_gates ++ [sub_sticky_gate] ++
    sub_rnd_gates ++ sub_inc_gates ++ sub_final_mant_gates ++
    sub_mant_any_gates ++ sub_zero_gates ++ pre_pack_gates ++
    e1_all1_gates ++ e2_all1_gates ++ exp_zero_gates ++ e1_all0_gates ++ e2_all0_gates ++
    m1_nz_gates ++ m2_nz_gates ++ classify_gates ++ special_gates ++ sp_res_gates ++
    scale_gates ++ cmp_sub_gates ++ cmp_eq_pre_gates ++ cmp_eq_tree ++ any_rem_tree ++
    rnd_cond_gates ++ rnd_inc_gates ++ rnd_mant_gates ++ exp_rnd_gates ++
    result_mant_gates ++
    result_exp_gates ++
    result_sign_gate ++
    final_result_gates ++
    tag_out_gates ++
    [nx_guard_gate, nx_all_gate] ++
    exc_gates ++
    valid_gate ++
    busy_gate

  { name := "FPDivider"
    inputs := src1_in ++ src2_in ++ rm_in ++ dest_tag ++
              [start, clock, reset, zero, one]
    outputs := result ++ tag_out ++ exc ++ [valid_out, busy_out]
    gates := all_gates
    instances := []
    signalGroups := [
      { name := "src1", width := 32, wires := src1_in },
      { name := "src2", width := 32, wires := src2_in },
      { name := "rm", width := 3, wires := rm_in },
      { name := "dest_tag", width := 6, wires := dest_tag },
      { name := "result", width := 32, wires := result },
      { name := "tag_out", width := 6, wires := tag_out },
      { name := "exc", width := 5, wires := exc },
      { name := "cnt_q", width := 5, wires := cnt_q },
      { name := "exp_q", width := 10, wires := exp_q },
      { name := "rem_q", width := 25, wires := rem_q },
      { name := "quot_q", width := 24, wires := quot_q },
      { name := "div_mant_q", width := 24, wires := div_mant_q }
    ]
  }

/-- Convenience definition for the FP divider circuit. -/
def fpDividerCircuit : Circuit := mkFPDivider

end Shoumei.Circuits.Sequential
