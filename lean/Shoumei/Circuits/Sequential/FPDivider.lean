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
import Shoumei.Circuits.Combinational.RippleCarryAdder

namespace Shoumei.Circuits.Sequential

open Shoumei
open Shoumei.Circuits.Combinational

/-! ## Helper: Indexed Wire Generation -/

private def makeIndexedWires (pfx : String) (n : Nat) : List Wire :=
  (List.range n).map fun i => Wire.mk (pfx ++ "_" ++ toString i)

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
  let exp_q := makeIndexedWires "exp_q" 8
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
  let exp_d := makeIndexedWires "exp_d" 8
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
  -- Exponent computation: res_exp = exp1 - exp2 + 127
  -- ══════════════════════════════════════════════
  -- Step 1: 8-bit subtraction diff = exp1 - exp2 (ripple subtractor)
  let exp_diff := makeIndexedWires "exp_diff" 8
  let sub_borrow := makeIndexedWires "sub_borrow" 9  -- borrow chain

  -- exp1 = src1_in[30:23], exp2 = src2_in[30:23]
  let exp_sub_gates :=
    [Gate.mkBUF zero (sub_borrow[0]!)] ++  -- initial borrow = 0
    (List.range 8).flatMap (fun i =>
      let a := src1_in[23 + i]!  -- exp1[i]
      let b := src2_in[23 + i]!  -- exp2[i]
      let bi := sub_borrow[i]!
      let xab := Wire.mk s!"exp_sub_xab_{i}"
      let diff_bit := exp_diff[i]!
      let not_a := Wire.mk s!"exp_sub_na_{i}"
      let t0 := Wire.mk s!"exp_sub_t0_{i}"
      let t1 := Wire.mk s!"exp_sub_t1_{i}"
      let t2 := Wire.mk s!"exp_sub_t2_{i}"
      let t01 := Wire.mk s!"exp_sub_t01_{i}"
      let bo := sub_borrow[i + 1]!
      [
        Gate.mkXOR a b xab,
        Gate.mkXOR xab bi diff_bit,
        -- borrow_out = (!a & b) | (!a & bi) | (b & bi)
        Gate.mkNOT a not_a,
        Gate.mkAND not_a b t0,
        Gate.mkAND not_a bi t1,
        Gate.mkAND b bi t2,
        Gate.mkOR t0 t1 t01,
        Gate.mkOR t01 t2 bo
      ]
    )

  -- Step 2: 8-bit addition init_exp = diff + 127 (01111111)
  -- bias[7]=0, bias[6:0]=1
  let init_exp := makeIndexedWires "init_exp" 8
  let add_carry := makeIndexedWires "add_carry" 9
  let bias_bits : List Wire := (List.range 8).map (fun i =>
    if i < 7 then one else zero  -- bits 0..6 = 1, bit 7 = 0
  )

  let exp_add_gates :=
    [Gate.mkBUF zero (add_carry[0]!)] ++  -- initial carry = 0
    (List.range 8).flatMap (fun i =>
      let a := exp_diff[i]!
      let b := bias_bits[i]!
      let ci := add_carry[i]!
      let xab := Wire.mk s!"exp_add_xab_{i}"
      let sum_bit := init_exp[i]!
      let t0 := Wire.mk s!"exp_add_t0_{i}"
      let t1 := Wire.mk s!"exp_add_t1_{i}"
      let t2 := Wire.mk s!"exp_add_t2_{i}"
      let t01 := Wire.mk s!"exp_add_t01_{i}"
      let co := add_carry[i + 1]!
      [
        Gate.mkXOR a b xab,
        Gate.mkXOR xab ci sum_bit,
        Gate.mkAND a b t0,
        Gate.mkAND a ci t1,
        Gate.mkAND b ci t2,
        Gate.mkOR t0 t1 t01,
        Gate.mkOR t01 t2 co
      ]
    )

  -- exp_d MUX: hold or load init on start_new
  let exp_mux_gates := (List.range 8).map (fun i =>
    Gate.mkMUX (exp_q[i]!) (init_exp[i]!) start_new (exp_d[i]!)
  )

  -- ══════════════════════════════════════════════
  -- Divisor mantissa: init = {1, src2[22:0]}
  -- Hold after start (only loaded once on start_new)
  -- ══════════════════════════════════════════════
  let div_mant_mux_gates := (List.range 24).map (fun i =>
    let init_bit := if i == 23 then one else src2_in[i]!  -- implicit leading 1 at bit 23
    Gate.mkMUX (div_mant_q[i]!) init_bit start_new (div_mant_d[i]!)
  )

  -- ══════════════════════════════════════════════
  -- Pre-comparison: dividend_mant - divisor_mant (on start_new)
  -- Determines first quotient bit and initial remainder
  -- ══════════════════════════════════════════════
  let pre_trial := makeIndexedWires "pre_trial" 25
  let pre_borrow := makeIndexedWires "pre_borrow" 26

  -- dividend_mant = {1, src1_in[22:0]}, divisor_mant = {1, src2_in[22:0]}
  -- Extend both to 25 bits (bit 24 = 0)
  let pre_sub_gates :=
    [Gate.mkBUF zero (pre_borrow[0]!)] ++
    (List.range 25).flatMap (fun i =>
      let a := if i == 24 then zero
               else if i == 23 then one
               else src1_in[i]!  -- dividend mantissa
      let b := if i == 24 then zero
               else if i == 23 then one
               else src2_in[i]!  -- divisor mantissa
      let bi := pre_borrow[i]!
      let xab := Wire.mk s!"pre_xab_{i}"
      let diff_bit := pre_trial[i]!
      let not_a := Wire.mk s!"pre_na_{i}"
      let t0 := Wire.mk s!"pre_t0_{i}"
      let t1 := Wire.mk s!"pre_t1_{i}"
      let t2 := Wire.mk s!"pre_t2_{i}"
      let t01 := Wire.mk s!"pre_t01_{i}"
      let bo := pre_borrow[i + 1]!
      [
        Gate.mkXOR a b xab,
        Gate.mkXOR xab bi diff_bit,
        Gate.mkNOT a not_a,
        Gate.mkAND not_a b t0,
        Gate.mkAND not_a bi t1,
        Gate.mkAND b bi t2,
        Gate.mkOR t0 t1 t01,
        Gate.mkOR t01 t2 bo
      ]
    )

  -- pre_q = NOT(borrow at bit 24) = 1 if dividend >= divisor
  let pre_q := Wire.mk "pre_q"
  let pre_q_gate := [Gate.mkNOT (pre_borrow[25]!) pre_q]

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

  -- 25-bit subtractor: trial = rem_shifted - {0, div_mant_q}
  -- divisor_ext[23:0] = div_mant_q, divisor_ext[24] = 0
  let trial := makeIndexedWires "trial" 25
  let trial_borrow := makeIndexedWires "trial_borrow" 26

  let trial_sub_gates :=
    [Gate.mkBUF zero (trial_borrow[0]!)] ++
    (List.range 25).flatMap (fun i =>
      let a := rem_shifted[i]!
      let b := if i < 24 then div_mant_q[i]! else zero  -- divisor_ext[24] = 0
      let bi := trial_borrow[i]!
      let xab := Wire.mk s!"trial_xab_{i}"
      let diff_bit := trial[i]!
      let not_a := Wire.mk s!"trial_na_{i}"
      let t0 := Wire.mk s!"trial_t0_{i}"
      let t1 := Wire.mk s!"trial_t1_{i}"
      let t2 := Wire.mk s!"trial_t2_{i}"
      let t01 := Wire.mk s!"trial_t01_{i}"
      let bo := trial_borrow[i + 1]!
      [
        Gate.mkXOR a b xab,
        Gate.mkXOR xab bi diff_bit,
        Gate.mkNOT a not_a,
        Gate.mkAND not_a b t0,
        Gate.mkAND not_a bi t1,
        Gate.mkAND b bi t2,
        Gate.mkOR t0 t1 t01,
        Gate.mkOR t01 t2 bo
      ]
    )

  -- q_bit = NOT trial[24] (no borrow means positive, quotient bit = 1)
  let q_bit := Wire.mk "q_bit"
  let q_bit_gate := [Gate.mkNOT (trial[24]!) q_bit]

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
  --           if pre_q=0 (dividend<divisor):  {0, 1, src1_in[22:0]}
  -- ══════════════════════════════════════════════
  let init_rem := makeIndexedWires "init_rem" 25
  let init_rem_gates := (List.range 25).map (fun i =>
    let orig_bit :=
      if i == 24 then zero
      else if i == 23 then one
      else src1_in[i]!
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
  let exp_dffs := (List.range 8).map (fun i =>
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
  let dec_exp := makeIndexedWires "dec_exp" 8
  let dec_borrow := makeIndexedWires "dec_borrow" 8
  let dec_gates :=
    -- bit 0
    [
      Gate.mkNOT (exp_q[0]!) (dec_exp[0]!),
      Gate.mkNOT (exp_q[0]!) (dec_borrow[0]!)
    ] ++
    -- bits 1..7
    (List.range 7).flatMap (fun j =>
      let i := j + 1
      let not_exp := Wire.mk s!"dec_nexp_{i}"
      [
        Gate.mkXOR (exp_q[i]!) (dec_borrow[i - 1]!) (dec_exp[i]!),
        Gate.mkNOT (exp_q[i]!) not_exp,
        Gate.mkAND not_exp (dec_borrow[i - 1]!) (dec_borrow[i]!)
      ]
    )

  -- final_exp[i] = MUX(exp_q[i], dec_exp[i], norm_needed)
  let final_exp := makeIndexedWires "final_exp" 8
  let final_exp_gates := (List.range 8).map (fun i =>
    Gate.mkMUX (exp_q[i]!) (dec_exp[i]!) norm_needed (final_exp[i]!)
  )

  -- result[22:0] = norm_mant[22:0]
  let result_mant_gates := (List.range 23).map (fun i =>
    Gate.mkBUF (norm_mant[i]!) (result[i]!)
  )

  -- result[30:23] = final_exp[7:0]
  let result_exp_gates := (List.range 8).map (fun i =>
    Gate.mkBUF (final_exp[i]!) (result[23 + i]!)
  )

  -- result[31] = sign_q
  let result_sign_gate := [Gate.mkBUF sign_q (result[31]!)]

  -- tag_out[5:0] = BUF from tag_q
  let tag_out_gates := (List.range 6).map (fun i =>
    Gate.mkBUF (tag_q[i]!) (tag_out[i]!)
  )

  -- exc[4:0] = all zero (placeholder)
  let exc_gates := (List.range 5).map (fun i =>
    Gate.mkBUF zero (exc[i]!)
  )

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
    exp_sub_gates ++
    exp_add_gates ++
    exp_mux_gates ++
    div_mant_mux_gates ++
    -- Pre-comparison (first quotient bit)
    pre_sub_gates ++
    pre_q_gate ++
    init_rem_gates ++
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
    result_mant_gates ++
    result_exp_gates ++
    result_sign_gate ++
    tag_out_gates ++
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
      { name := "exp_q", width := 8, wires := exp_q },
      { name := "rem_q", width := 25, wires := rem_q },
      { name := "quot_q", width := 24, wires := quot_q },
      { name := "div_mant_q", width := 24, wires := div_mant_q }
    ]
  }

/-- Convenience definition for the FP divider circuit. -/
def fpDividerCircuit : Circuit := mkFPDivider

end Shoumei.Circuits.Sequential
