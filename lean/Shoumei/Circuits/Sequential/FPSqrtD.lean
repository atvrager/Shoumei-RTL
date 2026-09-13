/-
Circuits/Sequential/FPSqrtD.lean - 54-Cycle Iterative Double-Precision FP Square Root

An iterative floating-point square root unit for IEEE 754 binary64.
Takes a 64-bit source operand and produces the square root over 54 cycles.

Algorithm:
  Restoring square root of 53-bit mantissa.
  - Detects special cases (±0, +inf, negative, NaN, sNaN)
  - Exponent computation: init_exp = (exp + 1023) >> 1
  - Sets up radicand in 56-bit shift register based on exponent parity (exp_odd)
  - 54 cycles of trial subtraction: trial = 4 * root + 1
  - Produces 54 root bits (bit 53 = 1, bits 52..1 = fraction, bit 0 = guard)
  - IEEE 754 rounding (RNE, RTZ, RDN, RUP, RMM) with mantissa rollover
  - Outputs result[63:0], tag_out[5:0], exc[4:0] (NV, NX), valid_out, busy

Interface:
- Inputs: src1[63:0], rm[2:0], dest_tag[5:0], start, clock, reset, zero, one
- Outputs: result[63:0], tag_out[5:0], exc[4:0], valid_out, busy
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.KoggeStoneAdder

namespace Shoumei.Circuits.Sequential

open Shoumei
open Shoumei.Circuits.Combinational

private def makeIndexedWires (pfx : String) (n : Nat) : List Wire :=
  (List.range n).map fun i => Wire.mk (pfx ++ "_" ++ toString i)

private def mkOrChain (wires : List Wire) (pfx : String) : List Gate × Wire :=
  match wires with
  | [] => ([], Wire.mk "zero")
  | [w] => ([], w)
  | w0 :: rest =>
    rest.enum.foldl (fun (gates, cur) (i, w) =>
      let nxt := Wire.mk s!"{pfx}_{i}"
      (gates ++ [Gate.mkOR cur w nxt], nxt)
    ) ([], w0)

private def mkAndChain (wires : List Wire) (pfx : String) : List Gate × Wire :=
  match wires with
  | [] => ([], Wire.mk "one")
  | [w] => ([], w)
  | w0 :: rest =>
    rest.enum.foldl (fun (gates, cur) (i, w) =>
      let nxt := Wire.mk s!"{pfx}_{i}"
      (gates ++ [Gate.mkAND cur w nxt], nxt)
    ) ([], w0)

/-- Build the 54-cycle iterative DP FP square root structural circuit. -/
def mkFPSqrtD : Circuit :=
  let src1_in := makeIndexedWires "src1" 64
  let rm_in := makeIndexedWires "rm" 3
  let dest_tag := makeIndexedWires "dest_tag" 6
  let start := Wire.mk "start"
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  let result := makeIndexedWires "result" 64
  let tag_out := makeIndexedWires "tag_out" 6
  let exc := makeIndexedWires "exc" 5
  let valid_out := Wire.mk "valid_out"
  let busy_out := Wire.mk "busy"

  -- State registers
  let src1_q := makeIndexedWires "src1_q" 64
  let rm_q := makeIndexedWires "rm_q" 3
  let tag_q := makeIndexedWires "tag_q" 6
  let cnt_q := makeIndexedWires "cnt_q" 6
  let busy_q := Wire.mk "busy_q"

  let exp_q := makeIndexedWires "exp_q" 11
  let rem_q := makeIndexedWires "rem_q" 57
  let root_q := makeIndexedWires "root_q" 54
  let mant_q := makeIndexedWires "mant_q" 56
  let is_special_q := Wire.mk "is_special_q"
  let sp_res_q := makeIndexedWires "sp_res_q" 64
  let sp_exc_q := makeIndexedWires "sp_exc_q" 5

  -- Next-state wires
  let src1_d := makeIndexedWires "src1_d" 64
  let rm_d := makeIndexedWires "rm_d" 3
  let tag_d := makeIndexedWires "tag_d" 6
  let cnt_d := makeIndexedWires "cnt_d" 6
  let busy_d := Wire.mk "busy_d"

  let exp_d := makeIndexedWires "exp_d" 11
  let rem_d := makeIndexedWires "rem_d" 57
  let root_d := makeIndexedWires "root_d" 54
  let mant_d := makeIndexedWires "mant_d" 56
  let is_special_d := Wire.mk "is_special_d"
  let sp_res_d := makeIndexedWires "sp_res_d" 64
  let sp_exc_d := makeIndexedWires "sp_exc_d" 5

  -- Control
  let not_busy := Wire.mk "not_busy"
  let start_new := Wire.mk "start_new"
  let done := Wire.mk "done"
  let not_done := Wire.mk "not_done"
  let busy_and_not_done := Wire.mk "busy_and_not_done"

  let ctrl_gates := [
    Gate.mkNOT busy_q not_busy,
    Gate.mkAND start not_busy start_new,
    Gate.mkNOT done not_done,
    Gate.mkAND busy_q not_done busy_and_not_done,
    Gate.mkOR start_new busy_and_not_done busy_d,
    Gate.mkBUF busy_q busy_out
  ]

  -- Done detection: cnt_q == 53 (0b110101)
  let cnt_is_53 := Wire.mk "cnt_is_53"
  let not_cnt1 := Wire.mk "not_cnt1"
  let not_cnt3 := Wire.mk "not_cnt3"
  let done_gates := [
    Gate.mkNOT (cnt_q[1]!) not_cnt1,
    Gate.mkNOT (cnt_q[3]!) not_cnt3,
    Gate.mkAND (cnt_q[0]!) not_cnt1 (Wire.mk "d_t0"),
    Gate.mkAND (cnt_q[2]!) not_cnt3 (Wire.mk "d_t1"),
    Gate.mkAND (cnt_q[4]!) (cnt_q[5]!) (Wire.mk "d_t2"),
    Gate.mkAND (Wire.mk "d_t0") (Wire.mk "d_t1") (Wire.mk "d_t3"),
    Gate.mkAND (Wire.mk "d_t3") (Wire.mk "d_t2") cnt_is_53,
    Gate.mkAND busy_q cnt_is_53 done,
    Gate.mkBUF done valid_out
  ]

  -- Counter increment
  let inc_carry := makeIndexedWires "inc_c" 7
  let cnt_next := makeIndexedWires "cnt_next" 6
  let cnt_inc_gates :=
    [Gate.mkBUF one (inc_carry[0]!)] ++
    (List.range 6).flatMap (fun i =>
      [Gate.mkXOR (cnt_q[i]!) (inc_carry[i]!) (cnt_next[i]!),
       Gate.mkAND (cnt_q[i]!) (inc_carry[i]!) (inc_carry[i + 1]!)]
    )

  let cnt_m1 := makeIndexedWires "cnt_m1" 6
  let cnt_mux_gates := (List.range 6).flatMap (fun i => [
    Gate.mkMUX (cnt_q[i]!) (cnt_next[i]!) busy_and_not_done (cnt_m1[i]!),
    Gate.mkMUX (cnt_m1[i]!) zero start_new (cnt_d[i]!)
  ])

  -- Operand fields
  let sign_a := src1_in[63]!
  let exp_a := (List.range 11).map fun i => src1_in[52 + i]!
  let frac_a := (List.range 52).map fun i => src1_in[i]!

  -- Classification
  let (ea_ao_gates, exp_all_ones) := mkAndChain exp_a "sq_ea_ao"
  let (ea_oz_gates, exp_any_set) := mkOrChain exp_a "sq_ea_oz"
  let exp_all_zeros := Wire.mk "sq_exp_all_zeros"
  let ea_allz_gate := Gate.mkNOT exp_any_set exp_all_zeros
  let (fa_any_gates, frac_any_set) := mkOrChain frac_a "sq_fa_any"

  let not_frac_any := Wire.mk "sq_not_frac_any"
  let not_sign_a := Wire.mk "sq_not_sign_a"
  let is_zero := Wire.mk "sq_is_zero"
  let not_is_zero := Wire.mk "sq_not_is_zero"
  let is_inf := Wire.mk "sq_is_inf"
  let is_nan := Wire.mk "sq_is_nan"
  let not_src1_51 := Wire.mk "sq_not_src1_51"
  let is_snan := Wire.mk "sq_is_snan"
  let is_neg_nonzero := Wire.mk "sq_is_neg_nonzero"
  let is_neg_or_snan := Wire.mk "sq_is_neg_or_snan"
  let is_special := Wire.mk "sq_is_special"

  let class_gates := [
    Gate.mkNOT frac_any_set not_frac_any,
    Gate.mkNOT sign_a not_sign_a,
    Gate.mkAND exp_all_zeros not_frac_any is_zero,
    Gate.mkNOT is_zero not_is_zero,
    Gate.mkAND exp_all_ones not_frac_any (Wire.mk "sq_inf_t0"),
    Gate.mkAND (Wire.mk "sq_inf_t0") not_sign_a is_inf,
    Gate.mkAND exp_all_ones frac_any_set is_nan,
    Gate.mkNOT (src1_in[51]!) not_src1_51,
    Gate.mkAND is_nan not_src1_51 is_snan,
    Gate.mkAND sign_a not_is_zero is_neg_nonzero,
    Gate.mkOR is_neg_nonzero is_snan is_neg_or_snan,

    Gate.mkOR is_zero is_inf (Wire.mk "sq_sp_01"),
    Gate.mkOR is_nan is_neg_nonzero (Wire.mk "sq_sp_23"),
    Gate.mkOR (Wire.mk "sq_sp_01") (Wire.mk "sq_sp_23") is_special
  ]

  -- Special result generation:
  -- if is_neg_or_snan | is_nan: canonical NaN 0x7ff8000000000000
  -- else if is_inf: +Inf 0x7ff0000000000000
  -- else (is_zero): src1_in (±0)
  let nan_target := Wire.mk "sq_nan_target"
  let nan_target_gate := Gate.mkOR is_neg_or_snan is_nan nan_target

  let sp_res_wire := makeIndexedWires "sq_sp_res" 64
  let sp_res_gates := (List.range 64).flatMap fun i =>
    if i < 51 then
      -- 0 for NaN/Inf, src1_in for Zero (which is 0 anyway)
      [Gate.mkBUF zero (sp_res_wire[i]!)]
    else if i == 51 then
      -- 1 for NaN, 0 for Inf, src1_in for Zero (0)
      [Gate.mkBUF nan_target (sp_res_wire[i]!)]
    else if i >= 52 && i <= 62 then
      -- 1 for NaN/Inf, 0 for Zero
      let exp_bit := Wire.mk s!"sq_sp_exp_{i}"
      [Gate.mkOR nan_target is_inf exp_bit,
       Gate.mkBUF exp_bit (sp_res_wire[i]!)]
    else
      -- bit 63 (sign): 0 for NaN/Inf, src1_in[63] for Zero
      let sign_bit := Wire.mk "sq_sp_sign"
      [Gate.mkAND is_zero sign_a sign_bit,
       Gate.mkBUF sign_bit (sp_res_wire[63]!)]

  let sp_exc_wire := makeIndexedWires "sq_sp_exc" 5
  let sp_exc_gates := [
    Gate.mkBUF zero (sp_exc_wire[0]!),  -- NX
    Gate.mkBUF zero (sp_exc_wire[1]!),  -- UF
    Gate.mkBUF zero (sp_exc_wire[2]!),  -- OF
    Gate.mkBUF zero (sp_exc_wire[3]!),  -- DZ
    Gate.mkBUF is_neg_or_snan (sp_exc_wire[4]!)  -- NV
  ]

  -- Normal Sqrt Setup:
  -- exp_odd = NOT src1_in[52]
  let exp_odd := Wire.mk "sq_exp_odd"
  let exp_odd_gate := Gate.mkNOT (src1_in[52]!) exp_odd

  -- init_exp = (exp_a + 1023) >> 1
  let exp_a_12 := exp_a ++ [zero]
  let bias_12 : List Wire := (List.range 12).map fun i => if i < 10 then one else zero
  let exp_sum := makeIndexedWires "sq_exp_sum" 12
  let (ea_add_gates, _) := mkKoggeStoneAdd exp_a_12 bias_12 zero exp_sum "sq_ea_add"
  let init_exp := (List.range 11).map fun i => exp_sum[i + 1]!

  -- mant_init (56 bits):
  -- if exp_odd == 0 (even): bit 54=1, bits 53..2=frac, bits 1..0=0, bit 55=0
  -- if exp_odd == 1 (odd):  bit 55=1, bits 54..3=frac, bits 2..0=0
  let mant_init := makeIndexedWires "sq_mant_init" 56
  let mant_init_gates := (List.range 56).map fun i =>
    let even_bit :=
      if i < 2 then zero
      else if i <= 53 then frac_a[i - 2]!
      else if i == 54 then one
      else zero
    let odd_bit :=
      if i < 3 then zero
      else if i <= 54 then frac_a[i - 3]!
      else one
    Gate.mkMUX even_bit odd_bit exp_odd (mant_init[i]!)

  -- Iteration step logic (54 cycles):
  -- rad_hi = mant_q[55], rad_lo = mant_q[54]
  let rad_hi := mant_q[55]!
  let rad_lo := mant_q[54]!

  -- rem_shifted = {rem_q[54:0], rad_hi, rad_lo} (57 bits)
  let rem_shifted := [rad_lo, rad_hi] ++ (List.range 55).map (fun i => rem_q[i]!)

  -- trial_val = {1'b0, root_q[53:0], 1'b0, 1'b1} (57 bits)
  let trial_val := [one, zero] ++ (List.range 54).map (fun i => root_q[i]!) ++ [zero]

  let trial_diff := makeIndexedWires "sq_trial_diff" 57
  let (trial_sub_gates, trial_borrow) := mkKoggeStoneSub rem_shifted trial_val trial_diff "sq_step_sub" one
  let accept := Wire.mk "sq_accept"
  let accept_gate := Gate.mkNOT trial_borrow accept

  let new_rem := makeIndexedWires "sq_new_rem" 57
  let new_rem_gates := (List.range 57).map fun i =>
    Gate.mkMUX (trial_diff[i]!) (rem_shifted[i]!) trial_borrow (new_rem[i]!)

  let new_root := [accept] ++ (List.range 53).map (fun i => root_q[i]!)

  -- mant_shifted = {mant_q[53:0], 2'b00} (56 bits)
  let mant_shifted := [zero, zero] ++ (List.range 54).map (fun i => mant_q[i]!)

  -- Next-state registers muxing
  let rem_m1 := makeIndexedWires "sq_rem_m1" 57
  let rem_mux_gates := (List.range 57).flatMap fun i => [
    Gate.mkMUX (rem_q[i]!) (new_rem[i]!) busy_and_not_done (rem_m1[i]!),
    Gate.mkMUX (rem_m1[i]!) zero start_new (rem_d[i]!)
  ]

  let root_m1 := makeIndexedWires "sq_root_m1" 54
  let root_mux_gates := (List.range 54).flatMap fun i => [
    Gate.mkMUX (root_q[i]!) (new_root[i]!) busy_and_not_done (root_m1[i]!),
    Gate.mkMUX (root_m1[i]!) zero start_new (root_d[i]!)
  ]

  let mant_m1 := makeIndexedWires "sq_mant_m1" 56
  let mant_mux_gates := (List.range 56).flatMap fun i => [
    Gate.mkMUX (mant_q[i]!) (mant_shifted[i]!) busy_and_not_done (mant_m1[i]!),
    Gate.mkMUX (mant_m1[i]!) (mant_init[i]!) start_new (mant_d[i]!)
  ]

  let exp_mux_gates := (List.range 11).map fun i =>
    Gate.mkMUX (exp_q[i]!) (init_exp[i]!) start_new (exp_d[i]!)

  let sp_flag_mux := Gate.mkMUX is_special_q is_special start_new is_special_d
  let sp_res_mux_gates := (List.range 64).map fun i =>
    Gate.mkMUX (sp_res_q[i]!) (sp_res_wire[i]!) start_new (sp_res_d[i]!)
  let sp_exc_mux_gates := (List.range 5).map fun i =>
    Gate.mkMUX (sp_exc_q[i]!) (sp_exc_wire[i]!) start_new (sp_exc_d[i]!)

  let src1_mux_gates := (List.range 64).map fun i =>
    Gate.mkMUX (src1_q[i]!) (src1_in[i]!) start_new (src1_d[i]!)
  let rm_mux_gates := (List.range 3).map fun i =>
    Gate.mkMUX (rm_q[i]!) (rm_in[i]!) start_new (rm_d[i]!)
  let tag_mux_gates := (List.range 6).map fun i =>
    Gate.mkMUX (tag_q[i]!) (dest_tag[i]!) start_new (tag_d[i]!)

  -- Output bypass & rounding on done:
  let out_root := new_root
  let out_rem := new_rem
  let (sticky_gates, sticky) := mkOrChain out_rem "sq_stk"

  let frac_out := (List.range 52).map fun i => out_root[1 + i]!
  let guard := out_root[0]!

  let any_round := Wire.mk "sq_any_round"
  let rnd_cond_gate := Gate.mkOR guard sticky any_round

  -- Rounding mode decoding
  let not_rm0 := Wire.mk "sq_not_rm0"
  let not_rm1 := Wire.mk "sq_not_rm1"
  let not_rm2 := Wire.mk "sq_not_rm2"
  let rm_is_0 := Wire.mk "sq_rm_is_0"
  let rm_is_1 := Wire.mk "sq_rm_is_1"
  let rm_is_2 := Wire.mk "sq_rm_is_2"
  let rm_is_3 := Wire.mk "sq_rm_is_3"
  let rm_is_4 := Wire.mk "sq_rm_is_4"
  let rm_is_7 := Wire.mk "sq_rm_is_7"
  let rm_is_rne := Wire.mk "sq_rm_is_rne"

  let rm_dec_gates := [
    Gate.mkNOT (rm_q[0]!) not_rm0,
    Gate.mkNOT (rm_q[1]!) not_rm1,
    Gate.mkNOT (rm_q[2]!) not_rm2,
    Gate.mkAND not_rm2 not_rm1 (Wire.mk "sq_rm0_t"),
    Gate.mkAND (Wire.mk "sq_rm0_t") not_rm0 rm_is_0,
    Gate.mkAND not_rm2 not_rm1 (Wire.mk "sq_rm1_t"),
    Gate.mkAND (Wire.mk "sq_rm1_t") (rm_q[0]!) rm_is_1,
    Gate.mkAND not_rm2 (rm_q[1]!) (Wire.mk "sq_rm2_t"),
    Gate.mkAND (Wire.mk "sq_rm2_t") not_rm0 rm_is_2,
    Gate.mkAND not_rm2 (rm_q[1]!) (Wire.mk "sq_rm3_t"),
    Gate.mkAND (Wire.mk "sq_rm3_t") (rm_q[0]!) rm_is_3,
    Gate.mkAND (rm_q[2]!) not_rm1 (Wire.mk "sq_rm4_t"),
    Gate.mkAND (Wire.mk "sq_rm4_t") not_rm0 rm_is_4,
    Gate.mkAND (rm_q[2]!) (rm_q[1]!) (Wire.mk "sq_rm7_t"),
    Gate.mkAND (Wire.mk "sq_rm7_t") (rm_q[0]!) rm_is_7,
    Gate.mkOR rm_is_0 rm_is_7 rm_is_rne
  ]

  let rne_tie := Wire.mk "sq_rne_tie"
  let rne_up := Wire.mk "sq_rne_up"
  let rup_up := Wire.mk "sq_rup_up"
  let rmm_up := guard
  let round_up := Wire.mk "sq_round_up"

  let rnd_eval_gates := [
    Gate.mkOR sticky (frac_out[0]!) rne_tie,
    Gate.mkAND guard rne_tie rne_up,
    Gate.mkAND rm_is_3 any_round rup_up,

    Gate.mkAND rm_is_rne rne_up (Wire.mk "sq_ru_t0"),
    Gate.mkAND rm_is_4 rmm_up (Wire.mk "sq_ru_t1"),
    Gate.mkOR (Wire.mk "sq_ru_t0") (Wire.mk "sq_ru_t1") (Wire.mk "sq_ru_t01"),
    Gate.mkOR (Wire.mk "sq_ru_t01") rup_up round_up
  ]

  -- Mantissa incrementer: frac_out + 1
  let zero52 := (List.range 52).map fun _ => zero
  let frac_inc := makeIndexedWires "sq_frac_inc" 52
  let (rnd_add_gates, frac_rollover) := mkKoggeStoneAdd frac_out zero52 one frac_inc "sq_rnd"

  let final_frac := makeIndexedWires "sq_final_frac" 52
  let final_frac_gates := (List.range 52).map fun i =>
    Gate.mkMUX (frac_out[i]!) (frac_inc[i]!) round_up (final_frac[i]!)

  -- Exponent increment on rollover
  let rollover_up := Wire.mk "sq_rollover_up"
  let ro_gate := Gate.mkAND frac_rollover round_up rollover_up

  let zero11 := (List.range 11).map fun _ => zero
  let exp_inc := makeIndexedWires "sq_exp_inc" 11
  let (exp_inc_gates, _) := mkKoggeStoneAdd exp_q zero11 one exp_inc "sq_exp_inc"

  let final_exp := makeIndexedWires "sq_final_exp" 11
  let final_exp_gates := (List.range 11).map fun i =>
    Gate.mkMUX (exp_q[i]!) (exp_inc[i]!) rollover_up (final_exp[i]!)

  -- Result assembler (sqrt result is always positive => sign = 0)
  let norm_res := (List.range 52).map (fun i => final_frac[i]!) ++
                  (List.range 11).map (fun i => final_exp[i]!) ++
                  [zero]

  let norm_exc := [any_round, zero, zero, zero, zero]

  let res_gates := (List.range 64).map fun i =>
    Gate.mkMUX (norm_res[i]!) (sp_res_q[i]!) is_special_q (result[i]!)

  let tag_gates := (List.range 6).map fun i => Gate.mkBUF (tag_q[i]!) (tag_out[i]!)

  let exc_out_gates := (List.range 5).map fun i =>
    Gate.mkMUX (norm_exc[i]!) (sp_exc_q[i]!) is_special_q (exc[i]!)

  -- Register DFFs
  let all_dffs :=
    (List.range 64).map (fun i => Gate.mkDFF (src1_d[i]!) clock reset (src1_q[i]!)) ++
    (List.range 3).map (fun i => Gate.mkDFF (rm_d[i]!) clock reset (rm_q[i]!)) ++
    (List.range 6).map (fun i => Gate.mkDFF (tag_d[i]!) clock reset (tag_q[i]!)) ++
    (List.range 6).map (fun i => Gate.mkDFF (cnt_d[i]!) clock reset (cnt_q[i]!)) ++
    [Gate.mkDFF busy_d clock reset busy_q] ++
    (List.range 11).map (fun i => Gate.mkDFF (exp_d[i]!) clock reset (exp_q[i]!)) ++
    (List.range 57).map (fun i => Gate.mkDFF (rem_d[i]!) clock reset (rem_q[i]!)) ++
    (List.range 54).map (fun i => Gate.mkDFF (root_d[i]!) clock reset (root_q[i]!)) ++
    (List.range 56).map (fun i => Gate.mkDFF (mant_d[i]!) clock reset (mant_q[i]!)) ++
    [Gate.mkDFF is_special_d clock reset is_special_q] ++
    (List.range 64).map (fun i => Gate.mkDFF (sp_res_d[i]!) clock reset (sp_res_q[i]!)) ++
    (List.range 5).map (fun i => Gate.mkDFF (sp_exc_d[i]!) clock reset (sp_exc_q[i]!))

  let all_gates :=
    ctrl_gates ++ done_gates ++ cnt_inc_gates ++ cnt_mux_gates ++
    ea_ao_gates ++ ea_oz_gates ++ [ea_allz_gate] ++ fa_any_gates ++
    class_gates ++ [nan_target_gate] ++ sp_res_gates ++ sp_exc_gates ++
    [exp_odd_gate] ++ ea_add_gates ++ mant_init_gates ++
    trial_sub_gates ++ [accept_gate] ++ new_rem_gates ++
    rem_mux_gates ++ root_mux_gates ++ mant_mux_gates ++ exp_mux_gates ++
    [sp_flag_mux] ++ sp_res_mux_gates ++ sp_exc_mux_gates ++
    src1_mux_gates ++ rm_mux_gates ++ tag_mux_gates ++
    sticky_gates ++ [rnd_cond_gate] ++ rm_dec_gates ++ rnd_eval_gates ++
    rnd_add_gates ++ final_frac_gates ++ [ro_gate] ++ exp_inc_gates ++ final_exp_gates ++
    res_gates ++ tag_gates ++ exc_out_gates ++ all_dffs

  { name := "FPSqrtD"
    inputs := src1_in ++ rm_in ++ dest_tag ++ [start, clock, reset, zero, one]
    outputs := result ++ tag_out ++ exc ++ [valid_out, busy_out]
    gates := all_gates
    instances := [] }

def fpSqrtDCircuit : Circuit := mkFPSqrtD

end Shoumei.Circuits.Sequential
