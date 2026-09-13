/-
Circuits/Sequential/FPDividerD.lean - 54-Cycle Iterative Double-Precision FP Divider

An iterative floating-point divider for IEEE 754 binary64.
Uses a busy/done state machine protocol matching FPDivider.

Algorithm:
  Pre-comparison and alignment on start:
  - Compares dividend and divisor mantissas.
  - If Ma >= Mb: init_rem = Ma - Mb, exp = Ea - Eb + 1023
  - If Ma < Mb:  init_rem = (Ma << 1) - Mb, exp = Ea - Eb + 1022
  In both cases, quotient is in [1.0, 2.0) with implicit bit = 1.
  54 iterative shift-subtract cycles produce:
  - 52 fraction bits (quot[53:2])
  - 1 guard bit (quot[1])
  - 1 round bit (quot[0])
  - sticky bit from non-zero final remainder
  IEEE 754 rounding (RNE, RTZ, RDN, RUP, RMM) with mantissa increment and rollover.
  Handles special cases: ±0, ±Inf, NaN, sNaN, and Divide-by-Zero (DZ flag).

Interface:
- Inputs: src1[63:0], src2[63:0], rm[2:0], dest_tag[5:0], start, clock, reset, zero, one
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

/-- Build the 54-cycle iterative Double-Precision FP divider structural circuit. -/
def mkFPDividerD : Circuit :=
  let src1_in := makeIndexedWires "src1" 64
  let src2_in := makeIndexedWires "src2" 64
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
  let src2_q := makeIndexedWires "src2_q" 64
  let rm_q := makeIndexedWires "rm_q" 3
  let tag_q := makeIndexedWires "tag_q" 6
  let cnt_q := makeIndexedWires "cnt_q" 6
  let busy_q := Wire.mk "busy_q"

  let sign_q := Wire.mk "sign_q"
  let exp_q := makeIndexedWires "exp_q" 11
  let div_mant_q := makeIndexedWires "div_mant_q" 55
  let rem_q := makeIndexedWires "rem_q" 55
  let quot_q := makeIndexedWires "quot_q" 54
  let is_special_q := Wire.mk "is_special_q"
  let sp_res_q := makeIndexedWires "sp_res_q" 64
  let sp_exc_q := makeIndexedWires "sp_exc_q" 5

  -- Next-state wires
  let src1_d := makeIndexedWires "src1_d" 64
  let src2_d := makeIndexedWires "src2_d" 64
  let rm_d := makeIndexedWires "rm_d" 3
  let tag_d := makeIndexedWires "tag_d" 6
  let cnt_d := makeIndexedWires "cnt_d" 6
  let busy_d := Wire.mk "busy_d"

  let sign_d := Wire.mk "sign_d"
  let exp_d := makeIndexedWires "exp_d" 11
  let div_mant_d := makeIndexedWires "div_mant_d" 55
  let rem_d := makeIndexedWires "rem_d" 55
  let quot_d := makeIndexedWires "quot_d" 54
  let is_special_d := Wire.mk "is_special_d"
  let sp_res_d := makeIndexedWires "sp_res_d" 64
  let sp_exc_d := makeIndexedWires "sp_exc_d" 5

  -- Control signals
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

  -- 6-bit counter increment
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
  let sign_b := src2_in[63]!
  let exp_a := (List.range 11).map fun i => src1_in[52 + i]!
  let frac_a := (List.range 52).map fun i => src1_in[i]!
  let exp_b := (List.range 11).map fun i => src2_in[52 + i]!
  let frac_b := (List.range 52).map fun i => src2_in[i]!

  -- Classification of A and B
  let (ea_ao_gates, exp_a_all_ones) := mkAndChain exp_a "div_ea_ao"
  let (ea_oz_gates, exp_a_any_set) := mkOrChain exp_a "div_ea_oz"
  let exp_a_all_zeros := Wire.mk "exp_a_all_zeros"
  let ea_allz_gate := Gate.mkNOT exp_a_any_set exp_a_all_zeros
  let (fa_any_gates, frac_a_any_set) := mkOrChain frac_a "div_fa_any"

  let (eb_ao_gates, exp_b_all_ones) := mkAndChain exp_b "div_eb_ao"
  let (eb_oz_gates, exp_b_any_set) := mkOrChain exp_b "div_eb_oz"
  let exp_b_all_zeros := Wire.mk "exp_b_all_zeros"
  let eb_allz_gate := Gate.mkNOT exp_b_any_set exp_b_all_zeros
  let (fb_any_gates, frac_b_any_set) := mkOrChain frac_b "div_fb_any"

  let not_frac_a_any := Wire.mk "not_frac_a_any"
  let not_frac_b_any := Wire.mk "not_frac_b_any"
  let is_zero_a := Wire.mk "is_zero_a"
  let is_inf_a := Wire.mk "is_inf_a"
  let is_nan_a := Wire.mk "is_nan_a"
  let not_src1_51 := Wire.mk "not_src1_51"
  let is_snan_a := Wire.mk "is_snan_a"

  let is_zero_b := Wire.mk "is_zero_b"
  let is_inf_b := Wire.mk "is_inf_b"
  let is_nan_b := Wire.mk "is_nan_b"
  let not_src2_51 := Wire.mk "not_src2_51"
  let is_snan_b := Wire.mk "is_snan_b"

  let class_gates := [
    Gate.mkNOT frac_a_any_set not_frac_a_any,
    Gate.mkNOT frac_b_any_set not_frac_b_any,
    Gate.mkAND exp_a_all_zeros not_frac_a_any is_zero_a,
    Gate.mkAND exp_a_all_ones not_frac_a_any is_inf_a,
    Gate.mkAND exp_a_all_ones frac_a_any_set is_nan_a,
    Gate.mkNOT (src1_in[51]!) not_src1_51,
    Gate.mkAND is_nan_a not_src1_51 is_snan_a,

    Gate.mkAND exp_b_all_zeros not_frac_b_any is_zero_b,
    Gate.mkAND exp_b_all_ones not_frac_b_any is_inf_b,
    Gate.mkAND exp_b_all_ones frac_b_any_set is_nan_b,
    Gate.mkNOT (src2_in[51]!) not_src2_51,
    Gate.mkAND is_nan_b not_src2_51 is_snan_b
  ]

  -- Special case conditions
  let res_sign := Wire.mk "div_res_sign"
  let any_nan := Wire.mk "div_any_nan"
  let any_snan := Wire.mk "div_any_snan"
  let both_inf := Wire.mk "div_both_inf"
  let both_zero := Wire.mk "div_both_zero"
  let inf_or_zero_div := Wire.mk "div_inf_or_zero_div"
  let nan_res := Wire.mk "div_nan_res"

  let not_zero_a := Wire.mk "not_zero_a"
  let not_zero_b := Wire.mk "not_zero_b"
  let not_inf_a := Wire.mk "not_inf_a"
  let not_inf_b := Wire.mk "not_inf_b"
  let not_any_nan := Wire.mk "not_any_nan"

  let dz_cond := Wire.mk "div_dz_cond"
  let inf_res_a := Wire.mk "div_inf_res_a"
  let inf_res := Wire.mk "div_inf_res"
  let zero_res_a := Wire.mk "div_zero_res_a"
  let zero_res_b := Wire.mk "div_zero_res_b"
  let zero_res := Wire.mk "div_zero_res"
  let is_special := Wire.mk "div_is_special"

  let sp_cond_gates := [
    Gate.mkXOR sign_a sign_b res_sign,
    Gate.mkOR is_nan_a is_nan_b any_nan,
    Gate.mkOR is_snan_a is_snan_b any_snan,
    Gate.mkAND is_inf_a is_inf_b both_inf,
    Gate.mkAND is_zero_a is_zero_b both_zero,
    Gate.mkOR both_inf both_zero inf_or_zero_div,
    Gate.mkOR any_nan inf_or_zero_div nan_res,

    Gate.mkNOT is_zero_a not_zero_a,
    Gate.mkNOT is_zero_b not_zero_b,
    Gate.mkNOT is_inf_a not_inf_a,
    Gate.mkNOT is_inf_b not_inf_b,
    Gate.mkNOT any_nan not_any_nan,

    -- dz_cond = is_zero_b & not_zero_a & not_any_nan & not_inf_a
    Gate.mkAND is_zero_b not_zero_a (Wire.mk "dz_t0"),
    Gate.mkAND not_any_nan not_inf_a (Wire.mk "dz_t1"),
    Gate.mkAND (Wire.mk "dz_t0") (Wire.mk "dz_t1") dz_cond,

    -- inf_res = (is_inf_a & not_inf_b & not_any_nan) | dz_cond
    Gate.mkAND is_inf_a not_inf_b (Wire.mk "ir_t0"),
    Gate.mkAND (Wire.mk "ir_t0") not_any_nan inf_res_a,
    Gate.mkOR inf_res_a dz_cond inf_res,

    -- zero_res = (is_zero_a & not_zero_b & not_any_nan) | (is_inf_b & not_inf_a & not_any_nan)
    Gate.mkAND is_zero_a not_zero_b (Wire.mk "zr_t0"),
    Gate.mkAND (Wire.mk "zr_t0") not_any_nan zero_res_a,
    Gate.mkAND is_inf_b not_inf_a (Wire.mk "zr_t1"),
    Gate.mkAND (Wire.mk "zr_t1") not_any_nan zero_res_b,
    Gate.mkOR zero_res_a zero_res_b zero_res,

    -- is_special = nan_res | inf_res | zero_res
    Gate.mkOR nan_res inf_res (Wire.mk "sp_t0"),
    Gate.mkOR (Wire.mk "sp_t0") zero_res is_special
  ]

  -- Special result generation:
  -- Canonical NaN: 0x7ff8000000000000 (sign=0, exp=0x7ff, frac[51]=1, others=0)
  -- Inf: {res_sign, 0x7ff, 52'b0}
  -- Zero: {res_sign, 11'b0, 52'b0}
  let sp_res_wire := makeIndexedWires "div_sp_res" 64
  let sp_res_gates := (List.range 64).flatMap fun i =>
    if i < 51 then
      [Gate.mkBUF zero (sp_res_wire[i]!)]
    else if i == 51 then
      [Gate.mkBUF nan_res (sp_res_wire[i]!)]
    else if i >= 52 && i <= 62 then
      let exp_bit := Wire.mk s!"div_sp_exp_{i}"
      [Gate.mkOR nan_res inf_res exp_bit,
       Gate.mkBUF exp_bit (sp_res_wire[i]!)]
    else
      let not_nan := Wire.mk "div_sp_not_nan"
      [Gate.mkNOT nan_res not_nan,
       Gate.mkAND res_sign not_nan (sp_res_wire[63]!)]

  let nv_bit := Wire.mk "div_sp_nv"
  let sp_exc_wire := makeIndexedWires "div_sp_exc" 5
  let sp_exc_gates := [
    Gate.mkBUF zero (sp_exc_wire[0]!),  -- NX
    Gate.mkBUF zero (sp_exc_wire[1]!),  -- UF
    Gate.mkBUF zero (sp_exc_wire[2]!),  -- OF
    Gate.mkBUF dz_cond (sp_exc_wire[3]!), -- DZ
    Gate.mkOR any_snan inf_or_zero_div nv_bit,
    Gate.mkBUF nv_bit (sp_exc_wire[4]!)  -- NV
  ]

  -- Normal division setup (start_new)
  -- Mantissa pre-comparison: frac_a >= frac_b
  let pre_diff := makeIndexedWires "div_pre_diff" 52
  let (cmp_gates, pre_borrow) := mkKoggeStoneSub frac_a frac_b pre_diff "div_pre_cmp" one
  let pre_ge := Wire.mk "div_pre_ge"
  let pre_ge_gate := Gate.mkNOT pre_borrow pre_ge

  -- Alignment muxes for op_a:
  -- if pre_ge: {0, 1, frac_a} (54 bits)
  -- else:      {1, frac_a, 0} (54 bits)
  let op_a := makeIndexedWires "div_op_a" 54
  let op_a_gates := (List.range 54).map fun i =>
    let ge_bit := if i < 52 then frac_a[i]! else if i == 52 then one else zero
    let lt_bit := if i == 0 then zero else if i <= 52 then frac_a[i - 1]! else one
    Gate.mkMUX lt_bit ge_bit pre_ge (op_a[i]!)

  -- op_b: {0, 1, frac_b} (54 bits)
  let op_b := (List.range 52).map (fun i => frac_b[i]!) ++ [one, zero]

  -- init_rem_54 = op_a - op_b
  let init_rem_54 := makeIndexedWires "div_init_rem54" 54
  let (init_sub_gates, _) := mkKoggeStoneSub op_a op_b init_rem_54 "div_init_sub" one
  let init_rem := init_rem_54 ++ [zero]  -- 55 bits

  -- init_exp computation:
  -- bias_adj = pre_ge ? 1023 : 1022
  let exp_a_12 := exp_a ++ [zero]
  let bias_12 : List Wire := (List.range 12).map fun i =>
    if i == 0 then pre_ge
    else if i < 10 then one
    else zero

  let exp_biased := makeIndexedWires "div_exp_biased" 12
  let (ea_add_gates, _) := mkKoggeStoneAdd exp_a_12 bias_12 zero exp_biased "div_ea_add"

  let exp_b_12 := exp_b ++ [zero]
  let init_exp_12 := makeIndexedWires "div_init_exp12" 12
  let (ea_sub_gates, _) := mkKoggeStoneSub exp_biased exp_b_12 init_exp_12 "div_ea_sub" one
  let init_exp := (List.range 11).map fun i => init_exp_12[i]!

  -- div_mant_init: {0, 0, 1, frac_b} (55 bits)
  let div_mant_init := (List.range 52).map (fun i => frac_b[i]!) ++ [one, zero, zero]

  -- Iterative step logic (54 cycles):
  -- rem_shifted = {rem_q[53:0], 1'b0} (55 bits)
  let rem_shifted := [zero] ++ (List.range 54).map (fun i => rem_q[i]!)
  let trial := makeIndexedWires "div_trial" 55
  let (trial_sub_gates, trial_borrow) := mkKoggeStoneSub rem_shifted div_mant_q trial "div_step_sub" one
  let q_bit := Wire.mk "div_q_bit"
  let qb_gate := Gate.mkNOT trial_borrow q_bit

  let new_rem := makeIndexedWires "div_new_rem" 55
  let new_rem_gates := (List.range 55).map fun i =>
    Gate.mkMUX (trial[i]!) (rem_shifted[i]!) trial_borrow (new_rem[i]!)

  let new_quot := [q_bit] ++ (List.range 53).map (fun i => quot_q[i]!)

  -- Next-state registers muxing
  let rem_m1 := makeIndexedWires "div_rem_m1" 55
  let rem_mux_gates := (List.range 55).flatMap fun i => [
    Gate.mkMUX (rem_q[i]!) (new_rem[i]!) busy_and_not_done (rem_m1[i]!),
    Gate.mkMUX (rem_m1[i]!) (init_rem[i]!) start_new (rem_d[i]!)
  ]

  let quot_m1 := makeIndexedWires "div_quot_m1" 54
  let quot_mux_gates := (List.range 54).flatMap fun i => [
    Gate.mkMUX (quot_q[i]!) (new_quot[i]!) busy_and_not_done (quot_m1[i]!),
    Gate.mkMUX (quot_m1[i]!) zero start_new (quot_d[i]!)
  ]

  let div_mant_mux_gates := (List.range 55).map fun i =>
    Gate.mkMUX (div_mant_q[i]!) (div_mant_init[i]!) start_new (div_mant_d[i]!)

  let exp_mux_gates := (List.range 11).map fun i =>
    Gate.mkMUX (exp_q[i]!) (init_exp[i]!) start_new (exp_d[i]!)

  let sign_mux_gate := Gate.mkMUX sign_q res_sign start_new sign_d
  let sp_flag_mux := Gate.mkMUX is_special_q is_special start_new is_special_d
  let sp_res_mux_gates := (List.range 64).map fun i =>
    Gate.mkMUX (sp_res_q[i]!) (sp_res_wire[i]!) start_new (sp_res_d[i]!)
  let sp_exc_mux_gates := (List.range 5).map fun i =>
    Gate.mkMUX (sp_exc_q[i]!) (sp_exc_wire[i]!) start_new (sp_exc_d[i]!)

  let src1_mux_gates := (List.range 64).map fun i =>
    Gate.mkMUX (src1_q[i]!) (src1_in[i]!) start_new (src1_d[i]!)
  let src2_mux_gates := (List.range 64).map fun i =>
    Gate.mkMUX (src2_q[i]!) (src2_in[i]!) start_new (src2_d[i]!)
  let rm_mux_gates := (List.range 3).map fun i =>
    Gate.mkMUX (rm_q[i]!) (rm_in[i]!) start_new (rm_d[i]!)
  let tag_mux_gates := (List.range 6).map fun i =>
    Gate.mkMUX (tag_q[i]!) (dest_tag[i]!) start_new (tag_d[i]!)

  -- Output bypass & rounding on done:
  let out_quot := new_quot
  let out_rem := new_rem
  let (sticky_gates, sticky) := mkOrChain out_rem "div_stk"

  let frac_out := (List.range 52).map fun i => out_quot[2 + i]!
  let guard := out_quot[1]!
  let round_b := out_quot[0]!

  let any_round := Wire.mk "div_any_round"
  let r_or_s := Wire.mk "div_r_or_s"
  let rnd_cond_gates := [
    Gate.mkOR round_b sticky r_or_s,
    Gate.mkOR guard r_or_s any_round
  ]

  -- Rounding mode decoding
  let not_rm0 := Wire.mk "not_rm0"
  let not_rm1 := Wire.mk "not_rm1"
  let not_rm2 := Wire.mk "not_rm2"
  let rm_is_0 := Wire.mk "rm_is_0"
  let rm_is_1 := Wire.mk "rm_is_1"
  let rm_is_2 := Wire.mk "rm_is_2"
  let rm_is_3 := Wire.mk "rm_is_3"
  let rm_is_4 := Wire.mk "rm_is_4"
  let rm_is_7 := Wire.mk "rm_is_7"
  let rm_is_rne := Wire.mk "rm_is_rne"

  let rm_dec_gates := [
    Gate.mkNOT (rm_q[0]!) not_rm0,
    Gate.mkNOT (rm_q[1]!) not_rm1,
    Gate.mkNOT (rm_q[2]!) not_rm2,
    Gate.mkAND not_rm2 not_rm1 (Wire.mk "rm0_t"),
    Gate.mkAND (Wire.mk "rm0_t") not_rm0 rm_is_0,
    Gate.mkAND not_rm2 not_rm1 (Wire.mk "rm1_t"),
    Gate.mkAND (Wire.mk "rm1_t") (rm_q[0]!) rm_is_1,
    Gate.mkAND not_rm2 (rm_q[1]!) (Wire.mk "rm2_t"),
    Gate.mkAND (Wire.mk "rm2_t") not_rm0 rm_is_2,
    Gate.mkAND not_rm2 (rm_q[1]!) (Wire.mk "rm3_t"),
    Gate.mkAND (Wire.mk "rm3_t") (rm_q[0]!) rm_is_3,
    Gate.mkAND (rm_q[2]!) not_rm1 (Wire.mk "rm4_t"),
    Gate.mkAND (Wire.mk "rm4_t") not_rm0 rm_is_4,
    Gate.mkAND (rm_q[2]!) (rm_q[1]!) (Wire.mk "rm7_t"),
    Gate.mkAND (Wire.mk "rm7_t") (rm_q[0]!) rm_is_7,
    Gate.mkOR rm_is_0 rm_is_7 rm_is_rne
  ]

  let rne_tie := Wire.mk "div_rne_tie"
  let rne_up := Wire.mk "div_rne_up"
  let rdn_up := Wire.mk "div_rdn_up"
  let rup_up := Wire.mk "div_rup_up"
  let rmm_up := guard
  let not_sign_q := Wire.mk "not_sign_q"
  let round_up := Wire.mk "div_round_up"

  let rnd_eval_gates := [
    Gate.mkOR r_or_s (frac_out[0]!) rne_tie,
    Gate.mkAND guard rne_tie rne_up,
    Gate.mkAND sign_q any_round rdn_up,
    Gate.mkNOT sign_q not_sign_q,
    Gate.mkAND not_sign_q any_round rup_up,

    Gate.mkAND rm_is_rne rne_up (Wire.mk "ru_t0"),
    Gate.mkAND rm_is_2 rdn_up (Wire.mk "ru_t1"),
    Gate.mkAND rm_is_3 rup_up (Wire.mk "ru_t2"),
    Gate.mkAND rm_is_4 rmm_up (Wire.mk "ru_t3"),
    Gate.mkOR (Wire.mk "ru_t0") (Wire.mk "ru_t1") (Wire.mk "ru_t01"),
    Gate.mkOR (Wire.mk "ru_t2") (Wire.mk "ru_t3") (Wire.mk "ru_t23"),
    Gate.mkOR (Wire.mk "ru_t01") (Wire.mk "ru_t23") round_up
  ]

  -- Mantissa incrementer: frac_out + 1
  let zero52 := (List.range 52).map fun _ => zero
  let frac_inc := makeIndexedWires "div_frac_inc" 52
  let (rnd_add_gates, frac_rollover) := mkKoggeStoneAdd frac_out zero52 one frac_inc "div_rnd"

  let final_frac := makeIndexedWires "div_final_frac" 52
  let final_frac_gates := (List.range 52).map fun i =>
    Gate.mkMUX (frac_out[i]!) (frac_inc[i]!) round_up (final_frac[i]!)

  -- Exponent increment on rollover
  let rollover_up := Wire.mk "div_rollover_up"
  let ro_gate := Gate.mkAND frac_rollover round_up rollover_up

  let zero11 := (List.range 11).map fun _ => zero
  let exp_inc := makeIndexedWires "div_exp_inc" 11
  let (exp_inc_gates, _) := mkKoggeStoneAdd exp_q zero11 one exp_inc "div_exp_inc"

  let final_exp := makeIndexedWires "div_final_exp" 11
  let final_exp_gates := (List.range 11).map fun i =>
    Gate.mkMUX (exp_q[i]!) (exp_inc[i]!) rollover_up (final_exp[i]!)

  -- Result assembler
  let norm_res := (List.range 52).map (fun i => final_frac[i]!) ++
                  (List.range 11).map (fun i => final_exp[i]!) ++
                  [sign_q]

  let norm_exc := [any_round, zero, zero, zero, zero]

  let res_gates := (List.range 64).map fun i =>
    Gate.mkMUX (norm_res[i]!) (sp_res_q[i]!) is_special_q (result[i]!)

  let tag_gates := (List.range 6).map fun i => Gate.mkBUF (tag_q[i]!) (tag_out[i]!)

  let exc_out_gates := (List.range 5).map fun i =>
    Gate.mkMUX (norm_exc[i]!) (sp_exc_q[i]!) is_special_q (exc[i]!)

  -- Register DFFs
  let all_dffs :=
    (List.range 64).map (fun i => Gate.mkDFF (src1_d[i]!) clock reset (src1_q[i]!)) ++
    (List.range 64).map (fun i => Gate.mkDFF (src2_d[i]!) clock reset (src2_q[i]!)) ++
    (List.range 3).map (fun i => Gate.mkDFF (rm_d[i]!) clock reset (rm_q[i]!)) ++
    (List.range 6).map (fun i => Gate.mkDFF (tag_d[i]!) clock reset (tag_q[i]!)) ++
    (List.range 6).map (fun i => Gate.mkDFF (cnt_d[i]!) clock reset (cnt_q[i]!)) ++
    [Gate.mkDFF busy_d clock reset busy_q] ++
    [Gate.mkDFF sign_d clock reset sign_q] ++
    (List.range 11).map (fun i => Gate.mkDFF (exp_d[i]!) clock reset (exp_q[i]!)) ++
    (List.range 55).map (fun i => Gate.mkDFF (div_mant_d[i]!) clock reset (div_mant_q[i]!)) ++
    (List.range 55).map (fun i => Gate.mkDFF (rem_d[i]!) clock reset (rem_q[i]!)) ++
    (List.range 54).map (fun i => Gate.mkDFF (quot_d[i]!) clock reset (quot_q[i]!)) ++
    [Gate.mkDFF is_special_d clock reset is_special_q] ++
    (List.range 64).map (fun i => Gate.mkDFF (sp_res_d[i]!) clock reset (sp_res_q[i]!)) ++
    (List.range 5).map (fun i => Gate.mkDFF (sp_exc_d[i]!) clock reset (sp_exc_q[i]!))

  let all_gates :=
    ctrl_gates ++ done_gates ++ cnt_inc_gates ++ cnt_mux_gates ++
    ea_ao_gates ++ ea_oz_gates ++ [ea_allz_gate] ++ fa_any_gates ++
    eb_ao_gates ++ eb_oz_gates ++ [eb_allz_gate] ++ fb_any_gates ++
    class_gates ++ sp_cond_gates ++ sp_res_gates ++ sp_exc_gates ++
    cmp_gates ++ [pre_ge_gate] ++ op_a_gates ++ init_sub_gates ++
    ea_add_gates ++ ea_sub_gates ++
    trial_sub_gates ++ [qb_gate] ++ new_rem_gates ++
    rem_mux_gates ++ quot_mux_gates ++ div_mant_mux_gates ++ exp_mux_gates ++
    [sign_mux_gate, sp_flag_mux] ++ sp_res_mux_gates ++ sp_exc_mux_gates ++
    src1_mux_gates ++ src2_mux_gates ++ rm_mux_gates ++ tag_mux_gates ++
    sticky_gates ++ rnd_cond_gates ++ rm_dec_gates ++ rnd_eval_gates ++
    rnd_add_gates ++ final_frac_gates ++ [ro_gate] ++ exp_inc_gates ++ final_exp_gates ++
    res_gates ++ tag_gates ++ exc_out_gates ++ all_dffs

  { name := "FPDividerD"
    inputs := src1_in ++ src2_in ++ rm_in ++ dest_tag ++ [start, clock, reset, zero, one]
    outputs := result ++ tag_out ++ exc ++ [valid_out, busy_out]
    gates := all_gates
    instances := [] }

def fpDividerDCircuit : Circuit := mkFPDividerD

end Shoumei.Circuits.Sequential
