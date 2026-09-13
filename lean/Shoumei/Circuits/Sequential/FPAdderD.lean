/-
Circuits/Sequential/FPAdderD.lean - 4-Stage Pipelined Double-Precision FP Adder/Subtractor

A pipelined floating-point adder/subtractor for IEEE 754 binary64.

Pipeline stages (4-cycle latency):
  Stage 1: Latch inputs + Unpack + Exponent diff + Swap signal + NaN/Inf detection
  Stage 2: Swap operands + Alignment barrel shift with sticky tracking
  Stage 3: Mantissa add/sub + Leading-zero detect
  Stage 4: Normalization shifter + Rounding + Special value handling + Pack

Interface:
- Inputs: src1[63:0], src2[63:0], op_sub, rm[2:0], dest_tag[5:0], valid_in, clock, reset, zero, one
- Outputs: result[63:0], tag_out[5:0], exc[4:0], valid_out
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.KoggeStoneAdder

namespace Shoumei.Circuits.Sequential

open Shoumei
open Shoumei.Circuits.Combinational

private def makeIndexedWires (pfx : String) (n : Nat) : List Wire :=
  (List.range n).map fun i => Wire.mk (pfx ++ "_" ++ toString i)

private def mkDFFBank (d_wires q_wires : List Wire) (clock reset : Wire) : List Gate :=
  List.zipWith (fun d q => Gate.mkDFF d clock reset q) d_wires q_wires

private def mkOrTree (pfx : String) (inputs : List Wire) : Wire × List Gate :=
  match inputs with
  | [] => (Wire.mk s!"{pfx}_empty", [])
  | [w] => (w, [])
  | w0 :: w1 :: rest =>
    let firstOut := Wire.mk s!"{pfx}_0"
    let firstGate := Gate.mkOR w0 w1 firstOut
    let (finalW, restGates) := rest.enum.foldl (fun (acc : Wire × List Gate) (idx, w) =>
      let out := Wire.mk s!"{pfx}_{idx + 1}"
      let g := Gate.mkOR acc.1 w out
      (out, acc.2 ++ [g])
    ) (firstOut, [])
    (finalW, [firstGate] ++ restGates)

private def mkAndTree (pfx : String) (inputs : List Wire) : Wire × List Gate :=
  match inputs with
  | [] => (Wire.mk s!"{pfx}_empty", [])
  | [w] => (w, [])
  | w0 :: w1 :: rest =>
    let firstOut := Wire.mk s!"{pfx}_0"
    let firstGate := Gate.mkAND w0 w1 firstOut
    let (finalW, restGates) := rest.enum.foldl (fun (acc : Wire × List Gate) (idx, w) =>
      let out := Wire.mk s!"{pfx}_{idx + 1}"
      let g := Gate.mkAND acc.1 w out
      (out, acc.2 ++ [g])
    ) (firstOut, [])
    (finalW, [firstGate] ++ restGates)

/-- 6-level barrel right shifter for 56-bit value with sticky tracking. -/
private def mkBarrelShiftRight56WithSticky (input : List Wire) (shift_amt : List Wire)
    (output : List Wire) (sticky_out : Wire) (zero_wire : Wire) (pfx : String) : List Gate :=
  let w := input.length
  let levels : List (List Wire) := (List.range 7).map fun level =>
    if level == 0 then input
    else (List.range w).map fun i => Wire.mk (pfx ++ "_l" ++ toString level ++ "_" ++ toString i)
  let stickies : List Wire := (List.range 7).map fun level =>
    Wire.mk (pfx ++ "_stk_" ++ toString level)
  let init_stk_gate := Gate.mkBUF zero_wire stickies[0]!
  let (mux_gates, stk_gates) := (List.range 6).foldl (fun (acc : List Gate × List Gate) level =>
    let shift_by := 1 <<< level
    let prev := levels[level]!
    let curr := levels[level + 1]!
    let sel := shift_amt[level]!
    let prev_stk := stickies[level]!
    let curr_stk := stickies[level + 1]!
    let m_gates := (List.range w).map fun i =>
      let unshifted := prev[i]!
      let shifted := if i + shift_by < w then prev[i + shift_by]! else zero_wire
      Gate.mkMUX unshifted shifted sel curr[i]!
    let lost_bits := (List.range (min shift_by w)).map fun i => prev[i]!
    let (lost_or, lost_or_gates) := mkOrTree (pfx ++ "_lost_l" ++ toString level) lost_bits
    let stk_c := Wire.mk (pfx ++ "_stk_c_" ++ toString level)
    let s_gates := lost_or_gates ++ [
      Gate.mkAND sel lost_or stk_c,
      Gate.mkOR prev_stk stk_c curr_stk
    ]
    (acc.1 ++ m_gates, acc.2 ++ s_gates)
  ) ([], [init_stk_gate])
  let copy_gates := (List.range w).map fun i =>
    Gate.mkBUF (levels[6]!)[i]! output[i]!
  let final_stk_gate := Gate.mkBUF stickies[6]! sticky_out
  mux_gates ++ stk_gates ++ copy_gates ++ [final_stk_gate]

/-- 6-level barrel left shifter for 56-bit value. -/
private def mkBarrelShiftLeft56 (input : List Wire) (shift_amt : List Wire)
    (output : List Wire) (zero_wire : Wire) (pfx : String) : List Gate :=
  let w := input.length
  let levels : List (List Wire) := (List.range 7).map fun level =>
    if level == 0 then input
    else (List.range w).map fun i => Wire.mk (pfx ++ "_l" ++ toString level ++ "_" ++ toString i)
  let mux_gates := (List.range 6).flatMap fun level =>
    let shift_by := 1 <<< level
    let prev := levels[level]!
    let curr := levels[level + 1]!
    let sel := shift_amt[level]!
    (List.range w).map fun i =>
      let unshifted := prev[i]!
      let shifted := if i >= shift_by then prev[i - shift_by]! else zero_wire
      Gate.mkMUX unshifted shifted sel curr[i]!
  let copy_gates := (List.range w).map fun i =>
    Gate.mkBUF (levels[6]!)[i]! output[i]!
  mux_gates ++ copy_gates

def mkFPAdderD : Circuit :=
  let src1 := makeIndexedWires "src1" 64
  let src2 := makeIndexedWires "src2" 64
  let op_sub := Wire.mk "op_sub"
  let rm := makeIndexedWires "rm" 3
  let dest_tag := makeIndexedWires "dest_tag" 6
  let valid_in := Wire.mk "valid_in"
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "fp_const_one"
  let one_gate := Gate.mkNOT zero one

  let result := makeIndexedWires "result" 64
  let tag_out := makeIndexedWires "tag_out" 6
  let exc := makeIndexedWires "exc" 5
  let valid_out := Wire.mk "valid_out"

  -- ══════════════════════════════════════════════
  -- STAGE 1: Unpack, Exponent difference, Swap, NaN/Inf
  -- ══════════════════════════════════════════════
  let s1_sign1 := src1[63]!
  let s1_sign2_raw := src2[63]!
  let s1_sign2 := Wire.mk "s1_sign2"
  let s1_sign2_gate := Gate.mkXOR s1_sign2_raw op_sub s1_sign2

  let s1_exp1 := (List.range 11).map fun i => src1[52 + i]!
  let s1_exp2 := (List.range 11).map fun i => src2[52 + i]!

  let (exp1_or_all, exp1_or_gates) := mkOrTree "s1_e1_or" s1_exp1
  let (exp2_or_all, exp2_or_gates) := mkOrTree "s1_e2_or" s1_exp2
  let (exp1_and_all, exp1_and_gates) := mkAndTree "s1_e1_and" s1_exp1
  let (exp2_and_all, exp2_and_gates) := mkAndTree "s1_e2_and" s1_exp2

  let (mant1_lo_or, mant1_lo_gates) := mkOrTree "s1_m1_or" ((List.range 52).map fun i => src1[i]!)
  let (mant2_lo_or, mant2_lo_gates) := mkOrTree "s1_m2_or" ((List.range 52).map fun i => src2[i]!)

  let a_is_nan := Wire.mk "s1_a_is_nan"
  let b_is_nan := Wire.mk "s1_b_is_nan"
  let a_is_inf := Wire.mk "s1_a_is_inf"
  let b_is_inf := Wire.mk "s1_b_is_inf"
  let not_m1_lo := Wire.mk "s1_not_m1_lo"
  let not_m2_lo := Wire.mk "s1_not_m2_lo"
  let any_nan := Wire.mk "s1_any_nan"
  let both_inf := Wire.mk "s1_both_inf"
  let any_inf := Wire.mk "s1_any_inf"

  let special_gates := [
    Gate.mkAND exp1_and_all mant1_lo_or a_is_nan,
    Gate.mkAND exp2_and_all mant2_lo_or b_is_nan,
    Gate.mkNOT mant1_lo_or not_m1_lo,
    Gate.mkNOT mant2_lo_or not_m2_lo,
    Gate.mkAND exp1_and_all not_m1_lo a_is_inf,
    Gate.mkAND exp2_and_all not_m2_lo b_is_inf,
    Gate.mkOR a_is_nan b_is_nan any_nan,
    Gate.mkAND a_is_inf b_is_inf both_inf,
    Gate.mkOR a_is_inf b_is_inf any_inf
  ]

  let s1_mant1 := (List.range 52).map (fun i => src1[i]!) ++ [exp1_or_all]
  let s1_mant2 := (List.range 52).map (fun i => src2[i]!) ++ [exp2_or_all]

  -- Exponent difference exp1 - exp2 (11-bit)
  let s1_exp_diff := makeIndexedWires "s1_exp_diff" 11
  let s1_borrow := makeIndexedWires "s1_borrow" 12
  let s1_sub_gates := [Gate.mkBUF zero (s1_borrow[0]!)] ++ (List.range 11).flatMap (fun i =>
    let a := s1_exp1[i]!
    let b := s1_exp2[i]!
    let bi := s1_borrow[i]!
    let bo := s1_borrow[i + 1]!
    let xab := Wire.mk s!"s1_es_x_{i}"
    [Gate.mkXOR a b xab,
     Gate.mkXOR xab bi (s1_exp_diff[i]!),
     Gate.mkNOT a (Wire.mk s!"s1_na_{i}"),
     Gate.mkAND (Wire.mk s!"s1_na_{i}") b (Wire.mk s!"s1_t0_{i}"),
     Gate.mkAND (Wire.mk s!"s1_na_{i}") bi (Wire.mk s!"s1_t1_{i}"),
     Gate.mkAND b bi (Wire.mk s!"s1_t2_{i}"),
     Gate.mkOR (Wire.mk s!"s1_t0_{i}") (Wire.mk s!"s1_t1_{i}") (Wire.mk s!"s1_t01_{i}"),
     Gate.mkOR (Wire.mk s!"s1_t01_{i}") (Wire.mk s!"s1_t2_{i}") bo]
  )

  -- Mantissa difference mant1 - mant2 (53-bit) for tie-breaker when exponents are equal
  let s1_mb := makeIndexedWires "s1_mb" 54
  let s1_mant_sub_gates := [Gate.mkBUF zero (s1_mb[0]!)] ++ (List.range 53).flatMap (fun i =>
    let a := s1_mant1[i]!
    let b := s1_mant2[i]!
    let bi := s1_mb[i]!
    let bo := s1_mb[i + 1]!
    let na := Wire.mk s!"s1_nma_{i}"
    let t0 := Wire.mk s!"s1_mt0_{i}"
    let t1 := Wire.mk s!"s1_mt1_{i}"
    let t2 := Wire.mk s!"s1_mt2_{i}"
    [Gate.mkNOT a na,
     Gate.mkAND na b t0,
     Gate.mkAND na bi t1,
     Gate.mkAND b bi t2,
     Gate.mkOR t0 t1 (Wire.mk s!"s1_mt01_{i}"),
     Gate.mkOR (Wire.mk s!"s1_mt01_{i}") t2 bo]
  )
  let s1_mant_borrow := s1_mb[53]!

  let (exp_diff_any, exp_diff_any_gates) := mkOrTree "s1_ediff_any" s1_exp_diff
  let not_ediff_any := Wire.mk "s1_not_ediff_any"
  let exp_eq := Wire.mk "s1_exp_eq"
  let swap_mant := Wire.mk "s1_swap_mant"
  let s1_swap := Wire.mk "s1_swap"
  let swap_gates := exp_diff_any_gates ++ [
    Gate.mkNOT exp_diff_any not_ediff_any,
    Gate.mkAND not_ediff_any not_ediff_any exp_eq,
    Gate.mkAND exp_eq s1_mant_borrow swap_mant,
    Gate.mkOR (s1_borrow[11]!) swap_mant s1_swap
  ]

  -- Pipeline register 1 (DFFs)
  let p1_sign1 := Wire.mk "p1_sign1"; let p1_sign2 := Wire.mk "p1_sign2"
  let p1_exp1 := makeIndexedWires "p1_exp1" 11
  let p1_exp2 := makeIndexedWires "p1_exp2" 11
  let p1_mant1 := makeIndexedWires "p1_mant1" 53
  let p1_mant2 := makeIndexedWires "p1_mant2" 53
  let p1_exp_diff := makeIndexedWires "p1_exp_diff" 11
  let p1_swap := Wire.mk "p1_swap"
  let p1_any_nan := Wire.mk "p1_any_nan"
  let p1_both_inf := Wire.mk "p1_both_inf"
  let p1_any_inf := Wire.mk "p1_any_inf"
  let p1_a_is_inf := Wire.mk "p1_a_is_inf"
  let p1_rm := makeIndexedWires "p1_rm" 3
  let p1_tag := makeIndexedWires "p1_tag" 6
  let p1_valid := Wire.mk "p1_valid"

  let p1_dffs :=
    [Gate.mkDFF s1_sign1 clock reset p1_sign1,
     Gate.mkDFF s1_sign2 clock reset p1_sign2] ++
    mkDFFBank s1_exp1 p1_exp1 clock reset ++
    mkDFFBank s1_exp2 p1_exp2 clock reset ++
    mkDFFBank s1_mant1 p1_mant1 clock reset ++
    mkDFFBank s1_mant2 p1_mant2 clock reset ++
    mkDFFBank s1_exp_diff p1_exp_diff clock reset ++
    [Gate.mkDFF s1_swap clock reset p1_swap,
     Gate.mkDFF any_nan clock reset p1_any_nan,
     Gate.mkDFF both_inf clock reset p1_both_inf,
     Gate.mkDFF any_inf clock reset p1_any_inf,
     Gate.mkDFF a_is_inf clock reset p1_a_is_inf] ++
    mkDFFBank rm p1_rm clock reset ++
    mkDFFBank dest_tag p1_tag clock reset ++
    [Gate.mkDFF valid_in clock reset p1_valid]

  -- ══════════════════════════════════════════════
  -- STAGE 2: Swap operands + Alignment barrel shift with sticky
  -- ══════════════════════════════════════════════
  let s2_big_sign := Wire.mk "s2_big_sign"
  let s2_small_sign := Wire.mk "s2_small_sign"
  let s2_sign_swap_gates := [
    Gate.mkMUX p1_sign1 p1_sign2 p1_swap s2_big_sign,
    Gate.mkMUX p1_sign2 p1_sign1 p1_swap s2_small_sign
  ]

  let s2_big_exp := makeIndexedWires "s2_big_exp" 11
  let s2_exp_swap_gates := (List.range 11).map fun i =>
    Gate.mkMUX (p1_exp1[i]!) (p1_exp2[i]!) p1_swap (s2_big_exp[i]!)

  let s2_big_mant := makeIndexedWires "s2_big_mant" 53
  let s2_small_mant := makeIndexedWires "s2_small_mant" 53
  let s2_mant_swap_gates := (List.range 53).flatMap fun i =>
    [Gate.mkMUX (p1_mant1[i]!) (p1_mant2[i]!) p1_swap (s2_big_mant[i]!),
     Gate.mkMUX (p1_mant2[i]!) (p1_mant1[i]!) p1_swap (s2_small_mant[i]!)]

  let s2_neg_diff := makeIndexedWires "s2_neg_diff" 6
  let s2_neg_carry := makeIndexedWires "s2_neg_c" 7
  let s2_neg_gates := [Gate.mkBUF one (s2_neg_carry[0]!)] ++ (List.range 6).flatMap (fun i =>
    let nbit := Wire.mk s!"s2_nd_{i}"
    [Gate.mkNOT (p1_exp_diff[i]!) nbit,
     Gate.mkXOR nbit (s2_neg_carry[i]!) (s2_neg_diff[i]!),
     Gate.mkAND nbit (s2_neg_carry[i]!) (s2_neg_carry[i + 1]!)]
  )

  let s2_shift_amt := makeIndexedWires "s2_sh_amt" 6
  let s2_sh_mux_gates := (List.range 6).map fun i =>
    Gate.mkMUX (p1_exp_diff[i]!) (s2_neg_diff[i]!) p1_swap (s2_shift_amt[i]!)

  let s2_small_mant56 := [zero, zero, zero] ++ s2_small_mant
  let s2_aligned_small := makeIndexedWires "s2_aligned_small" 56
  let s2_shift_sticky := Wire.mk "s2_shift_sticky"
  let s2_shift_gates := mkBarrelShiftRight56WithSticky s2_small_mant56 s2_shift_amt s2_aligned_small s2_shift_sticky zero "s2_align"

  let s2_eff_sub := Wire.mk "s2_eff_sub"
  let s2_eff_sub_gate := Gate.mkXOR s2_big_sign s2_small_sign s2_eff_sub

  let s2_inf_sub_inf := Wire.mk "s2_inf_sub_inf"
  let s2_inf_sub_inf_gate := Gate.mkAND p1_both_inf s2_eff_sub s2_inf_sub_inf

  let s2_inf_sign := Wire.mk "s2_inf_sign"
  let s2_inf_sign_gate := Gate.mkMUX p1_sign2 p1_sign1 p1_a_is_inf s2_inf_sign

  -- Pipeline register 2 (DFFs)
  let p2_big_sign := Wire.mk "p2_big_sign"
  let p2_small_sign := Wire.mk "p2_small_sign"
  let p2_big_exp := makeIndexedWires "p2_big_exp" 11
  let p2_big_mant := makeIndexedWires "p2_big_mant" 56
  let p2_aligned_small := makeIndexedWires "p2_aligned_small" 56
  let p2_eff_sub := Wire.mk "p2_eff_sub"
  let p2_sticky := Wire.mk "p2_sticky"
  let p2_any_nan := Wire.mk "p2_any_nan"
  let p2_inf_sub_inf := Wire.mk "p2_inf_sub_inf"
  let p2_any_inf := Wire.mk "p2_any_inf"
  let p2_inf_sign := Wire.mk "p2_inf_sign"
  let p2_rm := makeIndexedWires "p2_rm" 3
  let p2_tag := makeIndexedWires "p2_tag" 6
  let p2_valid := Wire.mk "p2_valid"

  let big_mant56 := [zero, zero, zero] ++ s2_big_mant
  let p2_dffs :=
    [Gate.mkDFF s2_big_sign clock reset p2_big_sign,
     Gate.mkDFF s2_small_sign clock reset p2_small_sign,
     Gate.mkDFF s2_eff_sub clock reset p2_eff_sub,
     Gate.mkDFF s2_shift_sticky clock reset p2_sticky,
     Gate.mkDFF p1_any_nan clock reset p2_any_nan,
     Gate.mkDFF s2_inf_sub_inf clock reset p2_inf_sub_inf,
     Gate.mkDFF p1_any_inf clock reset p2_any_inf,
     Gate.mkDFF s2_inf_sign clock reset p2_inf_sign] ++
    mkDFFBank s2_big_exp p2_big_exp clock reset ++
    mkDFFBank big_mant56 p2_big_mant clock reset ++
    mkDFFBank s2_aligned_small p2_aligned_small clock reset ++
    mkDFFBank p1_rm p2_rm clock reset ++
    mkDFFBank p1_tag p2_tag clock reset ++
    [Gate.mkDFF p1_valid clock reset p2_valid]

  -- ══════════════════════════════════════════════
  -- STAGE 3: Mantissa Add/Sub + Leading Zero Detect
  -- ══════════════════════════════════════════════
  let s3_sum := makeIndexedWires "s3_sum" 56
  let s3_carry := makeIndexedWires "s3_c" 57
  let s3_add_gates := [Gate.mkBUF p2_eff_sub (s3_carry[0]!)] ++ (List.range 56).flatMap (fun i =>
    let a := p2_big_mant[i]!
    let b_raw := p2_aligned_small[i]!
    let b := Wire.mk s!"s3_b_{i}"
    let ci := s3_carry[i]!
    let co := s3_carry[i + 1]!
    let xab := Wire.mk s!"s3_x_{i}"
    [Gate.mkXOR b_raw p2_eff_sub b,
     Gate.mkXOR a b xab,
     Gate.mkXOR xab ci (s3_sum[i]!),
     Gate.mkAND a b (Wire.mk s!"s3_at0_{i}"),
     Gate.mkAND a ci (Wire.mk s!"s3_at1_{i}"),
     Gate.mkAND b ci (Wire.mk s!"s3_at2_{i}"),
     Gate.mkOR (Wire.mk s!"s3_at0_{i}") (Wire.mk s!"s3_at1_{i}") (Wire.mk s!"s3_at01_{i}"),
     Gate.mkOR (Wire.mk s!"s3_at01_{i}") (Wire.mk s!"s3_at2_{i}") co]
  )

  let not_eff_sub := Wire.mk "s3_not_eff_sub"
  let s3_overflow := Wire.mk "s3_overflow"
  let s3_ovf_gates := [
    Gate.mkNOT p2_eff_sub not_eff_sub,
    Gate.mkAND (s3_carry[56]!) not_eff_sub s3_overflow
  ]

  -- Leading zero detection on 56-bit sum (parallel prefix)
  let lz_v := makeIndexedWires "s3_lz_v" 56
  let lz_p := (List.range 56).map fun i => makeIndexedWires ("s3_lz_p_" ++ toString i) 6
  let lz_leaf_gates := (List.range 56).flatMap fun i =>
    [Gate.mkBUF (s3_sum[i]!) (lz_v[i]!)] ++
    (List.range 6).map fun k =>
      let bit_val := if (i >>> k) &&& 1 == 1 then one else zero
      Gate.mkBUF bit_val ((lz_p[i]!)[k]!)

  let strides := [1, 2, 4, 8, 16, 32]
  let (lz_prefix_gates, lz_final_v, lz_final_p) :=
    strides.foldl (fun (acc : List Gate × List Wire × List (List Wire)) stride =>
      let (gates_acc, v_prev, p_prev) := acc
      let lt := "s3_lz_s" ++ toString stride
      let v_new := makeIndexedWires (lt ++ "_v") 56
      let p_new := (List.range 56).map fun i => makeIndexedWires (lt ++ "_p_" ++ toString i) 6

      let level_gates := (List.range 56).flatMap fun i =>
        if i + stride < 56 then
          let merge_v := Wire.mk (lt ++ "_mv_" ++ toString i)
          [Gate.mkOR (v_prev[i + stride]!) (v_prev[i]!) merge_v,
           Gate.mkBUF merge_v (v_new[i]!)] ++
          (List.range 6).map fun k =>
            Gate.mkMUX ((p_prev[i]!)[k]!) ((p_prev[i + stride]!)[k]!) (v_prev[i + stride]!) ((p_new[i]!)[k]!)
        else
          [Gate.mkBUF (v_prev[i]!) (v_new[i]!)] ++
          (List.range 6).map fun k =>
            Gate.mkBUF ((p_prev[i]!)[k]!) ((p_new[i]!)[k]!)

      (gates_acc ++ level_gates, v_new, p_new)
    ) ([], lz_v, lz_p)

  let s3_lead_pos := lz_final_p[0]!
  let s3_found := lz_final_v[0]!

  -- Pipeline register 3 (DFFs)
  let p3_sign := Wire.mk "p3_sign"
  let p3_exp := makeIndexedWires "p3_exp" 11
  let p3_sum := makeIndexedWires "p3_sum" 56
  let p3_overflow := Wire.mk "p3_overflow"
  let p3_lead_pos := makeIndexedWires "p3_lead_pos" 6
  let p3_found := Wire.mk "p3_found"
  let p3_sticky := Wire.mk "p3_sticky"
  let p3_any_nan := Wire.mk "p3_any_nan"
  let p3_inf_sub_inf := Wire.mk "p3_inf_sub_inf"
  let p3_any_inf := Wire.mk "p3_any_inf"
  let p3_inf_sign := Wire.mk "p3_inf_sign"
  let p3_rm := makeIndexedWires "p3_rm" 3
  let p3_tag := makeIndexedWires "p3_tag" 6
  let p3_valid := Wire.mk "p3_valid"

  let p3_dffs :=
    [Gate.mkDFF p2_big_sign clock reset p3_sign,
     Gate.mkDFF s3_overflow clock reset p3_overflow,
     Gate.mkDFF s3_found clock reset p3_found,
     Gate.mkDFF p2_sticky clock reset p3_sticky,
     Gate.mkDFF p2_any_nan clock reset p3_any_nan,
     Gate.mkDFF p2_inf_sub_inf clock reset p3_inf_sub_inf,
     Gate.mkDFF p2_any_inf clock reset p3_any_inf,
     Gate.mkDFF p2_inf_sign clock reset p3_inf_sign] ++
    mkDFFBank p2_big_exp p3_exp clock reset ++
    mkDFFBank s3_sum p3_sum clock reset ++
    mkDFFBank s3_lead_pos p3_lead_pos clock reset ++
    mkDFFBank p2_rm p3_rm clock reset ++
    mkDFFBank p2_tag p3_tag clock reset ++
    [Gate.mkDFF p2_valid clock reset p3_valid]

  -- ══════════════════════════════════════════════
  -- STAGE 4: Normalize, Round, Special values, Pack
  -- ══════════════════════════════════════════════
  -- Overflow path: sum >> 1 (mantissa is sum[55:4], G=sum[3], R=sum[2], S=sum[1]|sum[0]|p3_sticky)
  let ovf_mant := (List.range 52).map fun i => p3_sum[4 + i]!
  let ovf_G := p3_sum[3]!
  let ovf_R := p3_sum[2]!
  let ovf_S := Wire.mk "s4_ovf_S"
  let ovf_s_or := Wire.mk "s4_ovf_s_or"
  let ovf_s_gates := [
    Gate.mkOR (p3_sum[1]!) (p3_sum[0]!) ovf_s_or,
    Gate.mkOR ovf_s_or p3_sticky ovf_S
  ]

  let ovf_exp := makeIndexedWires "s4_ovf_exp" 11
  let ovf_exp_c := makeIndexedWires "s4_ovf_exp_c" 12
  let ovf_exp_gates := [Gate.mkBUF one (ovf_exp_c[0]!)] ++ (List.range 11).flatMap (fun i =>
    [Gate.mkXOR (p3_exp[i]!) (ovf_exp_c[i]!) (ovf_exp[i]!),
     Gate.mkAND (p3_exp[i]!) (ovf_exp_c[i]!) (ovf_exp_c[i + 1]!)]
  )

  -- Normal path: lshift_amt = 55 - p3_lead_pos (6 bits)
  -- 55 = 0b110111
  let lshift_amt := makeIndexedWires "s4_lsh_amt" 6
  let lsh_b := makeIndexedWires "s4_lsh_b" 7
  let lsh_sub_gates := [Gate.mkBUF zero (lsh_b[0]!)] ++ (List.range 6).flatMap (fun i =>
    let a := if i == 3 then zero else one
    let b := p3_lead_pos[i]!
    let bi := lsh_b[i]!
    let bo := lsh_b[i + 1]!
    let xab := Wire.mk s!"s4_ls_x_{i}"
    [Gate.mkXOR a b xab,
     Gate.mkXOR xab bi (lshift_amt[i]!),
     Gate.mkNOT a (Wire.mk s!"s4_ls_na_{i}"),
     Gate.mkAND (Wire.mk s!"s4_ls_na_{i}") b (Wire.mk s!"s4_ls_t0_{i}"),
     Gate.mkAND (Wire.mk s!"s4_ls_na_{i}") bi (Wire.mk s!"s4_ls_t1_{i}"),
     Gate.mkAND b bi (Wire.mk s!"s4_ls_t2_{i}"),
     Gate.mkOR (Wire.mk s!"s4_ls_t0_{i}") (Wire.mk s!"s4_ls_t1_{i}") (Wire.mk s!"s4_ls_t01_{i}"),
     Gate.mkOR (Wire.mk s!"s4_ls_t01_{i}") (Wire.mk s!"s4_ls_t2_{i}") bo]
  )

  let norm56 := makeIndexedWires "s4_norm56" 56
  let lshift_gates := mkBarrelShiftLeft56 p3_sum lshift_amt norm56 zero "s4_lshift"

  -- norm_mant is bits 54..3 (52 bits)
  let norm_mant := (List.range 52).map fun i => norm56[3 + i]!
  let norm_G := norm56[2]!
  let norm_R := norm56[1]!
  let norm_S := Wire.mk "s4_norm_S"
  let norm_s_gate := Gate.mkOR (norm56[0]!) p3_sticky norm_S

  -- norm_exp = p3_exp - lshift_amt (11-bit)
  let norm_exp := makeIndexedWires "s4_norm_exp" 11
  let norm_exp_b := makeIndexedWires "s4_nexp_b" 12
  let lsh_ext := lshift_amt ++ (List.range 5 |>.map fun _ => zero)
  let norm_exp_gates := [Gate.mkBUF zero (norm_exp_b[0]!)] ++ (List.range 11).flatMap (fun i =>
    let a := p3_exp[i]!
    let b := lsh_ext[i]!
    let bi := norm_exp_b[i]!
    let bo := norm_exp_b[i + 1]!
    let xab := Wire.mk s!"s4_ne_x_{i}"
    [Gate.mkXOR a b xab,
     Gate.mkXOR xab bi (norm_exp[i]!),
     Gate.mkNOT a (Wire.mk s!"s4_ne_na_{i}"),
     Gate.mkAND (Wire.mk s!"s4_ne_na_{i}") b (Wire.mk s!"s4_ne_t0_{i}"),
     Gate.mkAND (Wire.mk s!"s4_ne_na_{i}") bi (Wire.mk s!"s4_ne_t1_{i}"),
     Gate.mkAND b bi (Wire.mk s!"s4_ne_t2_{i}"),
     Gate.mkOR (Wire.mk s!"s4_ne_t0_{i}") (Wire.mk s!"s4_ne_t1_{i}") (Wire.mk s!"s4_ne_t01_{i}"),
     Gate.mkOR (Wire.mk s!"s4_ne_t01_{i}") (Wire.mk s!"s4_ne_t2_{i}") bo]
  )

  -- Select between normal and overflow
  let pre_mant := makeIndexedWires "s4_pre_mant" 52
  let pre_mant_gates := (List.range 52).map fun i =>
    Gate.mkMUX (norm_mant[i]!) (ovf_mant[i]!) p3_overflow (pre_mant[i]!)

  let pre_exp := makeIndexedWires "s4_pre_exp" 11
  let pre_exp_gates := (List.range 11).map fun i =>
    Gate.mkMUX (norm_exp[i]!) (ovf_exp[i]!) p3_overflow (pre_exp[i]!)

  let g_bit := Wire.mk "s4_g_bit"
  let r_bit := Wire.mk "s4_r_bit"
  let s_bit := Wire.mk "s4_s_bit"
  let grs_mux_gates := [
    Gate.mkMUX norm_G ovf_G p3_overflow g_bit,
    Gate.mkMUX norm_R ovf_R p3_overflow r_bit,
    Gate.mkMUX norm_S ovf_S p3_overflow s_bit
  ]

  -- Rounding: RNE (round up if G && (R || S || mant[0]))
  let rs_or := Wire.mk "s4_rs_or"
  let rsl_or := Wire.mk "s4_rsl_or"
  let rne_up := Wire.mk "s4_rne_up"
  let is_not_rtz := Wire.mk "s4_is_not_rtz"
  let round_up := Wire.mk "s4_round_up"
  let rnd_ctrl_gates := [
    Gate.mkOR r_bit s_bit rs_or,
    Gate.mkOR rs_or (pre_mant[0]!) rsl_or,
    Gate.mkAND g_bit rsl_or rne_up,
    Gate.mkNOT (p3_rm[0]!) is_not_rtz,
    Gate.mkAND rne_up is_not_rtz round_up
  ]

  -- Increment mantissa by round_up (52-bit incrementer)
  let mant_inc := makeIndexedWires "s4_m_inc" 52
  let mant_inc_c := makeIndexedWires "s4_m_inc_c" 53
  let mant_inc_gates := [Gate.mkBUF round_up (mant_inc_c[0]!)] ++ (List.range 52).flatMap (fun i =>
    [Gate.mkXOR (pre_mant[i]!) (mant_inc_c[i]!) (mant_inc[i]!),
     Gate.mkAND (pre_mant[i]!) (mant_inc_c[i]!) (mant_inc_c[i + 1]!)]
  )
  let mant_rollover := mant_inc_c[52]!

  -- If mantissa rolled over, exp increments by 1
  let exp_post_rnd := makeIndexedWires "s4_exp_post_rnd" 11
  let exp_pr_c := makeIndexedWires "s4_epr_c" 12
  let exp_pr_gates := [Gate.mkBUF mant_rollover (exp_pr_c[0]!)] ++ (List.range 11).flatMap (fun i =>
    [Gate.mkXOR (pre_exp[i]!) (exp_pr_c[i]!) (exp_post_rnd[i]!),
     Gate.mkAND (pre_exp[i]!) (exp_pr_c[i]!) (exp_pr_c[i + 1]!)]
  )

  -- Final rounded mantissa (if rollover, all zeros)
  let rounded_mant := makeIndexedWires "s4_rnd_mant" 52
  let not_rollover := Wire.mk "s4_not_rollover"
  let rnd_mant_gates := [Gate.mkNOT mant_rollover not_rollover] ++
    (List.range 52).map fun i =>
      Gate.mkAND (mant_inc[i]!) not_rollover (rounded_mant[i]!)

  -- Inexact flag: G || R || S
  let gr_or := Wire.mk "s4_gr_or"
  let inexact := Wire.mk "s4_inexact"
  let inx_gates := [
    Gate.mkOR g_bit r_bit gr_or,
    Gate.mkOR gr_or s_bit inexact
  ]

  -- Zero cancellation detection
  let not_found := Wire.mk "s4_not_found"
  let zero_res := Wire.mk "s4_zero_res"
  let not_zero_res := Wire.mk "s4_not_zero_res"
  let zero_det_gates := [
    Gate.mkNOT p3_found not_found,
    Gate.mkAND not_found (Wire.mk "not_ovf_tmp") zero_res,
    Gate.mkNOT p3_overflow (Wire.mk "not_ovf_tmp"),
    Gate.mkNOT zero_res not_zero_res
  ]

  -- Masked regular result: if zero_res, mant=0, exp=0, sign=0, nx=0
  let reg_res := makeIndexedWires "s4_reg_res" 64
  let reg_res_gates :=
    (List.range 52).map (fun i => Gate.mkAND (rounded_mant[i]!) not_zero_res (reg_res[i]!)) ++
    (List.range 11).map (fun i => Gate.mkAND (exp_post_rnd[i]!) not_zero_res (reg_res[52 + i]!)) ++
    [Gate.mkAND p3_sign not_zero_res (reg_res[63]!)]

  let reg_nx := Wire.mk "s4_reg_nx"
  let reg_nx_gate := Gate.mkAND inexact not_zero_res reg_nx

  -- Canonical NaN (0x7ff8000000000000): sign=0, exp=0x7ff, mant[51]=1, rest=0
  let is_nan_res := Wire.mk "s4_is_nan_res"
  let is_nan_gate := Gate.mkOR p3_any_nan p3_inf_sub_inf is_nan_res

  -- Infinity result: sign=p3_inf_sign, exp=0x7ff, mant=0
  let not_nan_res := Wire.mk "s4_not_nan_res"
  let is_inf_res := Wire.mk "s4_is_inf_res"
  let inf_res_gates := [
    Gate.mkNOT is_nan_res not_nan_res,
    Gate.mkAND p3_any_inf not_nan_res is_inf_res
  ]

  -- Final result multiplexing
  let res_m0 := makeIndexedWires "s4_rm0" 64
  let res_mux_gates := (List.range 64).flatMap fun i =>
    let inf_bit :=
      if i == 63 then p3_inf_sign
      else if i >= 52 then one
      else zero
    let nan_bit :=
      if i >= 51 && i <= 62 then one
      else zero
    [Gate.mkMUX (reg_res[i]!) inf_bit is_inf_res (res_m0[i]!),
     Gate.mkMUX (res_m0[i]!) nan_bit is_nan_res (result[i]!)]

  -- Exceptions:
  -- exc[4] = NV (any_nan || inf_sub_inf)
  -- exc[0] = NX (reg_nx && !is_nan_res && !is_inf_res)
  let not_special := Wire.mk "s4_not_special"
  let exc_gates := [
    Gate.mkBUF is_nan_res (exc[4]!),
    Gate.mkBUF zero (exc[3]!),
    Gate.mkBUF zero (exc[2]!),
    Gate.mkBUF zero (exc[1]!),
    Gate.mkOR is_nan_res is_inf_res (Wire.mk "s4_is_sp"),
    Gate.mkNOT (Wire.mk "s4_is_sp") not_special,
    Gate.mkAND reg_nx not_special (exc[0]!)
  ]

  let tag_gates := (List.range 6).map fun i => Gate.mkBUF (p3_tag[i]!) (tag_out[i]!)

  let all_gates :=
    [one_gate, s1_sign2_gate] ++ exp1_or_gates ++ exp2_or_gates ++
    exp1_and_gates ++ exp2_and_gates ++ mant1_lo_gates ++ mant2_lo_gates ++
    special_gates ++ s1_sub_gates ++ s1_mant_sub_gates ++ swap_gates ++ p1_dffs ++
    s2_sign_swap_gates ++ s2_exp_swap_gates ++ s2_mant_swap_gates ++
    s2_neg_gates ++ s2_sh_mux_gates ++ s2_shift_gates ++
    [s2_eff_sub_gate, s2_inf_sub_inf_gate, s2_inf_sign_gate] ++ p2_dffs ++
    s3_add_gates ++ s3_ovf_gates ++ lz_leaf_gates ++ lz_prefix_gates ++ p3_dffs ++
    ovf_s_gates ++ ovf_exp_gates ++ lsh_sub_gates ++ lshift_gates ++
    [norm_s_gate] ++ norm_exp_gates ++ pre_mant_gates ++ pre_exp_gates ++ grs_mux_gates ++
    rnd_ctrl_gates ++ mant_inc_gates ++ exp_pr_gates ++ rnd_mant_gates ++ inx_gates ++
    zero_det_gates ++ reg_res_gates ++ [reg_nx_gate, is_nan_gate] ++ inf_res_gates ++
    res_mux_gates ++ exc_gates ++ tag_gates ++ [Gate.mkBUF p3_valid valid_out]

  { name := "FPAdderD"
    inputs := src1 ++ src2 ++ [op_sub] ++ rm ++ dest_tag ++ [valid_in, clock, reset, zero]
    outputs := result ++ tag_out ++ exc ++ [valid_out]
    gates := all_gates
    instances := [] }

def fpAdderDCircuit : Circuit := mkFPAdderD

end Shoumei.Circuits.Sequential
