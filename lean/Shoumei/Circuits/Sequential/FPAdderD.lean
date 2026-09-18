/-
Circuits/Sequential/FPAdderD.lean - 4-Stage Pipelined Double-Precision FP Adder/Subtractor

A pipelined floating-point adder/subtractor for IEEE 754 binary64.

Decomposed hierarchically into 4 combinational pipeline stage modules:
  Stage 1 (FPAdderD_Stage1_Unpack): Unpack + Exponent difference + Swap detection + NaN/Inf detection
  Stage 2 (FPAdderD_Stage2_Align): Swap operands + Alignment barrel shift with sticky tracking
  Stage 3 (FPAdderD_Stage3_AddSub): Mantissa add/sub + Leading-zero parallel prefix detect
  Stage 4 (FPAdderD_Stage4_NormRound): Normalization shifter + Rounding + Special value handling + Pack

Interface:
- Inputs: src1[63:0], src2[63:0], op_sub, rm[2:0], dest_tag[5:0], valid_in, clock, reset, zero
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

/-! ## Pipeline Stage 1: Unpack, Exponent difference, Swap detection, Special cases -/

def mkFPAdderD_Stage1_Unpack : Circuit :=
  let src1 := makeIndexedWires "src1" 64
  let src2 := makeIndexedWires "src2" 64
  let op_sub := Wire.mk "op_sub"
  let zero := Wire.mk "zero"

  let sign1 := Wire.mk "sign1"
  let sign2 := Wire.mk "sign2"
  let exp1 := makeIndexedWires "exp1" 11
  let exp2 := makeIndexedWires "exp2" 11
  let mant1 := makeIndexedWires "mant1" 53
  let mant2 := makeIndexedWires "mant2" 53
  let exp_diff := makeIndexedWires "exp_diff" 11
  let swap := Wire.mk "swap"
  let any_nan := Wire.mk "any_nan"
  let both_inf := Wire.mk "both_inf"
  let any_inf := Wire.mk "any_inf"
  let a_is_inf := Wire.mk "a_is_inf"

  let s1_sign1_gate := Gate.mkBUF (src1[63]!) sign1
  let s1_sign2_gate := Gate.mkXOR (src2[63]!) op_sub sign2

  let s1_exp1_src := (List.range 11).map fun i => src1[52 + i]!
  let s1_exp2_src := (List.range 11).map fun i => src2[52 + i]!

  let exp1_buf_gates := List.zipWith Gate.mkBUF s1_exp1_src exp1
  let exp2_buf_gates := List.zipWith Gate.mkBUF s1_exp2_src exp2

  let (exp1_or_all, exp1_or_gates) := mkOrTree "s1_e1_or" s1_exp1_src
  let (exp2_or_all, exp2_or_gates) := mkOrTree "s1_e2_or" s1_exp2_src
  let (exp1_and_all, exp1_and_gates) := mkAndTree "s1_e1_and" s1_exp1_src
  let (exp2_and_all, exp2_and_gates) := mkAndTree "s1_e2_and" s1_exp2_src

  let (mant1_lo_or, mant1_lo_gates) := mkOrTree "s1_m1_or" ((List.range 52).map fun i => src1[i]!)
  let (mant2_lo_or, mant2_lo_gates) := mkOrTree "s1_m2_or" ((List.range 52).map fun i => src2[i]!)

  let a_is_nan := Wire.mk "s1_a_is_nan"
  let b_is_nan := Wire.mk "s1_b_is_nan"
  let not_m1_lo := Wire.mk "s1_not_m1_lo"
  let not_m2_lo := Wire.mk "s1_not_m2_lo"

  let special_gates := [
    Gate.mkAND exp1_and_all mant1_lo_or a_is_nan,
    Gate.mkAND exp2_and_all mant2_lo_or b_is_nan,
    Gate.mkNOT mant1_lo_or not_m1_lo,
    Gate.mkNOT mant2_lo_or not_m2_lo,
    Gate.mkAND exp1_and_all not_m1_lo a_is_inf,
    Gate.mkAND exp2_and_all not_m2_lo (Wire.mk "s1_b_is_inf"),
    Gate.mkOR a_is_nan b_is_nan any_nan,
    Gate.mkAND a_is_inf (Wire.mk "s1_b_is_inf") both_inf,
    Gate.mkOR a_is_inf (Wire.mk "s1_b_is_inf") any_inf
  ]

  let mant1_gates :=
    ((List.range 52).map fun i => Gate.mkBUF (src1[i]!) (mant1[i]!)) ++
    [Gate.mkBUF exp1_or_all (mant1[52]!)]
  let mant2_gates :=
    ((List.range 52).map fun i => Gate.mkBUF (src2[i]!) (mant2[i]!)) ++
    [Gate.mkBUF exp2_or_all (mant2[52]!)]

  -- Exponent difference exp1 - exp2 (11-bit)
  let s1_borrow := makeIndexedWires "s1_borrow" 12
  let s1_sub_gates := [Gate.mkBUF zero (s1_borrow[0]!)] ++ (List.range 11).flatMap (fun i =>
    let a := s1_exp1_src[i]!
    let b := s1_exp2_src[i]!
    let bi := s1_borrow[i]!
    let bo := s1_borrow[i + 1]!
    let xab := Wire.mk s!"s1_es_x_{i}"
    [Gate.mkXOR a b xab,
     Gate.mkXOR xab bi (exp_diff[i]!),
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
    let a := if i < 52 then src1[i]! else exp1_or_all
    let b := if i < 52 then src2[i]! else exp2_or_all
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

  let (exp_diff_any, exp_diff_any_gates) := mkOrTree "s1_ediff_any" exp_diff
  let not_ediff_any := Wire.mk "s1_not_ediff_any"
  let exp_eq := Wire.mk "s1_exp_eq"
  let swap_mant := Wire.mk "s1_swap_mant"
  let swap_gates := exp_diff_any_gates ++ [
    Gate.mkNOT exp_diff_any not_ediff_any,
    Gate.mkAND not_ediff_any not_ediff_any exp_eq,
    Gate.mkAND exp_eq s1_mant_borrow swap_mant,
    Gate.mkOR (s1_borrow[11]!) swap_mant swap
  ]

  let all_gates :=
    [s1_sign1_gate, s1_sign2_gate] ++ exp1_buf_gates ++ exp2_buf_gates ++
    exp1_or_gates ++ exp2_or_gates ++ exp1_and_gates ++ exp2_and_gates ++
    mant1_lo_gates ++ mant2_lo_gates ++ special_gates ++
    mant1_gates ++ mant2_gates ++ s1_sub_gates ++ s1_mant_sub_gates ++ swap_gates

  { name := "FPAdderD_Stage1_Unpack"
    inputs := src1 ++ src2 ++ [op_sub, zero]
    outputs := [sign1, sign2] ++ exp1 ++ exp2 ++ mant1 ++ mant2 ++ exp_diff ++
               [swap, any_nan, both_inf, any_inf, a_is_inf]
    gates := all_gates
    instances := []
    signalGroups := [
      { name := "src1", width := 64, wires := src1 },
      { name := "src2", width := 64, wires := src2 },
      { name := "exp1", width := 11, wires := exp1 },
      { name := "exp2", width := 11, wires := exp2 },
      { name := "mant1", width := 53, wires := mant1 },
      { name := "mant2", width := 53, wires := mant2 },
      { name := "exp_diff", width := 11, wires := exp_diff }
    ] }

def fpAdderD_Stage1Circuit : Circuit := mkFPAdderD_Stage1_Unpack

/-! ## Pipeline Stage 2: Swap operands + Alignment barrel shift with sticky -/

def mkFPAdderD_Stage2_Align : Circuit :=
  let sign1 := Wire.mk "sign1"
  let sign2 := Wire.mk "sign2"
  let exp1 := makeIndexedWires "exp1" 11
  let exp2 := makeIndexedWires "exp2" 11
  let mant1 := makeIndexedWires "mant1" 53
  let mant2 := makeIndexedWires "mant2" 53
  let exp_diff := makeIndexedWires "exp_diff" 11
  let swap := Wire.mk "swap"
  let both_inf := Wire.mk "both_inf"
  let a_is_inf := Wire.mk "a_is_inf"
  let zero := Wire.mk "zero"

  let big_sign := Wire.mk "big_sign"
  let small_sign := Wire.mk "small_sign"
  let eff_sub := Wire.mk "eff_sub"
  let shift_sticky := Wire.mk "shift_sticky"
  let inf_sub_inf := Wire.mk "inf_sub_inf"
  let inf_sign := Wire.mk "inf_sign"
  let big_exp := makeIndexedWires "big_exp" 11
  let big_mant := makeIndexedWires "big_mant" 56
  let aligned_small := makeIndexedWires "aligned_small" 56

  let one := Wire.mk "s2_one"
  let one_gate := Gate.mkNOT zero one

  let s2_sign_swap_gates := [
    Gate.mkMUX sign1 sign2 swap big_sign,
    Gate.mkMUX sign2 sign1 swap small_sign
  ]

  let s2_exp_swap_gates := (List.range 11).map fun i =>
    Gate.mkMUX (exp1[i]!) (exp2[i]!) swap (big_exp[i]!)

  let s2_big_mant53 := makeIndexedWires "s2_big_mant53" 53
  let s2_small_mant := makeIndexedWires "s2_small_mant" 53
  let s2_mant_swap_gates := (List.range 53).flatMap fun i =>
    [Gate.mkMUX (mant1[i]!) (mant2[i]!) swap (s2_big_mant53[i]!),
     Gate.mkMUX (mant2[i]!) (mant1[i]!) swap (s2_small_mant[i]!)]

  let s2_neg_diff := makeIndexedWires "s2_neg_diff" 6
  let s2_neg_carry := makeIndexedWires "s2_neg_c" 7
  let s2_neg_gates := [Gate.mkBUF one (s2_neg_carry[0]!)] ++ (List.range 6).flatMap (fun i =>
    let nbit := Wire.mk s!"s2_nd_{i}"
    [Gate.mkNOT (exp_diff[i]!) nbit,
     Gate.mkXOR nbit (s2_neg_carry[i]!) (s2_neg_diff[i]!),
     Gate.mkAND nbit (s2_neg_carry[i]!) (s2_neg_carry[i + 1]!)]
  )

  let exp_diff_zeros := (List.range 5).map fun i =>
    (Gate.mkNOT (exp_diff[6 + i]!) (Wire.mk s!"s2_ed_not_{6 + i}"),
     Gate.mkAND (exp_diff[6 + i]!) (Wire.mk s!"s2_ed_not_{6 + i}") (Wire.mk s!"s2_ed_z_{6 + i}"))
  let exp_diff_zero_gates := exp_diff_zeros.flatMap fun (g1, g2) => [g1, g2]
  let ed_z_or01 := Wire.mk "s2_ed_z_or01"
  let ed_z_or23 := Wire.mk "s2_ed_z_or23"
  let ed_z_or0123 := Wire.mk "s2_ed_z_or0123"
  let ed_z_all := Wire.mk "s2_ed_z_all"
  let ed_tree_gates := [
    Gate.mkOR (Wire.mk "s2_ed_z_6") (Wire.mk "s2_ed_z_7") ed_z_or01,
    Gate.mkOR (Wire.mk "s2_ed_z_8") (Wire.mk "s2_ed_z_9") ed_z_or23,
    Gate.mkOR ed_z_or01 ed_z_or23 ed_z_or0123,
    Gate.mkOR ed_z_or0123 (Wire.mk "s2_ed_z_10") ed_z_all
  ]

  let s2_shift_amt := makeIndexedWires "s2_sh_amt" 6
  let s2_sh_amt_pre0 := Wire.mk "s2_sh_amt_pre0"
  let s2_sh_mux_gates :=
    [Gate.mkMUX (exp_diff[0]!) (s2_neg_diff[0]!) swap s2_sh_amt_pre0,
     Gate.mkOR s2_sh_amt_pre0 ed_z_all (s2_shift_amt[0]!)] ++
    (List.range 5).map fun i =>
      Gate.mkMUX (exp_diff[i + 1]!) (s2_neg_diff[i + 1]!) swap (s2_shift_amt[i + 1]!)

  let s2_small_mant56 := [zero, zero, zero] ++ s2_small_mant
  let s2_shift_gates := mkBarrelShiftRight56WithSticky s2_small_mant56 s2_shift_amt aligned_small shift_sticky zero "s2_align"

  let s2_eff_sub_gate := Gate.mkXOR big_sign small_sign eff_sub
  let s2_inf_sub_inf_gate := Gate.mkAND both_inf eff_sub inf_sub_inf
  let s2_inf_sign_gate := Gate.mkMUX sign2 sign1 a_is_inf inf_sign

  let big_mant_gates :=
    [Gate.mkBUF zero (big_mant[0]!),
     Gate.mkBUF zero (big_mant[1]!),
     Gate.mkBUF zero (big_mant[2]!)] ++
    (List.range 53).map fun i =>
      Gate.mkBUF (s2_big_mant53[i]!) (big_mant[3 + i]!)

  let all_gates :=
    [one_gate] ++ s2_sign_swap_gates ++ s2_exp_swap_gates ++ s2_mant_swap_gates ++
    s2_neg_gates ++ exp_diff_zero_gates ++ ed_tree_gates ++ s2_sh_mux_gates ++ s2_shift_gates ++
    [s2_eff_sub_gate, s2_inf_sub_inf_gate, s2_inf_sign_gate] ++ big_mant_gates

  { name := "FPAdderD_Stage2_Align"
    inputs := [sign1, sign2] ++ exp1 ++ exp2 ++ mant1 ++ mant2 ++ exp_diff ++
              [swap, both_inf, a_is_inf, zero]
    outputs := [big_sign, small_sign, eff_sub, shift_sticky, inf_sub_inf, inf_sign] ++
               big_exp ++ big_mant ++ aligned_small
    gates := all_gates
    instances := []
    signalGroups := [
      { name := "exp1", width := 11, wires := exp1 },
      { name := "exp2", width := 11, wires := exp2 },
      { name := "mant1", width := 53, wires := mant1 },
      { name := "mant2", width := 53, wires := mant2 },
      { name := "exp_diff", width := 11, wires := exp_diff },
      { name := "big_exp", width := 11, wires := big_exp },
      { name := "big_mant", width := 56, wires := big_mant },
      { name := "aligned_small", width := 56, wires := aligned_small }
    ] }

def fpAdderD_Stage2Circuit : Circuit := mkFPAdderD_Stage2_Align

/-! ## Pipeline Stage 3: Mantissa Add/Sub + Leading Zero Detect -/

def mkFPAdderD_Stage3_AddSub : Circuit :=
  let big_mant := makeIndexedWires "big_mant" 56
  let aligned_small := makeIndexedWires "aligned_small" 56
  let eff_sub := Wire.mk "eff_sub"
  let zero := Wire.mk "zero"

  let sum := makeIndexedWires "sum" 56
  let overflow := Wire.mk "overflow"
  let lead_pos := makeIndexedWires "lead_pos" 6
  let found := Wire.mk "found"

  let one := Wire.mk "s3_one"
  let one_gate := Gate.mkNOT zero one

  let s3_carry := makeIndexedWires "s3_c" 57
  let s3_add_gates := [Gate.mkBUF eff_sub (s3_carry[0]!)] ++ (List.range 56).flatMap (fun i =>
    let a := big_mant[i]!
    let b_raw := aligned_small[i]!
    let b := Wire.mk s!"s3_b_{i}"
    let ci := s3_carry[i]!
    let co := s3_carry[i + 1]!
    let xab := Wire.mk s!"s3_x_{i}"
    [Gate.mkXOR b_raw eff_sub b,
     Gate.mkXOR a b xab,
     Gate.mkXOR xab ci (sum[i]!),
     Gate.mkAND a b (Wire.mk s!"s3_at0_{i}"),
     Gate.mkAND a ci (Wire.mk s!"s3_at1_{i}"),
     Gate.mkAND b ci (Wire.mk s!"s3_at2_{i}"),
     Gate.mkOR (Wire.mk s!"s3_at0_{i}") (Wire.mk s!"s3_at1_{i}") (Wire.mk s!"s3_at01_{i}"),
     Gate.mkOR (Wire.mk s!"s3_at01_{i}") (Wire.mk s!"s3_at2_{i}") co]
  )

  let not_eff_sub := Wire.mk "s3_not_eff_sub"
  let s3_ovf_gates := [
    Gate.mkNOT eff_sub not_eff_sub,
    Gate.mkAND (s3_carry[56]!) not_eff_sub overflow
  ]

  -- Leading zero detection on 56-bit sum (parallel prefix)
  let lz_v := makeIndexedWires "s3_lz_v" 56
  let lz_p := (List.range 56).map fun i => makeIndexedWires ("s3_lz_p_" ++ toString i) 6
  let lz_leaf_gates := (List.range 56).flatMap fun i =>
    [Gate.mkBUF (sum[i]!) (lz_v[i]!)] ++
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

  let s3_lead_pos_gates := (List.range 6).map fun k =>
    Gate.mkBUF ((lz_final_p[0]!)[k]!) (lead_pos[k]!)
  let s3_found_gate := Gate.mkBUF (lz_final_v[0]!) found

  let all_gates :=
    [one_gate] ++ s3_add_gates ++ s3_ovf_gates ++ lz_leaf_gates ++ lz_prefix_gates ++
    s3_lead_pos_gates ++ [s3_found_gate]

  { name := "FPAdderD_Stage3_AddSub"
    inputs := big_mant ++ aligned_small ++ [eff_sub, zero]
    outputs := sum ++ [overflow] ++ lead_pos ++ [found]
    gates := all_gates
    instances := []
    signalGroups := [
      { name := "big_mant", width := 56, wires := big_mant },
      { name := "aligned_small", width := 56, wires := aligned_small },
      { name := "sum", width := 56, wires := sum },
      { name := "lead_pos", width := 6, wires := lead_pos }
    ] }

def fpAdderD_Stage3Circuit : Circuit := mkFPAdderD_Stage3_AddSub

/-! ## Pipeline Stage 4: Normalize, Round, Special values, Pack -/

def mkFPAdderD_Stage4_NormRound : Circuit :=
  let sign := Wire.mk "sign"
  let exp := makeIndexedWires "exp" 11
  let sum := makeIndexedWires "sum" 56
  let overflow := Wire.mk "overflow"
  let lead_pos := makeIndexedWires "lead_pos" 6
  let found := Wire.mk "found"
  let sticky := Wire.mk "sticky"
  let any_nan := Wire.mk "any_nan"
  let inf_sub_inf := Wire.mk "inf_sub_inf"
  let any_inf := Wire.mk "any_inf"
  let inf_sign := Wire.mk "inf_sign"
  let rm := makeIndexedWires "rm" 3
  let zero := Wire.mk "zero"

  let result := makeIndexedWires "result" 64
  let exc := makeIndexedWires "exc" 5

  let one := Wire.mk "s4_one"
  let one_gate := Gate.mkNOT zero one

  -- Overflow path: sum >> 1
  let ovf_mant := (List.range 52).map fun i => sum[4 + i]!
  let ovf_G := sum[3]!
  let ovf_R := sum[2]!
  let ovf_S := Wire.mk "s4_ovf_S"
  let ovf_s_or := Wire.mk "s4_ovf_s_or"
  let ovf_s_gates := [
    Gate.mkOR (sum[1]!) (sum[0]!) ovf_s_or,
    Gate.mkOR ovf_s_or sticky ovf_S
  ]

  let ovf_exp := makeIndexedWires "s4_ovf_exp" 11
  let ovf_exp_c := makeIndexedWires "s4_ovf_exp_c" 12
  let ovf_exp_gates := [Gate.mkBUF one (ovf_exp_c[0]!)] ++ (List.range 11).flatMap (fun i =>
    [Gate.mkXOR (exp[i]!) (ovf_exp_c[i]!) (ovf_exp[i]!),
     Gate.mkAND (exp[i]!) (ovf_exp_c[i]!) (ovf_exp_c[i + 1]!)]
  )

  -- Normal path: lshift_amt = 55 - lead_pos (6 bits)
  let lshift_amt := makeIndexedWires "s4_lsh_amt" 6
  let lsh_b := makeIndexedWires "s4_lsh_b" 7
  let lsh_sub_gates := [Gate.mkBUF zero (lsh_b[0]!)] ++ (List.range 6).flatMap (fun i =>
    let a := if i == 3 then zero else one
    let b := lead_pos[i]!
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
  let lshift_gates := mkBarrelShiftLeft56 sum lshift_amt norm56 zero "s4_lshift"

  let norm_mant := (List.range 52).map fun i => norm56[3 + i]!
  let norm_G := norm56[2]!
  let norm_R := norm56[1]!
  let norm_S := Wire.mk "s4_norm_S"
  let norm_s_gate := Gate.mkOR (norm56[0]!) sticky norm_S

  let norm_exp := makeIndexedWires "s4_norm_exp" 11
  let norm_exp_b := makeIndexedWires "s4_nexp_b" 12
  let lsh_ext := lshift_amt ++ (List.range 5 |>.map fun _ => zero)
  let norm_exp_gates := [Gate.mkBUF zero (norm_exp_b[0]!)] ++ (List.range 11).flatMap (fun i =>
    let a := exp[i]!
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

  let pre_mant := makeIndexedWires "s4_pre_mant" 52
  let pre_mant_gates := (List.range 52).map fun i =>
    Gate.mkMUX (norm_mant[i]!) (ovf_mant[i]!) overflow (pre_mant[i]!)

  let pre_exp := makeIndexedWires "s4_pre_exp" 11
  let pre_exp_gates := (List.range 11).map fun i =>
    Gate.mkMUX (norm_exp[i]!) (ovf_exp[i]!) overflow (pre_exp[i]!)

  let g_bit := Wire.mk "s4_g_bit"
  let r_bit := Wire.mk "s4_r_bit"
  let s_bit := Wire.mk "s4_s_bit"
  let grs_mux_gates := [
    Gate.mkMUX norm_G ovf_G overflow g_bit,
    Gate.mkMUX norm_R ovf_R overflow r_bit,
    Gate.mkMUX norm_S ovf_S overflow s_bit
  ]

  let rs_or := Wire.mk "s4_rs_or"
  let rsl_or := Wire.mk "s4_rsl_or"
  let rne_up := Wire.mk "s4_rne_up"
  let is_not_rtz := Wire.mk "s4_is_not_rtz"
  let round_up := Wire.mk "s4_round_up"
  let rnd_ctrl_gates := [
    Gate.mkOR r_bit s_bit rs_or,
    Gate.mkOR rs_or (pre_mant[0]!) rsl_or,
    Gate.mkAND g_bit rsl_or rne_up,
    Gate.mkNOT (rm[0]!) is_not_rtz,
    Gate.mkAND rne_up is_not_rtz round_up
  ]

  let mant_inc := makeIndexedWires "s4_m_inc" 52
  let mant_inc_c := makeIndexedWires "s4_m_inc_c" 53
  let mant_inc_gates := [Gate.mkBUF round_up (mant_inc_c[0]!)] ++ (List.range 52).flatMap (fun i =>
    [Gate.mkXOR (pre_mant[i]!) (mant_inc_c[i]!) (mant_inc[i]!),
     Gate.mkAND (pre_mant[i]!) (mant_inc_c[i]!) (mant_inc_c[i + 1]!)]
  )
  let mant_rollover := mant_inc_c[52]!

  let exp_post_rnd := makeIndexedWires "s4_exp_post_rnd" 11
  let exp_pr_c := makeIndexedWires "s4_epr_c" 12
  let exp_pr_gates := [Gate.mkBUF mant_rollover (exp_pr_c[0]!)] ++ (List.range 11).flatMap (fun i =>
    [Gate.mkXOR (pre_exp[i]!) (exp_pr_c[i]!) (exp_post_rnd[i]!),
     Gate.mkAND (pre_exp[i]!) (exp_pr_c[i]!) (exp_pr_c[i + 1]!)]
  )

  let rounded_mant := makeIndexedWires "s4_rnd_mant" 52
  let not_rollover := Wire.mk "s4_not_rollover"
  let rnd_mant_gates := [Gate.mkNOT mant_rollover not_rollover] ++
    (List.range 52).map fun i =>
      Gate.mkAND (mant_inc[i]!) not_rollover (rounded_mant[i]!)

  let gr_or := Wire.mk "s4_gr_or"
  let inexact := Wire.mk "s4_inexact"
  let inx_gates := [
    Gate.mkOR g_bit r_bit gr_or,
    Gate.mkOR gr_or s_bit inexact
  ]

  let not_found := Wire.mk "s4_not_found"
  let zero_res := Wire.mk "s4_zero_res"
  let not_zero_res := Wire.mk "s4_not_zero_res"
  let zero_det_gates := [
    Gate.mkNOT found not_found,
    Gate.mkAND not_found (Wire.mk "not_ovf_tmp") zero_res,
    Gate.mkNOT overflow (Wire.mk "not_ovf_tmp"),
    Gate.mkNOT zero_res not_zero_res
  ]

  let reg_res := makeIndexedWires "s4_reg_res" 64
  let reg_res_gates :=
    (List.range 52).map (fun i => Gate.mkAND (rounded_mant[i]!) not_zero_res (reg_res[i]!)) ++
    (List.range 11).map (fun i => Gate.mkAND (exp_post_rnd[i]!) not_zero_res (reg_res[52 + i]!)) ++
    [Gate.mkAND sign not_zero_res (reg_res[63]!)]

  let reg_nx := Wire.mk "s4_reg_nx"
  let reg_nx_gate := Gate.mkAND inexact not_zero_res reg_nx

  let is_nan_res := Wire.mk "s4_is_nan_res"
  let is_nan_gate := Gate.mkOR any_nan inf_sub_inf is_nan_res

  let not_nan_res := Wire.mk "s4_not_nan_res"
  let is_inf_res := Wire.mk "s4_is_inf_res"
  let inf_res_gates := [
    Gate.mkNOT is_nan_res not_nan_res,
    Gate.mkAND any_inf not_nan_res is_inf_res
  ]

  let res_m0 := makeIndexedWires "s4_rm0" 64
  let res_mux_gates := (List.range 64).flatMap fun i =>
    let inf_bit :=
      if i == 63 then inf_sign
      else if i >= 52 then one
      else zero
    let nan_bit :=
      if i >= 51 && i <= 62 then one
      else zero
    [Gate.mkMUX (reg_res[i]!) inf_bit is_inf_res (res_m0[i]!),
     Gate.mkMUX (res_m0[i]!) nan_bit is_nan_res (result[i]!)]

  let not_rm1 := Wire.mk "s4_not_rm1"
  let not_rm2 := Wire.mk "s4_not_rm2"
  let rm_xor12 := Wire.mk "s4_rm_xor12"
  let not_rm_xor12 := Wire.mk "s4_not_rm_xor12"
  let not_special := Wire.mk "s4_not_special"
  let exc_gates := [
    Gate.mkBUF is_nan_res (exc[4]!),
    Gate.mkNOT (rm[1]!) not_rm1,
    Gate.mkAND (rm[1]!) not_rm1 (exc[1]!),
    Gate.mkNOT (rm[2]!) not_rm2,
    Gate.mkAND (rm[2]!) not_rm2 (exc[2]!),
    Gate.mkXOR (rm[1]!) (rm[2]!) rm_xor12,
    Gate.mkNOT rm_xor12 not_rm_xor12,
    Gate.mkAND rm_xor12 not_rm_xor12 (exc[3]!),
    Gate.mkOR is_nan_res is_inf_res (Wire.mk "s4_is_sp"),
    Gate.mkNOT (Wire.mk "s4_is_sp") not_special,
    Gate.mkAND reg_nx not_special (exc[0]!)
  ]

  let all_gates :=
    [one_gate] ++ ovf_s_gates ++ ovf_exp_gates ++ lsh_sub_gates ++ lshift_gates ++
    [norm_s_gate] ++ norm_exp_gates ++ pre_mant_gates ++ pre_exp_gates ++ grs_mux_gates ++
    rnd_ctrl_gates ++ mant_inc_gates ++ exp_pr_gates ++ rnd_mant_gates ++ inx_gates ++
    zero_det_gates ++ reg_res_gates ++ [reg_nx_gate, is_nan_gate] ++ inf_res_gates ++
    res_mux_gates ++ exc_gates

  { name := "FPAdderD_Stage4_NormRound"
    inputs := [sign] ++ exp ++ sum ++ [overflow] ++ lead_pos ++
              [found, sticky, any_nan, inf_sub_inf, any_inf, inf_sign] ++ rm ++ [zero]
    outputs := result ++ exc
    gates := all_gates
    instances := []
    signalGroups := [
      { name := "exp", width := 11, wires := exp },
      { name := "sum", width := 56, wires := sum },
      { name := "lead_pos", width := 6, wires := lead_pos },
      { name := "rm", width := 3, wires := rm },
      { name := "result", width := 64, wires := result },
      { name := "exc", width := 5, wires := exc }
    ] }

def fpAdderD_Stage4Circuit : Circuit := mkFPAdderD_Stage4_NormRound

/-! ## Top-Level Hierarchical Circuit -/

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

  let result := makeIndexedWires "result" 64
  let tag_out := makeIndexedWires "tag_out" 6
  let exc := makeIndexedWires "exc" 5
  let valid_out := Wire.mk "valid_out"

  -- Stage 1 wires (combinational outputs from Stage 1)
  let s1_sign1 := Wire.mk "s1_sign1"
  let s1_sign2 := Wire.mk "s1_sign2"
  let s1_exp1 := makeIndexedWires "s1_exp1" 11
  let s1_exp2 := makeIndexedWires "s1_exp2" 11
  let s1_mant1 := makeIndexedWires "s1_mant1" 53
  let s1_mant2 := makeIndexedWires "s1_mant2" 53
  let s1_exp_diff := makeIndexedWires "s1_exp_diff" 11
  let s1_swap := Wire.mk "s1_swap"
  let s1_any_nan := Wire.mk "s1_any_nan"
  let s1_both_inf := Wire.mk "s1_both_inf"
  let s1_any_inf := Wire.mk "s1_any_inf"
  let s1_a_is_inf := Wire.mk "s1_a_is_inf"

  let stage1_inst : CircuitInstance := {
    moduleName := "FPAdderD_Stage1_Unpack"
    instName := "u_stage1"
    portMap :=
      ((List.range 64).map fun i => (s!"src1_{i}", src1[i]!)) ++
      ((List.range 64).map fun i => (s!"src2_{i}", src2[i]!)) ++
      [("op_sub", op_sub), ("zero", zero),
       ("sign1", s1_sign1), ("sign2", s1_sign2)] ++
      ((List.range 11).map fun i => (s!"exp1_{i}", s1_exp1[i]!)) ++
      ((List.range 11).map fun i => (s!"exp2_{i}", s1_exp2[i]!)) ++
      ((List.range 53).map fun i => (s!"mant1_{i}", s1_mant1[i]!)) ++
      ((List.range 53).map fun i => (s!"mant2_{i}", s1_mant2[i]!)) ++
      ((List.range 11).map fun i => (s!"exp_diff_{i}", s1_exp_diff[i]!)) ++
      [("swap", s1_swap), ("any_nan", s1_any_nan),
       ("both_inf", s1_both_inf), ("any_inf", s1_any_inf), ("a_is_inf", s1_a_is_inf)]
  }

  -- Pipeline register 1 (DFFs)
  let p1_sign1 := Wire.mk "p1_sign1"
  let p1_sign2 := Wire.mk "p1_sign2"
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
     Gate.mkDFF s1_any_nan clock reset p1_any_nan,
     Gate.mkDFF s1_both_inf clock reset p1_both_inf,
     Gate.mkDFF s1_any_inf clock reset p1_any_inf,
     Gate.mkDFF s1_a_is_inf clock reset p1_a_is_inf] ++
    mkDFFBank rm p1_rm clock reset ++
    mkDFFBank dest_tag p1_tag clock reset ++
    [Gate.mkDFF valid_in clock reset p1_valid]

  -- Stage 2 wires (combinational outputs from Stage 2)
  let s2_big_sign := Wire.mk "s2_big_sign"
  let s2_small_sign := Wire.mk "s2_small_sign"
  let s2_eff_sub := Wire.mk "s2_eff_sub"
  let s2_shift_sticky := Wire.mk "s2_shift_sticky"
  let s2_inf_sub_inf := Wire.mk "s2_inf_sub_inf"
  let s2_inf_sign := Wire.mk "s2_inf_sign"
  let s2_big_exp := makeIndexedWires "s2_big_exp" 11
  let s2_big_mant := makeIndexedWires "s2_big_mant" 56
  let s2_aligned_small := makeIndexedWires "s2_aligned_small" 56

  let stage2_inst : CircuitInstance := {
    moduleName := "FPAdderD_Stage2_Align"
    instName := "u_stage2"
    portMap :=
      [("sign1", p1_sign1), ("sign2", p1_sign2)] ++
      ((List.range 11).map fun i => (s!"exp1_{i}", p1_exp1[i]!)) ++
      ((List.range 11).map fun i => (s!"exp2_{i}", p1_exp2[i]!)) ++
      ((List.range 53).map fun i => (s!"mant1_{i}", p1_mant1[i]!)) ++
      ((List.range 53).map fun i => (s!"mant2_{i}", p1_mant2[i]!)) ++
      ((List.range 11).map fun i => (s!"exp_diff_{i}", p1_exp_diff[i]!)) ++
      [("swap", p1_swap), ("both_inf", p1_both_inf), ("a_is_inf", p1_a_is_inf), ("zero", zero),
       ("big_sign", s2_big_sign), ("small_sign", s2_small_sign),
       ("eff_sub", s2_eff_sub), ("shift_sticky", s2_shift_sticky),
       ("inf_sub_inf", s2_inf_sub_inf), ("inf_sign", s2_inf_sign)] ++
      ((List.range 11).map fun i => (s!"big_exp_{i}", s2_big_exp[i]!)) ++
      ((List.range 56).map fun i => (s!"big_mant_{i}", s2_big_mant[i]!)) ++
      ((List.range 56).map fun i => (s!"aligned_small_{i}", s2_aligned_small[i]!))
  }

  -- Pipeline register 2 (DFFs)
  let p2_big_sign := Wire.mk "p2_big_sign"
  let p2_small_sign := Wire.mk "p2_small_sign"
  let p2_eff_sub := Wire.mk "p2_eff_sub"
  let p2_sticky := Wire.mk "p2_sticky"
  let p2_any_nan := Wire.mk "p2_any_nan"
  let p2_inf_sub_inf := Wire.mk "p2_inf_sub_inf"
  let p2_any_inf := Wire.mk "p2_any_inf"
  let p2_inf_sign := Wire.mk "p2_inf_sign"
  let p2_big_exp := makeIndexedWires "p2_big_exp" 11
  let p2_big_mant := makeIndexedWires "p2_big_mant" 56
  let p2_aligned_small := makeIndexedWires "p2_aligned_small" 56
  let p2_rm := makeIndexedWires "p2_rm" 3
  let p2_tag := makeIndexedWires "p2_tag" 6
  let p2_valid := Wire.mk "p2_valid"

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
    mkDFFBank s2_big_mant p2_big_mant clock reset ++
    mkDFFBank s2_aligned_small p2_aligned_small clock reset ++
    mkDFFBank p1_rm p2_rm clock reset ++
    mkDFFBank p1_tag p2_tag clock reset ++
    [Gate.mkDFF p1_valid clock reset p2_valid]

  -- Stage 3 wires (combinational outputs from Stage 3)
  let s3_sum := makeIndexedWires "s3_sum" 56
  let s3_overflow := Wire.mk "s3_overflow"
  let s3_lead_pos := makeIndexedWires "s3_lead_pos" 6
  let s3_found := Wire.mk "s3_found"

  let stage3_inst : CircuitInstance := {
    moduleName := "FPAdderD_Stage3_AddSub"
    instName := "u_stage3"
    portMap :=
      ((List.range 56).map fun i => (s!"big_mant_{i}", p2_big_mant[i]!)) ++
      ((List.range 56).map fun i => (s!"aligned_small_{i}", p2_aligned_small[i]!)) ++
      [("eff_sub", p2_eff_sub), ("zero", zero)] ++
      ((List.range 56).map fun i => (s!"sum_{i}", s3_sum[i]!)) ++
      [("overflow", s3_overflow)] ++
      ((List.range 6).map fun i => (s!"lead_pos_{i}", s3_lead_pos[i]!)) ++
      [("found", s3_found)]
  }

  -- Pipeline register 3 (DFFs)
  let p3_sign := Wire.mk "p3_sign"
  let p3_overflow := Wire.mk "p3_overflow"
  let p3_found := Wire.mk "p3_found"
  let p3_sticky := Wire.mk "p3_sticky"
  let p3_any_nan := Wire.mk "p3_any_nan"
  let p3_inf_sub_inf := Wire.mk "p3_inf_sub_inf"
  let p3_any_inf := Wire.mk "p3_any_inf"
  let p3_inf_sign := Wire.mk "p3_inf_sign"
  let p3_exp := makeIndexedWires "p3_exp" 11
  let p3_sum := makeIndexedWires "p3_sum" 56
  let p3_lead_pos := makeIndexedWires "p3_lead_pos" 6
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

  -- Stage 4: Normalize, Round, Special values, Pack
  let stage4_inst : CircuitInstance := {
    moduleName := "FPAdderD_Stage4_NormRound"
    instName := "u_stage4"
    portMap :=
      [("sign", p3_sign)] ++
      ((List.range 11).map fun i => (s!"exp_{i}", p3_exp[i]!)) ++
      ((List.range 56).map fun i => (s!"sum_{i}", p3_sum[i]!)) ++
      [("overflow", p3_overflow)] ++
      ((List.range 6).map fun i => (s!"lead_pos_{i}", p3_lead_pos[i]!)) ++
      [("found", p3_found), ("sticky", p3_sticky),
       ("any_nan", p3_any_nan), ("inf_sub_inf", p3_inf_sub_inf),
       ("any_inf", p3_any_inf), ("inf_sign", p3_inf_sign)] ++
      ((List.range 3).map fun i => (s!"rm_{i}", p3_rm[i]!)) ++
      [("zero", zero)] ++
      ((List.range 64).map fun i => (s!"result_{i}", result[i]!)) ++
      ((List.range 5).map fun i => (s!"exc_{i}", exc[i]!))
  }

  let tag_gates := (List.range 6).map fun i => Gate.mkBUF (p3_tag[i]!) (tag_out[i]!)
  let valid_gate := Gate.mkBUF p3_valid valid_out

  let all_gates := p1_dffs ++ p2_dffs ++ p3_dffs ++ tag_gates ++ [valid_gate]

  { name := "FPAdderD"
    inputs := src1 ++ src2 ++ [op_sub] ++ rm ++ dest_tag ++ [valid_in, clock, reset, zero]
    outputs := result ++ tag_out ++ exc ++ [valid_out]
    gates := all_gates
    instances := [stage1_inst, stage2_inst, stage3_inst, stage4_inst]
    signalGroups := [
      { name := "src1", width := 64, wires := src1 },
      { name := "src2", width := 64, wires := src2 },
      { name := "rm", width := 3, wires := rm },
      { name := "dest_tag", width := 6, wires := dest_tag },
      { name := "result", width := 64, wires := result },
      { name := "tag_out", width := 6, wires := tag_out },
      { name := "exc", width := 5, wires := exc }
    ] }

def fpAdderDCircuit : Circuit := mkFPAdderD

end Shoumei.Circuits.Sequential
