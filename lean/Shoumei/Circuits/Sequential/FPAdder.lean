/-
Circuits/Sequential/FPAdder.lean - 4-Stage Pipelined Single-Precision FP Adder/Subtractor

A pipelined floating-point adder/subtractor for IEEE 754 binary32.

Decomposed hierarchically into 4 combinational pipeline stage modules:
  Stage 1 (FPAdder_Stage1_Unpack): Unpack + Exponent difference + Swap detection + NaN/Inf detection
  Stage 2 (FPAdder_Stage2_Align): Swap operands + Alignment barrel shift with sticky tracking
  Stage 3 (FPAdder_Stage3_AddSub): Mantissa add (KSA) + Leading-zero parallel prefix detect
  Stage 4 (FPAdder_Stage4_NormRound): Normalize + Special values + Pack + Exceptions

Interface:
- Inputs: src1[31:0], src2[31:0], op_sub, rm[2:0], dest_tag[5:0], valid_in,
          clock, reset, zero
- Outputs: result[31:0], tag_out[5:0], exc[4:0], valid_out
-/

import Shoumei.DSL
import Shoumei.Components.Select
import Shoumei.Circuits.Combinational.KoggeStoneAdder

namespace Shoumei.Circuits.Sequential

open Shoumei
open Shoumei.Components
open Shoumei.Circuits.Combinational

/-! ## Helper: Indexed Wire Generation -/

private def makeIndexedWires (pfx : String) (n : Nat) : List Wire :=
  (List.range n).map fun i => Wire.mk (pfx ++ "_" ++ toString i)

/-! ## Helper: DFF Bank -/

private def mkDFFBank (d_wires q_wires : List Wire) (clock reset : Wire) : List Gate :=
  List.zipWith (fun d q => Gate.mkDFF d clock reset q) d_wires q_wires

private def mkBUFBank (src dst : List Wire) : List Gate :=
  List.zipWith (fun s d => Gate.mkBUF s d) src dst

/-! ## Arithmetic Helpers -/

/-- 5-level barrel right shifter for w-bit value. -/
private def mkBarrelShiftRight (input : List Wire) (shift_amt : List Wire)
    (output : List Wire) (zero_wire : Wire) (pfx : String) : List Gate :=
  let w := input.length
  let levels : List (List Wire) := (List.range 6).map fun level =>
    if level == 0 then input
    else (List.range w).map fun i => Wire.mk (pfx ++ "_l" ++ toString level ++ "_" ++ toString i)
  let mux_gates := (List.range 5).flatMap fun level =>
    let shift_by := 1 <<< level
    let prev := levels[level]!
    let curr := levels[level + 1]!
    let sel := shift_amt[level]!
    (List.range w).map fun i =>
      let unshifted := prev[i]!
      let shifted := if i + shift_by < w then prev[i + shift_by]! else zero_wire
      Gate.mkMUX unshifted shifted sel curr[i]!
  let copy_gates := (List.range w).map fun i =>
    Gate.mkBUF (levels[5]!)[i]! output[i]!
  mux_gates ++ copy_gates

/-- 5-level barrel left shifter for w-bit value. -/
private def mkBarrelShiftLeft (input : List Wire) (shift_amt : List Wire)
    (output : List Wire) (zero_wire : Wire) (pfx : String) : List Gate :=
  let w := input.length
  let levels : List (List Wire) := (List.range 6).map fun level =>
    if level == 0 then input
    else (List.range w).map fun i => Wire.mk (pfx ++ "_l" ++ toString level ++ "_" ++ toString i)
  let mux_gates := (List.range 5).flatMap fun level =>
    let shift_by := 1 <<< level
    let prev := levels[level]!
    let curr := levels[level + 1]!
    let sel := shift_amt[level]!
    (List.range w).map fun i =>
      let unshifted := prev[i]!
      let shifted := if i >= shift_by then prev[i - shift_by]! else zero_wire
      Gate.mkMUX unshifted shifted sel curr[i]!
  let copy_gates := (List.range w).map fun i =>
    Gate.mkBUF (levels[5]!)[i]! output[i]!
  mux_gates ++ copy_gates

/-! ## Pipeline Stage 1: Unpack + Exponent difference + Swap + NaN/Inf -/

def mkFPAdder_Stage1_Unpack : Circuit :=
  let src1 := makeIndexedWires "src1" 32
  let src2 := makeIndexedWires "src2" 32
  let op_sub := Wire.mk "op_sub"
  let zero := Wire.mk "zero"

  let sign_a := Wire.mk "sign_a"
  let eff_sign_b := Wire.mk "eff_sign_b"
  let exp_a := makeIndexedWires "exp_a" 8
  let exp_b := makeIndexedWires "exp_b" 8
  let mant_a := makeIndexedWires "mant_a" 24
  let mant_b := makeIndexedWires "mant_b" 24
  let exp_diff := makeIndexedWires "exp_diff" 9
  let swap := Wire.mk "swap"
  let any_nan := Wire.mk "any_nan"
  let any_special := Wire.mk "any_special"
  let both_inf := Wire.mk "both_inf"
  let a_is_inf := Wire.mk "a_is_inf"
  let b_is_inf := Wire.mk "b_is_inf"

  let one := Wire.mk "s1_one"
  let one_gate := Gate.mkNOT zero one

  -- Unpack operand A
  let not_sign_a := Wire.mk "s1_not_sign_a"
  let sign_a_gate := [Gate.mkNOT (src1[31]!) not_sign_a, Gate.mkNOT not_sign_a sign_a]
  let not_exp_a := makeIndexedWires "s1_not_exp_a" 8
  let exp_a_gates := (List.range 8).flatMap fun i =>
    [Gate.mkNOT (src1[23 + i]!) (not_exp_a[i]!),
     Gate.mkNOT (not_exp_a[i]!) (exp_a[i]!)]

  let exp_a_or01 := Wire.mk "s1_exp_a_or01"
  let exp_a_or23 := Wire.mk "s1_exp_a_or23"
  let exp_a_or45 := Wire.mk "s1_exp_a_or45"
  let exp_a_or67 := Wire.mk "s1_exp_a_or67"
  let exp_a_or0123 := Wire.mk "s1_exp_a_or0123"
  let exp_a_or4567 := Wire.mk "s1_exp_a_or4567"
  let exp_a_or_all := Wire.mk "s1_exp_a_or_all"
  let exp_a_zero_gates := [
    Gate.mkOR (exp_a[0]!) (exp_a[1]!) exp_a_or01,
    Gate.mkOR (exp_a[2]!) (exp_a[3]!) exp_a_or23,
    Gate.mkOR (exp_a[4]!) (exp_a[5]!) exp_a_or45,
    Gate.mkOR (exp_a[6]!) (exp_a[7]!) exp_a_or67,
    Gate.mkOR exp_a_or01 exp_a_or23 exp_a_or0123,
    Gate.mkOR exp_a_or45 exp_a_or67 exp_a_or4567,
    Gate.mkOR exp_a_or0123 exp_a_or4567 exp_a_or_all
  ]

  let not_mant_a := makeIndexedWires "s1_not_mant_a" 23
  let mant_a_gates := (List.range 23).flatMap (fun i =>
    [Gate.mkNOT (src1[i]!) (not_mant_a[i]!),
     Gate.mkNOT (not_mant_a[i]!) (mant_a[i]!)]) ++
    [Gate.mkBUF exp_a_or_all (mant_a[23]!)]

  -- Unpack operand B
  let sign_b_raw := Wire.mk "s1_sign_b_raw"
  let sign_b_raw_gate := Gate.mkBUF (src2[31]!) sign_b_raw
  let eff_sign_b_gate := Gate.mkXOR sign_b_raw op_sub eff_sign_b

  let not_exp_b := makeIndexedWires "s1_not_exp_b" 8
  let exp_b_gates := (List.range 8).flatMap fun i =>
    [Gate.mkNOT (src2[23 + i]!) (not_exp_b[i]!),
     Gate.mkNOT (not_exp_b[i]!) (exp_b[i]!)]

  let exp_b_or01 := Wire.mk "s1_exp_b_or01"
  let exp_b_or23 := Wire.mk "s1_exp_b_or23"
  let exp_b_or45 := Wire.mk "s1_exp_b_or45"
  let exp_b_or67 := Wire.mk "s1_exp_b_or67"
  let exp_b_or0123 := Wire.mk "s1_exp_b_or0123"
  let exp_b_or4567 := Wire.mk "s1_exp_b_or4567"
  let exp_b_or_all := Wire.mk "s1_exp_b_or_all"
  let exp_b_zero_gates := [
    Gate.mkOR (exp_b[0]!) (exp_b[1]!) exp_b_or01,
    Gate.mkOR (exp_b[2]!) (exp_b[3]!) exp_b_or23,
    Gate.mkOR (exp_b[4]!) (exp_b[5]!) exp_b_or45,
    Gate.mkOR (exp_b[6]!) (exp_b[7]!) exp_b_or67,
    Gate.mkOR exp_b_or01 exp_b_or23 exp_b_or0123,
    Gate.mkOR exp_b_or45 exp_b_or67 exp_b_or4567,
    Gate.mkOR exp_b_or0123 exp_b_or4567 exp_b_or_all
  ]

  let not_mant_b := makeIndexedWires "s1_not_mant_b" 23
  let mant_b_gates := (List.range 23).flatMap (fun i =>
    [Gate.mkNOT (src2[i]!) (not_mant_b[i]!),
     Gate.mkNOT (not_mant_b[i]!) (mant_b[i]!)]) ++
    [Gate.mkBUF exp_b_or_all (mant_b[23]!)]

  -- NaN / Inf detection for A
  let a_exp_and01 := Wire.mk "s1_a_and01"
  let a_exp_and23 := Wire.mk "s1_a_and23"
  let a_exp_and45 := Wire.mk "s1_a_and45"
  let a_exp_and67 := Wire.mk "s1_a_and67"
  let a_exp_and0123 := Wire.mk "s1_a_and0123"
  let a_exp_and4567 := Wire.mk "s1_a_and4567"
  let a_exp_all_ones := Wire.mk "s1_a_exp_all_ones"
  let exp_a_and_gates := [
    Gate.mkAND (exp_a[0]!) (exp_a[1]!) a_exp_and01,
    Gate.mkAND (exp_a[2]!) (exp_a[3]!) a_exp_and23,
    Gate.mkAND (exp_a[4]!) (exp_a[5]!) a_exp_and45,
    Gate.mkAND (exp_a[6]!) (exp_a[7]!) a_exp_and67,
    Gate.mkAND a_exp_and01 a_exp_and23 a_exp_and0123,
    Gate.mkAND a_exp_and45 a_exp_and67 a_exp_and4567,
    Gate.mkAND a_exp_and0123 a_exp_and4567 a_exp_all_ones
  ]

  -- NaN / Inf detection for B
  let b_exp_and01 := Wire.mk "s1_b_and01"
  let b_exp_and23 := Wire.mk "s1_b_and23"
  let b_exp_and45 := Wire.mk "s1_b_and45"
  let b_exp_and67 := Wire.mk "s1_b_and67"
  let b_exp_and0123 := Wire.mk "s1_b_and0123"
  let b_exp_and4567 := Wire.mk "s1_b_and4567"
  let b_exp_all_ones := Wire.mk "s1_b_exp_all_ones"
  let exp_b_and_gates := [
    Gate.mkAND (exp_b[0]!) (exp_b[1]!) b_exp_and01,
    Gate.mkAND (exp_b[2]!) (exp_b[3]!) b_exp_and23,
    Gate.mkAND (exp_b[4]!) (exp_b[5]!) b_exp_and45,
    Gate.mkAND (exp_b[6]!) (exp_b[7]!) b_exp_and67,
    Gate.mkAND b_exp_and01 b_exp_and23 b_exp_and0123,
    Gate.mkAND b_exp_and45 b_exp_and67 b_exp_and4567,
    Gate.mkAND b_exp_and0123 b_exp_and4567 b_exp_all_ones
  ]

  -- Mantissa nonzero OR tree for A
  let a_mant_nonzero := Wire.mk "s1_a_mant_nonzero"
  let mant_a_or_gates :=
    let l1 := (List.range 11).map fun i =>
      let w := Wire.mk s!"s1_a_mor_l1_{i}"
      Gate.mkOR (src1[2*i]!) (src1[2*i+1]!) w
    let l1_wires := (List.range 11).map fun i => Wire.mk s!"s1_a_mor_l1_{i}"
    let l1_plus := l1_wires ++ [src1[22]!]
    let l2 := (List.range 6).map fun i =>
      let w := Wire.mk s!"s1_a_mor_l2_{i}"
      Gate.mkOR (l1_plus[2*i]!) (l1_plus[2*i+1]!) w
    let l2_wires := (List.range 6).map fun i => Wire.mk s!"s1_a_mor_l2_{i}"
    let l3 := (List.range 3).map fun i =>
      let w := Wire.mk s!"s1_a_mor_l3_{i}"
      Gate.mkOR (l2_wires[2*i]!) (l2_wires[2*i+1]!) w
    let l3_wires := (List.range 3).map fun i => Wire.mk s!"s1_a_mor_l3_{i}"
    let or_01 := Wire.mk "s1_a_mor_01"
    let l4_gates := [
      Gate.mkOR (l3_wires[0]!) (l3_wires[1]!) or_01,
      Gate.mkOR or_01 (l3_wires[2]!) a_mant_nonzero
    ]
    l1 ++ l2 ++ l3 ++ l4_gates

  let a_is_nan := Wire.mk "s1_a_is_nan"
  let not_a_mant_nonzero := Wire.mk "s1_not_a_mant_nz"
  let a_nan_inf_gates := [
    Gate.mkAND a_exp_all_ones a_mant_nonzero a_is_nan,
    Gate.mkNOT a_mant_nonzero not_a_mant_nonzero,
    Gate.mkAND a_exp_all_ones not_a_mant_nonzero a_is_inf
  ]

  -- Mantissa nonzero OR tree for B
  let b_mant_nonzero := Wire.mk "s1_b_mant_nonzero"
  let mant_b_or_gates :=
    let l1 := (List.range 11).map fun i =>
      let w := Wire.mk s!"s1_b_mor_l1_{i}"
      Gate.mkOR (src2[2*i]!) (src2[2*i+1]!) w
    let l1_wires := (List.range 11).map fun i => Wire.mk s!"s1_b_mor_l1_{i}"
    let l1_plus := l1_wires ++ [src2[22]!]
    let l2 := (List.range 6).map fun i =>
      let w := Wire.mk s!"s1_b_mor_l2_{i}"
      Gate.mkOR (l1_plus[2*i]!) (l1_plus[2*i+1]!) w
    let l2_wires := (List.range 6).map fun i => Wire.mk s!"s1_b_mor_l2_{i}"
    let l3 := (List.range 3).map fun i =>
      let w := Wire.mk s!"s1_b_mor_l3_{i}"
      Gate.mkOR (l2_wires[2*i]!) (l2_wires[2*i+1]!) w
    let l3_wires := (List.range 3).map fun i => Wire.mk s!"s1_b_mor_l3_{i}"
    let or_01 := Wire.mk "s1_b_mor_01"
    let l4_gates := [
      Gate.mkOR (l3_wires[0]!) (l3_wires[1]!) or_01,
      Gate.mkOR or_01 (l3_wires[2]!) b_mant_nonzero
    ]
    l1 ++ l2 ++ l3 ++ l4_gates

  let b_is_nan := Wire.mk "s1_b_is_nan"
  let not_b_mant_nonzero := Wire.mk "s1_not_b_mant_nz"
  let b_nan_inf_gates := [
    Gate.mkAND b_exp_all_ones b_mant_nonzero b_is_nan,
    Gate.mkNOT b_mant_nonzero not_b_mant_nonzero,
    Gate.mkAND b_exp_all_ones not_b_mant_nonzero b_is_inf
  ]

  let any_nan_gate := Gate.mkOR a_is_nan b_is_nan any_nan
  let any_special_gate := Gate.mkOR a_exp_all_ones b_exp_all_ones any_special
  let both_inf_gate := Gate.mkAND a_is_inf b_is_inf both_inf

  -- Exponent difference (9-bit): exp_a - exp_b
  let exp_a_ext := makeIndexedWires "s1_exp_a_ext" 9
  let exp_a_ext_gates := (List.range 8).map (fun i =>
    Gate.mkBUF (exp_a[i]!) (exp_a_ext[i]!)) ++
    [Gate.mkBUF zero (exp_a_ext[8]!)]

  let exp_b_ext := makeIndexedWires "s1_exp_b_ext" 9
  let exp_b_ext_gates := (List.range 8).map (fun i =>
    Gate.mkBUF (exp_b[i]!) (exp_b_ext[i]!)) ++
    [Gate.mkBUF zero (exp_b_ext[8]!)]

  let (exp_diff_gates, _exp_diff_borrow) :=
    mkKoggeStoneSub exp_a_ext exp_b_ext exp_diff "s1_expdiff" one

  let swap_gate := Gate.mkBUF _exp_diff_borrow swap

  let all_gates :=
    [one_gate] ++ sign_a_gate ++ exp_a_gates ++ exp_a_zero_gates ++ mant_a_gates ++
    [sign_b_raw_gate, eff_sign_b_gate] ++ exp_b_gates ++ exp_b_zero_gates ++ mant_b_gates ++
    exp_a_and_gates ++ exp_b_and_gates ++ mant_a_or_gates ++ a_nan_inf_gates ++
    mant_b_or_gates ++ b_nan_inf_gates ++
    [any_nan_gate, any_special_gate, both_inf_gate] ++
    exp_a_ext_gates ++ exp_b_ext_gates ++ exp_diff_gates ++ [swap_gate]

  { name := "FPAdder_Stage1_Unpack"
    inputs := src1 ++ src2 ++ [op_sub, zero]
    outputs := [sign_a, eff_sign_b] ++ exp_a ++ exp_b ++ mant_a ++ mant_b ++ exp_diff ++
               [swap, any_nan, any_special, both_inf, a_is_inf, b_is_inf]
    gates := all_gates
    instances := []
    signalGroups := [
      { name := "src1", width := 32, wires := src1 },
      { name := "src2", width := 32, wires := src2 },
      { name := "exp_a", width := 8, wires := exp_a },
      { name := "exp_b", width := 8, wires := exp_b },
      { name := "mant_a", width := 24, wires := mant_a },
      { name := "mant_b", width := 24, wires := mant_b },
      { name := "exp_diff", width := 9, wires := exp_diff }
    ] }

def fpAdder_Stage1Circuit : Circuit := mkFPAdder_Stage1_Unpack

/-! ## Pipeline Stage 2: Swap + Align + Sticky -/

def mkFPAdder_Stage2_Align : Circuit :=
  let sign_a := Wire.mk "sign_a"
  let eff_sign_b := Wire.mk "eff_sign_b"
  let exp_a := makeIndexedWires "exp_a" 8
  let exp_b := makeIndexedWires "exp_b" 8
  let mant_a := makeIndexedWires "mant_a" 24
  let mant_b := makeIndexedWires "mant_b" 24
  let exp_diff := makeIndexedWires "exp_diff" 9
  let swap := Wire.mk "swap"
  let both_inf := Wire.mk "both_inf"
  let a_is_inf := Wire.mk "a_is_inf"
  let zero := Wire.mk "zero"

  let big_sign := Wire.mk "big_sign"
  let big_exp := makeIndexedWires "big_exp" 8
  let big_mant := makeIndexedWires "big_mant" 24
  let aligned := makeIndexedWires "aligned" 24
  let eff_sub := Wire.mk "eff_sub"
  let sticky := Wire.mk "sticky"
  let inf_sub_inf := Wire.mk "inf_sub_inf"
  let inf_result_sign := Wire.mk "inf_result_sign"

  let one := Wire.mk "s2_one"
  let one_gate := Gate.mkNOT zero one

  let big_sign_gate := Gate.mkMUX sign_a eff_sign_b swap big_sign

  let big_exp_gates := (List.range 8).map fun i =>
    Gate.mkMUX (exp_a[i]!) (exp_b[i]!) swap (big_exp[i]!)

  let big_mant_gates := (List.range 24).map fun i =>
    Gate.mkMUX (mant_a[i]!) (mant_b[i]!) swap (big_mant[i]!)

  let small_mant := makeIndexedWires "s2_small_mant" 24
  let small_mant_gates := (List.range 24).map fun i =>
    Gate.mkMUX (mant_b[i]!) (mant_a[i]!) swap (small_mant[i]!)

  let small_sign := Wire.mk "s2_small_sign"
  let small_sign_gate := Gate.mkMUX eff_sign_b sign_a swap small_sign

  let neg_diff := makeIndexedWires "s2_neg_diff" 8
  let inv_diff := makeIndexedWires "s2_inv_diff" 8
  let inv_diff_gates := (List.range 8).map fun i =>
    Gate.mkNOT (exp_diff[i]!) (inv_diff[i]!)

  let zeros8 := (List.range 8).map fun _ => zero
  let (neg_diff_add_gates, _neg_carry) :=
    mkKoggeStoneAdd inv_diff zeros8 one neg_diff "s2_negdiff"

  let exp_diff8_not := Wire.mk "s2_exp_diff8_not"
  let exp_diff8_zero := Wire.mk "s2_exp_diff8_zero"
  let exp_diff8_gates := [
    Gate.mkNOT (exp_diff[8]!) exp_diff8_not,
    Gate.mkAND (exp_diff[8]!) exp_diff8_not exp_diff8_zero
  ]

  let abs_diff := makeIndexedWires "s2_abs_diff" 8
  let abs_diff_pre0 := Wire.mk "s2_abs_diff_pre0"
  let abs_diff_gates :=
    [Gate.mkMUX (exp_diff[0]!) (neg_diff[0]!) swap abs_diff_pre0,
     Gate.mkOR abs_diff_pre0 exp_diff8_zero (abs_diff[0]!)] ++
    (List.range 7).map fun i =>
      Gate.mkMUX (exp_diff[i + 1]!) (neg_diff[i + 1]!) swap (abs_diff[i + 1]!)

  let clamp_or56 := Wire.mk "s2_clamp_or56"
  let clamp_or567 := Wire.mk "s2_clamp_or567"
  let clamp_gates := [
    Gate.mkOR (abs_diff[5]!) (abs_diff[6]!) clamp_or56,
    Gate.mkOR clamp_or56 (abs_diff[7]!) clamp_or567
  ]

  let shift_amt := (List.range 5).map fun i => abs_diff[i]!
  let aligned_pre := makeIndexedWires "s2_aligned_pre" 24
  let barrel_gates := mkBarrelShiftRight small_mant shift_amt aligned_pre zero "s2_bsr"

  let not_clamp := Wire.mk "s2_not_clamp"
  let not_clamp_gate := Gate.mkNOT clamp_or567 not_clamp
  let clamp_and_gates := (List.range 24).map fun i =>
    Gate.mkAND (aligned_pre[i]!) not_clamp (aligned[i]!)

  let sticky_l0 := Wire.mk "s2_sticky_l0"
  let sticky_l0_gate := Gate.mkAND (small_mant[0]!) (abs_diff[0]!) sticky_l0

  let bsr_l1 := (List.range 24).map fun i => Wire.mk s!"s2_bsr_l1_{i}"
  let sticky_l1_or := Wire.mk "s2_sticky_l1_or"
  let sticky_l1 := Wire.mk "s2_sticky_l1"
  let sticky_l1_gates := [
    Gate.mkOR (bsr_l1[0]!) (bsr_l1[1]!) sticky_l1_or,
    Gate.mkAND sticky_l1_or (abs_diff[1]!) sticky_l1
  ]

  let bsr_l2 := (List.range 24).map fun i => Wire.mk s!"s2_bsr_l2_{i}"
  let sticky_l2_or01 := Wire.mk "s2_sticky_l2_or01"
  let sticky_l2_or23 := Wire.mk "s2_sticky_l2_or23"
  let sticky_l2_or := Wire.mk "s2_sticky_l2_or"
  let sticky_l2 := Wire.mk "s2_sticky_l2"
  let sticky_l2_gates := [
    Gate.mkOR (bsr_l2[0]!) (bsr_l2[1]!) sticky_l2_or01,
    Gate.mkOR (bsr_l2[2]!) (bsr_l2[3]!) sticky_l2_or23,
    Gate.mkOR sticky_l2_or01 sticky_l2_or23 sticky_l2_or,
    Gate.mkAND sticky_l2_or (abs_diff[2]!) sticky_l2
  ]

  let bsr_l3 := (List.range 24).map fun i => Wire.mk s!"s2_bsr_l3_{i}"
  let sticky_l3_or01 := Wire.mk "s2_sticky_l3_or01"
  let sticky_l3_or23 := Wire.mk "s2_sticky_l3_or23"
  let sticky_l3_or45 := Wire.mk "s2_sticky_l3_or45"
  let sticky_l3_or67 := Wire.mk "s2_sticky_l3_or67"
  let sticky_l3_or0123 := Wire.mk "s2_sticky_l3_or0123"
  let sticky_l3_or4567 := Wire.mk "s2_sticky_l3_or4567"
  let sticky_l3_or := Wire.mk "s2_sticky_l3_or"
  let sticky_l3 := Wire.mk "s2_sticky_l3"
  let sticky_l3_gates := [
    Gate.mkOR (bsr_l3[0]!) (bsr_l3[1]!) sticky_l3_or01,
    Gate.mkOR (bsr_l3[2]!) (bsr_l3[3]!) sticky_l3_or23,
    Gate.mkOR (bsr_l3[4]!) (bsr_l3[5]!) sticky_l3_or45,
    Gate.mkOR (bsr_l3[6]!) (bsr_l3[7]!) sticky_l3_or67,
    Gate.mkOR sticky_l3_or01 sticky_l3_or23 sticky_l3_or0123,
    Gate.mkOR sticky_l3_or45 sticky_l3_or67 sticky_l3_or4567,
    Gate.mkOR sticky_l3_or0123 sticky_l3_or4567 sticky_l3_or,
    Gate.mkAND sticky_l3_or (abs_diff[3]!) sticky_l3
  ]

  let bsr_l4 := (List.range 24).map fun i => Wire.mk s!"s2_bsr_l4_{i}"
  let sticky_l4_final := Wire.mk "s2_stk_l4_final"
  let sticky_l4 := Wire.mk "s2_sticky_l4"
  let sticky_l4_gates :=
    let p01 := Wire.mk "s2_stk_l4_p01"; let p23 := Wire.mk "s2_stk_l4_p23"
    let p45 := Wire.mk "s2_stk_l4_p45"; let p67 := Wire.mk "s2_stk_l4_p67"
    let p89 := Wire.mk "s2_stk_l4_p89"; let pab := Wire.mk "s2_stk_l4_pab"
    let pcd := Wire.mk "s2_stk_l4_pcd"; let pef := Wire.mk "s2_stk_l4_pef"
    let q03 := Wire.mk "s2_stk_l4_q03"; let q47 := Wire.mk "s2_stk_l4_q47"
    let q8b := Wire.mk "s2_stk_l4_q8b"; let qcf := Wire.mk "s2_stk_l4_qcf"
    let r07 := Wire.mk "s2_stk_l4_r07"; let r8f := Wire.mk "s2_stk_l4_r8f"
    [Gate.mkOR (bsr_l4[0]!) (bsr_l4[1]!) p01,
     Gate.mkOR (bsr_l4[2]!) (bsr_l4[3]!) p23,
     Gate.mkOR (bsr_l4[4]!) (bsr_l4[5]!) p45,
     Gate.mkOR (bsr_l4[6]!) (bsr_l4[7]!) p67,
     Gate.mkOR (bsr_l4[8]!) (bsr_l4[9]!) p89,
     Gate.mkOR (bsr_l4[10]!) (bsr_l4[11]!) pab,
     Gate.mkOR (bsr_l4[12]!) (bsr_l4[13]!) pcd,
     Gate.mkOR (bsr_l4[14]!) (bsr_l4[15]!) pef,
     Gate.mkOR p01 p23 q03, Gate.mkOR p45 p67 q47,
     Gate.mkOR p89 pab q8b, Gate.mkOR pcd pef qcf,
     Gate.mkOR q03 q47 r07, Gate.mkOR q8b qcf r8f,
     Gate.mkOR r07 r8f sticky_l4_final,
     Gate.mkAND sticky_l4_final (abs_diff[4]!) sticky_l4]

  let small_mant_any := Wire.mk "s2_sm_any"
  let sm_or_gates :=
    let l1 := (List.range 12).map fun i =>
      let w := Wire.mk s!"s2_sm_or_l1_{i}"
      Gate.mkOR (small_mant[2*i]!) (small_mant[2*i+1]!) w
    let l1w := (List.range 12).map fun i => Wire.mk s!"s2_sm_or_l1_{i}"
    let l2 := (List.range 6).map fun i =>
      let w := Wire.mk s!"s2_sm_or_l2_{i}"
      Gate.mkOR (l1w[2*i]!) (l1w[2*i+1]!) w
    let l2w := (List.range 6).map fun i => Wire.mk s!"s2_sm_or_l2_{i}"
    let l3 := (List.range 3).map fun i =>
      let w := Wire.mk s!"s2_sm_or_l3_{i}"
      Gate.mkOR (l2w[2*i]!) (l2w[2*i+1]!) w
    let l3w := (List.range 3).map fun i => Wire.mk s!"s2_sm_or_l3_{i}"
    let l4a := Wire.mk "s2_sm_or_l4a"
    l1 ++ l2 ++ l3 ++ [
      Gate.mkOR (l3w[0]!) (l3w[1]!) l4a,
      Gate.mkOR l4a (l3w[2]!) small_mant_any
    ]

  let clamp_sticky := Wire.mk "s2_clamp_sticky"
  let clamp_sticky_gate := Gate.mkAND clamp_or567 small_mant_any clamp_sticky

  let sticky_c01 := Wire.mk "s2_sticky_c01"
  let sticky_c23 := Wire.mk "s2_sticky_c23"
  let sticky_c45 := Wire.mk "s2_sticky_c45"
  let sticky_c03 := Wire.mk "s2_sticky_c03"
  let sticky_combine_gates := [
    Gate.mkOR sticky_l0 sticky_l1 sticky_c01,
    Gate.mkOR sticky_l2 sticky_l3 sticky_c23,
    Gate.mkOR sticky_l4 clamp_sticky sticky_c45,
    Gate.mkOR sticky_c01 sticky_c23 sticky_c03,
    Gate.mkOR sticky_c03 sticky_c45 sticky
  ]

  let eff_sub_gate := Gate.mkXOR big_sign small_sign eff_sub
  let inf_sub_inf_gate := Gate.mkAND both_inf eff_sub inf_sub_inf
  let inf_result_sign_gate := Gate.mkMUX eff_sign_b sign_a a_is_inf inf_result_sign

  let all_gates :=
    [one_gate, big_sign_gate] ++ big_exp_gates ++ big_mant_gates ++ small_mant_gates ++ [small_sign_gate] ++
    inv_diff_gates ++ neg_diff_add_gates ++ exp_diff8_gates ++ abs_diff_gates ++ clamp_gates ++
    barrel_gates ++ [not_clamp_gate] ++ clamp_and_gates ++
    [sticky_l0_gate] ++ sticky_l1_gates ++ sticky_l2_gates ++ sticky_l3_gates ++ sticky_l4_gates ++
    sm_or_gates ++ [clamp_sticky_gate] ++ sticky_combine_gates ++
    [eff_sub_gate, inf_sub_inf_gate, inf_result_sign_gate]

  { name := "FPAdder_Stage2_Align"
    inputs := [sign_a, eff_sign_b] ++ exp_a ++ exp_b ++ mant_a ++ mant_b ++ exp_diff ++
              [swap, both_inf, a_is_inf, zero]
    outputs := [big_sign] ++ big_exp ++ big_mant ++ aligned ++
               [eff_sub, sticky, inf_sub_inf, inf_result_sign]
    gates := all_gates
    instances := []
    signalGroups := [
      { name := "exp_a", width := 8, wires := exp_a },
      { name := "exp_b", width := 8, wires := exp_b },
      { name := "mant_a", width := 24, wires := mant_a },
      { name := "mant_b", width := 24, wires := mant_b },
      { name := "exp_diff", width := 9, wires := exp_diff },
      { name := "big_exp", width := 8, wires := big_exp },
      { name := "big_mant", width := 24, wires := big_mant },
      { name := "aligned", width := 24, wires := aligned }
    ] }

def fpAdder_Stage2Circuit : Circuit := mkFPAdder_Stage2_Align

/-! ## Pipeline Stage 3: Mantissa Add + Leading-Zero Detect -/

def mkFPAdder_Stage3_AddSub : Circuit :=
  let big_mant := makeIndexedWires "big_mant" 24
  let aligned := makeIndexedWires "aligned" 24
  let eff_sub := Wire.mk "eff_sub"
  let zero := Wire.mk "zero"

  let sum_full := makeIndexedWires "s3_sum_full" 25
  let sum := makeIndexedWires "sum" 24
  let overflow := Wire.mk "overflow"
  let lead_pos := makeIndexedWires "lead_pos" 5
  let found := Wire.mk "found"

  let one := Wire.mk "s3_one"
  let one_gate := Gate.mkNOT zero one

  let big_ext := makeIndexedWires "s3_big_ext" 25
  let big_ext_gates := (List.range 24).map (fun i =>
    Gate.mkBUF (big_mant[i]!) (big_ext[i]!)) ++
    [Gate.mkBUF zero (big_ext[24]!)]

  let aligned_ext := makeIndexedWires "s3_aligned_ext" 25
  let aligned_ext_gates := (List.range 24).map (fun i =>
    Gate.mkBUF (aligned[i]!) (aligned_ext[i]!)) ++
    [Gate.mkBUF zero (aligned_ext[24]!)]

  let cond_inv_aligned := makeIndexedWires "s3_cond_inv_al" 25
  let cond_inv_gates := (List.range 25).map fun i =>
    Gate.mkXOR (aligned_ext[i]!) eff_sub (cond_inv_aligned[i]!)

  let (sum_add_gates, _sum_carry) :=
    mkKoggeStoneAdd big_ext cond_inv_aligned eff_sub sum_full "s3_mantadd"

  -- Parallel prefix leading zero count on 25-bit sum
  let lz_v := makeIndexedWires "s3_lz_v" 25
  let lz_p := (List.range 25).map fun i => makeIndexedWires ("s3_lz_p_" ++ toString i) 5
  let lz_leaf_gates := (List.range 25).flatMap fun i =>
    [Gate.mkBUF (sum_full[i]!) (lz_v[i]!)] ++
    (List.range 5).map fun k =>
      let bit_val := if (i >>> k) &&& 1 == 1 then one else zero
      Gate.mkBUF bit_val ((lz_p[i]!)[k]!)

  let strides := [1, 2, 4, 8, 16]
  let (lz_prefix_gates, lz_final_v, lz_final_p) :=
    strides.foldl (fun (acc : List Gate × List Wire × List (List Wire)) stride =>
      let (gates_acc, v_prev, p_prev) := acc
      let lt := "s3_lz_s" ++ toString stride
      let v_new := makeIndexedWires (lt ++ "_v") 25
      let p_new := (List.range 25).map fun i => makeIndexedWires (lt ++ "_p_" ++ toString i) 5

      let level_gates := (List.range 25).flatMap fun i =>
        if i + stride < 25 then
          let merge_v := Wire.mk (lt ++ "_mv_" ++ toString i)
          [Gate.mkOR (v_prev[i + stride]!) (v_prev[i]!) merge_v,
           Gate.mkBUF merge_v (v_new[i]!)] ++
          (List.range 5).map fun k =>
            Gate.mkMUX ((p_prev[i]!)[k]!) ((p_prev[i + stride]!)[k]!) (v_prev[i + stride]!) ((p_new[i]!)[k]!)
        else
          [Gate.mkBUF (v_prev[i]!) (v_new[i]!)] ++
          (List.range 5).map fun k =>
            Gate.mkBUF ((p_prev[i]!)[k]!) ((p_new[i]!)[k]!)

      (gates_acc ++ level_gates, v_new, p_new)
    ) ([], lz_v, lz_p)

  let lead_pos_gates := (List.range 5).map fun k =>
    Gate.mkBUF ((lz_final_p[0]!)[k]!) (lead_pos[k]!)
  let found_gate := Gate.mkBUF (lz_final_v[0]!) found
  let sum_out_gates := (List.range 24).map fun i =>
    Gate.mkBUF (sum_full[i]!) (sum[i]!)
  let overflow_gate := Gate.mkBUF (sum_full[24]!) overflow

  let all_gates :=
    [one_gate] ++ big_ext_gates ++ aligned_ext_gates ++ cond_inv_gates ++ sum_add_gates ++
    lz_leaf_gates ++ lz_prefix_gates ++ lead_pos_gates ++ sum_out_gates ++ [found_gate, overflow_gate]

  { name := "FPAdder_Stage3_AddSub"
    inputs := big_mant ++ aligned ++ [eff_sub, zero]
    outputs := sum ++ [overflow] ++ lead_pos ++ [found]
    gates := all_gates
    instances := []
    signalGroups := [
      { name := "big_mant", width := 24, wires := big_mant },
      { name := "aligned", width := 24, wires := aligned },
      { name := "sum", width := 24, wires := sum },
      { name := "lead_pos", width := 5, wires := lead_pos }
    ] }

def fpAdder_Stage3Circuit : Circuit := mkFPAdder_Stage3_AddSub

/-! ## Pipeline Stage 4: Normalize + Special values + Pack + Exceptions -/

def mkFPAdder_Stage4_NormRound : Circuit :=
  let big_sign := Wire.mk "big_sign"
  let big_exp := makeIndexedWires "big_exp" 8
  let sum := makeIndexedWires "sum" 24
  let lead_pos := makeIndexedWires "lead_pos" 5
  let overflow := Wire.mk "overflow"
  let found := Wire.mk "found"
  let sticky := Wire.mk "sticky"
  let any_nan := Wire.mk "any_nan"
  let any_special := Wire.mk "any_special"
  let inf_sub_inf := Wire.mk "inf_sub_inf"
  let inf_result_sign := Wire.mk "inf_result_sign"
  let a_is_inf := Wire.mk "a_is_inf"
  let b_is_inf := Wire.mk "b_is_inf"
  let zero := Wire.mk "zero"

  let result := makeIndexedWires "result" 32
  let exc := makeIndexedWires "exc" 5

  let one := Wire.mk "s4_one"
  let one_gate := Gate.mkNOT zero one

  -- Overflow case
  let ovf_mant := makeIndexedWires "s4_ovf_mant" 23
  let ovf_mant_gates := (List.range 23).map fun i =>
    Gate.mkBUF (sum[i + 1]!) (ovf_mant[i]!)

  let ovf_exp := makeIndexedWires "s4_ovf_exp" 8
  let ovf_exp_one := makeIndexedWires "s4_ovf_exp_one" 8
  let ovf_exp_one_gates := [Gate.mkBUF one (ovf_exp_one[0]!)] ++
    (List.range 7).map (fun i => Gate.mkBUF zero (ovf_exp_one[i+1]!))
  let (ovf_exp_add_gates, _ovf_exp_carry) :=
    mkAddFor (AdderSpec.minArea big_exp.length .none) big_exp ovf_exp_one zero ovf_exp "s4_ovfexp"

  -- Non-overflow: normalize left-shift
  let const_23 := makeIndexedWires "s4_const23" 5
  let const_23_gates := [
    Gate.mkBUF one (const_23[0]!),
    Gate.mkBUF one (const_23[1]!),
    Gate.mkBUF one (const_23[2]!),
    Gate.mkBUF zero (const_23[3]!),
    Gate.mkBUF one (const_23[4]!)
  ]

  let lshift_amt := makeIndexedWires "s4_lshift_amt" 5
  let (lshift_sub_gates, _lshift_borrow) :=
    mkSubFor (AdderSpec.minArea const_23.length .one) const_23 lead_pos lshift_amt "s4_lshamt" one

  let sum_lower := makeIndexedWires "s4_sum_lower" 24
  let sum_lower_gates := (List.range 24).map fun i =>
    Gate.mkBUF (sum[i]!) (sum_lower[i]!)

  let norm_mant_full := makeIndexedWires "s4_norm_mant_full" 24
  let lshift_gates := mkBarrelShiftLeft sum_lower lshift_amt norm_mant_full zero "s4_bsl"

  let norm_mant := makeIndexedWires "s4_norm_mant" 23
  let norm_mant_gates := (List.range 23).map fun i =>
    Gate.mkBUF (norm_mant_full[i]!) (norm_mant[i]!)

  let lshift_ext := makeIndexedWires "s4_lshift_ext" 8
  let lshift_ext_gates := (List.range 5).map (fun i =>
    Gate.mkBUF (lshift_amt[i]!) (lshift_ext[i]!)) ++
    (List.range 3).map (fun i => Gate.mkBUF zero (lshift_ext[i + 5]!))

  let norm_exp := makeIndexedWires "s4_norm_exp" 8
  let (norm_exp_sub_gates, _norm_exp_borrow) :=
    mkSubFor (AdderSpec.minArea big_exp.length .one) big_exp lshift_ext norm_exp "s4_normexp" one

  let result_mant := makeIndexedWires "s4_res_mant" 23
  let result_mant_gates := (List.range 23).map fun i =>
    Gate.mkMUX (norm_mant[i]!) (ovf_mant[i]!) overflow (result_mant[i]!)

  let result_exp := makeIndexedWires "s4_res_exp" 8
  let result_exp_gates := (List.range 8).map fun i =>
    Gate.mkMUX (norm_exp[i]!) (ovf_exp[i]!) overflow (result_exp[i]!)

  let not_found := Wire.mk "s4_not_found"
  let not_sum_is_zero := Wire.mk "s4_not_siz"
  let zero_det_gates := [
    Gate.mkNOT found not_found,
    Gate.mkNOT not_found not_sum_is_zero
  ]

  let result_sign := Wire.mk "s4_result_sign"
  let result_sign_gate := Gate.mkAND big_sign not_sum_is_zero result_sign

  let result_exp_masked := makeIndexedWires "s4_res_exp_m" 8
  let result_exp_mask_gates := (List.range 8).map fun i =>
    Gate.mkAND (result_exp[i]!) not_sum_is_zero (result_exp_masked[i]!)

  let result_mant_masked := makeIndexedWires "s4_res_mant_m" 23
  let result_mant_mask_gates := (List.range 23).map fun i =>
    Gate.mkAND (result_mant[i]!) not_sum_is_zero (result_mant_masked[i]!)

  let normal_result := makeIndexedWires "s4_normal_res" 32
  let normal_pack_gates :=
    (List.range 23).map (fun i => Gate.mkBUF (result_mant_masked[i]!) (normal_result[i]!)) ++
    (List.range 8).map (fun i => Gate.mkBUF (result_exp_masked[i]!) (normal_result[23 + i]!)) ++
    [Gate.mkBUF result_sign (normal_result[31]!)]

  let canonical_nan := makeIndexedWires "s4_cnan" 32
  let nan_gates := (List.range 32).map fun i =>
    let bit_val := match i with
      | 22 => one
      | 23 => one | 24 => one | 25 => one | 26 => one
      | 27 => one | 28 => one | 29 => one | 30 => one
      | _ => zero
    Gate.mkBUF bit_val (canonical_nan[i]!)

  let inf_result := makeIndexedWires "s4_inf_res" 32
  let inf_result_gates := (List.range 32).map fun i =>
    let bit_val := match i with
      | 31 => inf_result_sign
      | 23 => one | 24 => one | 25 => one | 26 => one
      | 27 => one | 28 => one | 29 => one | 30 => one
      | _ => zero
    Gate.mkBUF bit_val (inf_result[i]!)

  let any_inf := Wire.mk "s4_any_inf"
  let any_inf_gate := Gate.mkOR a_is_inf b_is_inf any_inf
  let not_inf_sub_inf := Wire.mk "s4_not_inf_sub_inf"
  let not_inf_sub_inf_gate := Gate.mkNOT inf_sub_inf not_inf_sub_inf
  let inf_not_nv := Wire.mk "s4_inf_not_nv"
  let inf_not_nv_gate := Gate.mkAND any_inf not_inf_sub_inf inf_not_nv

  let is_nan_result := Wire.mk "s4_is_nan_result"
  let is_nan_result_gate := Gate.mkOR any_nan inf_sub_inf is_nan_result

  let pre_result := makeIndexedWires "s4_pre_res" 32
  let mux1_gates := (List.range 32).map fun i =>
    Gate.mkMUX (normal_result[i]!) (inf_result[i]!) inf_not_nv (pre_result[i]!)
  let final_mux_gates := (List.range 32).map fun i =>
    Gate.mkMUX (pre_result[i]!) (canonical_nan[i]!) is_nan_result (result[i]!)

  let exc_nv := Wire.mk "s4_exc_nv"
  let exc_nv_gate := Gate.mkBUF is_nan_result exc_nv

  let ovf_loses_bit := Wire.mk "s4_ovf_loses_bit"
  let ovf_loses_gate := Gate.mkAND overflow (sum[0]!) ovf_loses_bit
  let nx_raw := Wire.mk "s4_nx_raw"
  let nx_raw_gate := Gate.mkOR sticky ovf_loses_bit nx_raw
  let not_any_special := Wire.mk "s4_not_any_special"
  let not_any_special_gate := Gate.mkNOT any_special not_any_special
  let exc_nx := Wire.mk "s4_exc_nx"
  let exc_nx_gate := Gate.mkAND nx_raw not_any_special exc_nx

  let not_ovf := Wire.mk "s4_not_ovf"
  let xor_ovf_0 := Wire.mk "s4_xor_ovf_0"
  let not_xor_ovf_0 := Wire.mk "s4_not_xor_ovf_0"
  let xor_ovf_1 := Wire.mk "s4_xor_ovf_1"
  let not_xor_ovf_1 := Wire.mk "s4_not_xor_ovf_1"
  let exc_output_gates := [
    Gate.mkBUF exc_nx (exc[0]!),
    Gate.mkNOT overflow not_ovf,
    Gate.mkAND overflow not_ovf (exc[1]!),
    Gate.mkXOR overflow (sum[0]!) xor_ovf_0,
    Gate.mkNOT xor_ovf_0 not_xor_ovf_0,
    Gate.mkAND xor_ovf_0 not_xor_ovf_0 (exc[2]!),
    Gate.mkXOR overflow (sum[1]!) xor_ovf_1,
    Gate.mkNOT xor_ovf_1 not_xor_ovf_1,
    Gate.mkAND xor_ovf_1 not_xor_ovf_1 (exc[3]!),
    Gate.mkBUF exc_nv (exc[4]!)
  ]

  let all_gates :=
    [one_gate] ++ ovf_mant_gates ++ ovf_exp_one_gates ++ ovf_exp_add_gates ++
    const_23_gates ++ lshift_sub_gates ++ sum_lower_gates ++ lshift_gates ++
    norm_mant_gates ++ lshift_ext_gates ++ norm_exp_sub_gates ++
    result_mant_gates ++ result_exp_gates ++
    zero_det_gates ++ [result_sign_gate] ++
    result_exp_mask_gates ++ result_mant_mask_gates ++ normal_pack_gates ++
    nan_gates ++ inf_result_gates ++
    [any_inf_gate, not_inf_sub_inf_gate, inf_not_nv_gate, is_nan_result_gate] ++
    mux1_gates ++ final_mux_gates ++
    [exc_nv_gate, ovf_loses_gate, nx_raw_gate, not_any_special_gate, exc_nx_gate] ++
    exc_output_gates

  { name := "FPAdder_Stage4_NormRound"
    inputs := [big_sign] ++ big_exp ++ sum ++ lead_pos ++
              [overflow, found, sticky, any_nan, any_special,
               inf_sub_inf, inf_result_sign, a_is_inf, b_is_inf, zero]
    outputs := result ++ exc
    gates := all_gates
    instances := []
    signalGroups := [
      { name := "big_exp", width := 8, wires := big_exp },
      { name := "sum", width := 24, wires := sum },
      { name := "lead_pos", width := 5, wires := lead_pos },
      { name := "result", width := 32, wires := result },
      { name := "exc", width := 5, wires := exc }
    ] }

def fpAdder_Stage4Circuit : Circuit := mkFPAdder_Stage4_NormRound

/-! ## Top-Level Hierarchical Circuit -/

def fpAdderCircuit : Circuit :=
  let src1       := makeIndexedWires "src1" 32
  let src2       := makeIndexedWires "src2" 32
  let op_sub     := Wire.mk "op_sub"
  let rm         := makeIndexedWires "rm" 3
  let dest_tag   := makeIndexedWires "dest_tag" 6
  let valid_in   := Wire.mk "valid_in"
  let clock      := Wire.mk "clock"
  let reset      := Wire.mk "reset"
  let zero       := Wire.mk "zero"

  let result     := makeIndexedWires "result" 32
  let tag_out    := makeIndexedWires "tag_out" 6
  let exc        := makeIndexedWires "exc" 5
  let valid_out  := Wire.mk "valid_out"

  -- Stage 1 wires
  let s1_sign_a := Wire.mk "s1_sign_a"
  let s1_eff_sign_b := Wire.mk "s1_eff_sign_b"
  let s1_exp_a := makeIndexedWires "s1_exp_a" 8
  let s1_exp_b := makeIndexedWires "s1_exp_b" 8
  let s1_mant_a := makeIndexedWires "s1_mant_a" 24
  let s1_mant_b := makeIndexedWires "s1_mant_b" 24
  let s1_exp_diff := makeIndexedWires "s1_exp_diff" 9
  let s1_swap := Wire.mk "s1_swap"
  let s1_any_nan := Wire.mk "s1_any_nan"
  let s1_any_special := Wire.mk "s1_any_special"
  let s1_both_inf := Wire.mk "s1_both_inf"
  let s1_a_is_inf := Wire.mk "s1_a_is_inf"
  let s1_b_is_inf := Wire.mk "s1_b_is_inf"

  let stage1_inst : CircuitInstance := {
    moduleName := "FPAdder_Stage1_Unpack"
    instName := "u_stage1"
    portMap :=
      ((List.range 32).map fun i => (s!"src1_{i}", src1[i]!)) ++
      ((List.range 32).map fun i => (s!"src2_{i}", src2[i]!)) ++
      [("op_sub", op_sub), ("zero", zero),
       ("sign_a", s1_sign_a), ("eff_sign_b", s1_eff_sign_b)] ++
      ((List.range 8).map fun i => (s!"exp_a_{i}", s1_exp_a[i]!)) ++
      ((List.range 8).map fun i => (s!"exp_b_{i}", s1_exp_b[i]!)) ++
      ((List.range 24).map fun i => (s!"mant_a_{i}", s1_mant_a[i]!)) ++
      ((List.range 24).map fun i => (s!"mant_b_{i}", s1_mant_b[i]!)) ++
      ((List.range 9).map fun i => (s!"exp_diff_{i}", s1_exp_diff[i]!)) ++
      [("swap", s1_swap), ("any_nan", s1_any_nan),
       ("any_special", s1_any_special), ("both_inf", s1_both_inf),
       ("a_is_inf", s1_a_is_inf), ("b_is_inf", s1_b_is_inf)]
  }

  -- Stage 1 DFFs
  let p1_sign_a := Wire.mk "p1_sign_a"
  let p1_eff_sign_b := Wire.mk "p1_eff_sign_b"
  let p1_exp_a := makeIndexedWires "p1_exp_a" 8
  let p1_exp_b := makeIndexedWires "p1_exp_b" 8
  let p1_mant_a := makeIndexedWires "p1_mant_a" 24
  let p1_mant_b := makeIndexedWires "p1_mant_b" 24
  let p1_exp_diff := makeIndexedWires "p1_exp_diff" 9
  let p1_swap := Wire.mk "p1_swap"
  let p1_any_nan := Wire.mk "p1_any_nan"
  let p1_any_special := Wire.mk "p1_any_special"
  let p1_both_inf := Wire.mk "p1_both_inf"
  let p1_a_is_inf := Wire.mk "p1_a_is_inf"
  let p1_b_is_inf := Wire.mk "p1_b_is_inf"
  let p1_rm := makeIndexedWires "p1_rm" 3
  let p1_tag := makeIndexedWires "p1_tag" 6
  let p1_valid := Wire.mk "p1_valid"

  let p1_dffs :=
    [Gate.mkDFF s1_sign_a clock reset p1_sign_a,
     Gate.mkDFF s1_eff_sign_b clock reset p1_eff_sign_b,
     Gate.mkDFF s1_swap clock reset p1_swap,
     Gate.mkDFF valid_in clock reset p1_valid,
     Gate.mkDFF s1_any_nan clock reset p1_any_nan,
     Gate.mkDFF s1_any_special clock reset p1_any_special,
     Gate.mkDFF s1_both_inf clock reset p1_both_inf,
     Gate.mkDFF s1_a_is_inf clock reset p1_a_is_inf,
     Gate.mkDFF s1_b_is_inf clock reset p1_b_is_inf] ++
    mkDFFBank s1_exp_a p1_exp_a clock reset ++
    mkDFFBank s1_exp_b p1_exp_b clock reset ++
    mkDFFBank s1_mant_a p1_mant_a clock reset ++
    mkDFFBank s1_mant_b p1_mant_b clock reset ++
    mkDFFBank s1_exp_diff p1_exp_diff clock reset ++
    mkDFFBank rm p1_rm clock reset ++
    mkDFFBank dest_tag p1_tag clock reset

  -- Stage 2 wires
  let s2_big_sign := Wire.mk "s2_big_sign"
  let s2_big_exp := makeIndexedWires "s2_big_exp" 8
  let s2_big_mant := makeIndexedWires "s2_big_mant" 24
  let s2_aligned := makeIndexedWires "s2_aligned" 24
  let s2_eff_sub := Wire.mk "s2_eff_sub"
  let s2_sticky := Wire.mk "s2_sticky"
  let s2_inf_sub_inf := Wire.mk "s2_inf_sub_inf"
  let s2_inf_result_sign := Wire.mk "s2_inf_result_sign"

  let stage2_inst : CircuitInstance := {
    moduleName := "FPAdder_Stage2_Align"
    instName := "u_stage2"
    portMap :=
      [("sign_a", p1_sign_a), ("eff_sign_b", p1_eff_sign_b)] ++
      ((List.range 8).map fun i => (s!"exp_a_{i}", p1_exp_a[i]!)) ++
      ((List.range 8).map fun i => (s!"exp_b_{i}", p1_exp_b[i]!)) ++
      ((List.range 24).map fun i => (s!"mant_a_{i}", p1_mant_a[i]!)) ++
      ((List.range 24).map fun i => (s!"mant_b_{i}", p1_mant_b[i]!)) ++
      ((List.range 9).map fun i => (s!"exp_diff_{i}", p1_exp_diff[i]!)) ++
      [("swap", p1_swap), ("both_inf", p1_both_inf), ("a_is_inf", p1_a_is_inf), ("zero", zero),
       ("big_sign", s2_big_sign)] ++
      ((List.range 8).map fun i => (s!"big_exp_{i}", s2_big_exp[i]!)) ++
      ((List.range 24).map fun i => (s!"big_mant_{i}", s2_big_mant[i]!)) ++
      ((List.range 24).map fun i => (s!"aligned_{i}", s2_aligned[i]!)) ++
      [("eff_sub", s2_eff_sub), ("sticky", s2_sticky),
       ("inf_sub_inf", s2_inf_sub_inf), ("inf_result_sign", s2_inf_result_sign)]
  }

  -- Stage 2 DFFs
  let p2_big_sign := Wire.mk "p2_big_sign"
  let p2_big_exp := makeIndexedWires "p2_big_exp" 8
  let p2_big_mant := makeIndexedWires "p2_big_mant" 24
  let p2_aligned := makeIndexedWires "p2_aligned" 24
  let p2_eff_sub := Wire.mk "p2_eff_sub"
  let p2_rm := makeIndexedWires "p2_rm" 3
  let p2_tag := makeIndexedWires "p2_tag" 6
  let p2_valid := Wire.mk "p2_valid"
  let p2_sticky := Wire.mk "p2_sticky"
  let p2_any_nan := Wire.mk "p2_any_nan"
  let p2_any_special := Wire.mk "p2_any_special"
  let p2_inf_sub_inf := Wire.mk "p2_inf_sub_inf"
  let p2_inf_result_sign := Wire.mk "p2_inf_result_sign"
  let p2_a_is_inf := Wire.mk "p2_a_is_inf"
  let p2_b_is_inf := Wire.mk "p2_b_is_inf"

  let p2_dffs :=
    [Gate.mkDFF s2_big_sign clock reset p2_big_sign,
     Gate.mkDFF s2_eff_sub clock reset p2_eff_sub,
     Gate.mkDFF p1_valid clock reset p2_valid,
     Gate.mkDFF s2_sticky clock reset p2_sticky,
     Gate.mkDFF p1_any_nan clock reset p2_any_nan,
     Gate.mkDFF p1_any_special clock reset p2_any_special,
     Gate.mkDFF s2_inf_sub_inf clock reset p2_inf_sub_inf,
     Gate.mkDFF s2_inf_result_sign clock reset p2_inf_result_sign,
     Gate.mkDFF p1_a_is_inf clock reset p2_a_is_inf,
     Gate.mkDFF p1_b_is_inf clock reset p2_b_is_inf] ++
    mkDFFBank s2_big_exp p2_big_exp clock reset ++
    mkDFFBank s2_big_mant p2_big_mant clock reset ++
    mkDFFBank s2_aligned p2_aligned clock reset ++
    mkDFFBank p1_rm p2_rm clock reset ++
    mkDFFBank p1_tag p2_tag clock reset

  -- Stage 3 wires
  let s3_sum := makeIndexedWires "s3_sum" 24
  let s3_overflow := Wire.mk "s3_overflow"
  let s3_lead_pos := makeIndexedWires "s3_lead_pos" 5
  let s3_found := Wire.mk "s3_found"

  let stage3_inst : CircuitInstance := {
    moduleName := "FPAdder_Stage3_AddSub"
    instName := "u_stage3"
    portMap :=
      ((List.range 24).map fun i => (s!"big_mant_{i}", p2_big_mant[i]!)) ++
      ((List.range 24).map fun i => (s!"aligned_{i}", p2_aligned[i]!)) ++
      [("eff_sub", p2_eff_sub), ("zero", zero)] ++
      ((List.range 24).map fun i => (s!"sum_{i}", s3_sum[i]!)) ++
      [("overflow", s3_overflow)] ++
      ((List.range 5).map fun i => (s!"lead_pos_{i}", s3_lead_pos[i]!)) ++
      [("found", s3_found)]
  }

  -- Stage 3 DFFs
  let p3_big_sign := Wire.mk "p3_big_sign"
  let p3_big_exp := makeIndexedWires "p3_big_exp" 8
  let p3_sum := makeIndexedWires "p3_sum" 24
  let p3_lead_pos := makeIndexedWires "p3_lead_pos" 5
  let p3_overflow := Wire.mk "p3_overflow"
  let p3_found := Wire.mk "p3_found"
  let p3_rm := makeIndexedWires "p3_rm" 3
  let p3_tag := makeIndexedWires "p3_tag" 6
  let p3_valid := Wire.mk "p3_valid"
  let p3_sticky := Wire.mk "p3_sticky"
  let p3_any_nan := Wire.mk "p3_any_nan"
  let p3_any_special := Wire.mk "p3_any_special"
  let p3_inf_sub_inf := Wire.mk "p3_inf_sub_inf"
  let p3_inf_result_sign := Wire.mk "p3_inf_result_sign"
  let p3_a_is_inf := Wire.mk "p3_a_is_inf"
  let p3_b_is_inf := Wire.mk "p3_b_is_inf"

  let p3_dffs :=
    [Gate.mkDFF p2_big_sign clock reset p3_big_sign,
     Gate.mkDFF s3_overflow clock reset p3_overflow,
     Gate.mkDFF s3_found clock reset p3_found,
     Gate.mkDFF p2_valid clock reset p3_valid,
     Gate.mkDFF p2_sticky clock reset p3_sticky,
     Gate.mkDFF p2_any_nan clock reset p3_any_nan,
     Gate.mkDFF p2_any_special clock reset p3_any_special,
     Gate.mkDFF p2_inf_sub_inf clock reset p3_inf_sub_inf,
     Gate.mkDFF p2_inf_result_sign clock reset p3_inf_result_sign,
     Gate.mkDFF p2_a_is_inf clock reset p3_a_is_inf,
     Gate.mkDFF p2_b_is_inf clock reset p3_b_is_inf] ++
    mkDFFBank p2_big_exp p3_big_exp clock reset ++
    mkDFFBank s3_sum p3_sum clock reset ++
    mkDFFBank s3_lead_pos p3_lead_pos clock reset ++
    mkDFFBank p2_rm p3_rm clock reset ++
    mkDFFBank p2_tag p3_tag clock reset

  -- Stage 4: Normalize + Special values + Pack + Exceptions
  let stage4_inst : CircuitInstance := {
    moduleName := "FPAdder_Stage4_NormRound"
    instName := "u_stage4"
    portMap :=
      [("big_sign", p3_big_sign)] ++
      ((List.range 8).map fun i => (s!"big_exp_{i}", p3_big_exp[i]!)) ++
      ((List.range 24).map fun i => (s!"sum_{i}", p3_sum[i]!)) ++
      ((List.range 5).map fun i => (s!"lead_pos_{i}", p3_lead_pos[i]!)) ++
      [("overflow", p3_overflow), ("found", p3_found),
       ("sticky", p3_sticky), ("any_nan", p3_any_nan),
       ("any_special", p3_any_special), ("inf_sub_inf", p3_inf_sub_inf),
       ("inf_result_sign", p3_inf_result_sign),
       ("a_is_inf", p3_a_is_inf), ("b_is_inf", p3_b_is_inf), ("zero", zero)] ++
      ((List.range 32).map fun i => (s!"result_{i}", result[i]!)) ++
      ((List.range 5).map fun i => (s!"exc_{i}", exc[i]!))
  }

  let tag_gates := mkBUFBank p3_tag tag_out
  let p3_rm_zero0 := Wire.mk "p3_rm_z0"
  let p3_rm_zero1 := Wire.mk "p3_rm_z1"
  let p3_rm_zero2 := Wire.mk "p3_rm_z2"
  let not_p3_rm0 := Wire.mk "not_p3_rm0"
  let not_p3_rm1 := Wire.mk "not_p3_rm1"
  let not_p3_rm2 := Wire.mk "not_p3_rm2"
  let valid_v0 := Wire.mk "valid_v0"
  let valid_v1 := Wire.mk "valid_v1"
  let rm_absorb_gates := [
    Gate.mkNOT (p3_rm[0]!) not_p3_rm0,
    Gate.mkAND (p3_rm[0]!) not_p3_rm0 p3_rm_zero0,
    Gate.mkNOT (p3_rm[1]!) not_p3_rm1,
    Gate.mkAND (p3_rm[1]!) not_p3_rm1 p3_rm_zero1,
    Gate.mkNOT (p3_rm[2]!) not_p3_rm2,
    Gate.mkAND (p3_rm[2]!) not_p3_rm2 p3_rm_zero2,
    Gate.mkOR p3_valid p3_rm_zero0 valid_v0,
    Gate.mkOR p3_rm_zero1 p3_rm_zero2 valid_v1,
    Gate.mkOR valid_v0 valid_v1 valid_out
  ]

  let all_gates := p1_dffs ++ p2_dffs ++ p3_dffs ++ tag_gates ++ rm_absorb_gates

  { name := "FPAdder"
    inputs := src1 ++ src2 ++ [op_sub] ++ rm ++ dest_tag ++ [valid_in, clock, reset, zero]
    outputs := result ++ tag_out ++ exc ++ [valid_out]
    gates := all_gates
    instances := [stage1_inst, stage2_inst, stage3_inst, stage4_inst]
    signalGroups := [
      { name := "src1",     width := 32, wires := src1 },
      { name := "src2",     width := 32, wires := src2 },
      { name := "rm",       width := 3,  wires := rm },
      { name := "dest_tag", width := 6,  wires := dest_tag },
      { name := "result",   width := 32, wires := result },
      { name := "tag_out",  width := 6,  wires := tag_out },
      { name := "exc",      width := 5,  wires := exc }
    ] }

end Shoumei.Circuits.Sequential
