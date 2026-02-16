/-
Circuits/Sequential/FPAdder.lean - 4-Stage Pipelined FP Adder/Subtractor

A pipelined floating-point adder/subtractor for IEEE 754 binary32.

Pipeline stages (4-cycle latency):
  Stage 1: Latch inputs + Unpack + Exponent diff + Swap signal
  Stage 2: Swap operands + Alignment barrel shift
  Stage 3: Mantissa add (KSA) + Leading-zero detect
  Stage 4: Normalize + Pack

Interface:
- Inputs: src1[31:0], src2[31:0], op_sub, rm[2:0], dest_tag[5:0], valid_in,
          clock, reset, zero
- Outputs: result[31:0], tag_out[5:0], exc[4:0], valid_out
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.KoggeStoneAdder

namespace Shoumei.Circuits.Sequential

open Shoumei
open Shoumei.Circuits.Combinational

/-! ## Helper: Indexed Wire Generation -/

private def makeIndexedWires (pfx : String) (n : Nat) : List Wire :=
  (List.range n).map fun i => Wire.mk (pfx ++ "_" ++ toString i)

/-! ## Helper: DFF Bank -/

/-- Create a bank of DFFs: for each i, mkDFF (d[i]) clock reset (q[i]). -/
private def mkDFFBank (d_wires q_wires : List Wire) (clock reset : Wire) : List Gate :=
  List.zipWith (fun d q => Gate.mkDFF d clock reset q) d_wires q_wires

/-- Create a bank of BUF gates: for each i, mkBUF (src[i]) (dst[i]). -/
private def mkBUFBank (src dst : List Wire) : List Gate :=
  List.zipWith (fun s d => Gate.mkBUF s d) src dst

/-! ## Arithmetic Helpers -/

/-- 5-level barrel right shifter for w-bit value.
    shift_amt: 5 wires [0..4] for shift amounts 1,2,4,8,16.
    zero_wire: constant 0 for bits shifted in. -/
private def mkBarrelShiftRight (input : List Wire) (shift_amt : List Wire)
    (output : List Wire) (zero_wire : Wire) (pfx : String) : List Gate :=
  let w := input.length
  -- 5 levels of MUX
  let levels : List (List Wire) := (List.range 6).map fun level =>
    if level == 0 then input
    else (List.range w).map fun i => Wire.mk (pfx ++ "_l" ++ toString level ++ "_" ++ toString i)
  let mux_gates := (List.range 5).flatMap fun level =>
    let shift_by := 1 <<< level  -- 1, 2, 4, 8, 16
    let prev := levels[level]!
    let curr := levels[level + 1]!
    let sel := shift_amt[level]!
    (List.range w).map fun i =>
      let unshifted := prev[i]!
      let shifted := if i + shift_by < w then prev[i + shift_by]! else zero_wire
      Gate.mkMUX unshifted shifted sel curr[i]!
  -- Copy final level to output
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
      -- Left shift: bit i comes from bit (i - shift_by)
      let shifted := if i ≥ shift_by then prev[i - shift_by]! else zero_wire
      Gate.mkMUX unshifted shifted sel curr[i]!
  let copy_gates := (List.range w).map fun i =>
    Gate.mkBUF (levels[5]!)[i]! output[i]!
  mux_gates ++ copy_gates

/-! ## Circuit Definition -/

def fpAdderCircuit : Circuit :=
  -- Primary inputs
  let src1       := makeIndexedWires "src1" 32
  let src2       := makeIndexedWires "src2" 32
  let op_sub     := Wire.mk "op_sub"
  let rm         := makeIndexedWires "rm" 3
  let dest_tag   := makeIndexedWires "dest_tag" 6
  let valid_in   := Wire.mk "valid_in"
  let clock      := Wire.mk "clock"
  let reset      := Wire.mk "reset"
  let zero       := Wire.mk "zero"

  -- Constant one wire (for subtraction carry-in)
  let one        := Wire.mk "fp_const_one"
  let one_gate   := Gate.mkNOT zero one

  -- Primary outputs
  let result     := makeIndexedWires "result" 32
  let tag_out    := makeIndexedWires "tag_out" 6
  let exc        := makeIndexedWires "exc" 5
  let valid_out  := Wire.mk "valid_out"

  ---------------------------------------------------------------
  -- Stage 1 combinational: Unpack + Exponent diff + Swap
  ---------------------------------------------------------------

  -- Unpack operand A
  let sign_a := Wire.mk "fp_sign_a"
  let sign_a_gate := Gate.mkBUF src1[31]! sign_a

  let exp_a := makeIndexedWires "fp_exp_a" 8
  let exp_a_gates := (List.range 8).map fun i =>
    Gate.mkBUF src1[23 + i]! exp_a[i]!

  -- exp_a_all_zeros: NOR tree
  let exp_a_or01 := Wire.mk "fp_exp_a_or01"
  let exp_a_or23 := Wire.mk "fp_exp_a_or23"
  let exp_a_or45 := Wire.mk "fp_exp_a_or45"
  let exp_a_or67 := Wire.mk "fp_exp_a_or67"
  let exp_a_or0123 := Wire.mk "fp_exp_a_or0123"
  let exp_a_or4567 := Wire.mk "fp_exp_a_or4567"
  let exp_a_or_all := Wire.mk "fp_exp_a_or_all"
  let exp_a_zero_gates := [
    Gate.mkOR exp_a[0]! exp_a[1]! exp_a_or01,
    Gate.mkOR exp_a[2]! exp_a[3]! exp_a_or23,
    Gate.mkOR exp_a[4]! exp_a[5]! exp_a_or45,
    Gate.mkOR exp_a[6]! exp_a[7]! exp_a_or67,
    Gate.mkOR exp_a_or01 exp_a_or23 exp_a_or0123,
    Gate.mkOR exp_a_or45 exp_a_or67 exp_a_or4567,
    Gate.mkOR exp_a_or0123 exp_a_or4567 exp_a_or_all
  ]

  -- implicit bit = NOT(exp_all_zeros) = or_all
  let implicit_a := Wire.mk "fp_implicit_a"
  let implicit_a_gate := Gate.mkBUF exp_a_or_all implicit_a

  -- mant_a[23:0] = {implicit_a, src1[22:0]}
  let mant_a := makeIndexedWires "fp_mant_a" 24
  let mant_a_gates := (List.range 23).map (fun i =>
    Gate.mkBUF src1[i]! mant_a[i]!) ++
    [Gate.mkBUF implicit_a mant_a[23]!]

  -- Unpack operand B
  let sign_b_raw := Wire.mk "fp_sign_b_raw"
  let sign_b_raw_gate := Gate.mkBUF src2[31]! sign_b_raw

  let eff_sign_b := Wire.mk "fp_eff_sign_b"
  let eff_sign_b_gate := Gate.mkXOR sign_b_raw op_sub eff_sign_b

  let exp_b := makeIndexedWires "fp_exp_b" 8
  let exp_b_gates := (List.range 8).map fun i =>
    Gate.mkBUF src2[23 + i]! exp_b[i]!

  let exp_b_or01 := Wire.mk "fp_exp_b_or01"
  let exp_b_or23 := Wire.mk "fp_exp_b_or23"
  let exp_b_or45 := Wire.mk "fp_exp_b_or45"
  let exp_b_or67 := Wire.mk "fp_exp_b_or67"
  let exp_b_or0123 := Wire.mk "fp_exp_b_or0123"
  let exp_b_or4567 := Wire.mk "fp_exp_b_or4567"
  let exp_b_or_all := Wire.mk "fp_exp_b_or_all"
  let exp_b_zero_gates := [
    Gate.mkOR exp_b[0]! exp_b[1]! exp_b_or01,
    Gate.mkOR exp_b[2]! exp_b[3]! exp_b_or23,
    Gate.mkOR exp_b[4]! exp_b[5]! exp_b_or45,
    Gate.mkOR exp_b[6]! exp_b[7]! exp_b_or67,
    Gate.mkOR exp_b_or01 exp_b_or23 exp_b_or0123,
    Gate.mkOR exp_b_or45 exp_b_or67 exp_b_or4567,
    Gate.mkOR exp_b_or0123 exp_b_or4567 exp_b_or_all
  ]

  let implicit_b := Wire.mk "fp_implicit_b"
  let implicit_b_gate := Gate.mkBUF exp_b_or_all implicit_b

  let mant_b := makeIndexedWires "fp_mant_b" 24
  let mant_b_gates := (List.range 23).map (fun i =>
    Gate.mkBUF src2[i]! mant_b[i]!) ++
    [Gate.mkBUF implicit_b mant_b[23]!]

  -- Detect special values: exp==0xFF means Inf or NaN
  -- a_is_special = exp_a_all_ones = AND(exp_a[7:0])
  let exp_a_and01 := Wire.mk "fp_exp_a_and01"
  let exp_a_and23 := Wire.mk "fp_exp_a_and23"
  let exp_a_and45 := Wire.mk "fp_exp_a_and45"
  let exp_a_and67 := Wire.mk "fp_exp_a_and67"
  let exp_a_and0123 := Wire.mk "fp_exp_a_and0123"
  let exp_a_and4567 := Wire.mk "fp_exp_a_and4567"
  let a_exp_all_ones := Wire.mk "fp_a_exp_all_ones"
  let exp_a_and_gates := [
    Gate.mkAND exp_a[0]! exp_a[1]! exp_a_and01,
    Gate.mkAND exp_a[2]! exp_a[3]! exp_a_and23,
    Gate.mkAND exp_a[4]! exp_a[5]! exp_a_and45,
    Gate.mkAND exp_a[6]! exp_a[7]! exp_a_and67,
    Gate.mkAND exp_a_and01 exp_a_and23 exp_a_and0123,
    Gate.mkAND exp_a_and45 exp_a_and67 exp_a_and4567,
    Gate.mkAND exp_a_and0123 exp_a_and4567 a_exp_all_ones
  ]

  let exp_b_and01 := Wire.mk "fp_exp_b_and01"
  let exp_b_and23 := Wire.mk "fp_exp_b_and23"
  let exp_b_and45 := Wire.mk "fp_exp_b_and45"
  let exp_b_and67 := Wire.mk "fp_exp_b_and67"
  let exp_b_and0123 := Wire.mk "fp_exp_b_and0123"
  let exp_b_and4567 := Wire.mk "fp_exp_b_and4567"
  let b_exp_all_ones := Wire.mk "fp_b_exp_all_ones"
  let exp_b_and_gates := [
    Gate.mkAND exp_b[0]! exp_b[1]! exp_b_and01,
    Gate.mkAND exp_b[2]! exp_b[3]! exp_b_and23,
    Gate.mkAND exp_b[4]! exp_b[5]! exp_b_and45,
    Gate.mkAND exp_b[6]! exp_b[7]! exp_b_and67,
    Gate.mkAND exp_b_and01 exp_b_and23 exp_b_and0123,
    Gate.mkAND exp_b_and45 exp_b_and67 exp_b_and4567,
    Gate.mkAND exp_b_and0123 exp_b_and4567 b_exp_all_ones
  ]

  -- NaN detection: exp==0xFF AND mant[22:0] != 0 (using existing mant OR tree)
  -- mant_a[22:0] = src1[22:0], OR tree to detect non-zero
  let _mant_a_or := makeIndexedWires "fp_mant_a_or" 4  -- 4-level OR reduction of 23 bits
  let mant_a_or_gates :=
    -- Level 1: pairs of mantissa bits
    let or_l1 := (List.range 12).map fun i =>
      let w := Wire.mk s!"fp_mant_a_or_l1_{i}"
      (Gate.mkOR src1[2*i]! src1[2*i+1]! w, w)
    let l1_gates := or_l1.map Prod.fst
    let l1_wires := or_l1.map Prod.snd ++ [src1[22]!]  -- 13 wires (12 pairs + bit 22)
    -- Level 2: pairs of level 1
    let or_l2 := (List.range 7).map fun i =>
      let src_a := if 2*i < l1_wires.length then l1_wires[2*i]! else zero
      let src_b := if 2*i+1 < l1_wires.length then l1_wires[2*i+1]! else zero
      let w := Wire.mk s!"fp_mant_a_or_l2_{i}"
      (Gate.mkOR src_a src_b w, w)
    let l2_gates := or_l2.map Prod.fst
    let l2_wires := or_l2.map Prod.snd
    -- Level 3: pairs of level 2
    let or_l3 := (List.range 4).map fun i =>
      let src_a := if 2*i < l2_wires.length then l2_wires[2*i]! else zero
      let src_b := if 2*i+1 < l2_wires.length then l2_wires[2*i+1]! else zero
      let w := Wire.mk s!"fp_mant_a_or_l3_{i}"
      (Gate.mkOR src_a src_b w, w)
    let l3_gates := or_l3.map Prod.fst
    let l3_wires := or_l3.map Prod.snd
    -- Level 4: final OR
    let or_01 := Wire.mk "fp_mant_a_or_01"
    let or_23 := Wire.mk "fp_mant_a_or_23"
    let a_mant_nonzero := Wire.mk "fp_a_mant_nonzero"
    let l4_gates := [
      Gate.mkOR (if l3_wires.length > 0 then l3_wires[0]! else zero)
               (if l3_wires.length > 1 then l3_wires[1]! else zero) or_01,
      Gate.mkOR (if l3_wires.length > 2 then l3_wires[2]! else zero)
               (if l3_wires.length > 3 then l3_wires[3]! else zero) or_23,
      Gate.mkOR or_01 or_23 a_mant_nonzero
    ]
    l1_gates ++ l2_gates ++ l3_gates ++ l4_gates

  let a_mant_nonzero := Wire.mk "fp_a_mant_nonzero"
  let a_is_nan := Wire.mk "fp_a_is_nan"
  let a_is_inf := Wire.mk "fp_a_is_inf"
  let not_a_mant_nonzero := Wire.mk "fp_not_a_mant_nz"
  let a_nan_inf_gates := [
    Gate.mkAND a_exp_all_ones a_mant_nonzero a_is_nan,
    Gate.mkNOT a_mant_nonzero not_a_mant_nonzero,
    Gate.mkAND a_exp_all_ones not_a_mant_nonzero a_is_inf
  ]

  -- Same for operand B
  let b_mant_nonzero := Wire.mk "fp_b_mant_nonzero"
  let mant_b_or_gates :=
    let or_l1 := (List.range 12).map fun i =>
      let w := Wire.mk s!"fp_mant_b_or_l1_{i}"
      (Gate.mkOR src2[2*i]! src2[2*i+1]! w, w)
    let l1_gates := or_l1.map Prod.fst
    let l1_wires := or_l1.map Prod.snd ++ [src2[22]!]
    let or_l2 := (List.range 7).map fun i =>
      let src_a := if 2*i < l1_wires.length then l1_wires[2*i]! else zero
      let src_b := if 2*i+1 < l1_wires.length then l1_wires[2*i+1]! else zero
      let w := Wire.mk s!"fp_mant_b_or_l2_{i}"
      (Gate.mkOR src_a src_b w, w)
    let l2_gates := or_l2.map Prod.fst
    let l2_wires := or_l2.map Prod.snd
    let or_l3 := (List.range 4).map fun i =>
      let src_a := if 2*i < l2_wires.length then l2_wires[2*i]! else zero
      let src_b := if 2*i+1 < l2_wires.length then l2_wires[2*i+1]! else zero
      let w := Wire.mk s!"fp_mant_b_or_l3_{i}"
      (Gate.mkOR src_a src_b w, w)
    let l3_gates := or_l3.map Prod.fst
    let l3_wires := or_l3.map Prod.snd
    let or_01 := Wire.mk "fp_mant_b_or_01"
    let or_23 := Wire.mk "fp_mant_b_or_23"
    let l4_gates := [
      Gate.mkOR (if l3_wires.length > 0 then l3_wires[0]! else zero)
               (if l3_wires.length > 1 then l3_wires[1]! else zero) or_01,
      Gate.mkOR (if l3_wires.length > 2 then l3_wires[2]! else zero)
               (if l3_wires.length > 3 then l3_wires[3]! else zero) or_23,
      Gate.mkOR or_01 or_23 b_mant_nonzero
    ]
    l1_gates ++ l2_gates ++ l3_gates ++ l4_gates

  let b_is_nan := Wire.mk "fp_b_is_nan"
  let b_is_inf := Wire.mk "fp_b_is_inf"
  let not_b_mant_nonzero := Wire.mk "fp_not_b_mant_nz"
  let b_nan_inf_gates := [
    Gate.mkAND b_exp_all_ones b_mant_nonzero b_is_nan,
    Gate.mkNOT b_mant_nonzero not_b_mant_nonzero,
    Gate.mkAND b_exp_all_ones not_b_mant_nonzero b_is_inf
  ]

  -- any_nan = a_is_nan OR b_is_nan
  -- any_special = a_exp_all_ones OR b_exp_all_ones (either input is NaN or Inf)
  -- inf_sub_inf = a_is_inf AND b_is_inf AND eff_sub (signs differ for effective subtract)
  -- But eff_sub isn't computed yet (it's in stage 2). So latch a_is_inf, b_is_inf through.
  let any_nan := Wire.mk "fp_any_nan"
  let any_special := Wire.mk "fp_any_special"
  let any_nan_gate := Gate.mkOR a_is_nan b_is_nan any_nan
  let any_special_gate := Gate.mkOR a_exp_all_ones b_exp_all_ones any_special
  let both_inf := Wire.mk "fp_both_inf"
  let both_inf_gate := Gate.mkAND a_is_inf b_is_inf both_inf

  -- Exponent difference (9-bit): exp_a - exp_b
  let exp_a_ext := makeIndexedWires "fp_exp_a_ext" 9
  let exp_a_ext_gates := (List.range 8).map (fun i =>
    Gate.mkBUF exp_a[i]! exp_a_ext[i]!) ++
    [Gate.mkBUF zero exp_a_ext[8]!]

  let exp_b_ext := makeIndexedWires "fp_exp_b_ext" 9
  let exp_b_ext_gates := (List.range 8).map (fun i =>
    Gate.mkBUF exp_b[i]! exp_b_ext[i]!) ++
    [Gate.mkBUF zero exp_b_ext[8]!]

  let exp_diff := makeIndexedWires "fp_exp_diff" 9
  let (exp_diff_gates, _exp_diff_borrow) :=
    mkKoggeStoneSub exp_a_ext exp_b_ext exp_diff "fp_expdiff" one

  -- swap = borrow (exp_a < exp_b)
  let swap := Wire.mk "fp_swap"
  let swap_gate := Gate.mkBUF _exp_diff_borrow swap

  let s1_comb_gates :=
    [sign_a_gate] ++ exp_a_gates ++ exp_a_zero_gates ++ [implicit_a_gate] ++ mant_a_gates ++
    [sign_b_raw_gate, eff_sign_b_gate] ++ exp_b_gates ++ exp_b_zero_gates ++
    [implicit_b_gate] ++ mant_b_gates ++
    exp_a_and_gates ++ exp_b_and_gates ++
    mant_a_or_gates ++ a_nan_inf_gates ++
    mant_b_or_gates ++ b_nan_inf_gates ++
    [any_nan_gate, any_special_gate, both_inf_gate] ++
    exp_a_ext_gates ++ exp_b_ext_gates ++ exp_diff_gates ++ [swap_gate]

  ---------------------------------------------------------------
  -- Stage 1 registers: latch unpacked fields
  ---------------------------------------------------------------
  let s1_sign_a    := Wire.mk "s1_sign_a"
  let s1_eff_sign_b := Wire.mk "s1_eff_sign_b"
  let s1_exp_a     := makeIndexedWires "s1_exp_a" 8
  let s1_exp_b     := makeIndexedWires "s1_exp_b" 8
  let s1_mant_a    := makeIndexedWires "s1_mant_a" 24
  let s1_mant_b    := makeIndexedWires "s1_mant_b" 24
  let s1_exp_diff  := makeIndexedWires "s1_exp_diff" 9
  let s1_swap      := Wire.mk "s1_swap"
  let s1_rm        := makeIndexedWires "s1_rm" 3
  let s1_tag       := makeIndexedWires "s1_tag" 6
  let s1_valid     := Wire.mk "s1_valid"
  let s1_any_nan   := Wire.mk "s1_any_nan"
  let s1_any_special := Wire.mk "s1_any_special"
  let s1_both_inf  := Wire.mk "s1_both_inf"
  let s1_a_is_inf  := Wire.mk "s1_a_is_inf"
  let s1_b_is_inf  := Wire.mk "s1_b_is_inf"
  let s1_sign_a_raw := Wire.mk "s1_sign_a_raw"  -- raw sign for inf result
  let s1_eff_sign_b_raw := Wire.mk "s1_eff_sign_b_raw"

  let stage1_dff :=
    [Gate.mkDFF sign_a clock reset s1_sign_a,
     Gate.mkDFF eff_sign_b clock reset s1_eff_sign_b,
     Gate.mkDFF swap clock reset s1_swap,
     Gate.mkDFF valid_in clock reset s1_valid,
     Gate.mkDFF any_nan clock reset s1_any_nan,
     Gate.mkDFF any_special clock reset s1_any_special,
     Gate.mkDFF both_inf clock reset s1_both_inf,
     Gate.mkDFF a_is_inf clock reset s1_a_is_inf,
     Gate.mkDFF b_is_inf clock reset s1_b_is_inf,
     Gate.mkDFF sign_a clock reset s1_sign_a_raw,
     Gate.mkDFF eff_sign_b clock reset s1_eff_sign_b_raw] ++
    mkDFFBank exp_a s1_exp_a clock reset ++
    mkDFFBank exp_b s1_exp_b clock reset ++
    mkDFFBank mant_a s1_mant_a clock reset ++
    mkDFFBank mant_b s1_mant_b clock reset ++
    mkDFFBank exp_diff s1_exp_diff clock reset ++
    mkDFFBank rm s1_rm clock reset ++
    mkDFFBank dest_tag s1_tag clock reset

  ---------------------------------------------------------------
  -- Stage 2 combinational: Swap + Align
  ---------------------------------------------------------------

  -- Swap operands based on swap signal
  let big_sign := Wire.mk "fp_big_sign"
  let big_sign_gate := Gate.mkMUX s1_sign_a s1_eff_sign_b s1_swap big_sign

  let big_exp := makeIndexedWires "fp_big_exp" 8
  let big_exp_gates := (List.range 8).map fun i =>
    Gate.mkMUX s1_exp_a[i]! s1_exp_b[i]! s1_swap big_exp[i]!

  let big_mant := makeIndexedWires "fp_big_mant" 24
  let big_mant_gates := (List.range 24).map fun i =>
    Gate.mkMUX s1_mant_a[i]! s1_mant_b[i]! s1_swap big_mant[i]!

  let small_mant := makeIndexedWires "fp_small_mant" 24
  let small_mant_gates := (List.range 24).map fun i =>
    Gate.mkMUX s1_mant_b[i]! s1_mant_a[i]! s1_swap small_mant[i]!

  let small_sign := Wire.mk "fp_small_sign"
  let small_sign_gate := Gate.mkMUX s1_eff_sign_b s1_sign_a s1_swap small_sign

  -- Absolute exponent difference
  let neg_diff := makeIndexedWires "fp_neg_diff" 8
  let inv_diff := makeIndexedWires "fp_inv_diff" 8
  let inv_diff_gates := (List.range 8).map fun i =>
    Gate.mkNOT s1_exp_diff[i]! inv_diff[i]!

  let zeros8 := (List.range 8).map fun _ => zero
  let (neg_diff_add_gates, _neg_carry) :=
    mkKoggeStoneAdd inv_diff zeros8 one neg_diff "fp_negdiff"

  let abs_diff := makeIndexedWires "fp_abs_diff" 8
  let abs_diff_gates := (List.range 8).map fun i =>
    Gate.mkMUX s1_exp_diff[i]! neg_diff[i]! s1_swap abs_diff[i]!

  -- Clamp check
  let clamp_or56 := Wire.mk "fp_clamp_or56"
  let clamp_or567 := Wire.mk "fp_clamp_or567"
  let clamp_gates := [
    Gate.mkOR abs_diff[5]! abs_diff[6]! clamp_or56,
    Gate.mkOR clamp_or56 abs_diff[7]! clamp_or567
  ]

  -- Barrel shift right for alignment
  let shift_amt := (List.range 5).map fun i => abs_diff[i]!
  let aligned_pre := makeIndexedWires "fp_aligned_pre" 24
  let barrel_gates := mkBarrelShiftRight small_mant shift_amt aligned_pre zero "fp_bsr"

  -- Apply clamp
  let not_clamp := Wire.mk "fp_not_clamp"
  let not_clamp_gate := Gate.mkNOT clamp_or567 not_clamp
  let aligned := makeIndexedWires "fp_aligned" 24
  let clamp_and_gates := (List.range 24).map fun i =>
    Gate.mkAND aligned_pre[i]! not_clamp aligned[i]!

  -- Sticky bit computation: OR of bits shifted out during alignment barrel shift.
  -- Level 0 (shift by 1, sel=abs_diff[0]): bit small_mant[0] shifted out
  -- Level 1 (shift by 2, sel=abs_diff[1]): bits bsr_l1[0..1] shifted out
  -- Level 2 (shift by 4, sel=abs_diff[2]): bits bsr_l2[0..3] shifted out
  -- Level 3 (shift by 8, sel=abs_diff[3]): bits bsr_l3[0..7] shifted out
  -- Level 4 (shift by 16, sel=abs_diff[4]): bits bsr_l4[0..15] shifted out

  -- Level 0: 1 bit → just small_mant[0]
  let sticky_l0 := Wire.mk "fp_sticky_l0"
  let sticky_l0_gate := Gate.mkAND small_mant[0]! abs_diff[0]! sticky_l0

  -- Level 1: 2 bits → OR(bsr_l1[0], bsr_l1[1])
  let bsr_l1 := (List.range 24).map fun i => Wire.mk s!"fp_bsr_l1_{i}"
  let sticky_l1_or := Wire.mk "fp_sticky_l1_or"
  let sticky_l1 := Wire.mk "fp_sticky_l1"
  let sticky_l1_gates := [
    Gate.mkOR bsr_l1[0]! bsr_l1[1]! sticky_l1_or,
    Gate.mkAND sticky_l1_or abs_diff[1]! sticky_l1
  ]

  -- Level 2: 4 bits → OR(bsr_l2[0..3])
  let bsr_l2 := (List.range 24).map fun i => Wire.mk s!"fp_bsr_l2_{i}"
  let sticky_l2_or01 := Wire.mk "fp_sticky_l2_or01"
  let sticky_l2_or23 := Wire.mk "fp_sticky_l2_or23"
  let sticky_l2_or := Wire.mk "fp_sticky_l2_or"
  let sticky_l2 := Wire.mk "fp_sticky_l2"
  let sticky_l2_gates := [
    Gate.mkOR bsr_l2[0]! bsr_l2[1]! sticky_l2_or01,
    Gate.mkOR bsr_l2[2]! bsr_l2[3]! sticky_l2_or23,
    Gate.mkOR sticky_l2_or01 sticky_l2_or23 sticky_l2_or,
    Gate.mkAND sticky_l2_or abs_diff[2]! sticky_l2
  ]

  -- Level 3: 8 bits → OR(bsr_l3[0..7])
  let bsr_l3 := (List.range 24).map fun i => Wire.mk s!"fp_bsr_l3_{i}"
  let sticky_l3_or01 := Wire.mk "fp_sticky_l3_or01"
  let sticky_l3_or23 := Wire.mk "fp_sticky_l3_or23"
  let sticky_l3_or45 := Wire.mk "fp_sticky_l3_or45"
  let sticky_l3_or67 := Wire.mk "fp_sticky_l3_or67"
  let sticky_l3_or0123 := Wire.mk "fp_sticky_l3_or0123"
  let sticky_l3_or4567 := Wire.mk "fp_sticky_l3_or4567"
  let sticky_l3_or := Wire.mk "fp_sticky_l3_or"
  let sticky_l3 := Wire.mk "fp_sticky_l3"
  let sticky_l3_gates := [
    Gate.mkOR bsr_l3[0]! bsr_l3[1]! sticky_l3_or01,
    Gate.mkOR bsr_l3[2]! bsr_l3[3]! sticky_l3_or23,
    Gate.mkOR bsr_l3[4]! bsr_l3[5]! sticky_l3_or45,
    Gate.mkOR bsr_l3[6]! bsr_l3[7]! sticky_l3_or67,
    Gate.mkOR sticky_l3_or01 sticky_l3_or23 sticky_l3_or0123,
    Gate.mkOR sticky_l3_or45 sticky_l3_or67 sticky_l3_or4567,
    Gate.mkOR sticky_l3_or0123 sticky_l3_or4567 sticky_l3_or,
    Gate.mkAND sticky_l3_or abs_diff[3]! sticky_l3
  ]

  -- Level 4: 16 bits → OR(bsr_l4[0..15])
  let bsr_l4 := (List.range 24).map fun i => Wire.mk s!"fp_bsr_l4_{i}"
  let _sticky_l4_or := makeIndexedWires "fp_sticky_l4_or" 4
  let sticky_l4_final := Wire.mk "fp_sticky_l4_or_final"
  let sticky_l4 := Wire.mk "fp_sticky_l4"
  let sticky_l4_gates :=
    -- Reduce 16 bits in 4 levels: pairs→4→2→1
    let p01 := Wire.mk "fp_stk_l4_p01"
    let p23 := Wire.mk "fp_stk_l4_p23"
    let p45 := Wire.mk "fp_stk_l4_p45"
    let p67 := Wire.mk "fp_stk_l4_p67"
    let p89 := Wire.mk "fp_stk_l4_p89"
    let pab := Wire.mk "fp_stk_l4_pab"
    let pcd := Wire.mk "fp_stk_l4_pcd"
    let pef := Wire.mk "fp_stk_l4_pef"
    let q03 := Wire.mk "fp_stk_l4_q03"
    let q47 := Wire.mk "fp_stk_l4_q47"
    let q8b := Wire.mk "fp_stk_l4_q8b"
    let qcf := Wire.mk "fp_stk_l4_qcf"
    let r07 := Wire.mk "fp_stk_l4_r07"
    let r8f := Wire.mk "fp_stk_l4_r8f"
    [Gate.mkOR bsr_l4[0]! bsr_l4[1]! p01,
     Gate.mkOR bsr_l4[2]! bsr_l4[3]! p23,
     Gate.mkOR bsr_l4[4]! bsr_l4[5]! p45,
     Gate.mkOR bsr_l4[6]! bsr_l4[7]! p67,
     Gate.mkOR bsr_l4[8]! bsr_l4[9]! p89,
     Gate.mkOR bsr_l4[10]! bsr_l4[11]! pab,
     Gate.mkOR bsr_l4[12]! bsr_l4[13]! pcd,
     Gate.mkOR bsr_l4[14]! bsr_l4[15]! pef,
     Gate.mkOR p01 p23 q03, Gate.mkOR p45 p67 q47,
     Gate.mkOR p89 pab q8b, Gate.mkOR pcd pef qcf,
     Gate.mkOR q03 q47 r07, Gate.mkOR q8b qcf r8f,
     Gate.mkOR r07 r8f sticky_l4_final,
     Gate.mkAND sticky_l4_final abs_diff[4]! sticky_l4]

  -- Clamp sticky: if abs_diff >= 32 (clamp=1) and small_mant != 0, everything shifted out
  let small_mant_any := Wire.mk "fp_sm_any"
  let sm_or_gates :=
    let l1 := (List.range 12).map fun i =>
      let w := Wire.mk s!"fp_sm_or_l1_{i}"
      Gate.mkOR small_mant[2*i]! small_mant[2*i+1]! w
    let l1w := (List.range 12).map fun i => Wire.mk s!"fp_sm_or_l1_{i}"
    let l2 := (List.range 6).map fun i =>
      let w := Wire.mk s!"fp_sm_or_l2_{i}"
      Gate.mkOR l1w[2*i]! l1w[2*i+1]! w
    let l2w := (List.range 6).map fun i => Wire.mk s!"fp_sm_or_l2_{i}"
    let l3 := (List.range 3).map fun i =>
      let w := Wire.mk s!"fp_sm_or_l3_{i}"
      Gate.mkOR l2w[2*i]! l2w[2*i+1]! w
    let l3w := (List.range 3).map fun i => Wire.mk s!"fp_sm_or_l3_{i}"
    let l4a := Wire.mk "fp_sm_or_l4a"
    l1 ++ l2 ++ l3 ++ [
      Gate.mkOR l3w[0]! l3w[1]! l4a,
      Gate.mkOR l4a l3w[2]! small_mant_any
    ]

  let clamp_sticky := Wire.mk "fp_clamp_sticky"
  let clamp_sticky_gate := Gate.mkAND clamp_or567 small_mant_any clamp_sticky

  -- Combine all sticky sources
  let sticky_combined := Wire.mk "fp_sticky_combined"
  let sticky_c01 := Wire.mk "fp_sticky_c01"
  let sticky_c23 := Wire.mk "fp_sticky_c23"
  let sticky_c45 := Wire.mk "fp_sticky_c45"
  let sticky_c03 := Wire.mk "fp_sticky_c03"
  let sticky_combine_gates := [
    Gate.mkOR sticky_l0 sticky_l1 sticky_c01,
    Gate.mkOR sticky_l2 sticky_l3 sticky_c23,
    Gate.mkOR sticky_l4 clamp_sticky sticky_c45,
    Gate.mkOR sticky_c01 sticky_c23 sticky_c03,
    Gate.mkOR sticky_c03 sticky_c45 sticky_combined
  ]

  -- inf_sub_inf detection: both inf AND effective subtract
  let inf_sub_inf := Wire.mk "fp_inf_sub_inf"
  let eff_sub := Wire.mk "fp_eff_sub"
  let eff_sub_gate := Gate.mkXOR big_sign small_sign eff_sub
  let inf_sub_inf_gate := Gate.mkAND s1_both_inf eff_sub inf_sub_inf

  -- Inf result sign: if one input is inf, use its sign
  -- inf_result_sign = a_is_inf ? sign_a : eff_sign_b (b must be inf if a isn't)
  let inf_result_sign := Wire.mk "fp_inf_result_sign"
  let inf_result_sign_gate := Gate.mkMUX s1_eff_sign_b_raw s1_sign_a_raw s1_a_is_inf inf_result_sign

  let s2_comb_gates :=
    [big_sign_gate] ++ big_exp_gates ++ big_mant_gates ++ small_mant_gates ++ [small_sign_gate] ++
    inv_diff_gates ++ neg_diff_add_gates ++ abs_diff_gates ++ clamp_gates ++
    barrel_gates ++ [not_clamp_gate] ++ clamp_and_gates ++
    [sticky_l0_gate] ++ sticky_l1_gates ++ sticky_l2_gates ++ sticky_l3_gates ++ sticky_l4_gates ++
    sm_or_gates ++ [clamp_sticky_gate] ++ sticky_combine_gates ++
    [eff_sub_gate, inf_sub_inf_gate, inf_result_sign_gate]

  ---------------------------------------------------------------
  -- Stage 2 registers
  ---------------------------------------------------------------
  let s2_big_sign  := Wire.mk "s2_big_sign"
  let s2_big_exp   := makeIndexedWires "s2_big_exp" 8
  let s2_big_mant  := makeIndexedWires "s2_big_mant" 24
  let s2_aligned   := makeIndexedWires "s2_aligned" 24
  let s2_eff_sub   := Wire.mk "s2_eff_sub"
  let s2_rm        := makeIndexedWires "s2_rm" 3
  let s2_tag       := makeIndexedWires "s2_tag" 6
  let s2_valid     := Wire.mk "s2_valid"
  let s2_sticky    := Wire.mk "s2_sticky"
  let s2_any_nan   := Wire.mk "s2_any_nan"
  let s2_any_special := Wire.mk "s2_any_special"
  let s2_inf_sub_inf := Wire.mk "s2_inf_sub_inf"
  let s2_inf_result_sign := Wire.mk "s2_inf_result_sign"
  let s2_a_is_inf  := Wire.mk "s2_a_is_inf"
  let s2_b_is_inf  := Wire.mk "s2_b_is_inf"

  let stage2_dff :=
    [Gate.mkDFF big_sign clock reset s2_big_sign,
     Gate.mkDFF eff_sub clock reset s2_eff_sub,
     Gate.mkDFF s1_valid clock reset s2_valid,
     Gate.mkDFF sticky_combined clock reset s2_sticky,
     Gate.mkDFF s1_any_nan clock reset s2_any_nan,
     Gate.mkDFF s1_any_special clock reset s2_any_special,
     Gate.mkDFF inf_sub_inf clock reset s2_inf_sub_inf,
     Gate.mkDFF inf_result_sign clock reset s2_inf_result_sign,
     Gate.mkDFF s1_a_is_inf clock reset s2_a_is_inf,
     Gate.mkDFF s1_b_is_inf clock reset s2_b_is_inf] ++
    mkDFFBank big_exp s2_big_exp clock reset ++
    mkDFFBank big_mant s2_big_mant clock reset ++
    mkDFFBank aligned s2_aligned clock reset ++
    mkDFFBank s1_rm s2_rm clock reset ++
    mkDFFBank s1_tag s2_tag clock reset

  ---------------------------------------------------------------
  -- Stage 3 combinational: Mantissa Add + Leading-Zero Detect
  ---------------------------------------------------------------

  -- Extend to 25 bits for overflow
  let big_ext := makeIndexedWires "fp_big_ext" 25
  let big_ext_gates := (List.range 24).map (fun i =>
    Gate.mkBUF s2_big_mant[i]! big_ext[i]!) ++
    [Gate.mkBUF zero big_ext[24]!]

  let aligned_ext := makeIndexedWires "fp_aligned_ext" 25
  let aligned_ext_gates := (List.range 24).map (fun i =>
    Gate.mkBUF s2_aligned[i]! aligned_ext[i]!) ++
    [Gate.mkBUF zero aligned_ext[24]!]

  -- Conditional invert for subtraction
  let cond_inv_aligned := makeIndexedWires "fp_cond_inv_al" 25
  let cond_inv_gates := (List.range 25).map fun i =>
    Gate.mkXOR aligned_ext[i]! s2_eff_sub cond_inv_aligned[i]!

  -- 25-bit mantissa add using KSA
  let sum := makeIndexedWires "fp_sum" 25
  let (sum_add_gates, _sum_carry) :=
    mkKoggeStoneAdd big_ext cond_inv_aligned s2_eff_sub sum "fp_mantadd"

  -- Leading-zero count on 25-bit sum using parallel-prefix tree (O(log n) depth)
  -- Each element is (valid, position[4:0]) where valid=1 means a leading 1 was found.
  -- Leaf: valid_i = sum[i], pos_i = encode(i)
  -- Merge(L, R): valid = L.valid OR R.valid
  --   pos = L.valid ? L.pos : R.pos  (leftmost / highest bit wins)

  -- Step 1: Create leaf nodes for bits 24 down to 0
  let lz_v := makeIndexedWires "fp_lz_v" 25    -- valid bit per leaf
  let lz_p := (List.range 25).map fun i => makeIndexedWires ("fp_lz_p_" ++ toString i) 5
  let lz_leaf_gates := (List.range 25).flatMap fun i =>
    [Gate.mkBUF sum[i]! lz_v[i]!] ++
    (List.range 5).map fun k =>
      let bit_val := if (i >>> k) &&& 1 == 1 then one else zero
      Gate.mkBUF bit_val (lz_p[i]!)[k]!

  -- Step 2: Parallel prefix merge (recursive doubling)
  -- We need ceil(log2(25)) = 5 levels, strides 1, 2, 4, 8, 16
  let strides := [1, 2, 4, 8, 16]

  let (lz_prefix_gates, lz_final_v, lz_final_p) :=
    strides.foldl (fun (acc : List Gate × List Wire × List (List Wire)) stride =>
      let (gates_acc, v_prev, p_prev) := acc
      let lt := "fp_lz_s" ++ toString stride
      let v_new := makeIndexedWires (lt ++ "_v") 25
      let p_new := (List.range 25).map fun i => makeIndexedWires (lt ++ "_p_" ++ toString i) 5

      let level_gates := (List.range 25).flatMap fun i =>
        if i + stride < 25 then
          -- Merge: element i merges with element i+stride (higher bit)
          -- new_valid = v_prev[i+stride] OR v_prev[i]
          -- new_pos = v_prev[i+stride] ? p_prev[i+stride] : p_prev[i]
          let merge_v := Wire.mk (lt ++ "_mv_" ++ toString i)
          [Gate.mkOR v_prev[i + stride]! v_prev[i]! merge_v,
           Gate.mkBUF merge_v v_new[i]!] ++
          (List.range 5).map fun k =>
            Gate.mkMUX (p_prev[i]!)[k]! (p_prev[i + stride]!)[k]! v_prev[i + stride]! (p_new[i]!)[k]!
        else
          -- Pass through (no merge partner at higher index)
          [Gate.mkBUF v_prev[i]! v_new[i]!] ++
          (List.range 5).map fun k =>
            Gate.mkBUF (p_prev[i]!)[k]! (p_new[i]!)[k]!

      (gates_acc ++ level_gates, v_new, p_new)
    ) ([], lz_v, lz_p)

  -- The result is at index 0 after all merges (covers the full range)
  let lead_pos := lz_final_p[0]!  -- 5-bit position of leading 1

  let lz_all_gates := lz_leaf_gates ++ lz_prefix_gates

  -- lz_found[25] equivalent: was any bit set?
  let lz_any_found := lz_final_v[0]!

  let overflow := Wire.mk "fp_overflow"
  let overflow_gate := Gate.mkBUF sum[24]! overflow

  let s3_comb_gates :=
    big_ext_gates ++ aligned_ext_gates ++ cond_inv_gates ++ sum_add_gates ++
    lz_all_gates ++ [overflow_gate]

  ---------------------------------------------------------------
  -- Stage 3 registers
  ---------------------------------------------------------------
  let s3_big_sign  := Wire.mk "s3_big_sign"
  let s3_big_exp   := makeIndexedWires "s3_big_exp" 8
  let s3_sum       := makeIndexedWires "s3_sum" 25
  let s3_lead_pos  := makeIndexedWires "s3_lead_pos" 5
  let s3_overflow  := Wire.mk "s3_overflow"
  let s3_found     := Wire.mk "s3_found"
  let s3_rm        := makeIndexedWires "s3_rm" 3
  let s3_tag       := makeIndexedWires "s3_tag" 6
  let s3_valid     := Wire.mk "s3_valid"
  let s3_sticky    := Wire.mk "s3_sticky"
  let s3_any_nan   := Wire.mk "s3_any_nan"
  let s3_any_special := Wire.mk "s3_any_special"
  let s3_inf_sub_inf := Wire.mk "s3_inf_sub_inf"
  let s3_inf_result_sign := Wire.mk "s3_inf_result_sign"
  let s3_a_is_inf  := Wire.mk "s3_a_is_inf"
  let s3_b_is_inf  := Wire.mk "s3_b_is_inf"

  let stage3_dff :=
    [Gate.mkDFF s2_big_sign clock reset s3_big_sign,
     Gate.mkDFF overflow clock reset s3_overflow,
     Gate.mkDFF lz_any_found clock reset s3_found,
     Gate.mkDFF s2_valid clock reset s3_valid,
     Gate.mkDFF s2_sticky clock reset s3_sticky,
     Gate.mkDFF s2_any_nan clock reset s3_any_nan,
     Gate.mkDFF s2_any_special clock reset s3_any_special,
     Gate.mkDFF s2_inf_sub_inf clock reset s3_inf_sub_inf,
     Gate.mkDFF s2_inf_result_sign clock reset s3_inf_result_sign,
     Gate.mkDFF s2_a_is_inf clock reset s3_a_is_inf,
     Gate.mkDFF s2_b_is_inf clock reset s3_b_is_inf] ++
    mkDFFBank s2_big_exp s3_big_exp clock reset ++
    mkDFFBank sum s3_sum clock reset ++
    mkDFFBank lead_pos s3_lead_pos clock reset ++
    mkDFFBank s2_rm s3_rm clock reset ++
    mkDFFBank s2_tag s3_tag clock reset

  ---------------------------------------------------------------
  -- Stage 4 combinational: Normalize + Pack
  ---------------------------------------------------------------

  -- Overflow case: right-shifted mantissa = sum[23:1]
  let ovf_mant := makeIndexedWires "fp_ovf_mant" 23
  let ovf_mant_gates := (List.range 23).map fun i =>
    Gate.mkBUF s3_sum[i + 1]! ovf_mant[i]!

  -- Overflow exponent: big_exp + 1
  let ovf_exp := makeIndexedWires "fp_ovf_exp" 8
  let ovf_exp_one := makeIndexedWires "fp_ovf_exp_one" 8
  let ovf_exp_one_gates := [Gate.mkBUF one ovf_exp_one[0]!] ++
    (List.range 7).map (fun i => Gate.mkBUF zero ovf_exp_one[i+1]!)
  let (ovf_exp_add_gates, _ovf_exp_carry) :=
    mkKoggeStoneAdd s3_big_exp ovf_exp_one zero ovf_exp "fp_ovfexp"

  -- Non-overflow: left-shift to normalize
  -- shift_amount = 23 - lead_pos
  let const_23 := makeIndexedWires "fp_const23" 5
  -- 23 = 10111
  let const_23_gates := [
    Gate.mkBUF one const_23[0]!,
    Gate.mkBUF one const_23[1]!,
    Gate.mkBUF one const_23[2]!,
    Gate.mkBUF zero const_23[3]!,
    Gate.mkBUF one const_23[4]!
  ]

  let lshift_amt := makeIndexedWires "fp_lshift_amt" 5
  let (lshift_sub_gates, _lshift_borrow) :=
    mkKoggeStoneSub const_23 s3_lead_pos lshift_amt "fp_lshamt" one

  -- Left-shift sum[23:0] by lshift_amt
  let sum_lower := makeIndexedWires "fp_sum_lower" 24
  let sum_lower_gates := (List.range 24).map fun i =>
    Gate.mkBUF s3_sum[i]! sum_lower[i]!

  let norm_mant_full := makeIndexedWires "fp_norm_mant_full" 24
  let lshift_gates := mkBarrelShiftLeft sum_lower lshift_amt norm_mant_full zero "fp_bsl"

  -- Normalized mantissa (23 bits, drop implicit bit 23)
  let norm_mant := makeIndexedWires "fp_norm_mant" 23
  let norm_mant_gates := (List.range 23).map fun i =>
    Gate.mkBUF norm_mant_full[i]! norm_mant[i]!

  -- Normalized exponent: big_exp - lshift_amt
  let lshift_ext := makeIndexedWires "fp_lshift_ext" 8
  let lshift_ext_gates := (List.range 5).map (fun i =>
    Gate.mkBUF lshift_amt[i]! lshift_ext[i]!) ++
    (List.range 3).map (fun i => Gate.mkBUF zero lshift_ext[i + 5]!)

  let norm_exp := makeIndexedWires "fp_norm_exp" 8
  let (norm_exp_sub_gates, _norm_exp_borrow) :=
    mkKoggeStoneSub s3_big_exp lshift_ext norm_exp "fp_normexp" one

  -- Select between overflow and normal paths
  let result_mant := makeIndexedWires "fp_res_mant" 23
  let result_mant_gates := (List.range 23).map fun i =>
    Gate.mkMUX norm_mant[i]! ovf_mant[i]! s3_overflow result_mant[i]!

  let result_exp := makeIndexedWires "fp_res_exp" 8
  let result_exp_gates := (List.range 8).map fun i =>
    Gate.mkMUX norm_exp[i]! ovf_exp[i]! s3_overflow result_exp[i]!

  -- Zero result detection
  let sum_is_zero := Wire.mk "fp_sum_is_zero"
  let not_found := Wire.mk "fp_not_found"
  let zero_det_gates := [
    Gate.mkNOT s3_found not_found,
    Gate.mkBUF not_found sum_is_zero
  ]

  let not_sum_is_zero := Wire.mk "fp_not_siz"
  let not_siz_gate := Gate.mkNOT sum_is_zero not_sum_is_zero

  -- Pack result
  let result_sign := Wire.mk "fp_result_sign"
  let result_sign_gate := Gate.mkAND s3_big_sign not_sum_is_zero result_sign

  let result_exp_masked := makeIndexedWires "fp_res_exp_m" 8
  let result_exp_mask_gates := (List.range 8).map fun i =>
    Gate.mkAND result_exp[i]! not_sum_is_zero result_exp_masked[i]!

  let result_mant_masked := makeIndexedWires "fp_res_mant_m" 23
  let result_mant_mask_gates := (List.range 23).map fun i =>
    Gate.mkAND result_mant[i]! not_sum_is_zero result_mant_masked[i]!

  -- Normal result (non-special): pack sign + exp + mant
  let normal_result := makeIndexedWires "fp_normal_res" 32
  let normal_pack_gates :=
    (List.range 23).map (fun i => Gate.mkBUF result_mant_masked[i]! normal_result[i]!) ++
    (List.range 8).map (fun i => Gate.mkBUF result_exp_masked[i]! normal_result[23 + i]!) ++
    [Gate.mkBUF result_sign normal_result[31]!]

  -- Special value results:
  -- Canonical NaN: 0x7FC00000 (sign=0, exp=0xFF, mant=0x400000 = bit 22 set)
  let canonical_nan := makeIndexedWires "fp_cnan" 32
  let nan_gates := (List.range 32).map fun i =>
    -- 0x7FC00000 = 0_11111111_10000000000000000000000
    let bit_val := match i with
      | 22 => one   -- mant bit 22 (quiet NaN bit)
      | 23 => one | 24 => one | 25 => one | 26 => one  -- exp bits
      | 27 => one | 28 => one | 29 => one | 30 => one
      | _ => zero
    Gate.mkBUF bit_val canonical_nan[i]!

  -- Infinity result: sign from inf_result_sign, exp=0xFF, mant=0
  let inf_result := makeIndexedWires "fp_inf_res" 32
  let inf_result_gates := (List.range 32).map fun i =>
    let bit_val := match i with
      | 31 => s3_inf_result_sign
      | 23 => one | 24 => one | 25 => one | 26 => one
      | 27 => one | 28 => one | 29 => one | 30 => one
      | _ => zero
    Gate.mkBUF bit_val inf_result[i]!

  -- Either input is inf (but not inf-inf): output infinity
  let any_inf := Wire.mk "fp_any_inf"
  let any_inf_gate := Gate.mkOR s3_a_is_inf s3_b_is_inf any_inf
  let not_inf_sub_inf := Wire.mk "fp_not_inf_sub_inf"
  let not_inf_sub_inf_gate := Gate.mkNOT s3_inf_sub_inf not_inf_sub_inf
  let inf_not_nv := Wire.mk "fp_inf_not_nv"
  let inf_not_nv_gate := Gate.mkAND any_inf not_inf_sub_inf inf_not_nv

  -- is_nan_or_inf_nv = any_nan OR inf_sub_inf → output canonical NaN
  let is_nan_result := Wire.mk "fp_is_nan_result"
  let is_nan_result_gate := Gate.mkOR s3_any_nan s3_inf_sub_inf is_nan_result

  -- MUX chain: if is_nan_result → canonical_nan; elif inf_not_nv → inf_result; else → normal_result
  let pre_result := makeIndexedWires "fp_pre_res" 32
  let mux1_gates := (List.range 32).map fun i =>
    Gate.mkMUX normal_result[i]! inf_result[i]! inf_not_nv pre_result[i]!
  let final_mux_gates := (List.range 32).map fun i =>
    Gate.mkMUX pre_result[i]! canonical_nan[i]! is_nan_result result[i]!

  -- Exception flag computation:
  -- NV (bit 4) = any_nan OR inf_sub_inf (but for NaN inputs, IEEE says NV for signaling NaN;
  --   we set NV for all NaN inputs and inf-inf for now)
  let exc_nv := Wire.mk "fp_exc_nv"
  let exc_nv_gate := Gate.mkBUF is_nan_result exc_nv

  -- NX (bit 0) = (sticky OR ovf_loses_bit) AND NOT any_special
  let ovf_loses_bit := Wire.mk "fp_ovf_loses_bit"
  let ovf_loses_gate := Gate.mkAND s3_overflow s3_sum[0]! ovf_loses_bit
  let nx_raw := Wire.mk "fp_nx_raw"
  let nx_raw_gate := Gate.mkOR s3_sticky ovf_loses_bit nx_raw
  let not_any_special := Wire.mk "fp_not_any_special"
  let not_any_special_gate := Gate.mkNOT s3_any_special not_any_special
  let exc_nx := Wire.mk "fp_exc_nx"
  let exc_nx_gate := Gate.mkAND nx_raw not_any_special exc_nx

  let exc_output_gates := [
    Gate.mkBUF exc_nx exc[0]!,     -- NX (inexact)
    Gate.mkBUF zero exc[1]!,       -- UF (underflow) - TODO
    Gate.mkBUF zero exc[2]!,       -- OF (overflow) - TODO
    Gate.mkBUF zero exc[3]!,       -- DZ (divide by zero) - N/A for add
    Gate.mkBUF exc_nv exc[4]!      -- NV (invalid)
  ]

  let s4_comb_gates :=
    ovf_mant_gates ++ ovf_exp_one_gates ++ ovf_exp_add_gates ++
    const_23_gates ++ lshift_sub_gates ++ sum_lower_gates ++ lshift_gates ++
    norm_mant_gates ++ lshift_ext_gates ++ norm_exp_sub_gates ++
    result_mant_gates ++ result_exp_gates ++
    zero_det_gates ++ [not_siz_gate, result_sign_gate] ++
    result_exp_mask_gates ++ result_mant_mask_gates ++ normal_pack_gates ++
    nan_gates ++ inf_result_gates ++
    [any_inf_gate, not_inf_sub_inf_gate, inf_not_nv_gate, is_nan_result_gate] ++
    mux1_gates ++ final_mux_gates ++
    [exc_nv_gate, ovf_loses_gate, nx_raw_gate, not_any_special_gate, exc_nx_gate] ++
    exc_output_gates

  -- Stage 4 output: tag, valid
  let output_gates :=
    s4_comb_gates ++
    mkBUFBank s3_tag tag_out ++
    [Gate.mkBUF s3_valid valid_out]

  { name := "FPAdder"
    inputs := src1 ++ src2 ++ [op_sub] ++ rm ++ dest_tag ++ [valid_in, clock, reset, zero]
    outputs := result ++ tag_out ++ exc ++ [valid_out]
    gates := [one_gate] ++ s1_comb_gates ++ stage1_dff ++ s2_comb_gates ++ stage2_dff ++
             s3_comb_gates ++ stage3_dff ++ output_gates
    instances := []
    signalGroups := [
      { name := "src1",     width := 32, wires := src1 },
      { name := "src2",     width := 32, wires := src2 },
      { name := "rm",       width := 3,  wires := rm },
      { name := "dest_tag", width := 6,  wires := dest_tag },
      { name := "result",   width := 32, wires := result },
      { name := "tag_out",  width := 6,  wires := tag_out },
      { name := "exc",      width := 5,  wires := exc }
    ]
  }

end Shoumei.Circuits.Sequential
