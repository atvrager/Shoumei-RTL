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

  let stage1_dff :=
    [Gate.mkDFF sign_a clock reset s1_sign_a,
     Gate.mkDFF eff_sign_b clock reset s1_eff_sign_b,
     Gate.mkDFF swap clock reset s1_swap,
     Gate.mkDFF valid_in clock reset s1_valid] ++
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

  -- Effective subtract
  let eff_sub := Wire.mk "fp_eff_sub"
  let eff_sub_gate := Gate.mkXOR big_sign small_sign eff_sub

  let s2_comb_gates :=
    [big_sign_gate] ++ big_exp_gates ++ big_mant_gates ++ small_mant_gates ++ [small_sign_gate] ++
    inv_diff_gates ++ neg_diff_add_gates ++ abs_diff_gates ++ clamp_gates ++
    barrel_gates ++ [not_clamp_gate] ++ clamp_and_gates ++ [eff_sub_gate]

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

  let stage2_dff :=
    [Gate.mkDFF big_sign clock reset s2_big_sign,
     Gate.mkDFF eff_sub clock reset s2_eff_sub,
     Gate.mkDFF s1_valid clock reset s2_valid] ++
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

  -- Leading-zero priority encoder on 25-bit sum
  let lz_found := (List.range 26).map fun j => Wire.mk ("fp_lz_found_" ++ toString j)
  let lz_pos := (List.range 26).map fun j => makeIndexedWires ("fp_lz_pos_" ++ toString j) 5

  let lz_init_gates :=
    [Gate.mkBUF zero lz_found[0]!] ++
    (List.range 5).map (fun k => Gate.mkBUF zero (lz_pos[0]!)[k]!)

  let lz_cascade_gates := (List.range 25).flatMap fun j =>
    let bit_idx := 24 - j
    let prev_found := lz_found[j]!
    let prev_pos := lz_pos[j]!
    let cur_found := lz_found[j + 1]!
    let cur_pos := lz_pos[j + 1]!
    let sum_bit := sum[bit_idx]!

    let nfp := Wire.mk ("fp_lz_nfp_" ++ toString j)
    let upd := Wire.mk ("fp_lz_upd_" ++ toString j)
    let ctrl_gates := [
      Gate.mkNOT prev_found nfp,
      Gate.mkAND nfp sum_bit upd
    ]

    let found_gate := Gate.mkOR prev_found sum_bit cur_found

    let pos_gates := (List.range 5).map fun k =>
      let const_bit := if (bit_idx >>> k) &&& 1 == 1 then one else zero
      Gate.mkMUX prev_pos[k]! const_bit upd cur_pos[k]!

    ctrl_gates ++ [found_gate] ++ pos_gates

  let lead_pos := lz_pos[25]!  -- 5-bit position of leading 1

  let overflow := Wire.mk "fp_overflow"
  let overflow_gate := Gate.mkBUF sum[24]! overflow

  let s3_comb_gates :=
    big_ext_gates ++ aligned_ext_gates ++ cond_inv_gates ++ sum_add_gates ++
    lz_init_gates ++ lz_cascade_gates ++ [overflow_gate]

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

  let stage3_dff :=
    [Gate.mkDFF s2_big_sign clock reset s3_big_sign,
     Gate.mkDFF overflow clock reset s3_overflow,
     Gate.mkDFF lz_found[25]! clock reset s3_found,
     Gate.mkDFF s2_valid clock reset s3_valid] ++
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

  -- Drive output wires
  let pack_gates :=
    (List.range 23).map (fun i => Gate.mkBUF result_mant_masked[i]! result[i]!) ++
    (List.range 8).map (fun i => Gate.mkBUF result_exp_masked[i]! result[23 + i]!) ++
    [Gate.mkBUF result_sign result[31]!]

  let s4_comb_gates :=
    ovf_mant_gates ++ ovf_exp_one_gates ++ ovf_exp_add_gates ++
    const_23_gates ++ lshift_sub_gates ++ sum_lower_gates ++ lshift_gates ++
    norm_mant_gates ++ lshift_ext_gates ++ norm_exp_sub_gates ++
    result_mant_gates ++ result_exp_gates ++
    zero_det_gates ++ [not_siz_gate, result_sign_gate] ++
    result_exp_mask_gates ++ result_mant_mask_gates ++ pack_gates

  -- Stage 4 output: tag, valid, exc passthrough
  let output_gates :=
    s4_comb_gates ++
    mkBUFBank s3_tag tag_out ++
    [Gate.mkBUF s3_valid valid_out] ++
    (exc.map fun e => Gate.mkBUF zero e)

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
