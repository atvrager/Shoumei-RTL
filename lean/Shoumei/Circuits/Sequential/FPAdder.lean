/-
Circuits/Sequential/FPAdder.lean - 4-Stage Pipelined FP Adder/Subtractor

A pipelined floating-point adder/subtractor for IEEE 754 binary32.

Pipeline stages (4-cycle latency):
  Stage 1: Latch inputs into pipeline registers
  Stage 2: Pass through (alignment placeholder)
  Stage 3: Pass through (addition placeholder)
  Stage 4: IEEE 754 SP addition of s3_src1 and s3_src2

Interface:
- Inputs: src1[31:0], src2[31:0], op_sub, rm[2:0], dest_tag[5:0], valid_in,
          clock, reset, zero
- Outputs: result[31:0], tag_out[5:0], exc[4:0], valid_out
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.RippleCarryAdder

namespace Shoumei.Circuits.Sequential

open Shoumei

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

/-- n-bit ripple adder. Returns (gates, sum_wires, carry_out).
    a, b: n-bit inputs (LSB first). carry_in: single wire. -/
private def mkRippleAdd (a b : List Wire) (carry_in : Wire)
    (sum_out : List Wire) (pfx : String) : List Gate × Wire :=
  let n := a.length
  let carries := (List.range (n + 1)).map fun i => Wire.mk (pfx ++ "_c_" ++ toString i)
  let xor1s := (List.range n).map fun i => Wire.mk (pfx ++ "_xor1_" ++ toString i)
  let and1s := (List.range n).map fun i => Wire.mk (pfx ++ "_and1_" ++ toString i)
  let and2s := (List.range n).map fun i => Wire.mk (pfx ++ "_and2_" ++ toString i)
  let cin_buf_wire := carries[0]!
  let cin_gate := Gate.mkBUF carry_in cin_buf_wire
  let bit_gates := (List.range n).flatMap fun i =>
    let ai := a[i]!
    let bi := b[i]!
    let ci := carries[i]!
    let ci1 := carries[i+1]!
    let si := sum_out[i]!
    let x1 := xor1s[i]!
    let a1 := and1s[i]!
    let a2 := and2s[i]!
    [ Gate.mkXOR ai bi x1,          -- x1 = a ^ b
      Gate.mkXOR x1 ci si,          -- sum = a ^ b ^ c
      Gate.mkAND ai bi a1,          -- a1 = a & b
      Gate.mkAND x1 ci a2,          -- a2 = (a^b) & c
      Gate.mkOR a1 a2 ci1 ]         -- cout = a&b | (a^b)&c
  ([cin_gate] ++ bit_gates, carries[n]!)

/-- n-bit subtractor: out = a - b, returns (gates, borrow_out).
    Implemented as a + ~b + 1. -/
private def mkRippleSub (a b : List Wire) (sum_out : List Wire)
    (pfx : String) (one_wire : Wire) : List Gate × Wire :=
  let n := b.length
  let inv_b := (List.range n).map fun i => Wire.mk (pfx ++ "_invb_" ++ toString i)
  let inv_gates := (List.range n).map fun i => Gate.mkNOT b[i]! inv_b[i]!
  let (add_gates, carry_out) := mkRippleAdd a inv_b one_wire sum_out (pfx ++ "_add")
  -- For subtraction a - b = a + ~b + 1
  -- carry_out = 1 means no borrow (a >= b), carry_out = 0 means borrow (a < b)
  -- We want borrow = NOT carry_out
  let borrow_wire := Wire.mk (pfx ++ "_borrow")
  let borrow_gate := Gate.mkNOT carry_out borrow_wire
  (inv_gates ++ add_gates ++ [borrow_gate], borrow_wire)

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

  -- Stage 1 registers (input → s1)
  let s1_src1    := makeIndexedWires "s1_src1" 32
  let s1_src2    := makeIndexedWires "s1_src2" 32
  let s1_sub     := Wire.mk "s1_sub"
  let s1_rm      := makeIndexedWires "s1_rm" 3
  let s1_tag     := makeIndexedWires "s1_tag" 6
  let s1_valid   := Wire.mk "s1_valid"

  -- Stage 2 registers (s1 → s2)
  let s2_src1    := makeIndexedWires "s2_src1" 32
  let s2_src2    := makeIndexedWires "s2_src2" 32
  let s2_sub     := Wire.mk "s2_sub"
  let s2_rm      := makeIndexedWires "s2_rm" 3
  let s2_tag     := makeIndexedWires "s2_tag" 6
  let s2_valid   := Wire.mk "s2_valid"

  -- Stage 3 registers (s2 → s3)
  let s3_src1    := makeIndexedWires "s3_src1" 32
  let s3_src2    := makeIndexedWires "s3_src2" 32
  let s3_sub     := Wire.mk "s3_sub"
  let s3_rm      := makeIndexedWires "s3_rm" 3
  let s3_tag     := makeIndexedWires "s3_tag" 6
  let s3_valid   := Wire.mk "s3_valid"

  -- Stage 1 DFFs: latch inputs
  let stage1_gates :=
    mkDFFBank src1 s1_src1 clock reset ++
    mkDFFBank src2 s1_src2 clock reset ++
    [Gate.mkDFF op_sub clock reset s1_sub] ++
    mkDFFBank rm s1_rm clock reset ++
    mkDFFBank dest_tag s1_tag clock reset ++
    [Gate.mkDFF valid_in clock reset s1_valid]

  -- Stage 2 DFFs: pass through
  let stage2_gates :=
    mkDFFBank s1_src1 s2_src1 clock reset ++
    mkDFFBank s1_src2 s2_src2 clock reset ++
    [Gate.mkDFF s1_sub clock reset s2_sub] ++
    mkDFFBank s1_rm s2_rm clock reset ++
    mkDFFBank s1_tag s2_tag clock reset ++
    [Gate.mkDFF s1_valid clock reset s2_valid]

  -- Stage 3 DFFs: pass through
  let stage3_gates :=
    mkDFFBank s2_src1 s3_src1 clock reset ++
    mkDFFBank s2_src2 s3_src2 clock reset ++
    [Gate.mkDFF s2_sub clock reset s3_sub] ++
    mkDFFBank s2_rm s3_rm clock reset ++
    mkDFFBank s2_tag s3_tag clock reset ++
    [Gate.mkDFF s2_valid clock reset s3_valid]

  ---------------------------------------------------------------
  -- Stage 4: IEEE 754 SP Floating-Point Addition
  ---------------------------------------------------------------

  -- ===== Step 1: Unpack =====
  -- a = s3_src1, b = s3_src2
  let sign_a := Wire.mk "fp_sign_a"
  let sign_a_gate := Gate.mkBUF s3_src1[31]! sign_a

  let exp_a := makeIndexedWires "fp_exp_a" 8
  let exp_a_gates := (List.range 8).map fun i =>
    Gate.mkBUF s3_src1[23 + i]! exp_a[i]!

  -- exp_all_zeros_a: NOR of all exp bits
  -- Compute with OR tree then NOT
  let exp_a_or01 := Wire.mk "fp_exp_a_or01"
  let exp_a_or23 := Wire.mk "fp_exp_a_or23"
  let exp_a_or45 := Wire.mk "fp_exp_a_or45"
  let exp_a_or67 := Wire.mk "fp_exp_a_or67"
  let exp_a_or0123 := Wire.mk "fp_exp_a_or0123"
  let exp_a_or4567 := Wire.mk "fp_exp_a_or4567"
  let exp_a_or_all := Wire.mk "fp_exp_a_or_all"
  let exp_a_all_zeros := Wire.mk "fp_exp_a_all_zeros"
  let exp_a_zero_gates := [
    Gate.mkOR exp_a[0]! exp_a[1]! exp_a_or01,
    Gate.mkOR exp_a[2]! exp_a[3]! exp_a_or23,
    Gate.mkOR exp_a[4]! exp_a[5]! exp_a_or45,
    Gate.mkOR exp_a[6]! exp_a[7]! exp_a_or67,
    Gate.mkOR exp_a_or01 exp_a_or23 exp_a_or0123,
    Gate.mkOR exp_a_or45 exp_a_or67 exp_a_or4567,
    Gate.mkOR exp_a_or0123 exp_a_or4567 exp_a_or_all,
    Gate.mkNOT exp_a_or_all exp_a_all_zeros
  ]

  -- implicit bit = NOT(exp_all_zeros)
  let implicit_a := Wire.mk "fp_implicit_a"
  let implicit_a_gate := Gate.mkBUF exp_a_or_all implicit_a  -- NOT of all_zeros = or_all

  -- mant_a[23:0] = {implicit_a, src1[22:0]}
  let mant_a := makeIndexedWires "fp_mant_a" 24
  let mant_a_gates := (List.range 23).map (fun i =>
    Gate.mkBUF s3_src1[i]! mant_a[i]!) ++
    [Gate.mkBUF implicit_a mant_a[23]!]

  -- Operand B
  let sign_b_raw := Wire.mk "fp_sign_b_raw"
  let sign_b_raw_gate := Gate.mkBUF s3_src2[31]! sign_b_raw

  -- eff_sign_b = sign_b_raw XOR s3_sub
  let eff_sign_b := Wire.mk "fp_eff_sign_b"
  let eff_sign_b_gate := Gate.mkXOR sign_b_raw s3_sub eff_sign_b

  let exp_b := makeIndexedWires "fp_exp_b" 8
  let exp_b_gates := (List.range 8).map fun i =>
    Gate.mkBUF s3_src2[23 + i]! exp_b[i]!

  -- exp_b_all_zeros
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
    Gate.mkBUF s3_src2[i]! mant_b[i]!) ++
    [Gate.mkBUF implicit_b mant_b[23]!]

  -- ===== Step 2: Exponent difference (9-bit) =====
  -- diff[8:0] = {0,exp_a} - {0,exp_b}  (9-bit subtraction)
  -- Extend to 9 bits with zero MSB
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
    mkRippleSub exp_a_ext exp_b_ext exp_diff "fp_expdiff" one

  -- swap = borrow (i.e., exp_a < exp_b)
  -- In our subtractor, borrow = NOT(carry_out of a + ~b + 1)
  -- _exp_diff_borrow IS the borrow signal
  let swap := Wire.mk "fp_swap"
  let swap_gate := Gate.mkBUF _exp_diff_borrow swap

  -- ===== Step 3: Swap operands =====
  let big_sign := Wire.mk "fp_big_sign"
  let big_sign_gate := Gate.mkMUX sign_a eff_sign_b swap big_sign

  let big_exp := makeIndexedWires "fp_big_exp" 8
  let big_exp_gates := (List.range 8).map fun i =>
    Gate.mkMUX exp_a[i]! exp_b[i]! swap big_exp[i]!

  let big_mant := makeIndexedWires "fp_big_mant" 24
  let big_mant_gates := (List.range 24).map fun i =>
    Gate.mkMUX mant_a[i]! mant_b[i]! swap big_mant[i]!

  let small_mant := makeIndexedWires "fp_small_mant" 24
  let small_mant_gates := (List.range 24).map fun i =>
    Gate.mkMUX mant_b[i]! mant_a[i]! swap small_mant[i]!

  let small_sign := Wire.mk "fp_small_sign"
  let small_sign_gate := Gate.mkMUX eff_sign_b sign_a swap small_sign

  -- ===== Step 4: Absolute exponent difference =====
  -- If swap: abs_diff = ~diff + 1 (negate), else abs_diff = diff
  -- Only need lower 8 bits (clamped later)
  let neg_diff := makeIndexedWires "fp_neg_diff" 8
  let inv_diff := makeIndexedWires "fp_inv_diff" 8
  let inv_diff_gates := (List.range 8).map fun i =>
    Gate.mkNOT exp_diff[i]! inv_diff[i]!

  let zeros8 := (List.range 8).map fun _ => zero
  let (neg_diff_add_gates, _neg_carry) :=
    mkRippleAdd inv_diff zeros8 one neg_diff "fp_negdiff"
  -- neg_diff = ~diff[7:0] + 1

  let abs_diff := makeIndexedWires "fp_abs_diff" 8
  let abs_diff_gates := (List.range 8).map fun i =>
    Gate.mkMUX exp_diff[i]! neg_diff[i]! swap abs_diff[i]!

  -- Clamp: if any of abs_diff[7:5] is set, clamp to 24 (shift everything out)
  -- If abs_diff > 24, result of shift is 0 anyway, so just OR bits 5,6,7
  -- and if set, force shift amount to 11000 (=24). Actually simpler:
  -- Use abs_diff[4:0] as shift amount, but if abs_diff >= 25, the barrel shifter
  -- will shift out everything since we only have 24 bits. So abs_diff[4:0] naturally
  -- works when bits [7:5] are 0. When they're set, we need to force all output to 0.
  -- Easiest: just clamp by OR-ing bits 5,6,7 into a "clamp" signal and AND-gating output.
  let clamp_or56 := Wire.mk "fp_clamp_or56"
  let clamp_or567 := Wire.mk "fp_clamp_or567"
  let clamp_gates := [
    Gate.mkOR abs_diff[5]! abs_diff[6]! clamp_or56,
    Gate.mkOR clamp_or56 abs_diff[7]! clamp_or567
  ]

  -- ===== Step 5: Barrel shift right =====
  let shift_amt := (List.range 5).map fun i => abs_diff[i]!
  let aligned_pre := makeIndexedWires "fp_aligned_pre" 24
  let barrel_gates := mkBarrelShiftRight small_mant shift_amt aligned_pre zero "fp_bsr"

  -- Apply clamp: if clamp_or567, force all bits to zero
  let not_clamp := Wire.mk "fp_not_clamp"
  let not_clamp_gate := Gate.mkNOT clamp_or567 not_clamp
  let aligned := makeIndexedWires "fp_aligned" 24
  let clamp_and_gates := (List.range 24).map fun i =>
    Gate.mkAND aligned_pre[i]! not_clamp aligned[i]!

  -- ===== Step 6: Add or subtract mantissas =====
  let eff_sub := Wire.mk "fp_eff_sub"
  let eff_sub_gate := Gate.mkXOR big_sign small_sign eff_sub

  -- Extend to 25 bits (MSB = 0) for overflow
  let big_ext := makeIndexedWires "fp_big_ext" 25
  let big_ext_gates := (List.range 24).map (fun i =>
    Gate.mkBUF big_mant[i]! big_ext[i]!) ++
    [Gate.mkBUF zero big_ext[24]!]

  let aligned_ext := makeIndexedWires "fp_aligned_ext" 25
  let aligned_ext_gates := (List.range 24).map (fun i =>
    Gate.mkBUF aligned[i]! aligned_ext[i]!) ++
    [Gate.mkBUF zero aligned_ext[24]!]

  -- If eff_sub=0: sum = big + aligned
  -- If eff_sub=1: sum = big - aligned = big + ~aligned + 1
  -- Invert aligned conditionally: inv_aligned[i] = aligned_ext[i] XOR eff_sub
  let cond_inv_aligned := makeIndexedWires "fp_cond_inv_al" 25
  let cond_inv_gates := (List.range 25).map fun i =>
    Gate.mkXOR aligned_ext[i]! eff_sub cond_inv_aligned[i]!

  -- carry_in = eff_sub (for two's complement when subtracting)
  let sum := makeIndexedWires "fp_sum" 25
  let (sum_add_gates, _sum_carry) :=
    mkRippleAdd big_ext cond_inv_aligned eff_sub sum "fp_mantadd"

  -- ===== Step 7: Normalize =====
  -- Priority encoder: find leading 1 in sum[24:0]
  -- We build a simple cascade from MSB down.
  -- lz_count[4:0] = number of leading zeros (from bit 24 downward)
  -- Then shift_amt = lz_count - 1 (since bit 24 is overflow position,
  --   normal position is bit 23)
  --
  -- Simpler approach for normalization:
  --   Case A: sum[24]=1 → overflow, right shift by 1, exp+1
  --   Case B: sum[24]=0, sum[23]=1 → normalized, no shift, exp unchanged
  --   Case C: sum[24]=0, sum[23]=0 → need left shift
  --
  -- For case C, find leading one in sum[22:0] and shift.
  -- Leading one position p means we shift left by (23-p) and subtract (23-p) from exp.
  --
  -- For simplicity, we use a priority encoder to find the leading 1 position
  -- in the 25-bit sum, then compute shift amount.

  -- Priority encoder for 25 bits: find position of highest set bit
  -- We'll encode it as a 5-bit value (0-24).
  -- Use a cascade: start with "found" = 0, "pos" = 0
  -- For each bit from 24 down to 0:
  --   if bit set and not found: pos = i, found = 1

  -- Build with MUX cascade: found_i and pos_i wires
  -- found_24 = sum[24], pos_24 = 24 = 11000
  -- For i from 23 down to 0:
  --   found_i = found_{i+1} OR sum[i]... no wait
  --   found_i = found_{i+1} OR sum[i] is wrong, it should be:
  --   found_i = found_{i+1}, pos_i = pos_{i+1}  if found_{i+1}
  --   found_i = sum[i], pos_i = i               if NOT found_{i+1}
  -- So: found_i = found_{i+1} OR sum[i]
  --     pos_i = found_{i+1} ? pos_{i+1} : (sum[i] ? i : 0)
  -- Simplify: pos_i[k] = MUX(i_bit_k, pos_{i+1}[k], found_{i+1})
  --   where i_bit_k is bit k of constant i
  --   but only when sum[i] = 1, otherwise keep pos_{i+1}
  -- Actually: pos_i[k] = found_{i+1} ? pos_{i+1}[k] : (sum[i] ? i[k] : pos_{i+1}[k])
  --         = MUX(pos_{i+1}[k], i[k], AND(NOT(found_{i+1}), sum[i]))
  -- Let update_i = NOT(found_{i+1}) AND sum[i]
  -- pos_i[k] = MUX(pos_{i+1}[k], i_const[k], update_i)

  -- This is 25 iterations × 5 bits + control = ~200 gates. Let's build it.
  -- Start from bit 24 (MSB)

  -- found and pos wires for each stage (25 stages, indexed by bit position going from 24 to 0)
  -- We'll use arrays indexed 0..24 where index j corresponds to processing from bit 24 down to bit (24-j)
  -- Actually, let's index by bit position for clarity.

  -- Initialize: before any bit is checked, found=0, pos=00000
  -- After checking bit 24: found=sum[24], pos= sum[24]?24:0
  -- After checking bit i (going 23,22,...,0): update as above

  -- We build from bit 24 down. Let stage 0 = after checking bit 24.
  let lz_found := (List.range 26).map fun j => Wire.mk ("fp_lz_found_" ++ toString j)
  let lz_pos := (List.range 26).map fun j => makeIndexedWires ("fp_lz_pos_" ++ toString j) 5

  -- Stage 0: initial state (no bit checked yet)
  let lz_init_gates :=
    [Gate.mkBUF zero lz_found[0]!] ++
    (List.range 5).map (fun k => Gate.mkBUF zero (lz_pos[0]!)[k]!)

  -- Stages 1..25: check bits 24, 23, 22, ..., 0
  let lz_cascade_gates := (List.range 25).flatMap fun j =>
    let bit_idx := 24 - j  -- checking this bit
    let prev_found := lz_found[j]!
    let prev_pos := lz_pos[j]!
    let cur_found := lz_found[j + 1]!
    let cur_pos := lz_pos[j + 1]!
    let sum_bit := sum[bit_idx]!

    -- not_found_prev
    let nfp := Wire.mk ("fp_lz_nfp_" ++ toString j)
    -- update = NOT(prev_found) AND sum[bit_idx]
    let upd := Wire.mk ("fp_lz_upd_" ++ toString j)
    let ctrl_gates := [
      Gate.mkNOT prev_found nfp,
      Gate.mkAND nfp sum_bit upd
    ]

    -- cur_found = prev_found OR sum[bit_idx]  (actually = prev_found OR update = prev_found OR (nfp AND sum_bit))
    -- simpler: cur_found = prev_found OR sum[bit_idx]
    let found_gate := Gate.mkOR prev_found sum_bit cur_found

    -- cur_pos[k] = MUX(prev_pos[k], bit_idx_const[k], upd)
    let pos_gates := (List.range 5).map fun k =>
      let const_bit := if (bit_idx >>> k) &&& 1 == 1 then one else zero
      Gate.mkMUX prev_pos[k]! const_bit upd cur_pos[k]!

    ctrl_gates ++ [found_gate] ++ pos_gates

  -- Final leading-one position is lz_pos[25], found is lz_found[25]
  let lead_pos := lz_pos[25]!  -- 5-bit position of leading 1

  -- Now compute normalization:
  -- If sum[24]=1 (overflow): right-shift sum by 1, exp = big_exp + 1
  -- If sum[24]=0 and lead_pos = 23: no shift, exp = big_exp
  -- If sum[24]=0 and lead_pos < 23: left-shift by (23 - lead_pos), exp = big_exp - (23 - lead_pos)
  -- If found=0: result is zero

  let overflow := Wire.mk "fp_overflow"
  let overflow_gate := Gate.mkBUF sum[24]! overflow

  -- Overflow case: right-shifted mantissa = sum[24:1] (drop bit 0, bit 24 becomes implicit)
  -- We take sum[23:1] as the 23-bit fraction
  let ovf_mant := makeIndexedWires "fp_ovf_mant" 23
  let ovf_mant_gates := (List.range 23).map fun i =>
    Gate.mkBUF sum[i + 1]! ovf_mant[i]!

  -- Overflow exponent: big_exp + 1
  let ovf_exp := makeIndexedWires "fp_ovf_exp" 8
  let ovf_exp_one := makeIndexedWires "fp_ovf_exp_one" 8
  let ovf_exp_one_gates := [Gate.mkBUF one ovf_exp_one[0]!] ++
    (List.range 7).map (fun i => Gate.mkBUF zero ovf_exp_one[i+1]!)
  let (ovf_exp_add_gates, _ovf_exp_carry) :=
    mkRippleAdd big_exp ovf_exp_one zero ovf_exp "fp_ovfexp"

  -- Non-overflow case: need to left-shift sum[23:0] to normalize
  -- shift_amount = 23 - lead_pos (if lead_pos <= 23)
  -- We compute 23 - lead_pos using subtractor
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
    mkRippleSub const_23 lead_pos lshift_amt "fp_lshamt" one

  -- Left-shift sum[23:0] by lshift_amt (we work on 24 bits, ignoring sum[24] in this path)
  let sum_lower := makeIndexedWires "fp_sum_lower" 24
  let sum_lower_gates := (List.range 24).map fun i =>
    Gate.mkBUF sum[i]! sum_lower[i]!

  let norm_mant_full := makeIndexedWires "fp_norm_mant_full" 24
  let lshift_gates := mkBarrelShiftLeft sum_lower lshift_amt norm_mant_full zero "fp_bsl"

  -- Normalized mantissa (23 bits, drop implicit bit 23)
  let norm_mant := makeIndexedWires "fp_norm_mant" 23
  let norm_mant_gates := (List.range 23).map fun i =>
    Gate.mkBUF norm_mant_full[i]! norm_mant[i]!

  -- Normalized exponent: big_exp - lshift_amt
  -- Extend lshift_amt to 8 bits
  let lshift_ext := makeIndexedWires "fp_lshift_ext" 8
  let lshift_ext_gates := (List.range 5).map (fun i =>
    Gate.mkBUF lshift_amt[i]! lshift_ext[i]!) ++
    (List.range 3).map (fun i => Gate.mkBUF zero lshift_ext[i + 5]!)

  let norm_exp := makeIndexedWires "fp_norm_exp" 8
  let (norm_exp_sub_gates, _norm_exp_borrow) :=
    mkRippleSub big_exp lshift_ext norm_exp "fp_normexp" one

  -- ===== Step 8: Select between overflow and normal paths =====
  -- If overflow: use ovf_mant, ovf_exp
  -- Else: use norm_mant, norm_exp

  let result_mant := makeIndexedWires "fp_res_mant" 23
  let result_mant_gates := (List.range 23).map fun i =>
    Gate.mkMUX norm_mant[i]! ovf_mant[i]! overflow result_mant[i]!

  let result_exp := makeIndexedWires "fp_res_exp" 8
  let result_exp_gates := (List.range 8).map fun i =>
    Gate.mkMUX norm_exp[i]! ovf_exp[i]! overflow result_exp[i]!

  -- ===== Zero result detection =====
  -- If lz_found[25] = 0, the sum is zero → force result to +0
  let sum_is_zero := Wire.mk "fp_sum_is_zero"
  let not_found := Wire.mk "fp_not_found"
  let zero_det_gates := [
    Gate.mkNOT lz_found[25]! not_found,
    Gate.mkBUF not_found sum_is_zero
  ]

  let not_sum_is_zero := Wire.mk "fp_not_siz"
  let not_siz_gate := Gate.mkNOT sum_is_zero not_sum_is_zero

  -- ===== Pack result =====
  -- result[31] = big_sign (AND NOT sum_is_zero)
  let result_sign := Wire.mk "fp_result_sign"
  let result_sign_gate := Gate.mkAND big_sign not_sum_is_zero result_sign

  -- result[30:23] = result_exp (AND NOT sum_is_zero for each bit)
  let result_exp_masked := makeIndexedWires "fp_res_exp_m" 8
  let result_exp_mask_gates := (List.range 8).map fun i =>
    Gate.mkAND result_exp[i]! not_sum_is_zero result_exp_masked[i]!

  -- result[22:0] = result_mant (AND NOT sum_is_zero)
  let result_mant_masked := makeIndexedWires "fp_res_mant_m" 23
  let result_mant_mask_gates := (List.range 23).map fun i =>
    Gate.mkAND result_mant[i]! not_sum_is_zero result_mant_masked[i]!

  -- Drive output wires
  let pack_gates :=
    (List.range 23).map (fun i => Gate.mkBUF result_mant_masked[i]! result[i]!) ++
    (List.range 8).map (fun i => Gate.mkBUF result_exp_masked[i]! result[23 + i]!) ++
    [Gate.mkBUF result_sign result[31]!]

  -- Collect all FP addition gates
  let fp_gates :=
    [sign_a_gate] ++ exp_a_gates ++ exp_a_zero_gates ++ [implicit_a_gate] ++ mant_a_gates ++
    [sign_b_raw_gate, eff_sign_b_gate] ++ exp_b_gates ++ exp_b_zero_gates ++
    [implicit_b_gate] ++ mant_b_gates ++
    exp_a_ext_gates ++ exp_b_ext_gates ++ exp_diff_gates ++ [swap_gate] ++
    [big_sign_gate] ++ big_exp_gates ++ big_mant_gates ++ small_mant_gates ++ [small_sign_gate] ++
    inv_diff_gates ++ neg_diff_add_gates ++ abs_diff_gates ++ clamp_gates ++
    barrel_gates ++ [not_clamp_gate] ++ clamp_and_gates ++
    [eff_sub_gate] ++ big_ext_gates ++ aligned_ext_gates ++ cond_inv_gates ++ sum_add_gates ++
    lz_init_gates ++ lz_cascade_gates ++ [overflow_gate] ++
    ovf_mant_gates ++ ovf_exp_one_gates ++ ovf_exp_add_gates ++
    const_23_gates ++ lshift_sub_gates ++ sum_lower_gates ++ lshift_gates ++
    norm_mant_gates ++ lshift_ext_gates ++ norm_exp_sub_gates ++
    result_mant_gates ++ result_exp_gates ++
    zero_det_gates ++ [not_siz_gate, result_sign_gate] ++
    result_exp_mask_gates ++ result_mant_mask_gates ++ pack_gates

  -- Stage 4 output gates (tag, valid, exc passthrough + FP result)
  let output_gates :=
    fp_gates ++
    mkBUFBank s3_tag tag_out ++
    [Gate.mkBUF s3_valid valid_out] ++
    (exc.map fun e => Gate.mkBUF zero e)

  { name := "FPAdder"
    inputs := src1 ++ src2 ++ [op_sub] ++ rm ++ dest_tag ++ [valid_in, clock, reset, zero]
    outputs := result ++ tag_out ++ exc ++ [valid_out]
    gates := [one_gate] ++ stage1_gates ++ stage2_gates ++ stage3_gates ++ output_gates
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
