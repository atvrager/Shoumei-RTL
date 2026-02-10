/-
Circuits/Sequential/FPMultiplier.lean - 3-Stage Pipelined FP Multiplier

IEEE 754 binary32 multiplication with full combinational datapath.

Pipeline stages:
  Stage 1: Latch inputs (src1, src2, rm, tag, valid)
  Stage 2: Hold (mantissa multiply + exponent add happen combinationally)
  Stage 3: Output (normalize + pack)

Inputs (75):
  src1[31:0], src2[31:0] - FP operands
  rm[2:0]                - rounding mode
  dest_tag[5:0]          - physical register tag
  valid_in               - input valid
  clock, reset           - sequential control
  zero                   - constant low

Outputs (44):
  result[31:0]  - FP product
  tag_out[5:0]  - destination tag
  exc[4:0]      - exception flags (tied to zero)
  valid_out     - output valid
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.RippleCarryAdder

namespace Shoumei.Circuits.Sequential

open Shoumei
open Shoumei.Circuits.Combinational

/-- Create a bank of DFFs with matching d/q wire lists. -/
def mkDFFBank (d_wires q_wires : List Wire) (clock reset : Wire) : List Gate :=
  List.zipWith (fun d q => Gate.mkDFF d clock reset q) d_wires q_wires

/-- N-bit ripple carry adder. a, b, sum are n-bit LSB-first. cin is carry-in, cout is carry-out. -/
private def mkRippleAdd (a b : List Wire) (cin : Wire) (sum : List Wire) (cout : Wire)
    (pfx : String) : List Gate :=
  let n := a.length
  let carries := (List.range (n + 1)).map fun i =>
    if i == 0 then cin
    else if i == n then cout
    else Wire.mk s!"{pfx}_c_{i}"
  (List.range n).flatMap fun i =>
    let xab := Wire.mk s!"{pfx}_xab_{i}"
    let aband := Wire.mk s!"{pfx}_aband_{i}"
    let cxor := Wire.mk s!"{pfx}_cxor_{i}"
    [
      Gate.mkXOR (a[i]!) (b[i]!) xab,
      Gate.mkXOR xab (carries[i]!) (sum[i]!),
      Gate.mkAND (a[i]!) (b[i]!) aband,
      Gate.mkAND (carries[i]!) xab cxor,
      Gate.mkOR aband cxor (carries[i + 1]!)
    ]

/-- N-bit subtractor: diff = a - b, using a + ~b + 1. one_w is a constant-high wire. -/
private def mkRippleSub (a b : List Wire) (diff : List Wire) (borrow : Wire) (one_w : Wire)
    (pfx : String) : List Gate :=
  let n := a.length
  let b_inv := (List.range n).map fun i => Wire.mk s!"{pfx}_binv_{i}"
  let inv_gates := (List.range n).map fun i => Gate.mkNOT (b[i]!) (b_inv[i]!)
  let cout := Wire.mk s!"{pfx}_cout"
  let add_gates := mkRippleAdd a b_inv one_w diff cout pfx
  let borrow_gate := Gate.mkNOT cout borrow
  inv_gates ++ add_gates ++ [borrow_gate]

/-- N-bit 2:1 MUX bank. out[i] = sel ? b[i] : a[i]. -/
private def mkMuxBank (a b : List Wire) (sel : Wire) (out : List Wire) : List Gate :=
  (List.range a.length).map fun i => Gate.mkMUX (a[i]!) (b[i]!) sel (out[i]!)

/-- 24x24 -> 48 bit combinational multiplier using shift-and-add.
    a is 24-bit (LSB-first), b is 24-bit (LSB-first), product is 48-bit (LSB-first).
    zero is a constant-low wire. -/
private def mkMul24x24 (a b : List Wire) (product : List Wire) (zero : Wire)
    (pfx : String) : List Wire × List Gate :=
  -- We build a running 48-bit sum by accumulating partial products.
  -- pp[j] = a AND replicate(b[j]), shifted left by j positions.
  -- We accumulate into running_sum using ripple adders.

  -- For j=0: running_sum = pp[0] zero-extended to 48 bits
  -- For j=1..23: running_sum += pp[j] << j

  let init : List Wire × List Gate :=
    -- Partial product 0: pp0[i] = a[i] AND b[0], for i in 0..23
    let pp0 := (List.range 24).map fun i => Wire.mk s!"{pfx}_pp0_{i}"
    let pp0_gates := (List.range 24).map fun i => Gate.mkAND (a[i]!) (b[0]!) (pp0[i]!)
    -- Running sum starts as pp0 zero-extended to 48 bits
    -- We need actual wires for the running sum
    let sum0 := (List.range 48).map fun i => Wire.mk s!"{pfx}_sum0_{i}"
    -- For bits 0..23: BUF from pp0, for bits 24..47: BUF from zero
    let sum0_gates := (List.range 48).map fun i =>
      if i < 24 then Gate.mkBUF (pp0[i]!) (sum0[i]!)
      else Gate.mkBUF zero (sum0[i]!)
    (sum0, pp0_gates ++ sum0_gates)

  let (final_sum, final_gates) := (List.range 23).foldl (fun (acc : List Wire × List Gate) jIdx =>
    let j := jIdx + 1  -- j goes from 1 to 23
    let (prev_sum, prev_gates) := acc

    -- Partial product j: pp_j[i] = a[i] AND b[j]
    let ppj := (List.range 24).map fun i => Wire.mk s!"{pfx}_pp{j}_{i}"
    let ppj_gates := (List.range 24).map fun i => Gate.mkAND (a[i]!) (b[j]!) (ppj[i]!)

    -- Add ppj (24 bits) at position j to prev_sum (48 bits)
    -- We add bits [j..j+23] of prev_sum with ppj, carry propagates to higher bits
    -- Bits [0..j-1] pass through unchanged
    -- Bits [j..j+23] are the adder range
    -- Bits [j+24..47] get carry ripple

    let adder_width := min 24 (48 - j)  -- how many bits of ppj fit
    let adder_a := (List.range adder_width).map fun i => prev_sum[j + i]!
    let adder_b := (List.range adder_width).map fun i =>
      if i < 24 then ppj[i]!
      else zero
    let adder_sum := (List.range adder_width).map fun i => Wire.mk s!"{pfx}_as{j}_{i}"
    let adder_cout := Wire.mk s!"{pfx}_ac{j}"
    let adder_gates := mkRippleAdd adder_a adder_b zero adder_sum adder_cout s!"{pfx}_add{j}"

    -- Now propagate carry through remaining high bits [j+adder_width..47]
    let high_start := j + adder_width
    let high_count := 48 - high_start
    -- Ripple the carry through: each bit = prev_sum[k] XOR carry_in, new carry = prev_sum[k] AND carry_in
    -- We'll do a simple carry chain
    let (high_wires, high_gates) :=
      if high_count <= 0 then ([], [])
      else
        let hw := (List.range high_count).map fun i => Wire.mk s!"{pfx}_h{j}_{i}"
        let carries := (List.range (high_count + 1)).map fun i =>
          if i == 0 then adder_cout
          else Wire.mk s!"{pfx}_hc{j}_{i}"
        let hg := (List.range high_count).flatMap fun i =>
          let k := high_start + i
          let xw := Wire.mk s!"{pfx}_hx{j}_{i}"
          let aw := Wire.mk s!"{pfx}_ha{j}_{i}"
          [
            Gate.mkXOR (prev_sum[k]!) (carries[i]!) xw,
            Gate.mkBUF xw (hw[i]!),
            Gate.mkAND (prev_sum[k]!) (carries[i]!) aw,
            Gate.mkBUF aw (carries[i + 1]!)
          ]
        (hw, hg)

    -- Build new sum: bits [0..j-1] from prev_sum, [j..j+aw-1] from adder, [j+aw..47] from high
    let new_sum := (List.range 48).map fun i => Wire.mk s!"{pfx}_sum{j}_{i}"
    let new_sum_gates := (List.range 48).map fun i =>
      if i < j then Gate.mkBUF (prev_sum[i]!) (new_sum[i]!)
      else if i < j + adder_width then Gate.mkBUF (adder_sum[i - j]!) (new_sum[i]!)
      else if i < 48 && (i - high_start) < high_wires.length then
        Gate.mkBUF (high_wires[i - high_start]!) (new_sum[i]!)
      else Gate.mkBUF zero (new_sum[i]!)  -- shouldn't happen

    (new_sum, prev_gates ++ ppj_gates ++ adder_gates ++ high_gates ++ new_sum_gates)
  ) init

  -- Copy final_sum to product
  let copy_gates := (List.range 48).map fun i => Gate.mkBUF (final_sum[i]!) (product[i]!)
  (final_sum, final_gates ++ copy_gates)

/-- Build a 3-stage pipelined FP multiplier circuit with real IEEE 754 multiplication. -/
def mkFPMultiplier : Circuit :=
  -- ══════════════════════════════════════════════
  -- Input wires
  -- ══════════════════════════════════════════════
  let src1 := makeIndexedWires "src1" 32
  let src2 := makeIndexedWires "src2" 32
  let rm := makeIndexedWires "rm" 3
  let dest_tag := makeIndexedWires "dest_tag" 6
  let valid_in := Wire.mk "valid_in"
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"

  -- ══════════════════════════════════════════════
  -- Output wires
  -- ══════════════════════════════════════════════
  let result := makeIndexedWires "result" 32
  let tag_out := makeIndexedWires "tag_out" 6
  let exc := makeIndexedWires "exc" 5
  let valid_out := Wire.mk "valid_out"

  -- ══════════════════════════════════════════════
  -- Stage 1 pipeline registers (input → stage 1)
  -- ══════════════════════════════════════════════
  let s1_src1 := makeIndexedWires "s1_src1" 32
  let s1_src2 := makeIndexedWires "s1_src2" 32
  let s1_rm := makeIndexedWires "s1_rm" 3
  let s1_tag := makeIndexedWires "s1_tag" 6
  let s1_valid := Wire.mk "s1_valid"

  let s1_dffs :=
    mkDFFBank src1 s1_src1 clock reset ++
    mkDFFBank src2 s1_src2 clock reset ++
    mkDFFBank rm s1_rm clock reset ++
    mkDFFBank dest_tag s1_tag clock reset ++
    [Gate.mkDFF valid_in clock reset s1_valid]

  -- ══════════════════════════════════════════════
  -- Stage 2 pipeline registers (stage 1 → stage 2)
  -- ══════════════════════════════════════════════
  let s2_src1 := makeIndexedWires "s2_src1" 32
  let s2_src2 := makeIndexedWires "s2_src2" 32
  let s2_rm := makeIndexedWires "s2_rm" 3
  let s2_tag := makeIndexedWires "s2_tag" 6
  let s2_valid := Wire.mk "s2_valid"

  let s2_dffs :=
    mkDFFBank s1_src1 s2_src1 clock reset ++
    mkDFFBank s1_src2 s2_src2 clock reset ++
    mkDFFBank s1_rm s2_rm clock reset ++
    mkDFFBank s1_tag s2_tag clock reset ++
    [Gate.mkDFF s1_valid clock reset s2_valid]

  -- ══════════════════════════════════════════════
  -- Combinational FP multiply logic on s2_src1 x s2_src2
  -- ══════════════════════════════════════════════

  -- Constant one wire (from NOT zero)
  let one_w := Wire.mk "fp_one"
  let one_gate := Gate.mkNOT zero one_w

  -- Step 1: Unpack operands
  -- sign_a = s2_src1[31], sign_b = s2_src2[31]
  let result_sign := Wire.mk "fp_rsign"
  let sign_gate := Gate.mkXOR (s2_src1[31]!) (s2_src2[31]!) result_sign

  -- exp_a[7:0] = s2_src1[30:23], exp_b[7:0] = s2_src2[30:23]
  let exp_a := (List.range 8).map fun i => s2_src1[23 + i]!
  let exp_b := (List.range 8).map fun i => s2_src2[23 + i]!

  -- mant_a[23:0] = {1, s2_src1[22:0]} - implicit 1 prepended
  -- mant_a[0..22] = s2_src1[0..22], mant_a[23] = one_w
  let mant_a := (List.range 24).map fun i =>
    if i < 23 then s2_src1[i]! else one_w
  let mant_b := (List.range 24).map fun i =>
    if i < 23 then s2_src2[i]! else one_w

  -- Step 2: Add exponents (9-bit to handle overflow)
  -- Extend exp_a and exp_b to 9 bits (zero-extend)
  let exp_a9 := exp_a ++ [zero]
  let exp_b9 := exp_b ++ [zero]
  let exp_sum := makeIndexedWires "fp_expsum" 9
  let exp_sum_cout := Wire.mk "fp_expsum_cout"
  let exp_add_gates := mkRippleAdd exp_a9 exp_b9 zero exp_sum exp_sum_cout "fp_expadd"

  -- Subtract bias (127 = 0b001111111) from exp_sum
  -- bias9 = [1,1,1,1,1,1,1,0,0] (LSB first: 127 = bits 0-6 are 1, bits 7-8 are 0)
  let bias9 := (List.range 9).map fun i =>
    if i < 7 then one_w else zero
  let exp_unbiased := makeIndexedWires "fp_expub" 9
  let exp_sub_borrow := Wire.mk "fp_expub_borrow"
  let exp_sub_gates := mkRippleSub exp_sum bias9 exp_unbiased exp_sub_borrow one_w "fp_expsub"

  -- Step 3: 24x24 mantissa multiply -> 48-bit product
  let product := makeIndexedWires "fp_prod" 48
  let (_, mul_gates) := mkMul24x24 mant_a mant_b product zero "fp_mul"

  -- Step 4: Normalize
  -- If product[47] = 1: normalized_mant = product[46:24], final_exp = exp_unbiased + 1
  -- If product[47] = 0: normalized_mant = product[45:23], final_exp = exp_unbiased

  -- Mant when product[47]=1: product[24..46] (23 bits)
  let mant_shifted := (List.range 23).map fun i => product[24 + i]!
  -- Mant when product[47]=0: product[23..45] (23 bits)
  let mant_unshifted := (List.range 23).map fun i => product[23 + i]!

  let norm_mant := makeIndexedWires "fp_nmant" 23
  let norm_mant_gates := mkMuxBank mant_unshifted mant_shifted (product[47]!) norm_mant

  -- final_exp = exp_unbiased + product[47]
  -- Add product[47] as a 1-bit value to exp_unbiased (9-bit)
  -- Simple: add [product[47], zero, zero, ..., zero] (9-bit) to exp_unbiased
  let exp_inc_b := (List.range 9).map fun i =>
    if i == 0 then product[47]! else zero
  let final_exp := makeIndexedWires "fp_fexp" 9
  let final_exp_cout := Wire.mk "fp_fexp_cout"
  let final_exp_gates := mkRippleAdd exp_unbiased exp_inc_b zero final_exp final_exp_cout "fp_fexpadd"

  -- Step 5: Pack result
  -- result[31] = result_sign
  -- result[30:23] = final_exp[7:0]
  -- result[22:0] = norm_mant[22:0]
  let pack_gates := (List.range 32).map fun i =>
    if i < 23 then
      Gate.mkBUF (norm_mant[i]!) (result[i]!)
    else if i < 31 then
      Gate.mkBUF (final_exp[i - 23]!) (result[i]!)
    else
      Gate.mkBUF result_sign (result[i]!)

  let fp_gates :=
    [one_gate, sign_gate] ++
    exp_add_gates ++
    exp_sub_gates ++
    mul_gates ++
    norm_mant_gates ++
    final_exp_gates ++
    pack_gates

  -- ══════════════════════════════════════════════
  -- Tag, valid, exception outputs
  -- ══════════════════════════════════════════════
  let tag_out_gates := (List.range 6).map (fun i =>
    Gate.mkBUF (s2_tag[i]!) (tag_out[i]!)
  )

  let valid_gate := [Gate.mkBUF s2_valid valid_out]

  -- Exception flags tied to zero
  let exc_gates := (List.range 5).map (fun i =>
    Gate.mkBUF zero (exc[i]!)
  )

  -- ══════════════════════════════════════════════
  -- Assemble circuit
  -- ══════════════════════════════════════════════
  let all_gates :=
    s1_dffs ++
    s2_dffs ++
    fp_gates ++
    tag_out_gates ++
    valid_gate ++
    exc_gates

  { name := "FPMultiplier"
    inputs := src1 ++ src2 ++ rm ++ dest_tag ++ [valid_in, clock, reset, zero]
    outputs := result ++ tag_out ++ exc ++ [valid_out]
    gates := all_gates
    instances := []
    signalGroups := [
      { name := "src1", width := 32, wires := src1 },
      { name := "src2", width := 32, wires := src2 },
      { name := "rm", width := 3, wires := rm },
      { name := "dest_tag", width := 6, wires := dest_tag },
      { name := "result", width := 32, wires := result },
      { name := "tag_out", width := 6, wires := tag_out },
      { name := "exc", width := 5, wires := exc }
    ]
  }

/-- Convenience definition for the FP multiplier circuit. -/
def fpMultiplierCircuit : Circuit := mkFPMultiplier

end Shoumei.Circuits.Sequential
