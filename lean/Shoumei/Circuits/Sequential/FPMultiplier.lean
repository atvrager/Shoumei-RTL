/-
Circuits/Sequential/FPMultiplier.lean - 3-Stage Pipelined FP Multiplier

IEEE 754 binary32 multiplication with pipelined datapath.

Pipeline stages:
  Stage 1: Latch inputs → Unpack + exponent add/sub + CSA tree (24x24)
  Stage 2: Latch intermediates → Final 48-bit KSA + normalize + pack

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
import Shoumei.Circuits.Combinational.KoggeStoneAdder

namespace Shoumei.Circuits.Sequential

open Shoumei
open Shoumei.Circuits.Combinational

/-- Create a bank of DFFs with matching d/q wire lists. -/
def mkDFFBank (d_wires q_wires : List Wire) (clock reset : Wire) : List Gate :=
  List.zipWith (fun d q => Gate.mkDFF d clock reset q) d_wires q_wires

/-- Inline 3:2 CSA compressor for w-bit values.
    sum[i] = x[i] XOR y[i] XOR z[i]
    carry[i+1] = MAJ(x[i], y[i], z[i]), carry[0] = zero -/
private def mkCSAInline (x y z : List Wire) (sum carry : List Wire)
    (zero : Wire) (pfx : String) : List Gate :=
  let w := x.length
  let c_raw := makeIndexedWires (pfx ++ "_cr") w
  let csa_gates := (List.range w).flatMap fun i =>
    let xy := Wire.mk s!"{pfx}_xy{i}"
    let ab := Wire.mk s!"{pfx}_ab{i}"
    let bc := Wire.mk s!"{pfx}_bc{i}"
    let ac := Wire.mk s!"{pfx}_ac{i}"
    let abbc := Wire.mk s!"{pfx}_abbc{i}"
    [
      Gate.mkXOR (x[i]!) (y[i]!) xy,
      Gate.mkXOR xy (z[i]!) (sum[i]!),
      Gate.mkAND (x[i]!) (y[i]!) ab,
      Gate.mkAND (y[i]!) (z[i]!) bc,
      Gate.mkAND (x[i]!) (z[i]!) ac,
      Gate.mkOR ab bc abbc,
      Gate.mkOR abbc ac (c_raw[i]!)
    ]
  -- Shift carry left by 1
  let shift_gates := [Gate.mkBUF zero (carry[0]!)] ++
    (List.range (w - 1)).map fun i => Gate.mkBUF (c_raw[i]!) (carry[i + 1]!)
  csa_gates ++ shift_gates

/-- Reduce a list of 48-bit rows to 2 (sum + carry) using a CSA tree.
    Returns (final_sum, final_carry, all_gates). -/
private partial def mkCSATree (rows : List (List Wire)) (zero : Wire)
    (level : Nat) : List Wire × List Wire × List Gate :=
  match rows with
  | [] =>
    let s := makeIndexedWires "csa_empty_s" 48
    let c := makeIndexedWires "csa_empty_c" 48
    let g := (List.range 48).flatMap fun j =>
      [Gate.mkBUF zero (s[j]!), Gate.mkBUF zero (c[j]!)]
    (s, c, g)
  | [single] =>
    let c := makeIndexedWires s!"csa_l{level}_one_c" 48
    let g := (List.range 48).map fun j => Gate.mkBUF zero (c[j]!)
    (single, c, g)
  | [r1, r2] => (r1, r2, [])
  | _ =>
    -- Compress groups of 3
    let rec compress (rs : List (List Wire)) (idx : Nat)
        : List (List Wire) × List Gate :=
      match rs with
      | x :: y :: z :: rest =>
        let pfx := s!"csa_l{level}_g{idx}"
        let s := makeIndexedWires (pfx ++ "_s") 48
        let c := makeIndexedWires (pfx ++ "_c") 48
        let g := mkCSAInline x y z s c zero pfx
        let (more, mg) := compress rest (idx + 1)
        (s :: c :: more, g ++ mg)
      | remaining => (remaining, [])
    let (next, gates) := compress rows 0
    let (fs, fc, more_gates) := mkCSATree next zero (level + 1)
    (fs, fc, gates ++ more_gates)

/-- N-bit 2:1 MUX bank. out[i] = sel ? b[i] : a[i]. -/
private def mkMuxBank (a b : List Wire) (sel : Wire) (out : List Wire) : List Gate :=
  (List.range a.length).map fun i => Gate.mkMUX (a[i]!) (b[i]!) sel (out[i]!)

/-- Build a 3-stage pipelined FP multiplier circuit with CSA tree multiplication.

    Pipeline:
      Stage 1 comb: Unpack + exponent add/sub (KSA) + 24 partial products + CSA tree
      Stage 2 comb: Final 48-bit KSA + normalize + exponent increment + pack -/
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
  -- Stage 1 combinational: Unpack + Exponent + CSA tree
  -- ══════════════════════════════════════════════

  -- Constant one wire (from NOT zero)
  let one_w := Wire.mk "fp_one"
  let one_gate := Gate.mkNOT zero one_w

  -- Unpack: sign
  let result_sign := Wire.mk "fp_rsign"
  let sign_gate := Gate.mkXOR (s1_src1[31]!) (s1_src2[31]!) result_sign

  -- Unpack: exponents (8-bit, from bits [30:23])
  let exp_a := (List.range 8).map fun i => s1_src1[23 + i]!
  let exp_b := (List.range 8).map fun i => s1_src2[23 + i]!

  -- Unpack: mantissas with implicit 1 bit (24-bit)
  let mant_a := (List.range 24).map fun i =>
    if i < 23 then s1_src1[i]! else one_w
  let mant_b := (List.range 24).map fun i =>
    if i < 23 then s1_src2[i]! else one_w

  -- Exponent sum: exp_a + exp_b (9-bit KSA)
  let exp_a9 := exp_a ++ [zero]
  let exp_b9 := exp_b ++ [zero]
  let exp_sum := makeIndexedWires "fp_expsum" 9
  let (exp_add_gates, _) := mkKoggeStoneAdd exp_a9 exp_b9 zero exp_sum "fp_expadd"

  -- Subtract bias (127): exp_unbiased = exp_sum - 127
  let bias9 := (List.range 9).map fun i =>
    if i < 7 then one_w else zero
  let exp_unbiased := makeIndexedWires "fp_expub" 9
  let (exp_sub_gates, _) := mkKoggeStoneSub exp_sum bias9 exp_unbiased "fp_expsub" one_w

  -- Generate 24 partial products (each 48 bits, shifted)
  -- pp[j][i] = mant_a[i-j] AND mant_b[j], zero-padded
  let pp_rows := (List.range 24).map fun j =>
    let pp := makeIndexedWires s!"fp_pp{j}" 48
    (pp, (List.range 48).map fun i =>
      if i >= j && i < j + 24 then
        Gate.mkAND (mant_a[i - j]!) (mant_b[j]!) (pp[i]!)
      else
        Gate.mkBUF zero (pp[i]!))

  let pp_wires := pp_rows.map (·.1)
  let pp_gates := pp_rows.map (·.2) |>.flatten

  -- CSA tree: reduce 24 partial products to 2 (sum + carry)
  let (csa_sum, csa_carry, csa_tree_gates) := mkCSATree pp_wires zero 0

  -- ══════════════════════════════════════════════
  -- Stage 2 pipeline registers: latch intermediate results
  -- ══════════════════════════════════════════════
  let s2_rsign := Wire.mk "s2_rsign"
  let s2_expub := makeIndexedWires "s2_expub" 9
  let s2_csa_sum := makeIndexedWires "s2_csa_sum" 48
  let s2_csa_carry := makeIndexedWires "s2_csa_carry" 48
  let s2_rm := makeIndexedWires "s2_rm" 3
  let s2_tag := makeIndexedWires "s2_tag" 6
  let s2_valid := Wire.mk "s2_valid"

  let s2_dffs :=
    [Gate.mkDFF result_sign clock reset s2_rsign] ++
    mkDFFBank exp_unbiased s2_expub clock reset ++
    mkDFFBank csa_sum s2_csa_sum clock reset ++
    mkDFFBank csa_carry s2_csa_carry clock reset ++
    mkDFFBank s1_rm s2_rm clock reset ++
    mkDFFBank s1_tag s2_tag clock reset ++
    [Gate.mkDFF s1_valid clock reset s2_valid]

  -- ══════════════════════════════════════════════
  -- Stage 2 combinational: Final CPA + Normalize + Pack
  -- ══════════════════════════════════════════════

  -- Final 48-bit Kogge-Stone addition: product = csa_sum + csa_carry
  let product := makeIndexedWires "fp_prod" 48
  let (final_add_gates, _) := mkKoggeStoneAdd s2_csa_sum s2_csa_carry zero product "fp_cpa"

  -- Normalize:
  -- If product[47] = 1: mant = product[24..46], exp = exp_unbiased + 1
  -- If product[47] = 0: mant = product[23..45], exp = exp_unbiased
  let mant_shifted := (List.range 23).map fun i => product[24 + i]!
  let mant_unshifted := (List.range 23).map fun i => product[23 + i]!
  let norm_mant := makeIndexedWires "fp_nmant" 23
  let norm_mant_gates := mkMuxBank mant_unshifted mant_shifted (product[47]!) norm_mant

  -- Exponent increment: final_exp = exp_unbiased + product[47]
  let exp_inc_b := (List.range 9).map fun i =>
    if i == 0 then product[47]! else zero
  let final_exp := makeIndexedWires "fp_fexp" 9
  let (final_exp_gates, _) := mkKoggeStoneAdd s2_expub exp_inc_b zero final_exp "fp_fexpadd"

  -- Pack: result[31] = sign, result[30:23] = exp[7:0], result[22:0] = mant
  let pack_gates := (List.range 32).map fun i =>
    if i < 23 then
      Gate.mkBUF (norm_mant[i]!) (result[i]!)
    else if i < 31 then
      Gate.mkBUF (final_exp[i - 23]!) (result[i]!)
    else
      Gate.mkBUF s2_rsign (result[i]!)

  -- ══════════════════════════════════════════════
  -- Tag, valid, exception outputs
  -- ══════════════════════════════════════════════
  let tag_out_gates := (List.range 6).map fun i =>
    Gate.mkBUF (s2_tag[i]!) (tag_out[i]!)
  let valid_gate := [Gate.mkBUF s2_valid valid_out]
  let exc_gates := (List.range 5).map fun i =>
    Gate.mkBUF zero (exc[i]!)

  -- ══════════════════════════════════════════════
  -- Assemble circuit
  -- ══════════════════════════════════════════════
  let all_gates :=
    s1_dffs ++
    [one_gate, sign_gate] ++
    exp_add_gates ++
    exp_sub_gates ++
    pp_gates ++
    csa_tree_gates ++
    s2_dffs ++
    final_add_gates ++
    norm_mant_gates ++
    final_exp_gates ++
    pack_gates ++
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
