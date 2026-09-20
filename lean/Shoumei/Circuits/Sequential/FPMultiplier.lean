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
import Shoumei.Components.Select
import Shoumei.Circuits.Combinational.KoggeStoneAdder
import Shoumei.Circuits.Combinational.Multiplier

namespace Shoumei.Circuits.Sequential

open Shoumei
open Shoumei.Components
open Shoumei.Circuits.Combinational

/-- OR-reduce: returns (wire, gates) where wire = OR of all input wires. -/
private def mkOrTree (pfx : String) (inputs : List Wire) : Wire × List Gate :=
  match inputs with
  | [] => (Wire.mk s!"{pfx}_empty", [])
  | [w] =>
    let out := Wire.mk s!"{pfx}_buf"
    (out, [Gate.mkBUF w out])
  | w0 :: w1 :: rest =>
    let firstOut := Wire.mk s!"{pfx}_0"
    let firstGate := Gate.mkOR w0 w1 firstOut
    let (finalW, restGates) := rest.enum.foldl (fun (acc : Wire × List Gate) (idx, w) =>
      let out := Wire.mk s!"{pfx}_{idx + 1}"
      let g := Gate.mkOR acc.1 w out
      (out, acc.2 ++ [g])
    ) (firstOut, [])
    (finalW, [firstGate] ++ restGates)

/-- AND-reduce: returns (wire, gates) where wire = AND of all input wires. -/
private def mkAndTree (pfx : String) (inputs : List Wire) : Wire × List Gate :=
  match inputs with
  | [] => (Wire.mk s!"{pfx}_empty", [])
  | [w] =>
    let out := Wire.mk s!"{pfx}_buf"
    (out, [Gate.mkBUF w out])
  | w0 :: w1 :: rest =>
    let firstOut := Wire.mk s!"{pfx}_0"
    let firstGate := Gate.mkAND w0 w1 firstOut
    let (finalW, restGates) := rest.enum.foldl (fun (acc : Wire × List Gate) (idx, w) =>
      let out := Wire.mk s!"{pfx}_{idx + 1}"
      let g := Gate.mkAND acc.1 w out
      (out, acc.2 ++ [g])
    ) (firstOut, [])
    (finalW, [firstGate] ++ restGates)

/-- Create a bank of DFFs with matching d/q wire lists. -/
def mkDFFBank (d_wires q_wires : List Wire) (clock reset : Wire) : List Gate :=
  List.zipWith (fun d q => Gate.mkDFF d clock reset q) d_wires q_wires


/-- N-bit 2:1 MUX bank. out[i] = sel ? b[i] : a[i]. -/
private def mkMuxBank (a b : List Wire) (sel : Wire) (out : List Wire) : List Gate :=
  (List.range a.length).map fun i => Gate.mkMUX (a[i]!) (b[i]!) sel (out[i]!)

private def mkBarrelShiftLeft48 (input : List Wire) (shift_amt : List Wire)
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
      Gate.mkMUX unshifted shifted sel (curr[i]!)
  let copy_gates := (List.range w).map fun i =>
    Gate.mkBUF ((levels[6]!)[i]!) (output[i]!)
  mux_gates ++ copy_gates

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

  -- Unpack mantissa bits for operand classification
  let s1_exp1_bits := exp_a
  let (s1_exp1_ones, s1_exp1_ones_gates) := mkAndTree "mul_e1o" s1_exp1_bits
  let s1_mant1_bits := (List.range 23).map fun i => s1_src1[i]!
  let (s1_mant1_nz, s1_mant1_nz_gates) := mkOrTree "mul_m1nz" s1_mant1_bits
  let s1_exp2_bits := exp_b
  let (s1_exp2_ones, s1_exp2_ones_gates) := mkAndTree "mul_e2o" s1_exp2_bits
  let s1_mant2_bits := (List.range 23).map fun i => s1_src2[i]!
  let (s1_mant2_nz, s1_mant2_nz_gates) := mkOrTree "mul_m2nz" s1_mant2_bits

  -- NaN detection
  let is_nan1 := Wire.mk "mul_is_nan1"
  let is_nan2 := Wire.mk "mul_is_nan2"
  let either_nan := Wire.mk "mul_either_nan"
  let nan_gates := [
    Gate.mkAND s1_exp1_ones s1_mant1_nz is_nan1,
    Gate.mkAND s1_exp2_ones s1_mant2_nz is_nan2,
    Gate.mkOR is_nan1 is_nan2 either_nan
  ]

  -- Inf detection
  let not_mant1_nz := Wire.mk "mul_nm1nz"
  let not_mant2_nz := Wire.mk "mul_nm2nz"
  let is_inf1 := Wire.mk "mul_is_inf1"
  let is_inf2 := Wire.mk "mul_is_inf2"
  let inf_gates := [
    Gate.mkNOT s1_mant1_nz not_mant1_nz,
    Gate.mkNOT s1_mant2_nz not_mant2_nz,
    Gate.mkAND s1_exp1_ones not_mant1_nz is_inf1,
    Gate.mkAND s1_exp2_ones not_mant2_nz is_inf2
  ]

  -- Zero detection: exp=0 and mant=0
  let (s1_exp1_any, s1_exp1_any_gates) := mkOrTree "mul_e1a" s1_exp1_bits
  let (s1_exp2_any, s1_exp2_any_gates) := mkOrTree "mul_e2a" s1_exp2_bits
  let not_exp1_any := Wire.mk "mul_ne1a"
  let not_exp2_any := Wire.mk "mul_ne2a"
  let is_zero1 := Wire.mk "mul_is_zero1"
  let is_zero2 := Wire.mk "mul_is_zero2"
  let zero_det_gates := [
    Gate.mkNOT s1_exp1_any not_exp1_any,
    Gate.mkNOT s1_exp2_any not_exp2_any,
    Gate.mkAND not_exp1_any not_mant1_nz is_zero1,
    Gate.mkAND not_exp2_any not_mant2_nz is_zero2
  ]

  -- Subnormal operand detection
  let is_subnorm_a := Wire.mk "mul_subn_a"
  let is_subnorm_b := Wire.mk "mul_subn_b"
  let has_subnorm := Wire.mk "mul_has_subnorm"
  let subnorm_det_gates := [
    Gate.mkAND not_exp1_any s1_mant1_nz is_subnorm_a,
    Gate.mkAND not_exp2_any s1_mant2_nz is_subnorm_b,
    Gate.mkOR is_subnorm_a is_subnorm_b has_subnorm
  ]

  -- Unpack: mantissas with implicit bit (0 if subnormal, 1 if normal)
  let mant_a := (List.range 24).map fun i =>
    if i < 23 then s1_src1[i]! else s1_exp1_any
  let mant_b := (List.range 24).map fun i =>
    if i < 23 then s1_src2[i]! else s1_exp2_any

  -- Effective exponents (if subnormal, exponent is treated as 1)
  let eff_exp_a := (List.range 8).map fun i =>
    if i == 0 then Wire.mk "fp_eff_ea0" else Wire.mk s!"fp_eff_ea_{i}"
  let eff_ea_gates :=
    [Gate.mkMUX (exp_a[0]!) one_w is_subnorm_a (eff_exp_a[0]!)] ++
    (List.range 7).map fun i =>
      Gate.mkMUX (exp_a[i + 1]!) zero is_subnorm_a (eff_exp_a[i + 1]!)

  let eff_exp_b := (List.range 8).map fun i =>
    if i == 0 then Wire.mk "fp_eff_eb0" else Wire.mk s!"fp_eff_eb_{i}"
  let eff_eb_gates :=
    [Gate.mkMUX (exp_b[0]!) one_w is_subnorm_b (eff_exp_b[0]!)] ++
    (List.range 7).map fun i =>
      Gate.mkMUX (exp_b[i + 1]!) zero is_subnorm_b (eff_exp_b[i + 1]!)

  -- Exponent sum: eff_exp_a + eff_exp_b (9-bit KSA)
  let exp_a9 := eff_exp_a ++ [zero]
  let exp_b9 := eff_exp_b ++ [zero]
  let exp_sum := makeIndexedWires "fp_expsum" 9
  let (exp_add_gates, _) := mkAddFor (AdderSpec.minArea exp_a9.length .none) exp_a9 exp_b9 zero exp_sum "fp_expadd"

  -- Subtract bias (127): exp_unbiased = exp_sum - 127
  let bias9 := (List.range 9).map fun i =>
    if i < 7 then one_w else zero
  let exp_unbiased := makeIndexedWires "fp_expub" 9
  let (exp_sub_gates, _) := mkSubFor (AdderSpec.minArea exp_sum.length .one) exp_sum bias9 exp_unbiased "fp_expsub" one_w

  -- Generate 24 partial products (each 48 bits, shifted)
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
  let (csa_sum, csa_carry, csa_tree_gates, csa_instances) :=
    mkCSATreeHierarchical pp_wires zero 48

  -- NV = either_nan | (inf1 & zero2) | (zero1 & inf2)
  let inf1_zero2 := Wire.mk "mul_inf1_zero2"
  let zero1_inf2 := Wire.mk "mul_zero1_inf2"
  let inf_zero := Wire.mk "mul_inf_zero"
  let mul_nv := Wire.mk "mul_nv"
  let nv_gates := [
    Gate.mkAND is_inf1 is_zero2 inf1_zero2,
    Gate.mkAND is_zero1 is_inf2 zero1_inf2,
    Gate.mkOR inf1_zero2 zero1_inf2 inf_zero,
    Gate.mkOR either_nan inf_zero mul_nv
  ]

  -- any_special = either_nan | inf1 | inf2 | zero1 | zero2
  let any_special_or1 := Wire.mk "mul_aso1"
  let any_special_or2 := Wire.mk "mul_aso2"
  let any_special_or3 := Wire.mk "mul_aso3"
  let any_special := Wire.mk "mul_any_special"
  let not_special := Wire.mk "mul_not_special"
  let special_gates := [
    Gate.mkOR is_inf1 is_inf2 any_special_or1,
    Gate.mkOR is_zero1 is_zero2 any_special_or2,
    Gate.mkOR any_special_or1 any_special_or2 any_special_or3,
    Gate.mkOR either_nan any_special_or3 any_special,
    Gate.mkNOT any_special not_special
  ]

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
  let s2_has_subnorm := Wire.mk "s2_has_subnorm"

  let s2_dffs :=
    [Gate.mkDFF result_sign clock reset s2_rsign] ++
    mkDFFBank exp_unbiased s2_expub clock reset ++
    mkDFFBank csa_sum s2_csa_sum clock reset ++
    mkDFFBank csa_carry s2_csa_carry clock reset ++
    mkDFFBank s1_rm s2_rm clock reset ++
    mkDFFBank s1_tag s2_tag clock reset ++
    [Gate.mkDFF s1_valid clock reset s2_valid,
     Gate.mkDFF has_subnorm clock reset s2_has_subnorm]

  -- ══════════════════════════════════════════════
  -- Stage 2 combinational: Final CPA + Normalize + Pack
  -- ══════════════════════════════════════════════

  -- Final 48-bit Kogge-Stone addition: product = csa_sum + csa_carry
  let product := makeIndexedWires "fp_prod" 48
  let (final_add_gates, _) := mkKoggeStoneAdd s2_csa_sum s2_csa_carry zero product "fp_cpa"

  -- Normal path:
  let mant_shifted := (List.range 23).map fun i => product[24 + i]!
  let mant_unshifted := (List.range 23).map fun i => product[23 + i]!
  let norm_mant := makeIndexedWires "fp_nmant" 23
  let norm_mant_gates := mkMuxBank mant_unshifted mant_shifted (product[47]!) norm_mant

  let exp_inc_b := (List.range 9).map fun i =>
    if i == 0 then product[47]! else zero
  let final_exp := makeIndexedWires "fp_fexp" 9
  let (final_exp_gates, _) := mkKoggeStoneAdd s2_expub exp_inc_b zero final_exp "fp_fexpadd"

  let packed := makeIndexedWires "mul_packed" 32
  let pack_gates := (List.range 32).map fun i =>
    if i < 23 then
      Gate.mkBUF (norm_mant[i]!) (packed[i]!)
    else if i < 31 then
      Gate.mkBUF (final_exp[i - 23]!) (packed[i]!)
    else
      Gate.mkBUF s2_rsign (packed[i]!)

  -- Subnormal normalization path via 48-bit LZD + Barrel Left Shift
  let lz_v := makeIndexedWires "fp_lz_v" 48
  let lz_p := (List.range 48).map fun i => makeIndexedWires ("fp_lz_p_" ++ toString i) 6
  let lz_leaf_gates := (List.range 48).flatMap fun i =>
    [Gate.mkBUF (product[i]!) (lz_v[i]!)] ++
    (List.range 6).map fun k =>
      let bit_val := if (i >>> k) &&& 1 == 1 then one_w else zero
      Gate.mkBUF bit_val ((lz_p[i]!)[k]!)

  let strides := [1, 2, 4, 8, 16, 32]
  let (lz_prefix_gates, _lz_final_v, lz_final_p) :=
    strides.foldl (fun (acc : List Gate × List Wire × List (List Wire)) stride =>
      let (gates_acc, v_prev, p_prev) := acc
      let lt := "fp_lz_s" ++ toString stride
      let v_new := makeIndexedWires (lt ++ "_v") 48
      let p_new := (List.range 48).map fun i => makeIndexedWires (lt ++ "_p_" ++ toString i) 6

      let level_gates := (List.range 48).flatMap fun i =>
        if i + stride < 48 then
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

  let lead_pos := lz_final_p[0]!  -- 6-bit position of leading 1 (0 to 47)
  let lz_all_gates := lz_leaf_gates ++ lz_prefix_gates

  -- lshift_amt = 47 - lead_pos (6 bits, 47 = 6'b101111)
  let lshift_amt := makeIndexedWires "fp_lsh_amt" 6
  let lsh_b := makeIndexedWires "fp_lsh_b" 7
  let lsh_sub_gates := [Gate.mkBUF zero (lsh_b[0]!)] ++ (List.range 6).flatMap (fun i =>
    let a := if i == 4 then zero else one_w
    let b := lead_pos[i]!
    let bi := lsh_b[i]!
    let bo := lsh_b[i + 1]!
    let xab := Wire.mk s!"fp_ls_x_{i}"
    [Gate.mkXOR a b xab,
     Gate.mkXOR xab bi (lshift_amt[i]!),
     Gate.mkNOT a (Wire.mk s!"fp_ls_na_{i}"),
     Gate.mkAND (Wire.mk s!"fp_ls_na_{i}") b (Wire.mk s!"fp_ls_t0_{i}"),
     Gate.mkAND (Wire.mk s!"fp_ls_na_{i}") bi (Wire.mk s!"fp_ls_t1_{i}"),
     Gate.mkAND b bi (Wire.mk s!"fp_ls_t2_{i}"),
     Gate.mkOR (Wire.mk s!"fp_ls_t0_{i}") (Wire.mk s!"fp_ls_t1_{i}") (Wire.mk s!"fp_ls_t01_{i}"),
     Gate.mkOR (Wire.mk s!"fp_ls_t01_{i}") (Wire.mk s!"fp_ls_t2_{i}") bo]
  )

  let norm_prod := makeIndexedWires "fp_nprod" 48
  let lshift_gates := mkBarrelShiftLeft48 product lshift_amt norm_prod zero "fp_lsh"

  let sub_mant := (List.range 23).map fun i => norm_prod[24 + i]!
  let sub_G := norm_prod[23]!
  let sub_R := norm_prod[22]!
  let (sub_S, sub_S_gates) := mkOrTree "fp_sub_s" (List.range 22 |>.map fun i => norm_prod[i]!)

  let sub_rs_or := Wire.mk "fp_sub_rs"
  let sub_rnd_cand := Wire.mk "fp_sub_rcand"
  let sub_rnd_up := Wire.mk "fp_sub_rup"
  let sub_rnd_gates := [
    Gate.mkOR sub_R sub_S sub_rs_or,
    Gate.mkOR sub_rs_or (sub_mant[0]!) sub_rnd_cand,
    Gate.mkAND sub_G sub_rnd_cand sub_rnd_up
  ]

  let sub_mant_inc := makeIndexedWires "fp_sub_minc" 23
  let sub_mant_c := makeIndexedWires "fp_sub_mc" 24
  let sub_mant_inc_gates := [Gate.mkBUF sub_rnd_up (sub_mant_c[0]!)] ++ (List.range 23).flatMap (fun i =>
    [Gate.mkXOR (sub_mant[i]!) (sub_mant_c[i]!) (sub_mant_inc[i]!),
     Gate.mkAND (sub_mant[i]!) (sub_mant_c[i]!) (sub_mant_c[i + 1]!)]
  )
  let sub_rollover := sub_mant_c[23]!
  let sub_not_rollover := Wire.mk "fp_sub_nroll"
  let sub_final_mant := makeIndexedWires "fp_sub_fmant" 23
  let sub_final_mant_gates := [Gate.mkNOT sub_rollover sub_not_rollover] ++
    (List.range 23).map fun i => Gate.mkAND (sub_mant_inc[i]!) sub_not_rollover (sub_final_mant[i]!)

  let const_one_9 := [one_w] ++ (List.replicate 8 zero)
  let exp_plus_1 := makeIndexedWires "fp_eplus1" 9
  let (exp_plus1_gates, _) := mkKoggeStoneAdd s2_expub const_one_9 zero exp_plus_1 "fp_ep1"

  let lsh_ext9 := lshift_amt ++ [zero, zero, zero]
  let sub_exp_pre := makeIndexedWires "fp_sub_epre" 9
  let (sub_exp_sub_gates, _) := mkKoggeStoneSub exp_plus_1 lsh_ext9 sub_exp_pre "fp_esub" one_w

  let roll_ext9 := [sub_rollover] ++ (List.replicate 8 zero)
  let sub_exp_final := makeIndexedWires "fp_sub_efin" 9
  let (sub_exp_roll_gates, _) := mkKoggeStoneAdd sub_exp_pre roll_ext9 zero sub_exp_final "fp_eroll"

  let sub_packed := makeIndexedWires "fp_sub_packed" 32
  let sub_pack_gates := (List.range 32).map fun i =>
    if i < 23 then Gate.mkBUF (sub_final_mant[i]!) (sub_packed[i]!)
    else if i < 31 then Gate.mkBUF (sub_exp_final[i - 23]!) (sub_packed[i]!)
    else Gate.mkBUF s2_rsign (sub_packed[i]!)

  let final_packed := makeIndexedWires "fp_fin_packed" 32
  let final_pack_gates := mkMuxBank packed sub_packed s2_has_subnorm final_packed

  -- NX (Inexact)
  let low23_bits := (List.range 23).map fun i => product[i]!
  let (low23_or, low23_or_gates) := mkOrTree "mul_low23" low23_bits
  let mul_extra_lost := Wire.mk "mul_extra_lost"
  let mul_nx := Wire.mk "mul_nx"
  let nx_gates := [
    Gate.mkAND (product[47]!) (product[23]!) mul_extra_lost,
    Gate.mkOR low23_or mul_extra_lost mul_nx
  ]

  let mul_nx_final := Wire.mk "mul_nx_final"
  let nx_final_gate := Gate.mkAND mul_nx not_special mul_nx_final

  -- Latch NV, special flags, inf/zero indicators through stage 2
  let s2_nv := Wire.mk "s2_nv"
  let s2_not_special := Wire.mk "s2_not_special"
  let s2_is_inf := Wire.mk "s2_is_inf"
  let s2_is_zero := Wire.mk "s2_is_zero"
  let s2_nv_dff := Gate.mkDFF mul_nv clock reset s2_nv
  let s2_ns_dff := Gate.mkDFF not_special clock reset s2_not_special
  let s2_inf_dff := Gate.mkDFF any_special_or1 clock reset s2_is_inf
  let s2_zero_dff := Gate.mkDFF any_special_or2 clock reset s2_is_zero

  let final_nx := Wire.mk "mul_final_nx"
  let final_nx_gate := Gate.mkAND mul_nx s2_not_special final_nx

  -- Step 1: zero override
  let zero_result := makeIndexedWires "mul_zero_res" 32
  let zero_override_gates := (List.range 32).map fun i =>
    if i < 31 then
      Gate.mkMUX (final_packed[i]!) zero s2_is_zero (zero_result[i]!)
    else
      Gate.mkBUF (final_packed[i]!) (zero_result[i]!)

  -- Step 2: inf override: if s2_is_inf, force exp=0xFF mant=0 (sign preserved)
  let inf_result := makeIndexedWires "mul_inf_res" 32
  let inf_override_gates := (List.range 32).map fun i =>
    if i < 23 then
      -- Inf has mant = 0
      Gate.mkMUX (zero_result[i]!) zero s2_is_inf (inf_result[i]!)
    else if i < 31 then
      -- Inf has exp = 0xFF (all ones)
      Gate.mkMUX (zero_result[i]!) one_w s2_is_inf (inf_result[i]!)
    else
      Gate.mkBUF (zero_result[i]!) (inf_result[i]!)  -- sign stays

  -- Step 3: NaN override: if s2_nv, force canonical NaN 0x7FC00000
  -- Write directly to the output `result` wires
  let nan_override_gates := (List.range 32).map fun i =>
    if i == 22 then
      -- Quiet NaN bit
      Gate.mkMUX (inf_result[i]!) one_w s2_nv (result[i]!)
    else if i < 22 then
      -- mant = 0 (except quiet bit)
      Gate.mkMUX (inf_result[i]!) zero s2_nv (result[i]!)
    else if i < 31 then
      -- exp = 0xFF
      Gate.mkMUX (inf_result[i]!) one_w s2_nv (result[i]!)
    else
      -- sign = 0 for canonical NaN
      Gate.mkMUX (inf_result[i]!) zero s2_nv (result[i]!)

  -- ══════════════════════════════════════════════
  -- Tag, valid, exception outputs
  -- ══════════════════════════════════════════════
  let tag_out_gates := (List.range 6).map fun i =>
    Gate.mkBUF (s2_tag[i]!) (tag_out[i]!)
  let valid_gate := [Gate.mkBUF s2_valid valid_out]
  let not_s2_rm0 := Wire.mk "not_s2_rm0"
  let not_s2_rm1 := Wire.mk "not_s2_rm1"
  let not_s2_rm2 := Wire.mk "not_s2_rm2"
  let exc_gates := [
    Gate.mkBUF final_nx (exc[0]!),
    Gate.mkNOT (s2_rm[0]!) not_s2_rm0,
    Gate.mkAND (s2_rm[0]!) not_s2_rm0 (exc[1]!),
    Gate.mkNOT (s2_rm[1]!) not_s2_rm1,
    Gate.mkAND (s2_rm[1]!) not_s2_rm1 (exc[2]!),
    Gate.mkNOT (s2_rm[2]!) not_s2_rm2,
    Gate.mkAND (s2_rm[2]!) not_s2_rm2 (exc[3]!),
    Gate.mkBUF s2_nv (exc[4]!)
  ]

  -- ══════════════════════════════════════════════
  -- Assemble circuit
  -- ══════════════════════════════════════════════
  let all_gates :=
    s1_dffs ++
    [one_gate, sign_gate] ++
    s1_exp1_ones_gates ++ s1_mant1_nz_gates ++
    s1_exp2_ones_gates ++ s1_mant2_nz_gates ++
    nan_gates ++ inf_gates ++
    s1_exp1_any_gates ++ s1_exp2_any_gates ++
    zero_det_gates ++ subnorm_det_gates ++
    eff_ea_gates ++ eff_eb_gates ++
    exp_add_gates ++
    exp_sub_gates ++
    pp_gates ++
    csa_tree_gates ++
    nv_gates ++ special_gates ++
    -- Stage 2 DFFs (including exception latches)
    s2_dffs ++ [s2_nv_dff, s2_ns_dff, s2_inf_dff, s2_zero_dff] ++
    -- Stage 2 combinational
    final_add_gates ++
    low23_or_gates ++ nx_gates ++ [nx_final_gate, final_nx_gate] ++
    norm_mant_gates ++
    final_exp_gates ++
    pack_gates ++
    lz_all_gates ++ lsh_sub_gates ++ lshift_gates ++
    sub_S_gates ++ sub_rnd_gates ++ sub_mant_inc_gates ++ sub_final_mant_gates ++
    exp_plus1_gates ++ sub_exp_sub_gates ++ sub_exp_roll_gates ++
    sub_pack_gates ++ final_pack_gates ++
    -- Special result override: NaN > Inf > Zero > Normal
    zero_override_gates ++ inf_override_gates ++ nan_override_gates ++
    tag_out_gates ++
    valid_gate ++
    exc_gates

  { name := "FPMultiplier"
    inputs := src1 ++ src2 ++ rm ++ dest_tag ++ [valid_in, clock, reset, zero]
    outputs := result ++ tag_out ++ exc ++ [valid_out]
    gates := all_gates
    instances := csa_instances
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
