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

/-- Right barrel shifter that accumulates every bit shifted below position 0
    into `sticky_out`.  Two extra input positions above the data let the guard and
    round bits survive the shift while the remainder below them is still visible,
    which is what a subnormal result needs. -/
private def mkBarrelShiftRightSticky (input : List Wire) (shift_amt : List Wire)
    (output : List Wire) (sticky_out : Wire) (zero_wire : Wire) (pfx : String) : List Gate :=
  let w := input.length
  let levels : List (List Wire) := (List.range 7).map fun level =>
    if level == 0 then input
    else (List.range w).map fun i => Wire.mk (pfx ++ "_l" ++ toString level ++ "_" ++ toString i)
  let stickies : List Wire := (List.range 7).map fun level => Wire.mk (pfx ++ "_stk_" ++ toString
    level)
  let init_stk_gate := Gate.mkBUF zero_wire stickies[0]!
  let (mux_gates, stk_gates) := (List.range 6).foldl (fun (acc : List Gate × List Gate) level =>
    let shift_by := 1 <<< level
    let prev := levels[level]!
    let curr := levels[level + 1]!
    let sel := shift_amt[level]!
    let prev_stk := stickies[level]!
    let curr_stk := stickies[level + 1]!
    let m_gates := (List.range w).map fun i =>
      let shifted := if i + shift_by < w then prev[i + shift_by]! else zero_wire
      Gate.mkMUX prev[i]! shifted sel curr[i]!
    let lost_bits := (List.range (min shift_by w)).map fun i => prev[i]!
    let (lost_or, lost_or_gates) := mkOrTree (pfx ++ "_lost_" ++ toString level) lost_bits
    let stk_c := Wire.mk (pfx ++ "_stkc_" ++ toString level)
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

  -- A signaling NaN is a NaN whose significand's top bit, the quiet bit, is
  -- clear.  Only it raises NV; a quiet NaN propagates as the canonical NaN
  -- without setting a flag.
  let not_quiet1 := Wire.mk "mul_nq1"
  let not_quiet2 := Wire.mk "mul_nq2"
  let is_snan1 := Wire.mk "mul_is_snan1"
  let is_snan2 := Wire.mk "mul_is_snan2"
  let either_snan := Wire.mk "mul_either_snan"
  let snan_gates := [
    Gate.mkNOT (s1_src1[22]!) not_quiet1,
    Gate.mkNOT (s1_src2[22]!) not_quiet2,
    Gate.mkAND is_nan1 not_quiet1 is_snan1,
    Gate.mkAND is_nan2 not_quiet2 is_snan2,
    Gate.mkOR is_snan1 is_snan2 either_snan
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

  -- Exponent sum: eff_exp_a + eff_exp_b (10-bit KSA).  The sign bit is needed to
  -- tell underflow from overflow, which 9 bits cannot do: the product exponent
  -- ranges from -125 to 381, so 256..381 collides with the negative range on the
  -- single available high bit.
  let exp_a10 := eff_exp_a ++ [zero, zero]
  let exp_b10 := eff_exp_b ++ [zero, zero]
  let exp_sum := makeIndexedWires "fp_expsum" 10
  let (exp_add_gates, _) := mkAddFor (AdderSpec.minArea exp_a10.length .none) exp_a10 exp_b10 zero
    exp_sum "fp_expadd"

  -- Subtract bias (127): exp_unbiased = exp_sum - 127
  let bias10 := (List.range 10).map fun i =>
    if i < 7 then one_w else zero
  let exp_unbiased := makeIndexedWires "fp_expub" 10
  let (exp_sub_gates, _) := mkSubFor (AdderSpec.minArea exp_sum.length .one) exp_sum bias10
    exp_unbiased "fp_expsub" one_w

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

  -- NV = signaling NaN | (inf1 & zero2) | (zero1 & inf2)
  let inf1_zero2 := Wire.mk "mul_inf1_zero2"
  let zero1_inf2 := Wire.mk "mul_zero1_inf2"
  let inf_zero := Wire.mk "mul_inf_zero"
  let mul_nv := Wire.mk "mul_nv"
  let mul_nan_res := Wire.mk "mul_nan_res"
  let nv_gates := [
    Gate.mkAND is_inf1 is_zero2 inf1_zero2,
    Gate.mkAND is_zero1 is_inf2 zero1_inf2,
    Gate.mkOR inf1_zero2 zero1_inf2 inf_zero,
    Gate.mkOR either_snan inf_zero mul_nv,
    -- The canonical-NaN result still applies to every NaN, quiet or not.
    Gate.mkOR either_nan inf_zero mul_nan_res
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
  let s2_expub := makeIndexedWires "s2_expub" 10
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

  let exp_inc_b := (List.range 10).map fun i =>
    if i == 0 then product[47]! else zero
  let final_exp := makeIndexedWires "fp_fexp" 10
  let (final_exp_gates, _) := mkKoggeStoneAdd s2_expub exp_inc_b zero final_exp "fp_fexpadd"

  -- Guard, round and sticky for the normal path.  product[47] selects whether the
  -- mantissa is taken shifted (top bit set) or not, which moves all three by one
  -- position; everything below sticky is the remainder.
  let (norm_S_a, norm_S_a_gates) :=
    mkOrTree "fp_ns_a" ((List.range 22).map fun i => product[i]!)
  let (norm_S_b, norm_S_b_gates) :=
    mkOrTree "fp_ns_b" ((List.range 21).map fun i => product[i]!)
  let norm_G := Wire.mk "fp_ng"
  let norm_R := Wire.mk "fp_nr"
  let norm_S := Wire.mk "fp_ns"
  let norm_grs_gates := [
    Gate.mkMUX (product[22]!) (product[23]!) (product[47]!) norm_G,
    Gate.mkMUX (product[21]!) (product[22]!) (product[47]!) norm_R,
    Gate.mkMUX norm_S_b norm_S_a (product[47]!) norm_S
  ]

  -- Rounding-mode decode, as in FPMultiplierD and the adders: RISC-V rm is
  -- 000 RNE, 001 RTZ, 010 RDN, 011 RUP, 100 RMM, and 101..111 behave as RNE.
  let rs_or := Wire.mk "fp_rs_or"
  let grs_or := Wire.mk "fp_grs_or"
  let rne_cand := Wire.mk "fp_rne_cand"
  let rne_up := Wire.mk "fp_rne_up"
  let any_rem := Wire.mk "fp_any_rem"
  let rdn_up := Wire.mk "fp_rdn_up"
  let rup_up := Wire.mk "fp_rup_up"
  let not_sign := Wire.mk "fp_not_sign"
  let not_rm0 := Wire.mk "fp_not_rm0"
  let not_rm1 := Wire.mk "fp_not_rm1"
  let not_rm2 := Wire.mk "fp_not_rm2"
  let is_rtz := Wire.mk "fp_is_rtz"
  let is_rdn := Wire.mk "fp_is_rdn"
  let is_rup := Wire.mk "fp_is_rup"
  let is_rmm := Wire.mk "fp_is_rmm"
  let grp_n2n1 := Wire.mk "fp_grp_n2n1"
  let grp_n2p1 := Wire.mk "fp_grp_n2p1"
  let grp_p2n1 := Wire.mk "fp_grp_p2n1"
  let up_rdn := Wire.mk "fp_up_rdn"
  let up_rup := Wire.mk "fp_up_rup"
  let up_rmm := Wire.mk "fp_up_rmm"
  let round_up := Wire.mk "fp_round_up"
  let rnd_cond_gates := [
    Gate.mkOR norm_R norm_S rs_or,
    Gate.mkOR norm_G rs_or grs_or,
    Gate.mkOR rs_or (norm_mant[0]!) rne_cand,
    Gate.mkAND norm_G rne_cand rne_up,
    Gate.mkOR norm_G rs_or any_rem,
    Gate.mkNOT s2_rsign not_sign,
    Gate.mkAND any_rem s2_rsign rdn_up,
    Gate.mkAND any_rem not_sign rup_up,
    Gate.mkNOT (s2_rm[0]!) not_rm0,
    Gate.mkNOT (s2_rm[1]!) not_rm1,
    Gate.mkNOT (s2_rm[2]!) not_rm2,
    Gate.mkAND not_rm2 not_rm1 grp_n2n1,
    Gate.mkAND grp_n2n1 (s2_rm[0]!) is_rtz,
    Gate.mkAND not_rm2 (s2_rm[1]!) grp_n2p1,
    Gate.mkAND grp_n2p1 not_rm0 is_rdn,
    Gate.mkAND grp_n2p1 (s2_rm[0]!) is_rup,
    Gate.mkAND (s2_rm[2]!) not_rm1 grp_p2n1,
    Gate.mkAND grp_p2n1 not_rm0 is_rmm,
    Gate.mkMUX rne_up rdn_up is_rdn up_rdn,
    Gate.mkMUX up_rdn rup_up is_rup up_rup,
    Gate.mkMUX up_rup norm_G is_rmm up_rmm,
    Gate.mkMUX up_rmm zero is_rtz round_up
  ]

  let norm_mant_inc := makeIndexedWires "fp_nm_inc" 23
  let norm_mant_c := makeIndexedWires "fp_nm_c" 24
  let norm_mant_inc_gates := [Gate.mkBUF round_up (norm_mant_c[0]!)] ++ (List.range 23).flatMap fun
    i =>
    [Gate.mkXOR (norm_mant[i]!) (norm_mant_c[i]!) (norm_mant_inc[i]!),
     Gate.mkAND (norm_mant[i]!) (norm_mant_c[i]!) (norm_mant_c[i + 1]!)]
  let norm_rollover := norm_mant_c[23]!
  let norm_not_roll := Wire.mk "fp_nm_nroll"
  let norm_mant_final := makeIndexedWires "fp_nm_fin" 23
  let norm_mant_final_gates := [Gate.mkNOT norm_rollover norm_not_roll] ++
    (List.range 23).map fun i =>
      Gate.mkAND (norm_mant_inc[i]!) norm_not_roll (norm_mant_final[i]!)

  let roll_inc := (List.range 10).map fun i =>
    if i == 0 then norm_rollover else zero
  let final_exp_r := makeIndexedWires "fp_fexpr" 10
  let (final_exp_r_gates, _) := mkKoggeStoneAdd final_exp roll_inc zero final_exp_r "fp_fexpradd"

  -- Overflow and underflow, mirroring FPMultiplierD: bit 9 is the sign of the
  -- exponent sum, bit 8 is a carry past the exponent field.
  let (exp8_all1, exp8_all1_gates) :=
    mkAndTree "mul_e8o" ((List.range 8).map fun i => final_exp_r[i]!)
  let not_neg_exp := Wire.mk "mul_nnege"
  let ovf_cand := Wire.mk "mul_ovf_cand"
  let is_overflow := Wire.mk "mul_ovf"
  let exp_neg := final_exp_r[9]!
  let ovf_unf_gates := [
    Gate.mkNOT exp_neg not_neg_exp,
    Gate.mkOR (final_exp_r[8]!) exp8_all1 ovf_cand,
    Gate.mkAND not_neg_exp ovf_cand is_overflow
  ]

  let packed := makeIndexedWires "mul_packed" 32
  let pack_gates := (List.range 32).map fun i =>
    if i < 23 then
      Gate.mkBUF (norm_mant_final[i]!) (packed[i]!)
    else if i < 31 then
      Gate.mkBUF (final_exp_r[i - 23]!) (packed[i]!)
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
            Gate.mkMUX ((p_prev[i]!)[k]!) ((p_prev[i + stride]!)[k]!) (v_prev[i + stride]!)
              ((p_new[i]!)[k]!)
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
  let sub_mant_inc_gates := [Gate.mkBUF sub_rnd_up (sub_mant_c[0]!)] ++ (List.range 23).flatMap (fun
    i =>
    [Gate.mkXOR (sub_mant[i]!) (sub_mant_c[i]!) (sub_mant_inc[i]!),
     Gate.mkAND (sub_mant[i]!) (sub_mant_c[i]!) (sub_mant_c[i + 1]!)]
  )
  let sub_rollover := sub_mant_c[23]!
  let sub_not_rollover := Wire.mk "fp_sub_nroll"
  let sub_final_mant := makeIndexedWires "fp_sub_fmant" 23
  let sub_final_mant_gates := [Gate.mkNOT sub_rollover sub_not_rollover] ++
    (List.range 23).map fun i => Gate.mkAND (sub_mant_inc[i]!) sub_not_rollover (sub_final_mant[i]!)

  let const_one_10 := [one_w] ++ (List.replicate 9 zero)
  let exp_plus_1 := makeIndexedWires "fp_eplus1" 10
  let (exp_plus1_gates, _) := mkKoggeStoneAdd s2_expub const_one_10 zero exp_plus_1 "fp_ep1"

  let lsh_ext10 := lshift_amt ++ [zero, zero, zero, zero]
  let sub_exp_pre := makeIndexedWires "fp_sub_epre" 10
  let (sub_exp_sub_gates, _) := mkKoggeStoneSub exp_plus_1 lsh_ext10 sub_exp_pre "fp_esub" one_w

  let roll_ext10 := [sub_rollover] ++ (List.replicate 9 zero)
  let sub_exp_final := makeIndexedWires "fp_sub_efin" 10
  let (sub_exp_roll_gates, _) := mkKoggeStoneAdd sub_exp_pre roll_ext10 zero sub_exp_final
    "fp_eroll"

  let sub_packed := makeIndexedWires "fp_sub_packed" 32
  let sub_pack_gates := (List.range 32).map fun i =>
    if i < 23 then Gate.mkBUF (sub_final_mant[i]!) (sub_packed[i]!)
    else if i < 31 then Gate.mkBUF (sub_exp_final[i - 23]!) (sub_packed[i]!)
    else Gate.mkBUF s2_rsign (sub_packed[i]!)

  -- ── Subnormal result ───────────────────────────────────────────────────────
  -- A product below the minimum normal is emitted with exponent field 0 and a
  -- mantissa counted in multiples of 2^-149.  sub_exp_pre is the biased exponent
  -- the product would have as a normal number, so 0 or less means the result is
  -- subnormal and the normalized product must be shifted down by (25 - E) to
  -- reach the quantum.
  --
  -- norm_prod enters with two low zeros appended, so the guard and round
  -- positions survive the shift and the shifter's sticky keeps the remainder
  -- below them.  A shift of 64 or more leaves zero.
  let sub_exp_neg := sub_exp_pre[9]!
  let (sub_exp_pre_or, sub_exp_pre_or_gates) := mkOrTree "mul_epre_or" sub_exp_pre
  let sub_exp_pre_zero := Wire.mk "mul_epre_zero"
  let sub_exp_le0 := Wire.mk "mul_epre_le0"
  let subnormal_res := Wire.mk "mul_subres"
  let not_ovf := Wire.mk "mul_not_ovf"
  let subres_gates := [
    Gate.mkNOT sub_exp_pre_or sub_exp_pre_zero,
    Gate.mkOR sub_exp_neg sub_exp_pre_zero sub_exp_le0,
    Gate.mkNOT is_overflow not_ovf,
    Gate.mkAND sub_exp_le0 not_ovf subnormal_res
  ]

  let zeros8 := (List.range 8).map fun _ => zero
  let sub_e8 := (List.range 8).map fun i => sub_exp_pre[i]!
  let abs_e := makeIndexedWires "mul_abse" 8
  let (abs_e_gates, _abs_e_borrow) := mkKoggeStoneSub zeros8 sub_e8 abs_e "mul_abse" one_w
  let const25 := (List.range 8).map fun i => if i == 0 || i == 3 || i == 4 then one_w else zero
  let sub_shift8 := makeIndexedWires "mul_subsh8" 8
  let (sub_shift8_gates, _sub_shift8_carry) :=
    mkKoggeStoneAdd abs_e const25 zero sub_shift8 "mul_subsh8"
  let sub_shift_over := Wire.mk "mul_subsh_over"
  let sub_shift_over_gate := Gate.mkOR (sub_shift8[6]!) (sub_shift8[7]!) sub_shift_over
  let sub_shift := makeIndexedWires "mul_subsh" 6
  let sub_shift_gates := (List.range 6).map fun i =>
    Gate.mkMUX (sub_shift8[i]!) one_w sub_shift_over (sub_shift[i]!)

  let sub_shift_in := [zero, zero] ++ norm_prod
  let sub_shifted := makeIndexedWires "mul_subshifted" 50
  let sub_sticky := Wire.mk "mul_substk"
  let sub_barrel_gates :=
    mkBarrelShiftRightSticky sub_shift_in sub_shift sub_shifted sub_sticky zero "mul_sbr"

  let sub2_R := sub_shifted[0]!
  let sub2_G := sub_shifted[1]!
  let sub2_mant := makeIndexedWires "mul_sub2mant" 23
  let sub2_mant_gates := (List.range 23).map fun i =>
    Gate.mkBUF (sub_shifted[2 + i]!) (sub2_mant[i]!)

  let sub2_rs_or := Wire.mk "mul_sub2_rs"
  let sub2_cand := Wire.mk "mul_sub2_cand"
  let sub2_rne := Wire.mk "mul_sub2_rne"
  let sub2_rem := Wire.mk "mul_sub2_rem"
  let sub2_rdn := Wire.mk "mul_sub2_rdn"
  let sub2_rup := Wire.mk "mul_sub2_rup"
  let sub2_t0 := Wire.mk "mul_sub2_t0"
  let sub2_t1 := Wire.mk "mul_sub2_t1"
  let sub2_round_pre := Wire.mk "mul_sub2_rpre"
  let sub2_round := Wire.mk "mul_sub2_round"
  let sub2_rnd_gates := [
    Gate.mkOR sub2_R sub_sticky sub2_rs_or,
    Gate.mkOR sub2_rs_or (sub2_mant[0]!) sub2_cand,
    Gate.mkAND sub2_G sub2_cand sub2_rne,
    Gate.mkOR sub2_G sub2_rs_or sub2_rem,
    Gate.mkAND sub2_rem s2_rsign sub2_rdn,
    Gate.mkAND sub2_rem not_sign sub2_rup,
    Gate.mkMUX sub2_rne sub2_rdn is_rdn sub2_t0,
    Gate.mkMUX sub2_t0 sub2_rup is_rup sub2_t1,
    Gate.mkMUX sub2_t1 sub2_G is_rmm sub2_round_pre,
    Gate.mkMUX sub2_round_pre zero is_rtz sub2_round
  ]

  let sub2_inc := makeIndexedWires "mul_sub2inc" 23
  let sub2_c := makeIndexedWires "mul_sub2c" 24
  let sub2_inc_gates := [Gate.mkBUF sub2_round (sub2_c[0]!)] ++ (List.range 23).flatMap fun i =>
    [Gate.mkXOR (sub2_mant[i]!) (sub2_c[i]!) (sub2_inc[i]!),
     Gate.mkAND (sub2_mant[i]!) (sub2_c[i]!) (sub2_c[i + 1]!)]
  let sub2_carry := sub2_c[23]!
  let sub2_not_carry := Wire.mk "mul_sub2ncarry"
  let sub2_final_mant := makeIndexedWires "mul_sub2fm" 23
  let sub2_final_mant_gates := [Gate.mkNOT sub2_carry sub2_not_carry] ++
    (List.range 23).map fun i =>
      Gate.mkAND (sub2_inc[i]!) sub2_not_carry (sub2_final_mant[i]!)

  -- Packing: exponent field 0, or 1 with a zero mantissa when rounding carried
  -- the mantissa up to the smallest normal.
  let sub2_packed := makeIndexedWires "mul_sub2packed" 32
  let sub2_pack_gates := (List.range 32).map fun i =>
    if i < 23 then Gate.mkBUF (sub2_final_mant[i]!) (sub2_packed[i]!)
    else if i < 31 then
      (if i == 23 then Gate.mkBUF sub2_carry (sub2_packed[i]!)
       else Gate.mkBUF zero (sub2_packed[i]!))
    else Gate.mkBUF s2_rsign (sub2_packed[i]!)

  -- A subnormal result is zero when the rounded mantissa is zero.
  let (sub2_mant_or, sub2_mant_or_gates) := mkOrTree "mul_sub2mor" sub2_final_mant
  let sub2_mz := Wire.mk "mul_sub2mz"
  let sub2_zero_pre := Wire.mk "mul_sub2zpre"
  let sub2_zero := Wire.mk "mul_sub2zero"
  let sub2_zero_gates := [
    Gate.mkNOT sub2_mant_or sub2_mz,
    Gate.mkAND subnormal_res sub2_not_carry sub2_zero_pre,
    Gate.mkAND sub2_zero_pre sub2_mz sub2_zero
  ]

  let packed_or_sub_in := makeIndexedWires "mul_psub_in" 32
  let packed_or_sub_in_gates := (List.range 32).map fun i =>
    Gate.mkMUX (packed[i]!) (sub_packed[i]!) s2_has_subnorm (packed_or_sub_in[i]!)
  let final_packed := makeIndexedWires "fp_fin_packed" 32
  let final_pack_gates := (List.range 32).map fun i =>
    Gate.mkMUX (packed_or_sub_in[i]!) (sub2_packed[i]!) subnormal_res (final_packed[i]!)

  -- NX (Inexact)
  let low23_bits := (List.range 23).map fun i => product[i]!
  let (low23_or, low23_or_gates) := mkOrTree "mul_low23" low23_bits
  let mul_extra_lost := Wire.mk "mul_extra_lost"
  let mul_nx := Wire.mk "mul_nx"
  let nx_gates := [
    Gate.mkAND (product[47]!) (product[23]!) mul_extra_lost,
    Gate.mkOR low23_or mul_extra_lost mul_nx
  ]

  -- The subnormal path takes its inexactness from the shifted-out remainder;
  -- the raw-product test above describes the normal path only.  An overflow is
  -- inexact too, and it is the only inexactness the normal path cannot see.
  let sub2_inexact := Wire.mk "mul_sub2inx"
  let sub2_inexact_gate := Gate.mkOR sub2_G sub2_rs_or sub2_inexact
  let nx_sel := Wire.mk "mul_nxsel"
  let nx_sel_gate := Gate.mkMUX mul_nx sub2_inexact subnormal_res nx_sel
  let nx_all := Wire.mk "mul_nx_all"
  let nx_of_gate := Gate.mkOR nx_sel is_overflow nx_all
  let mul_nx_final := Wire.mk "mul_nx_final"
  let nx_final_gate := Gate.mkAND nx_all not_special mul_nx_final

  -- Latch NV, special flags, inf/zero indicators through stage 2
  let s2_nv := Wire.mk "s2_nv"
  let s2_not_special := Wire.mk "s2_not_special"
  let s2_is_inf := Wire.mk "s2_is_inf"
  let s2_is_zero := Wire.mk "s2_is_zero"
  let s2_nan_res := Wire.mk "s2_nan_res"
  let s2_nv_dff := Gate.mkDFF mul_nv clock reset s2_nv
  let s2_nan_res_dff := Gate.mkDFF mul_nan_res clock reset s2_nan_res
  let s2_ns_dff := Gate.mkDFF not_special clock reset s2_not_special
  let s2_inf_dff := Gate.mkDFF any_special_or1 clock reset s2_is_inf
  let s2_zero_dff := Gate.mkDFF any_special_or2 clock reset s2_is_zero

  let final_nx := Wire.mk "mul_final_nx"
  let final_nx_gate := Gate.mkAND nx_all s2_not_special final_nx

  -- An underflowed product rounds to zero and an overflowed one is infinity,
  -- exactly as the zero/infinity overrides already treat a zero/inf input.
  let is_zero_sel := Wire.mk "mul_zsel"
  let is_inf_sel := Wire.mk "mul_isel"
  let is_ovf_max := Wire.mk "mul_ovfmax"
  let not_ovf_to_inf := Wire.mk "mul_novfinf"
  let ovf_to_inf := Wire.mk "mul_ovfinf"
  let sel_gates := [
    Gate.mkOR s2_is_zero sub2_zero is_zero_sel,
    -- IEEE 754 section 7.4: an overflowing product is an infinity only when the
    -- rounding direction points away from zero for this sign.  Toward zero is
    -- rtz always, rdn for a positive sign and rup for a negative sign; round to
    -- nearest counts as away.  The rest give the largest finite magnitude.
    Gate.mkAND is_rdn not_sign (Wire.mk "mul_tz_rdn"),
    Gate.mkAND is_rup s2_rsign (Wire.mk "mul_tz_rup"),
    Gate.mkOR is_rtz (Wire.mk "mul_tz_rdn") (Wire.mk "mul_tz_a"),
    Gate.mkOR (Wire.mk "mul_tz_a") (Wire.mk "mul_tz_rup") not_ovf_to_inf,
    Gate.mkNOT not_ovf_to_inf ovf_to_inf,
    Gate.mkAND is_overflow not_ovf_to_inf is_ovf_max,
    Gate.mkAND is_overflow ovf_to_inf (Wire.mk "mul_ovfinfsel"),
    Gate.mkOR s2_is_inf (Wire.mk "mul_ovfinfsel") is_inf_sel
  ]

  -- Step 1: zero override
  let zero_result := makeIndexedWires "mul_zero_res" 32
  let zero_override_gates := (List.range 32).map fun i =>
    if i < 31 then
      Gate.mkMUX (final_packed[i]!) zero is_zero_sel (zero_result[i]!)
    else
      Gate.mkBUF (final_packed[i]!) (zero_result[i]!)

  -- Step 2: saturate an overflown product to the largest finite magnitude.
  -- The exponent field is all ones minus one, so only its low bit (bit 23)
  -- differs from an infinity; the fraction becomes all ones.
  let sat_result := makeIndexedWires "mul_sat_res" 32
  let sat_override_gates := (List.range 32).map fun i =>
    if i == 31 then
      Gate.mkBUF (zero_result[31]!) (sat_result[31]!)  -- sign stays
    else if i == 23 then
      Gate.mkMUX (zero_result[i]!) zero is_ovf_max (sat_result[i]!)
    else
      Gate.mkMUX (zero_result[i]!) one_w is_ovf_max (sat_result[i]!)

  -- Step 3: inf override: if s2_is_inf, force exp=0xFF mant=0 (sign preserved)
  let inf_result := makeIndexedWires "mul_inf_res" 32
  let inf_override_gates := (List.range 32).map fun i =>
    if i < 23 then
      -- Inf has mant = 0
      Gate.mkMUX (sat_result[i]!) zero is_inf_sel (inf_result[i]!)
    else if i < 31 then
      -- Inf has exp = 0xFF (all ones)
      Gate.mkMUX (sat_result[i]!) one_w is_inf_sel (inf_result[i]!)
    else
      Gate.mkBUF (sat_result[i]!) (inf_result[i]!)  -- sign stays

  -- Step 3: NaN override: if s2_nan_res, force canonical NaN 0x7FC00000
  -- Write directly to the output `result` wires
  let nan_override_gates := (List.range 32).map fun i =>
    if i == 22 then
      -- Quiet NaN bit
      Gate.mkMUX (inf_result[i]!) one_w s2_nan_res (result[i]!)
    else if i < 22 then
      -- mant = 0 (except quiet bit)
      Gate.mkMUX (inf_result[i]!) zero s2_nan_res (result[i]!)
    else if i < 31 then
      -- exp = 0xFF
      Gate.mkMUX (inf_result[i]!) one_w s2_nan_res (result[i]!)
    else
      -- sign = 0 for canonical NaN
      Gate.mkMUX (inf_result[i]!) zero s2_nan_res (result[i]!)

  -- ══════════════════════════════════════════════
  -- Tag, valid, exception outputs
  -- ══════════════════════════════════════════════
  let tag_out_gates := (List.range 6).map fun i =>
    Gate.mkBUF (s2_tag[i]!) (tag_out[i]!)
  let valid_gate := [Gate.mkBUF s2_valid valid_out]
  -- fflags: bit0=NX bit1=UF bit2=OF bit3=DZ bit4=NV.  OF and UF used to be
  -- rm[i] & ~rm[i]; DZ stays 0 because a multiplier cannot divide by zero.
  let is_underflow := Wire.mk "mul_uf"
  let uf_gates := [
    -- UF needs a tiny and inexact result.  subnormal_res confirms tininess.
    Gate.mkAND subnormal_res sub2_inexact is_underflow
  ]
  let exc_gates := [
    Gate.mkBUF final_nx (exc[0]!),
    Gate.mkAND is_underflow s2_not_special (exc[1]!),
    Gate.mkAND is_overflow s2_not_special (exc[2]!),
    Gate.mkBUF zero (exc[3]!),
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
    nan_gates ++ snan_gates ++ inf_gates ++
    s1_exp1_any_gates ++ s1_exp2_any_gates ++
    zero_det_gates ++ subnorm_det_gates ++
    eff_ea_gates ++ eff_eb_gates ++
    exp_add_gates ++
    exp_sub_gates ++
    pp_gates ++
    csa_tree_gates ++
    nv_gates ++ special_gates ++
    -- Stage 2 DFFs (including exception latches)
    s2_dffs ++ [s2_nv_dff, s2_nan_res_dff, s2_ns_dff, s2_inf_dff, s2_zero_dff] ++
    -- Stage 2 combinational
    final_add_gates ++
    low23_or_gates ++ nx_gates ++ [sub2_inexact_gate, nx_sel_gate, nx_of_gate, nx_final_gate,
      final_nx_gate] ++
    uf_gates ++
    norm_mant_gates ++
    final_exp_gates ++ norm_S_a_gates ++ norm_S_b_gates ++ norm_grs_gates ++
    rnd_cond_gates ++ norm_mant_inc_gates ++ norm_mant_final_gates ++ final_exp_r_gates ++
    exp8_all1_gates ++ ovf_unf_gates ++
    pack_gates ++
    lz_all_gates ++ lsh_sub_gates ++ lshift_gates ++
    sub_S_gates ++ sub_rnd_gates ++ sub_mant_inc_gates ++ sub_final_mant_gates ++
    exp_plus1_gates ++ sub_exp_sub_gates ++ sub_exp_roll_gates ++
    sub_pack_gates ++
    sub_exp_pre_or_gates ++ subres_gates ++ abs_e_gates ++ sub_shift8_gates ++
    [sub_shift_over_gate] ++ sub_shift_gates ++ sub_barrel_gates ++ sub2_mant_gates ++
    sub2_rnd_gates ++ sub2_inc_gates ++ sub2_final_mant_gates ++ sub2_pack_gates ++
    sub2_mant_or_gates ++ sub2_zero_gates ++ packed_or_sub_in_gates ++ final_pack_gates ++
    -- Special result override: NaN > Inf > Zero > Normal
    sel_gates ++ zero_override_gates ++ sat_override_gates ++ inf_override_gates ++
      nan_override_gates ++
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
