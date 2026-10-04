/-
Circuits/Sequential/FPMultiplierD.lean - 4-Stage Pipelined Double-Precision FP Multiplier

IEEE 754 binary64 multiplication with pipelined datapath.

Pipeline stages:
  Stage 1a: Latch inputs -> Unpack + exponent addition + partial products + CSA tree levels 0-4
  Stage 1b: Latch intermediate CSA rows -> CSA tree levels 5-8
  Stage 2: Latch CSA result -> 106-bit CPA + normalize
  Stage 3: Latch normalized product -> Round + pack + special cases

Inputs (141):
  src1[63:0], src2[63:0] - FP operands
  rm[2:0]                - rounding mode
  dest_tag[5:0]          - physical register tag
  valid_in               - input valid
  clock, reset           - sequential control
  zero                   - constant low

Outputs (76):
  result[63:0]  - FP product
  tag_out[5:0]  - destination tag
  exc[4:0]      - exception flags
  valid_out     - output valid
-/

import Shoumei.DSL
import Shoumei.Components.Select
import Shoumei.Circuits.Combinational.KoggeStoneAdder
import Shoumei.Circuits.Combinational.Multiplier
import Shoumei.Circuits.Sequential.FPNormalize

namespace Shoumei.Circuits.Sequential

open Shoumei
open Shoumei.Components
open Shoumei.Circuits.Combinational

private def makeIndexedWires (pfx : String) (n : Nat) : List Wire :=
  (List.range n).map fun i => Wire.mk (pfx ++ "_" ++ toString i)

private def mkDFFBank (d_wires q_wires : List Wire) (clock reset : Wire) : List Gate :=
  List.zipWith (fun d q => Gate.mkDFF d clock reset q) d_wires q_wires

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

private def mkMuxBank (in0 in1 : List Wire) (sel : Wire) (out : List Wire) : List Gate :=
  (List.range in0.length).map fun i => Gate.mkMUX (in0[i]!) (in1[i]!) sel (out[i]!)


/-- Right barrel shifter that accumulates every bit shifted below position 0 into
    `sticky_out`, so a subnormal result keeps its guard/round window and the
    remainder below it stays visible. -/
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
  let copy_gates := (List.range w).map fun i => Gate.mkBUF (levels[6]!)[i]! output[i]!
  mux_gates ++ stk_gates ++ copy_gates ++ [Gate.mkBUF stickies[6]! sticky_out]

def mkFPMultiplierD : Circuit :=
  -- Input wires
  let src1 := makeIndexedWires "src1" 64
  let src2 := makeIndexedWires "src2" 64
  let rm := makeIndexedWires "rm" 3
  let dest_tag := makeIndexedWires "dest_tag" 6
  let valid_in := Wire.mk "valid_in"
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"

  -- Output wires
  let result := makeIndexedWires "result" 64
  let tag_out := makeIndexedWires "tag_out" 6
  let exc := makeIndexedWires "exc" 5
  let valid_out := Wire.mk "valid_out"

  -- Stage 1 pipeline registers (input -> stage 1)
  let s1_src1 := makeIndexedWires "s1_src1" 64
  let s1_src2 := makeIndexedWires "s1_src2" 64
  let s1_rm := makeIndexedWires "s1_rm" 3
  let s1_tag := makeIndexedWires "s1_tag" 6
  let s1_valid := Wire.mk "s1_valid"

  let s1_dffs :=
    mkDFFBank src1 s1_src1 clock reset ++
    mkDFFBank src2 s1_src2 clock reset ++
    mkDFFBank rm s1_rm clock reset ++
    mkDFFBank dest_tag s1_tag clock reset ++
    [Gate.mkDFF valid_in clock reset s1_valid]

  -- Stage 1 Combinational: Unpack + Exponent + CSA Tree
  let one_w := Wire.mk "muld_one"
  let one_gate := Gate.mkNOT zero one_w

  let s1_sign1 := s1_src1[63]!
  let s1_sign2 := s1_src2[63]!
  let prod_sign := Wire.mk "muld_prod_sign"
  let sign_gate := Gate.mkXOR s1_sign1 s1_sign2 prod_sign

  let exp1 := (List.range 11).map fun i => s1_src1[52 + i]!
  let exp2 := (List.range 11).map fun i => s1_src2[52 + i]!
  let frac1 := (List.range 52).map fun i => s1_src1[i]!
  let frac2 := (List.range 52).map fun i => s1_src2[i]!

  -- Classification of inputs
  let (exp1_any, exp1_any_gates) := mkOrTree "muld_e1a" exp1
  let (exp2_any, exp2_any_gates) := mkOrTree "muld_e2a" exp2
  let (exp1_all1, exp1_all1_gates) := mkAndTree "muld_e1o" exp1
  let (exp2_all1, exp2_all1_gates) := mkAndTree "muld_e2o" exp2
  let (frac1_nz, frac1_nz_gates) := mkOrTree "muld_f1nz" frac1
  let (frac2_nz, frac2_nz_gates) := mkOrTree "muld_f2nz" frac2

  let exp1_zero := Wire.mk "muld_e1z"
  let exp2_zero := Wire.mk "muld_e2z"
  let frac1_zero := Wire.mk "muld_f1z"
  let frac2_zero := Wire.mk "muld_f2z"
  let zero_det_gates := [
    Gate.mkNOT exp1_any exp1_zero,
    Gate.mkNOT exp2_any exp2_zero,
    Gate.mkNOT frac1_nz frac1_zero,
    Gate.mkNOT frac2_nz frac2_zero
  ]

  -- Special operand checks
  let is_nan1 := Wire.mk "muld_nan1"
  let is_nan2 := Wire.mk "muld_nan2"
  let either_nan := Wire.mk "muld_either_nan"
  let is_inf1 := Wire.mk "muld_inf1"
  let is_inf2 := Wire.mk "muld_inf2"
  let either_inf := Wire.mk "muld_either_inf"
  let is_zero1 := Wire.mk "muld_zero1"
  let is_zero2 := Wire.mk "muld_zero2"
  let either_zero := Wire.mk "muld_either_zero"
  let inf1_zero2 := Wire.mk "muld_inf1_zero2"
  let zero1_inf2 := Wire.mk "muld_zero1_inf2"
  let inf_zero := Wire.mk "muld_inf_zero"
  let not_f1_51 := Wire.mk "muld_nf1_51"
  let not_f2_51 := Wire.mk "muld_nf2_51"
  let is_snan1 := Wire.mk "muld_snan1"
  let is_snan2 := Wire.mk "muld_snan2"
  let either_snan := Wire.mk "muld_either_snan"

  let s1_nv := Wire.mk "s1_nv"
  let s1_nan_res := Wire.mk "s1_nan_res"
  let s1_inf_res := Wire.mk "s1_inf_res"
  let s1_zero_res := Wire.mk "s1_zero_res"
  let s1_any_special_0 := Wire.mk "s1_as_0"
  let s1_any_special := Wire.mk "s1_any_special"
  let s1_not_special := Wire.mk "s1_not_special"

  let spec_det_gates := [
    Gate.mkAND exp1_all1 frac1_nz is_nan1,
    Gate.mkAND exp2_all1 frac2_nz is_nan2,
    Gate.mkOR is_nan1 is_nan2 either_nan,
    Gate.mkAND exp1_all1 frac1_zero is_inf1,
    Gate.mkAND exp2_all1 frac2_zero is_inf2,
    Gate.mkOR is_inf1 is_inf2 either_inf,
    Gate.mkAND exp1_zero frac1_zero is_zero1,
    Gate.mkAND exp2_zero frac2_zero is_zero2,
    Gate.mkOR is_zero1 is_zero2 either_zero,
    Gate.mkAND is_inf1 is_zero2 inf1_zero2,
    Gate.mkAND is_zero1 is_inf2 zero1_inf2,
    Gate.mkOR inf1_zero2 zero1_inf2 inf_zero,
    Gate.mkNOT (frac1[51]!) not_f1_51,
    Gate.mkNOT (frac2[51]!) not_f2_51,
    Gate.mkAND is_nan1 not_f1_51 is_snan1,
    Gate.mkAND is_nan2 not_f2_51 is_snan2,
    Gate.mkOR is_snan1 is_snan2 either_snan,
    Gate.mkOR either_snan inf_zero s1_nv,
    Gate.mkOR either_nan inf_zero s1_nan_res,
    Gate.mkBUF either_inf s1_inf_res,
    Gate.mkBUF either_zero s1_zero_res,
    Gate.mkOR s1_nan_res s1_inf_res s1_any_special_0,
    Gate.mkOR s1_any_special_0 s1_zero_res s1_any_special,
    Gate.mkNOT s1_any_special s1_not_special
  ]

  -- ── Operand normalization ──────────────────────────────────────────────────
  -- A nonzero subnormal operand has no implicit bit, so its fraction must be
  -- shifted up until its leading one reaches the implicit position and its
  -- exponent lowered by that shift.  That puts both mantissas in [1, 2), which
  -- is what the partial-product tree and the one-bit result normalization
  -- assume.  A normal operand shifts by nothing; a zero operand is overridden by
  -- the special-case result either way.
  let pos1 := makeIndexedWires "muld_pos1" 6
  let pos2 := makeIndexedWires "muld_pos2" 6
  let (pos1_w, lead1_gates) := mkLeadPos "muld_lz1" frac1 zero 6
  let (pos2_w, lead2_gates) := mkLeadPos "muld_lz2" frac2 zero 6
  let pos1_gates := (List.range 6).map fun i => Gate.mkBUF (pos1_w[i]!) (pos1[i]!)
  let pos2_gates := (List.range 6).map fun i => Gate.mkBUF (pos2_w[i]!) (pos2[i]!)
  let const52 := (List.range 6).map fun i => if i == 2 || i == 4 || i == 5 then one_w else zero
  let sh1 := makeIndexedWires "muld_sh1" 6
  let sh2 := makeIndexedWires "muld_sh2" 6
  let (sh1_gates, _sh1_borrow) := mkKoggeStoneSub const52 pos1 sh1 "muld_sh1sub" one_w
  let (sh2_gates, _sh2_borrow) := mkKoggeStoneSub const52 pos2 sh2 "muld_sh2sub" one_w

  let nsub1 := Wire.mk "muld_ns1"
  let nsub2 := Wire.mk "muld_ns2"
  let e1_sub := Wire.mk "muld_e1s"
  let e2_sub := Wire.mk "muld_e2s"
  let sub_op_gates := [
    Gate.mkNOT exp1_any nsub1,
    Gate.mkNOT exp2_any nsub2,
    Gate.mkAND nsub1 frac1_nz e1_sub,
    Gate.mkAND nsub2 frac2_nz e2_sub
  ]

  let norm1_pre := makeIndexedWires "muld_nm1p" 53
  let norm2_pre := makeIndexedWires "muld_nm2p" 53
  let norm1_gates := mkBarrelShiftLeft (((List.range 52).map fun i => frac1[i]!) ++ [zero]) sh1
    norm1_pre zero "muld_bsl1"
  let norm2_gates := mkBarrelShiftLeft (((List.range 52).map fun i => frac2[i]!) ++ [zero]) sh2
    norm2_pre zero "muld_bsl2"

  let mant1 := makeIndexedWires "muld_mant1" 53
  let mant2 := makeIndexedWires "muld_mant2" 53
  let mant_norm_gates := (List.range 53).flatMap fun i =>
    let implicit1 := if i == 52 then exp1_any else frac1[i]!
    let implicit2 := if i == 52 then exp2_any else frac2[i]!
    [Gate.mkMUX implicit1 (norm1_pre[i]!) e1_sub (mant1[i]!),
     Gate.mkMUX implicit2 (norm2_pre[i]!) e2_sub (mant2[i]!)]

  -- Effective exponents in the 13-bit path: 1 - shift for a subnormal operand,
  -- the raw field (which is unsigned, hence zero-extended) otherwise.  The
  -- subtracted form is signed, so it is computed at full width.
  let one13 := (List.range 13).map fun i => if i == 0 then one_w else zero
  let sh1_13 := (List.range 13).map fun i => if i < 6 then sh1[i]! else zero
  let sh2_13 := (List.range 13).map fun i => if i < 6 then sh2[i]! else zero
  let eff1_13 := makeIndexedWires "muld_eff1" 13
  let eff2_13 := makeIndexedWires "muld_eff2" 13
  let (eff1_gates, _eff1_borrow) := mkSubFor (AdderSpec.minArea 13 .one) one13 sh1_13 eff1_13
    "muld_eff1s" one_w
  let (eff2_gates, _eff2_borrow) := mkSubFor (AdderSpec.minArea 13 .one) one13 sh2_13 eff2_13
    "muld_eff2s" one_w
  let exp1_13 := makeIndexedWires "muld_exp1_13" 13
  let exp2_13 := makeIndexedWires "muld_exp2_13" 13
  let exp_norm_gates := (List.range 13).flatMap fun i =>
    let raw1 := if i < 11 then exp1[i]! else zero
    let raw2 := if i < 11 then exp2[i]! else zero
    [Gate.mkMUX raw1 (eff1_13[i]!) e1_sub (exp1_13[i]!),
     Gate.mkMUX raw2 (eff2_13[i]!) e2_sub (exp2_13[i]!)]

  let exp_sum13 := makeIndexedWires "muld_esum" 13
  let (exp_add_gates, _) := mkAddFor (AdderSpec.minArea exp1_13.length .none) exp1_13 exp2_13 zero
    exp_sum13 "muld_eadd"
  let bias13 := (List.range 13).map fun i => if i < 10 then one_w else zero
  let exp_ub13 := makeIndexedWires "muld_eub" 13
  let (exp_sub_gates, _) := mkSubFor (AdderSpec.minArea exp_sum13.length .one) exp_sum13 bias13
    exp_ub13 "muld_esub" one_w

  -- 53 partial products of 106 bits
  let pp_rows := (List.range 53).map fun j =>
    let pp := makeIndexedWires s!"muld_pp{j}" 106
    (pp, (List.range 106).map fun i =>
      if i >= j && i < j + 53 then
        Gate.mkAND (mant1[i - j]!) (mant2[j]!) (pp[i]!)
      else
        Gate.mkBUF zero (pp[i]!))
  let pp_wires := pp_rows.map (·.1)
  let pp_gates := pp_rows.map (·.2) |>.flatten

  -- CSA Tree Level 0-4: 53 rows -> 8 rows (106 bits each)
  let (csa_p1_rows, csa_tree_gates1, csa_instances1) :=
    mkCSATreeToDepth pp_wires zero 5 106 0

  -- Stage 1b Pipeline Registers: Latch 8 CSA rows + control signals
  let s1b_sign := Wire.mk "s1b_sign"
  let s1b_expub := makeIndexedWires "s1b_expub" 13
  let s1b_rm := makeIndexedWires "s1b_rm" 3
  let s1b_tag := makeIndexedWires "s1b_tag" 6
  let s1b_valid := Wire.mk "s1b_valid"
  let s1b_nv := Wire.mk "s1b_nv"
  let s1b_nan_res := Wire.mk "s1b_nan_res"
  let s1b_inf_res := Wire.mk "s1b_inf_res"
  let s1b_zero_res := Wire.mk "s1b_zero_res"
  let s1b_not_special := Wire.mk "s1b_not_special"
  let s1b_csa_rows := (List.range 8).map fun r => makeIndexedWires s!"s1b_csa_r{r}" 106

  let s1b_csa_dffs := (List.range 8).flatMap fun r =>
    mkDFFBank (csa_p1_rows[r]!) (s1b_csa_rows[r]!) clock reset

  let s1b_dffs :=
    [Gate.mkDFF prod_sign clock reset s1b_sign] ++
    mkDFFBank exp_ub13 s1b_expub clock reset ++
    s1b_csa_dffs ++
    mkDFFBank s1_rm s1b_rm clock reset ++
    mkDFFBank s1_tag s1b_tag clock reset ++
    [Gate.mkDFF s1_valid clock reset s1b_valid,
     Gate.mkDFF s1_nv clock reset s1b_nv,
     Gate.mkDFF s1_nan_res clock reset s1b_nan_res,
     Gate.mkDFF s1_inf_res clock reset s1b_inf_res,
     Gate.mkDFF s1_zero_res clock reset s1b_zero_res,
     Gate.mkDFF s1_not_special clock reset s1b_not_special]

  -- Stage 1b Combinational: CSA Tree Level 5-8: 8 rows -> 2 rows (106 bits each)
  let (csa_sum, csa_carry, csa_tree_gates2, csa_instances2) :=
    mkCSATreeHierarchical s1b_csa_rows zero 106 5

  -- Stage 2 Pipeline Registers
  let s2_sign := Wire.mk "s2_sign"
  let s2_expub := makeIndexedWires "s2_expub" 13
  let s2_csa_sum := makeIndexedWires "s2_csa_sum" 106
  let s2_csa_carry := makeIndexedWires "s2_csa_carry" 106
  let s2_rm := makeIndexedWires "s2_rm" 3
  let s2_tag := makeIndexedWires "s2_tag" 6
  let s2_valid := Wire.mk "s2_valid"
  let s2_nv := Wire.mk "s2_nv"
  let s2_nan_res := Wire.mk "s2_nan_res"
  let s2_inf_res := Wire.mk "s2_inf_res"
  let s2_zero_res := Wire.mk "s2_zero_res"
  let s2_not_special := Wire.mk "s2_not_special"

  let s2_dffs :=
    [Gate.mkDFF s1b_sign clock reset s2_sign] ++
    mkDFFBank s1b_expub s2_expub clock reset ++
    mkDFFBank csa_sum s2_csa_sum clock reset ++
    mkDFFBank csa_carry s2_csa_carry clock reset ++
    mkDFFBank s1b_rm s2_rm clock reset ++
    mkDFFBank s1b_tag s2_tag clock reset ++
    [Gate.mkDFF s1b_valid clock reset s2_valid,
     Gate.mkDFF s1b_nv clock reset s2_nv,
     Gate.mkDFF s1b_nan_res clock reset s2_nan_res,
     Gate.mkDFF s1b_inf_res clock reset s2_inf_res,
     Gate.mkDFF s1b_zero_res clock reset s2_zero_res,
     Gate.mkDFF s1b_not_special clock reset s2_not_special]

  -- Stage 2 Combinational: Final CPA + Normalization
  let product := makeIndexedWires "muld_prod" 106
  let cpa_inst : CircuitInstance := {
    moduleName := adderModule (AdderSpec.minDelay 106 .none)
    instName := "u_cpa"
    portMap :=
      (s2_csa_sum.enum.map (fun ⟨i, w⟩ => (s!"a[{i}]", w))) ++
      (s2_csa_carry.enum.map (fun ⟨i, w⟩ => (s!"b[{i}]", w))) ++
      (product.enum.map (fun ⟨i, w⟩ => (s!"sum[{i}]", w)))
  }

  -- Normalization shift: if product[105] is 1, shift right 1
  let is_shift := product[105]!
  let mant_shifted := (List.range 52).map fun i => product[53 + i]!
  let mant_unshifted := (List.range 52).map fun i => product[52 + i]!
  let pre_mant_comb := makeIndexedWires "muld_pre_mant_c" 52
  let pre_mant_gates := mkMuxBank mant_unshifted mant_shifted is_shift pre_mant_comb

  let g_bit_comb := Wire.mk "muld_g_c"
  let r_bit_comb := Wire.mk "muld_r_c"
  let g_gate := Gate.mkMUX (product[51]!) (product[52]!) is_shift g_bit_comb
  let r_gate := Gate.mkMUX (product[50]!) (product[51]!) is_shift r_bit_comb

  let s_extra := Wire.mk "muld_s_extra"
  let s_extra_gate := Gate.mkAND is_shift (product[50]!) s_extra

  let low50 := (List.range 50).map fun i => product[i]!
  let (s_low50, s_low50_gates) := mkOrTree "muld_low50" low50
  let s_bit_comb := Wire.mk "muld_s_c"
  let s_gate := Gate.mkOR s_low50 s_extra s_bit_comb

  -- Exponent adjustment by shift: exp_adj = s2_expub + is_shift
  let exp_inc_13 := [is_shift] ++ (List.replicate 12 zero)
  let exp_adj13_comb := makeIndexedWires "muld_eadj_c" 13
  let (exp_adj_gates, _) := mkKoggeStoneAdd s2_expub exp_inc_13 zero exp_adj13_comb "muld_eadj"

  -- Stage 3 Pipeline Registers: Latch intermediate normalized product and status
  let s3_pre_mant := makeIndexedWires "s3_pre_mant" 52
  let s3_g := Wire.mk "s3_g"
  let s3_r := Wire.mk "s3_r"
  let s3_s := Wire.mk "s3_s"
  let s3_exp_adj13 := makeIndexedWires "s3_exp_adj13" 13
  let s3_sign := Wire.mk "s3_sign"
  let s3_rm := makeIndexedWires "s3_rm" 3
  let s3_tag := makeIndexedWires "s3_tag" 6
  let s3_valid := Wire.mk "s3_valid"
  let s3_nv := Wire.mk "s3_nv"
  let s3_nan_res := Wire.mk "s3_nan_res"
  let s3_inf_res := Wire.mk "s3_inf_res"
  let s3_zero_res := Wire.mk "s3_zero_res"
  let s3_not_special := Wire.mk "s3_not_special"

  let s3_dffs :=
    mkDFFBank pre_mant_comb s3_pre_mant clock reset ++
    [Gate.mkDFF g_bit_comb clock reset s3_g,
     Gate.mkDFF r_bit_comb clock reset s3_r,
     Gate.mkDFF s_bit_comb clock reset s3_s] ++
    mkDFFBank exp_adj13_comb s3_exp_adj13 clock reset ++
    [Gate.mkDFF s2_sign clock reset s3_sign] ++
    mkDFFBank s2_rm s3_rm clock reset ++
    mkDFFBank s2_tag s3_tag clock reset ++
    [Gate.mkDFF s2_valid clock reset s3_valid,
     Gate.mkDFF s2_nv clock reset s3_nv,
     Gate.mkDFF s2_nan_res clock reset s3_nan_res,
     Gate.mkDFF s2_inf_res clock reset s3_inf_res,
     Gate.mkDFF s2_zero_res clock reset s3_zero_res,
     Gate.mkDFF s2_not_special clock reset s3_not_special]

  -- Stage 3 Combinational: Rounding + Format Packing + Special Cases
  let pre_mant := s3_pre_mant
  let g_bit := s3_g
  let r_bit := s3_r
  let s_bit := s3_s
  let exp_adj13 := s3_exp_adj13
  let s2_sign := s3_sign
  let s2_rm := s3_rm
  let s2_tag := s3_tag
  let s2_valid := s3_valid
  let s2_nv := s3_nv
  let s2_nan_res := s3_nan_res
  let s2_inf_res := s3_inf_res
  let s2_zero_res := s3_zero_res
  let s2_not_special := s3_not_special

  -- Rounding mode decoding
  let rm0 := s2_rm[0]!
  let rm1 := s2_rm[1]!
  let rm2 := s2_rm[2]!
  let n_rm0 := Wire.mk "muld_nrm0"
  let n_rm1 := Wire.mk "muld_nrm1"
  let n_rm2 := Wire.mk "muld_nrm2"
  let rm_inv_gates := [Gate.mkNOT rm0 n_rm0, Gate.mkNOT rm1 n_rm1, Gate.mkNOT rm2 n_rm2]

  let is_rm0_0 := Wire.mk "muld_rm0_0"
  let is_rm0 := Wire.mk "muld_is_rm0"  -- 000 (RNE)
  let is_rm2_0 := Wire.mk "muld_rm2_0"
  let is_rm2 := Wire.mk "muld_is_rm2"  -- 010 (RDN)
  let is_rm3_0 := Wire.mk "muld_rm3_0"
  let is_rm3 := Wire.mk "muld_is_rm3"  -- 011 (RUP)
  let is_rm4_0 := Wire.mk "muld_rm4_0"
  let is_rm4 := Wire.mk "muld_is_rm4"  -- 100 (RMM)
  let is_rm7_0 := Wire.mk "muld_rm7_0"
  let is_rm7 := Wire.mk "muld_is_rm7"  -- 111 (dyn -> RNE)
  let rm_dec_gates := [
    Gate.mkAND n_rm2 n_rm1 is_rm0_0,
    Gate.mkAND is_rm0_0 n_rm0 is_rm0,
    Gate.mkAND n_rm2 rm1 is_rm2_0,
    Gate.mkAND is_rm2_0 n_rm0 is_rm2,
    Gate.mkAND n_rm2 rm1 is_rm3_0,
    Gate.mkAND is_rm3_0 rm0 is_rm3,
    Gate.mkAND rm2 n_rm1 is_rm4_0,
    Gate.mkAND is_rm4_0 n_rm0 is_rm4,
    Gate.mkAND rm2 rm1 is_rm7_0,
    Gate.mkAND is_rm7_0 rm0 is_rm7
  ]

  -- Rounding condition
  let grs_or := Wire.mk "muld_grs_or"
  let rs_or := Wire.mk "muld_rs_or"
  let gr_or := Wire.mk "muld_gr_or"
  let rne_cand := Wire.mk "muld_rne_cand"
  let rne_up := Wire.mk "muld_rne_up"
  let not_s2_sign := Wire.mk "muld_nsign"
  let rdn_up := Wire.mk "muld_rdn_up"
  let rup_up := Wire.mk "muld_rup_up"
  let rmm_up := g_bit
  let rne_active := Wire.mk "muld_rne_act"
  let rne_term := Wire.mk "muld_rne_term"
  let rdn_term := Wire.mk "muld_rdn_term"
  let rup_term := Wire.mk "muld_rup_term"
  let rmm_term := Wire.mk "muld_rmm_term"
  let rnd_t01 := Wire.mk "muld_rt01"
  let rnd_t23 := Wire.mk "muld_rt23"
  let round_up := Wire.mk "muld_round_up"
  let ovf_to_inf := Wire.mk "muld_ovfinf"

  let rnd_cond_gates := [
    Gate.mkOR g_bit r_bit gr_or,
    Gate.mkOR gr_or s_bit grs_or,
    Gate.mkOR r_bit s_bit rs_or,
    Gate.mkOR rs_or (pre_mant[0]!) rne_cand,
    Gate.mkAND g_bit rne_cand rne_up,
    Gate.mkNOT s2_sign not_s2_sign,
    Gate.mkAND s2_sign grs_or rdn_up,
    Gate.mkAND not_s2_sign grs_or rup_up,
    Gate.mkOR is_rm0 is_rm7 rne_active,
    Gate.mkAND rne_active rne_up rne_term,
    Gate.mkAND is_rm2 rdn_up rdn_term,
    Gate.mkAND is_rm3 rup_up rup_term,
    Gate.mkAND is_rm4 rmm_up rmm_term,
    Gate.mkOR rne_term rdn_term rnd_t01,
    Gate.mkOR rup_term rmm_term rnd_t23,
    Gate.mkOR rnd_t01 rnd_t23 round_up,
    -- IEEE 754 section 7.4: overflow gives an infinity only when the rounding
    -- direction points away from zero for this sign, and round to nearest
    -- counts as away.  Every other mode gives the largest finite magnitude.
    -- Away from zero is rdn for a negative product and rup for a positive one.
    Gate.mkAND s2_sign is_rm2 (Wire.mk "muld_ovf_srdn"),
    Gate.mkAND not_s2_sign is_rm3 (Wire.mk "muld_ovf_nrup"),
    Gate.mkOR is_rm0 is_rm7 (Wire.mk "muld_ovf_rne"),
    Gate.mkOR (Wire.mk "muld_ovf_rne") is_rm4 (Wire.mk "muld_ovf_nr"),
    Gate.mkOR (Wire.mk "muld_ovf_nr") (Wire.mk "muld_ovf_srdn") (Wire.mk "muld_ovf_dir"),
    Gate.mkOR (Wire.mk "muld_ovf_dir") (Wire.mk "muld_ovf_nrup") ovf_to_inf
  ]

  -- Mantissa increment: pre_mant + round_up (52 bits)
  let mant_inc := makeIndexedWires "muld_minc" 52
  let mant_inc_c := makeIndexedWires "muld_minc_c" 53
  let mant_inc_gates := [Gate.mkBUF round_up (mant_inc_c[0]!)] ++ (List.range 52).flatMap (fun i =>
    [Gate.mkXOR (pre_mant[i]!) (mant_inc_c[i]!) (mant_inc[i]!),
     Gate.mkAND (pre_mant[i]!) (mant_inc_c[i]!) (mant_inc_c[i + 1]!)]
  )
  let mant_rollover := mant_inc_c[52]!

  let final_mant := makeIndexedWires "muld_fmant" 52
  let not_rollover := Wire.mk "muld_nroll"
  let final_mant_gates := [Gate.mkNOT mant_rollover not_rollover] ++
    (List.range 52).map fun i => Gate.mkAND (mant_inc[i]!) not_rollover (final_mant[i]!)

  -- Exponent increment on rollover
  let exp_roll_13 := [mant_rollover] ++ (List.replicate 12 zero)
  let exp_final13 := makeIndexedWires "muld_efinal" 13
  let (exp_final_gates, _) := mkKoggeStoneAdd exp_adj13 exp_roll_13 zero exp_final13 "muld_efinal"

  -- Normal result: packed {sign, exp_final13[10:0], final_mant[51:0]}
  let norm_res := makeIndexedWires "muld_norm_res" 64
  let norm_res_gates :=
    (List.range 52).map (fun i => Gate.mkBUF (final_mant[i]!) (norm_res[i]!)) ++
    (List.range 11).map (fun i => Gate.mkBUF (exp_final13[i]!) (norm_res[52 + i]!)) ++
    [Gate.mkBUF s2_sign (norm_res[63]!)]

  -- ── Subnormal result ───────────────────────────────────────────────────────
  -- A product below the minimum normal is emitted with exponent field 0 and a
  -- mantissa counted in multiples of 2^-1074.  exp_adj13 is the biased exponent
  -- the product would have as a normal number, so 0 or less selects that pack:
  -- the normalized mantissa's guard/round window is shifted down by (4 - E) and
  -- the shifted-out bits feed the sticky.
  let (exp_adj_any, exp_adj_any_gates) := mkOrTree "muld_eadj_or" exp_adj13
  let exp_adj_zero := Wire.mk "muld_eadj_z"
  let exp_adj_le0 := Wire.mk "muld_eadj_le0"
  let exp_adj_neg := exp_adj13[12]!
  let subnormal_res := Wire.mk "muld_subres"

  -- Window: implicit one at 55, fraction at [54:3], guard/round/sticky at [2:0].
  let sub_window := makeIndexedWires "muld_subwin" 56
  let sub_window_gates := [
    Gate.mkBUF s_bit (sub_window[0]!),
    Gate.mkBUF r_bit (sub_window[1]!),
    Gate.mkBUF g_bit (sub_window[2]!),
    Gate.mkBUF one_w (sub_window[55]!)
  ] ++ (List.range 52).map fun i => Gate.mkBUF (pre_mant[i]!) (sub_window[3 + i]!)

  let four_13 := (List.range 13).map fun i => if i == 2 then one_w else zero
  let sub_shift13 := makeIndexedWires "muld_subsh13" 13
  let (sub_shift13_gates, _sub_shift13_borrow) :=
    mkKoggeStoneSub four_13 exp_adj13 sub_shift13 "muld_subsh13" one_w
  let (sub_over, sub_over_gates) := mkOrTree "muld_subover" ((List.range 7).map fun i =>
    sub_shift13[6 + i]!)
  let sub_shift := makeIndexedWires "muld_subsh" 6
  let sub_shift_gates := (List.range 6).map fun i =>
    Gate.mkMUX (sub_shift13[i]!) one_w sub_over (sub_shift[i]!)

  let sub_in := [zero, zero] ++ sub_window
  let sub_shifted := makeIndexedWires "muld_subshifted" 58
  let sub_sticky_shift := Wire.mk "muld_substk"
  let sub_barrel_gates :=
    mkBarrelShiftRightSticky sub_in sub_shift sub_shifted sub_sticky_shift zero "muld_sbr"
  let sub_R := sub_shifted[0]!
  let sub_G := sub_shifted[1]!
  let sub_mant := makeIndexedWires "muld_submant" 52
  let sub_mant_gates := (List.range 52).map fun i =>
    Gate.mkBUF (sub_shifted[2 + i]!) (sub_mant[i]!)

  let sub_rs_or := Wire.mk "muld_subrs"
  let sub_rne := Wire.mk "muld_subrne"
  let sub_rne_up := Wire.mk "muld_subrnu"
  let sub_any_rem := Wire.mk "muld_subany"
  let sub_rdn := Wire.mk "muld_subrdn"
  let sub_rup := Wire.mk "muld_subrup"
  let sub_t0 := Wire.mk "muld_subt0"
  let sub_t1 := Wire.mk "muld_subt1"
  let sub_round_pre := Wire.mk "muld_subrpre"
  let sub_round := Wire.mk "muld_subround"
  let sub_rnd_gates := [
    Gate.mkOR sub_R sub_sticky_shift sub_rs_or,
    Gate.mkOR sub_rs_or (sub_mant[0]!) sub_rne,
    Gate.mkAND sub_G sub_rne sub_rne_up,
    Gate.mkOR sub_G sub_rs_or sub_any_rem,
    Gate.mkAND sub_any_rem s2_sign sub_rdn,
    Gate.mkAND sub_any_rem not_s2_sign sub_rup,
    Gate.mkMUX sub_rne_up sub_rdn is_rm2 sub_t0,
    Gate.mkMUX sub_t0 sub_rup is_rm3 sub_t1,
    Gate.mkMUX sub_t1 sub_G is_rm4 sub_round_pre,
    Gate.mkMUX sub_round_pre zero (Wire.mk "muld_is_rtz") sub_round
  ]
  let not_rtz := Wire.mk "muld_is_rtz"
  let not_rtz_gates := [Gate.mkAND n_rm2 n_rm1 (Wire.mk "muld_rtz_pre"),
                        Gate.mkAND (Wire.mk "muld_rtz_pre") rm0 not_rtz]

  let sub_inc := makeIndexedWires "muld_subinc" 52
  let sub_c := makeIndexedWires "muld_subc" 53
  let sub_inc_gates := [Gate.mkBUF sub_round (sub_c[0]!)] ++ (List.range 52).flatMap fun i =>
    [Gate.mkXOR (sub_mant[i]!) (sub_c[i]!) (sub_inc[i]!),
     Gate.mkAND (sub_mant[i]!) (sub_c[i]!) (sub_c[i + 1]!)]
  let sub_carry := sub_c[52]!
  let sub_not_carry := Wire.mk "muld_subncarry"
  let sub_final_mant := makeIndexedWires "muld_subfm" 52
  let sub_final_mant_gates := [Gate.mkNOT sub_carry sub_not_carry] ++
    (List.range 52).map fun i =>
      Gate.mkAND (sub_inc[i]!) sub_not_carry (sub_final_mant[i]!)
  let (sub_mant_any, sub_mant_any_gates) := mkOrTree "muld_submany" sub_final_mant
  let sub_mant_nz := Wire.mk "muld_submnz"
  let sub_zero_pre := Wire.mk "muld_subzpre"
  let sub_zero := Wire.mk "muld_subzero"
  let sub_zero_gates := [
    Gate.mkNOT sub_mant_any sub_mant_nz,
    Gate.mkAND subnormal_res sub_not_carry sub_zero_pre,
    Gate.mkAND sub_zero_pre sub_mant_nz sub_zero
  ]
  let sub_exp_final := makeIndexedWires "muld_subexp" 11
  let sub_exp_gates := (List.range 11).map fun i =>
    if i == 0 then Gate.mkBUF sub_carry (sub_exp_final[i]!)
    else Gate.mkBUF zero (sub_exp_final[i]!)

  let sub_neg_gates := [
    Gate.mkNOT exp_adj_any exp_adj_zero,
    Gate.mkOR exp_adj_zero exp_adj_neg exp_adj_le0,
    Gate.mkBUF exp_adj_le0 subnormal_res
  ]

  -- Normal versus subnormal, before the zero/inf/NaN overrides.
  let res_l0 := makeIndexedWires "muld_res_l0" 64
  let l0_gates := (List.range 64).map fun i =>
    if i == 63 then Gate.mkBUF (norm_res[63]!) (res_l0[63]!)
    else if i < 52 then
      Gate.mkMUX (norm_res[i]!) (sub_final_mant[i]!) subnormal_res (res_l0[i]!)
    else
      Gate.mkMUX (norm_res[i]!) (sub_exp_final[i - 52]!) subnormal_res (res_l0[i]!)

  -- Overflow and Underflow detection
  let (exp11_all1, exp11_all1_gates) := mkAndTree "muld_e11o" ((List.range 11).map fun i =>
    exp_final13[i]!)
  let not_neg_exp := Wire.mk "muld_nnege"
  let ovf_cand := Wire.mk "muld_ovf_cand"
  let is_overflow := Wire.mk "muld_ovf"
  let is_underflow := Wire.mk "muld_uf"

  let ovf_unf_gates := [
    Gate.mkNOT (exp_final13[12]!) not_neg_exp,
    Gate.mkOR (exp_final13[11]!) exp11_all1 ovf_cand,
    Gate.mkAND not_neg_exp ovf_cand is_overflow,
    -- UF needs a tiny and inexact result.  subnormal_res confirms tininess.
    -- Any remainder sets inexact.
    Gate.mkAND subnormal_res sub_any_rem is_underflow
  ]

  -- Special result values
  let is_zero_sel := Wire.mk "muld_zsel"
  let is_inf_sel := Wire.mk "muld_isel"
  let is_ovf_max := Wire.mk "muld_ovfmax"
  let not_ovf_to_inf := Wire.mk "muld_novfinf"
  let sel_gates := [
    Gate.mkOR s2_zero_res sub_zero is_zero_sel,
    -- An overflowing product is an infinity only under a direction that points
    -- away from zero; the other modes saturate to the largest finite magnitude.
    Gate.mkNOT ovf_to_inf not_ovf_to_inf,
    Gate.mkAND is_overflow not_ovf_to_inf is_ovf_max,
    Gate.mkAND is_overflow ovf_to_inf (Wire.mk "muld_ovfinfsel"),
    Gate.mkOR s2_inf_res (Wire.mk "muld_ovfinfsel") is_inf_sel
  ]

  -- Level 1: Normal vs Zero
  let res_l1 := makeIndexedWires "muld_res_l1" 64
  let l1_gates := (List.range 64).map fun i =>
    if i == 63 then Gate.mkBUF (res_l0[63]!) (res_l1[63]!)
    else Gate.mkMUX (res_l0[i]!) zero is_zero_sel (res_l1[i]!)

  -- Level 2a: saturate an overflowing product to the largest finite magnitude.
  -- The exponent field is all ones minus one, so only its low bit (bit 52)
  -- differs from an infinity; the fraction becomes all ones.
  let res_l2a := makeIndexedWires "muld_res_l2a" 64
  let l2a_gates := (List.range 64).map fun i =>
    if i == 63 then Gate.mkBUF (res_l1[63]!) (res_l2a[63]!)
    else if i == 52 then Gate.mkMUX (res_l1[52]!) zero is_ovf_max (res_l2a[52]!)
    else Gate.mkMUX (res_l1[i]!) one_w is_ovf_max (res_l2a[i]!)

  -- Level 2b: res_l2a vs Inf
  let res_l2 := makeIndexedWires "muld_res_l2" 64
  let l2_gates := (List.range 64).map fun i =>
    if i == 63 then Gate.mkBUF (res_l2a[63]!) (res_l2[63]!)
    else if i >= 52 then Gate.mkMUX (res_l2a[i]!) one_w is_inf_sel (res_l2[i]!)
    else Gate.mkMUX (res_l2a[i]!) zero is_inf_sel (res_l2[i]!)

  -- Level 3: res_l2 vs Canonical NaN (0x7ff8000000000000)
  let l3_gates := (List.range 64).map fun i =>
    if i == 63 then Gate.mkMUX (res_l2[63]!) zero s2_nan_res (result[63]!)
    else if i >= 52 then Gate.mkMUX (res_l2[i]!) one_w s2_nan_res (result[i]!)
    else if i == 51 then Gate.mkMUX (res_l2[51]!) one_w s2_nan_res (result[51]!)
    else Gate.mkMUX (res_l2[i]!) zero s2_nan_res (result[i]!)

  -- Exceptions
  let nx_cand_a := Wire.mk "muld_nxc_a"
  let _nx_cand_b := Wire.mk "muld_nxc_b"
  let final_nx := Wire.mk "muld_fnx"
  let final_uf := Wire.mk "muld_fuf"
  let final_of := Wire.mk "muld_fof"

  let exc_eval_gates := [
    Gate.mkMUX grs_or sub_any_rem subnormal_res (Wire.mk "muld_nxsel"),
    Gate.mkOR (Wire.mk "muld_nxsel") is_overflow nx_cand_a,
    Gate.mkAND nx_cand_a s2_not_special final_nx,
    Gate.mkAND is_underflow s2_not_special final_uf,
    Gate.mkAND is_overflow s2_not_special final_of
  ]

  let not_rm2 := Wire.mk "fpmd_not_rm2"
  let exc_out_gates := [
    Gate.mkBUF final_nx (exc[0]!),
    Gate.mkBUF final_uf (exc[1]!),
    Gate.mkBUF final_of (exc[2]!),
    Gate.mkNOT rm2 not_rm2,
    Gate.mkAND rm2 not_rm2 (exc[3]!),
    Gate.mkBUF s2_nv (exc[4]!)
  ]

  let tag_out_gates := (List.range 6).map fun i =>
    Gate.mkBUF (s2_tag[i]!) (tag_out[i]!)
  let valid_out_gate := Gate.mkBUF s2_valid valid_out

  let all_gates :=
    s1_dffs ++ [one_gate, sign_gate] ++
    exp1_any_gates ++ exp2_any_gates ++ exp1_all1_gates ++ exp2_all1_gates ++
    frac1_nz_gates ++ frac2_nz_gates ++ zero_det_gates ++ spec_det_gates ++
    lead1_gates ++ lead2_gates ++ pos1_gates ++ pos2_gates ++ sh1_gates ++ sh2_gates ++
    sub_op_gates ++ norm1_gates ++ norm2_gates ++ mant_norm_gates ++
    eff1_gates ++ eff2_gates ++ exp_norm_gates ++
    exp_add_gates ++ exp_sub_gates ++ pp_gates ++
    csa_tree_gates1 ++ s1b_dffs ++ csa_tree_gates2 ++ s2_dffs ++ pre_mant_gates ++
    [g_gate, r_gate, s_extra_gate] ++ s_low50_gates ++ [s_gate] ++
    exp_adj_gates ++ s3_dffs ++ rm_inv_gates ++ rm_dec_gates ++ rnd_cond_gates ++
    mant_inc_gates ++ final_mant_gates ++ exp_final_gates ++ norm_res_gates ++
    exp_adj_any_gates ++ sub_neg_gates ++ sub_window_gates ++ sub_shift13_gates ++
    sub_over_gates ++ sub_shift_gates ++ sub_barrel_gates ++ sub_mant_gates ++
    sub_rnd_gates ++ not_rtz_gates ++ sub_inc_gates ++ sub_final_mant_gates ++
    sub_mant_any_gates ++ sub_zero_gates ++ sub_exp_gates ++ l0_gates ++
    exp11_all1_gates ++ ovf_unf_gates ++ sel_gates ++
    l1_gates ++ l2a_gates ++ l2_gates ++ l3_gates ++
    exc_eval_gates ++ exc_out_gates ++ tag_out_gates ++ [valid_out_gate]

  { name := "FPMultiplierD"
    inputs := src1 ++ src2 ++ rm ++ dest_tag ++ [valid_in, clock, reset, zero]
    outputs := result ++ tag_out ++ exc ++ [valid_out]
    gates := all_gates
    instances := csa_instances1 ++ csa_instances2 ++ [cpa_inst]
    keepHierarchy := true
    signalGroups := [
      { name := "src1", width := 64, wires := src1 },
      { name := "src2", width := 64, wires := src2 },
      { name := "rm", width := 3, wires := rm },
      { name := "dest_tag", width := 6, wires := dest_tag },
      { name := "result", width := 64, wires := result },
      { name := "tag_out", width := 6, wires := tag_out },
      { name := "exc", width := 5, wires := exc }
    ] }

def fpMultiplierDCircuit : Circuit := mkFPMultiplierD

end Shoumei.Circuits.Sequential
