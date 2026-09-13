/-
Circuits/Sequential/FPMultiplierD.lean - 3-Stage Pipelined Double-Precision FP Multiplier

IEEE 754 binary64 multiplication with pipelined datapath.

Pipeline stages:
  Stage 1: Latch inputs -> Unpack + exponent addition + partial products + CSA tree
  Stage 2: Latch intermediate CSA results -> 106-bit CPA + normalize + round + pack + special cases

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
  let shift_gates := [Gate.mkBUF zero (carry[0]!)] ++
    (List.range (w - 1)).map fun i => Gate.mkBUF (c_raw[i]!) (carry[i + 1]!)
  csa_gates ++ shift_gates

/-- Reduce a list of w-bit rows to 2 (sum + carry) using a CSA tree. -/
private def mkCSATree (rows : List (List Wire)) (zero : Wire)
    (fuel : Nat) (level : Nat) (w : Nat) : List Wire × List Wire × List Gate :=
  match fuel with
  | 0 =>
    let s := makeIndexedWires s!"csa_f0_s_{level}" w
    let c := makeIndexedWires s!"csa_f0_c_{level}" w
    let g := (List.range w).flatMap fun j =>
      [Gate.mkBUF zero (s[j]!), Gate.mkBUF zero (c[j]!)]
    (s, c, g)
  | fuel + 1 =>
    match rows with
    | [] =>
      let s := makeIndexedWires s!"csa_empty_s_{level}" w
      let c := makeIndexedWires s!"csa_empty_c_{level}" w
      let g := (List.range w).flatMap fun j =>
        [Gate.mkBUF zero (s[j]!), Gate.mkBUF zero (c[j]!)]
      (s, c, g)
    | [single] =>
      let c := makeIndexedWires s!"csa_l{level}_one_c" w
      let g := (List.range w).map fun j => Gate.mkBUF zero (c[j]!)
      (single, c, g)
    | [r1, r2] => (r1, r2, [])
    | _ =>
      let rec compress (rs : List (List Wire)) (idx : Nat)
          : List (List Wire) × List Gate :=
        match rs with
        | x :: y :: z :: rest =>
          let pfx := s!"csa_l{level}_g{idx}"
          let s := makeIndexedWires (pfx ++ "_s") w
          let c := makeIndexedWires (pfx ++ "_c") w
          let g := mkCSAInline x y z s c zero pfx
          let (more, mg) := compress rest (idx + 1)
          (s :: c :: more, g ++ mg)
        | remaining => (remaining, [])
      let (next, gates) := compress rows 0
      let (fs, fc, more_gates) := mkCSATree next zero fuel (level + 1) w
      (fs, fc, gates ++ more_gates)

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

  -- Mantissas (53 bits with implicit leading bit)
  let mant1 := frac1 ++ [exp1_any]
  let mant2 := frac2 ++ [exp2_any]

  -- Exponent addition: exp1 + exp2 - 1023 (13 bits)
  let exp1_13 := exp1 ++ [zero, zero]
  let exp2_13 := exp2 ++ [zero, zero]
  let exp_sum13 := makeIndexedWires "muld_esum" 13
  let (exp_add_gates, _) := mkKoggeStoneAdd exp1_13 exp2_13 zero exp_sum13 "muld_eadd"
  let bias13 := (List.range 13).map fun i => if i < 10 then one_w else zero
  let exp_ub13 := makeIndexedWires "muld_eub" 13
  let (exp_sub_gates, _) := mkKoggeStoneSub exp_sum13 bias13 exp_ub13 "muld_esub" one_w

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

  -- CSA Tree: 53 rows -> 2 rows (106 bits each)
  let (csa_sum, csa_carry, csa_tree_gates) := mkCSATree pp_wires zero 20 0 106

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
    [Gate.mkDFF prod_sign clock reset s2_sign] ++
    mkDFFBank exp_ub13 s2_expub clock reset ++
    mkDFFBank csa_sum s2_csa_sum clock reset ++
    mkDFFBank csa_carry s2_csa_carry clock reset ++
    mkDFFBank s1_rm s2_rm clock reset ++
    mkDFFBank s1_tag s2_tag clock reset ++
    [Gate.mkDFF s1_valid clock reset s2_valid,
     Gate.mkDFF s1_nv clock reset s2_nv,
     Gate.mkDFF s1_nan_res clock reset s2_nan_res,
     Gate.mkDFF s1_inf_res clock reset s2_inf_res,
     Gate.mkDFF s1_zero_res clock reset s2_zero_res,
     Gate.mkDFF s1_not_special clock reset s2_not_special]

  -- Stage 2 Combinational: Final CPA + Normalize + Round + Pack
  let product := makeIndexedWires "muld_prod" 106
  let (cpa_gates, _) := mkKoggeStoneAdd s2_csa_sum s2_csa_carry zero product "muld_cpa"

  -- Normalization shift: if product[105] is 1, shift right 1
  let is_shift := product[105]!
  let mant_shifted := (List.range 52).map fun i => product[53 + i]!
  let mant_unshifted := (List.range 52).map fun i => product[52 + i]!
  let pre_mant := makeIndexedWires "muld_pre_mant" 52
  let pre_mant_gates := mkMuxBank mant_unshifted mant_shifted is_shift pre_mant

  let g_bit := Wire.mk "muld_g"
  let r_bit := Wire.mk "muld_r"
  let g_gate := Gate.mkMUX (product[51]!) (product[52]!) is_shift g_bit
  let r_gate := Gate.mkMUX (product[50]!) (product[51]!) is_shift r_bit

  let s_extra := Wire.mk "muld_s_extra"
  let s_extra_gate := Gate.mkAND is_shift (product[50]!) s_extra

  let low50 := (List.range 50).map fun i => product[i]!
  let (s_low50, s_low50_gates) := mkOrTree "muld_low50" low50
  let s_bit := Wire.mk "muld_s"
  let s_gate := Gate.mkOR s_low50 s_extra s_bit

  -- Exponent adjustment by shift: exp_adj = s2_expub + is_shift
  let exp_inc_13 := [is_shift] ++ (List.replicate 12 zero)
  let exp_adj13 := makeIndexedWires "muld_eadj" 13
  let (exp_adj_gates, _) := mkKoggeStoneAdd s2_expub exp_inc_13 zero exp_adj13 "muld_eadj"

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
    Gate.mkOR rnd_t01 rnd_t23 round_up
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

  -- Overflow and Underflow detection
  let (exp11_all1, exp11_all1_gates) := mkAndTree "muld_e11o" ((List.range 11).map fun i => exp_final13[i]!)
  let not_neg_exp := Wire.mk "muld_nnege"
  let ovf_cand := Wire.mk "muld_ovf_cand"
  let is_overflow := Wire.mk "muld_ovf"
  let is_underflow := exp_final13[12]!

  let ovf_unf_gates := [
    Gate.mkNOT (exp_final13[12]!) not_neg_exp,
    Gate.mkOR (exp_final13[11]!) exp11_all1 ovf_cand,
    Gate.mkAND not_neg_exp ovf_cand is_overflow
  ]

  -- Special result values
  let is_zero_sel := Wire.mk "muld_zsel"
  let is_inf_sel := Wire.mk "muld_isel"
  let sel_gates := [
    Gate.mkOR s2_zero_res is_underflow is_zero_sel,
    Gate.mkOR s2_inf_res is_overflow is_inf_sel
  ]

  -- Level 1: Normal vs Zero
  let res_l1 := makeIndexedWires "muld_res_l1" 64
  let l1_gates := (List.range 64).map fun i =>
    if i == 63 then Gate.mkBUF (norm_res[63]!) (res_l1[63]!)
    else Gate.mkMUX (norm_res[i]!) zero is_zero_sel (res_l1[i]!)

  -- Level 2: res_l1 vs Inf
  let res_l2 := makeIndexedWires "muld_res_l2" 64
  let l2_gates := (List.range 64).map fun i =>
    if i == 63 then Gate.mkBUF (res_l1[63]!) (res_l2[63]!)
    else if i >= 52 then Gate.mkMUX (res_l1[i]!) one_w is_inf_sel (res_l2[i]!)
    else Gate.mkMUX (res_l1[i]!) zero is_inf_sel (res_l2[i]!)

  -- Level 3: res_l2 vs Canonical NaN (0x7ff8000000000000)
  let l3_gates := (List.range 64).map fun i =>
    if i == 63 then Gate.mkMUX (res_l2[63]!) zero s2_nan_res (result[63]!)
    else if i >= 52 then Gate.mkMUX (res_l2[i]!) one_w s2_nan_res (result[i]!)
    else if i == 51 then Gate.mkMUX (res_l2[51]!) one_w s2_nan_res (result[51]!)
    else Gate.mkMUX (res_l2[i]!) zero s2_nan_res (result[i]!)

  -- Exceptions
  let nx_cand_a := Wire.mk "muld_nxc_a"
  let nx_cand_b := Wire.mk "muld_nxc_b"
  let final_nx := Wire.mk "muld_fnx"
  let final_uf := Wire.mk "muld_fuf"
  let final_of := Wire.mk "muld_fof"

  let exc_eval_gates := [
    Gate.mkOR grs_or is_overflow nx_cand_a,
    Gate.mkOR nx_cand_a is_underflow nx_cand_b,
    Gate.mkAND nx_cand_b s2_not_special final_nx,
    Gate.mkAND is_underflow s2_not_special final_uf,
    Gate.mkAND is_overflow s2_not_special final_of
  ]

  let exc_out_gates := [
    Gate.mkBUF final_nx (exc[0]!),
    Gate.mkBUF final_uf (exc[1]!),
    Gate.mkBUF final_of (exc[2]!),
    Gate.mkBUF zero (exc[3]!),
    Gate.mkBUF s2_nv (exc[4]!)
  ]

  let tag_out_gates := (List.range 6).map fun i =>
    Gate.mkBUF (s2_tag[i]!) (tag_out[i]!)
  let valid_out_gate := Gate.mkBUF s2_valid valid_out

  let all_gates :=
    s1_dffs ++ [one_gate, sign_gate] ++
    exp1_any_gates ++ exp2_any_gates ++ exp1_all1_gates ++ exp2_all1_gates ++
    frac1_nz_gates ++ frac2_nz_gates ++ zero_det_gates ++ spec_det_gates ++
    exp_add_gates ++ exp_sub_gates ++ pp_gates ++ csa_tree_gates ++
    s2_dffs ++ cpa_gates ++ pre_mant_gates ++
    [g_gate, r_gate, s_extra_gate] ++ s_low50_gates ++ [s_gate] ++
    exp_adj_gates ++ rm_inv_gates ++ rm_dec_gates ++ rnd_cond_gates ++
    mant_inc_gates ++ final_mant_gates ++ exp_final_gates ++ norm_res_gates ++
    exp11_all1_gates ++ ovf_unf_gates ++ sel_gates ++
    l1_gates ++ l2_gates ++ l3_gates ++
    exc_eval_gates ++ exc_out_gates ++ tag_out_gates ++ [valid_out_gate]

  { name := "FPMultiplierD"
    inputs := src1 ++ src2 ++ rm ++ dest_tag ++ [valid_in, clock, reset, zero]
    outputs := result ++ tag_out ++ exc ++ [valid_out]
    gates := all_gates
    instances := [] }

def fpMultiplierDCircuit : Circuit := mkFPMultiplierD

end Shoumei.Circuits.Sequential
