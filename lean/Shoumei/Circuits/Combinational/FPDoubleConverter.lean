/-
Circuits/Combinational/FPDoubleConverter.lean - Double-Precision Conversions Circuit

Implements all conversion operations for RV32D:
- FCVT.W.D  (op=44): DP float -> signed 32-bit int
- FCVT.WU.D (op=45): DP float -> unsigned 32-bit int
- FCVT.D.W  (op=46): signed 32-bit int -> DP float
- FCVT.D.WU (op=47): unsigned 32-bit int -> DP float
- FCVT.S.D  (op=48): DP float -> NaN-boxed SP float
- FCVT.D.S  (op=49): SP float -> DP float (with NaN-unboxing check)

Interface:
- Inputs:
  * src1[63:0]: Operand
  * op[5:0]: FPU opcode (44..49)
  * rm[2:0]: Rounding mode
  * zero, one: Constant wires
- Outputs:
  * result[63:0]: Converted value
  * exc[4:0]: Exceptions (NV, DZ, OF, UF, NX)
  * result_is_int: High when targeting INT PRF (FCVT.W.D, FCVT.WU.D)
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.KoggeStoneAdder

namespace Shoumei.Circuits.Combinational

open Shoumei

private def mkOrTree (pfx : String) (inputs : List Wire) : Wire × List Gate :=
  match inputs with
  | [] => (Wire.mk s!"{pfx}_empty", [])
  | [w] => (w, [])
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
  | [w] => (w, [])
  | w0 :: w1 :: rest =>
    let firstOut := Wire.mk s!"{pfx}_0"
    let firstGate := Gate.mkAND w0 w1 firstOut
    let (finalW, restGates) := rest.enum.foldl (fun (acc : Wire × List Gate) (idx, w) =>
      let out := Wire.mk s!"{pfx}_{idx + 1}"
      let g := Gate.mkAND acc.1 w out
      (out, acc.2 ++ [g])
    ) (firstOut, [])
    (finalW, [firstGate] ++ restGates)

/-- Double-Precision FP Converter Circuit -/
def fpDoubleConverterCircuit : Circuit :=
  let src1 := makeIndexedWires "src1" 64
  let op := makeIndexedWires "op" 6
  let rm := makeIndexedWires "rm" 3
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  let result := makeIndexedWires "result" 64
  let exc := makeIndexedWires "exc" 5
  let result_is_int := Wire.mk "result_is_int"

  -- Inverted op bits
  let not_op0 := Wire.mk "not_op0"
  let not_op1 := Wire.mk "not_op1"
  let not_op2 := Wire.mk "not_op2"
  let not_op3 := Wire.mk "not_op3"
  let not_op4 := Wire.mk "not_op4"
  let op_inv_gates := [
    Gate.mkNOT (op[0]!) not_op0,
    Gate.mkNOT (op[1]!) not_op1,
    Gate.mkNOT (op[2]!) not_op2,
    Gate.mkNOT (op[3]!) not_op3,
    Gate.mkNOT (op[4]!) not_op4
  ]

  -- Opcode decoding:
  -- 44 = 101100 (FCVT.W.D)
  let is_fcvt_w_d := Wire.mk "is_fcvt_w_d"
  let dec_44 := [
    Gate.mkAND (op[5]!) not_op4 (Wire.mk "d44_t0"),
    Gate.mkAND (op[3]!) (op[2]!) (Wire.mk "d44_t1"),
    Gate.mkAND not_op1 not_op0 (Wire.mk "d44_t2"),
    Gate.mkAND (Wire.mk "d44_t0") (Wire.mk "d44_t1") (Wire.mk "d44_t3"),
    Gate.mkAND (Wire.mk "d44_t3") (Wire.mk "d44_t2") is_fcvt_w_d
  ]

  -- 45 = 101101 (FCVT.WU.D)
  let is_fcvt_wu_d := Wire.mk "is_fcvt_wu_d"
  let dec_45 := [
    Gate.mkAND (Wire.mk "d44_t3") not_op1 (Wire.mk "d45_t0"),
    Gate.mkAND (Wire.mk "d45_t0") (op[0]!) is_fcvt_wu_d
  ]

  -- 46 = 101110 (FCVT.D.W)
  let is_fcvt_d_w := Wire.mk "is_fcvt_d_w"
  let dec_46 := [
    Gate.mkAND (Wire.mk "d44_t3") (op[1]!) (Wire.mk "d46_t0"),
    Gate.mkAND (Wire.mk "d46_t0") not_op0 is_fcvt_d_w
  ]

  -- 47 = 101111 (FCVT.D.WU)
  let is_fcvt_d_wu := Wire.mk "is_fcvt_d_wu"
  let dec_47 := [
    Gate.mkAND (Wire.mk "d44_t3") (op[1]!) (Wire.mk "d47_t0"),
    Gate.mkAND (Wire.mk "d47_t0") (op[0]!) is_fcvt_d_wu
  ]

  -- 48 = 110000 (FCVT.S.D)
  let is_fcvt_s_d := Wire.mk "is_fcvt_s_d"
  let dec_48 := [
    Gate.mkAND (op[5]!) (op[4]!) (Wire.mk "d48_t0"),
    Gate.mkAND not_op3 not_op2 (Wire.mk "d48_t1"),
    Gate.mkAND not_op1 not_op0 (Wire.mk "d48_t2"),
    Gate.mkAND (Wire.mk "d48_t0") (Wire.mk "d48_t1") (Wire.mk "d48_t3"),
    Gate.mkAND (Wire.mk "d48_t3") (Wire.mk "d48_t2") is_fcvt_s_d
  ]

  -- 49 = 110001 (FCVT.D.S)
  let is_fcvt_d_s := Wire.mk "is_fcvt_d_s"
  let dec_49 := [
    Gate.mkAND (Wire.mk "d48_t3") not_op1 (Wire.mk "d49_t0"),
    Gate.mkAND (Wire.mk "d49_t0") (op[0]!) is_fcvt_d_s
  ]

  -- 56 = 111000 (FMV.X.D)
  -- 57 = 111001 (FMV.D.X)
  let is_fmv_x_d := Wire.mk "is_fmv_x_d"
  let is_fmv_d_x := Wire.mk "is_fmv_d_x"
  let is_any_fmv_d := Wire.mk "is_any_fmv_d"
  let dec_fmv := [
    Gate.mkAND (op[5]!) (op[4]!) (Wire.mk "dfmv_t0"),
    Gate.mkAND (Wire.mk "dfmv_t0") (op[3]!) (Wire.mk "dfmv_t1"),
    Gate.mkAND not_op2 not_op1 (Wire.mk "dfmv_t2"),
    Gate.mkAND (Wire.mk "dfmv_t1") (Wire.mk "dfmv_t2") is_any_fmv_d,
    Gate.mkAND is_any_fmv_d not_op0 is_fmv_x_d,
    Gate.mkAND is_any_fmv_d (op[0]!) is_fmv_d_x
  ]

  -- result_is_int = FCVT.W.D | FCVT.WU.D | FMV.X.D
  let res_is_int_t := Wire.mk "res_is_int_t"
  let result_is_int_gates := [
    Gate.mkOR is_fcvt_w_d is_fcvt_wu_d res_is_int_t,
    Gate.mkOR res_is_int_t is_fmv_x_d result_is_int
  ]

  -- ══════════════════════════════════════════════
  -- 1. Integer to DP float: FCVT.D.W / FCVT.D.WU
  -- ══════════════════════════════════════════════
  let int_in := (List.range 32).map fun i => src1[i]!
  let int_is_signed := is_fcvt_d_w
  let int_sign := Wire.mk "int_sign"
  let int_sign_gate := Gate.mkAND (int_in[31]!) int_is_signed int_sign

  -- Abs value: if int_sign, invert and add 1
  let int_neg := makeIndexedWires "int_neg" 32
  let int_neg_carry := makeIndexedWires "int_neg_c" 33
  let int_neg_gates := [Gate.mkBUF one (int_neg_carry[0]!)] ++ (List.range 32).flatMap fun i =>
    let nb := Wire.mk s!"inb_{i}"
    [Gate.mkNOT (int_in[i]!) nb,
     Gate.mkXOR nb (int_neg_carry[i]!) (int_neg[i]!),
     Gate.mkAND nb (int_neg_carry[i]!) (int_neg_carry[i + 1]!)]

  let int_abs := makeIndexedWires "int_abs" 32
  let int_abs_gates := (List.range 32).map fun i =>
    Gate.mkMUX (int_in[i]!) (int_neg[i]!) int_sign (int_abs[i]!)

  -- Check if int_abs is zero
  let (int_abs_any, int_abs_any_gates) := mkOrTree "int_abs_any" int_abs
  let int_is_zero := Wire.mk "int_is_zero"
  let int_is_zero_gate := Gate.mkNOT int_abs_any int_is_zero

  -- Find leading 1 in int_abs (31 down to 0)
  let pe_init := makeIndexedWires "pe_init" 5
  let pe_init_gates := (List.range 5).map fun k => Gate.mkBUF zero (pe_init[k]!)
  let (_, _, pe_fold_gates) := (List.range 32).foldl
    (fun (acc : Wire × (List Wire × List Gate)) idx =>
      let i := 31 - idx
      let old_found := acc.1
      let old_pos := acc.2.1
      let gates_acc := acc.2.2
      let nf := Wire.mk s!"pe_nf_{i}"
      let take := Wire.mk s!"pe_take_{i}"
      let g_nf := Gate.mkNOT old_found nf
      let g_take := Gate.mkAND (int_abs[i]!) nf take
      let new_found := Wire.mk s!"pe_found_{i}"
      let g_found := Gate.mkOR old_found (int_abs[i]!) new_found
      let new_pos := makeIndexedWires s!"pe_pos_{i}" 5
      let pos_gates := (List.range 5).map fun k =>
        let bit_val := if (i / Nat.pow 2 k) % 2 == 1 then one else zero
        Gate.mkMUX (old_pos[k]!) bit_val take (new_pos[k]!)
      (new_found, (new_pos, gates_acc ++ [g_nf, g_take, g_found] ++ pos_gates))
    ) (zero, (pe_init, []))

  let lead_pos := makeIndexedWires "pe_pos_0" 5

  -- Barrel left shift int_abs by (31 - lead_pos) to normalize (bit 31 will be 1)
  -- 31 - lead_pos in 5 bits is NOT(lead_pos)
  let norm_shamt := makeIndexedWires "norm_shamt" 5
  let norm_shamt_gates := (List.range 5).map fun k => Gate.mkNOT (lead_pos[k]!) (norm_shamt[k]!)

  -- 32-bit barrel shifter left
  let bsl_stage0 := makeIndexedWires "bsl_s0" 32
  let bsl_s0_gates := (List.range 32).map fun i =>
    if i >= 16 then Gate.mkMUX (int_abs[i]!) (int_abs[i - 16]!) (norm_shamt[4]!) (bsl_stage0[i]!)
    else Gate.mkMUX (int_abs[i]!) zero (norm_shamt[4]!) (bsl_stage0[i]!)

  let bsl_stage1 := makeIndexedWires "bsl_s1" 32
  let bsl_s1_gates := (List.range 32).map fun i =>
    if i >= 8 then Gate.mkMUX (bsl_stage0[i]!) (bsl_stage0[i - 8]!) (norm_shamt[3]!) (bsl_stage1[i]!)
    else Gate.mkMUX (bsl_stage0[i]!) zero (norm_shamt[3]!) (bsl_stage1[i]!)

  let bsl_stage2 := makeIndexedWires "bsl_s2" 32
  let bsl_s2_gates := (List.range 32).map fun i =>
    if i >= 4 then Gate.mkMUX (bsl_stage1[i]!) (bsl_stage1[i - 4]!) (norm_shamt[2]!) (bsl_stage2[i]!)
    else Gate.mkMUX (bsl_stage1[i]!) zero (norm_shamt[2]!) (bsl_stage2[i]!)

  let bsl_stage3 := makeIndexedWires "bsl_s3" 32
  let bsl_s3_gates := (List.range 32).map fun i =>
    if i >= 2 then Gate.mkMUX (bsl_stage2[i]!) (bsl_stage2[i - 2]!) (norm_shamt[1]!) (bsl_stage3[i]!)
    else Gate.mkMUX (bsl_stage2[i]!) zero (norm_shamt[1]!) (bsl_stage3[i]!)

  let norm_mant := makeIndexedWires "norm_mant" 32
  let bsl_s4_gates := (List.range 32).map fun i =>
    if i >= 1 then Gate.mkMUX (bsl_stage3[i]!) (bsl_stage3[i - 1]!) (norm_shamt[0]!) (norm_mant[i]!)
    else Gate.mkMUX (bsl_stage3[i]!) zero (norm_shamt[0]!) (norm_mant[i]!)

  -- Exponent = 1023 + lead_pos.
  let (pos_any, pos_any_gates) := mkOrTree "pos_any" (List.range 5 |>.map fun i => lead_pos[i]!)
  let pos_minus_1 := makeIndexedWires "pos_m1" 5
  let pos_borrow := makeIndexedWires "pos_bor" 6
  let pos_m1_gates := [Gate.mkBUF one (pos_borrow[0]!)] ++ (List.range 5).flatMap fun i =>
    let nb := Wire.mk s!"pnb_{i}"
    [Gate.mkNOT (lead_pos[i]!) nb,
     Gate.mkXOR (lead_pos[i]!) (pos_borrow[i]!) (pos_minus_1[i]!),
     Gate.mkAND nb (pos_borrow[i]!) (pos_borrow[i + 1]!)]

  let fcvt_d_exp := makeIndexedWires "fcvt_d_exp" 11
  let fcvt_d_exp_gates := (List.range 11).map fun i =>
    if i < 5 then
      Gate.mkMUX one (pos_minus_1[i]!) pos_any (fcvt_d_exp[i]!)
    else if i < 10 then
      Gate.mkMUX one zero pos_any (fcvt_d_exp[i]!)
    else
      Gate.mkMUX zero one pos_any (fcvt_d_exp[10]!)

  let res_fcvt_d_int := makeIndexedWires "res_fcvt_d_int" 64
  let res_fcvt_d_int_gates := (List.range 63).map fun i =>
    if i < 21 then
      Gate.mkBUF zero (res_fcvt_d_int[i]!)
    else if i < 52 then
      let mant_bit := norm_mant[i - 21]!
      Gate.mkMUX mant_bit zero int_is_zero (res_fcvt_d_int[i]!)
    else
      let exp_bit := fcvt_d_exp[i - 52]!
      Gate.mkMUX exp_bit zero int_is_zero (res_fcvt_d_int[i]!)

  let not_int_zero_gate := Gate.mkNOT int_is_zero (Wire.mk "not_int_zero")
  let res_fcvt_d_sign_gate := [
    Gate.mkAND int_sign (Wire.mk "not_int_zero") (Wire.mk "fcvt_d_fsign"),
    Gate.mkBUF (Wire.mk "fcvt_d_fsign") (res_fcvt_d_int[63]!)
  ]

  -- ══════════════════════════════════════════════
  -- 2. SP float to DP float: FCVT.D.S (op=49)
  -- ══════════════════════════════════════════════
  let (box_and, box_and_gates) := mkAndTree "box_and" (List.range 32 |>.map fun i => src1[32 + i]!)
  let is_boxed := box_and

  let sp_sign := src1[31]!
  let sp_exp := (List.range 8).map fun i => src1[23 + i]!
  let sp_mant := (List.range 23).map fun i => src1[i]!

  let (sp_exp_ones, sp_exp_ones_gates) := mkAndTree "spe_ones" sp_exp
  let (sp_exp_any, sp_exp_any_gates) := mkOrTree "spe_any" sp_exp
  let sp_exp_zeros := Wire.mk "spe_zeros"
  let sp_exp_zeros_gate := Gate.mkNOT sp_exp_any sp_exp_zeros

  let (sp_mant_any, sp_mant_any_gates) := mkOrTree "spm_any" sp_mant
  let sp_mant_zeros := Wire.mk "spm_zeros"
  let sp_mant_zeros_gate := Gate.mkNOT sp_mant_any sp_mant_zeros

  let sp_is_nan := Wire.mk "sp_is_nan"
  let sp_is_snan := Wire.mk "sp_is_snan"
  let sp_is_inf := Wire.mk "sp_is_inf"
  let sp_is_zero := Wire.mk "sp_is_zero"
  let not_sp_quiet := Wire.mk "not_sp_quiet"

  let sp_class_gates := [
    Gate.mkAND sp_exp_ones sp_mant_any sp_is_nan,
    Gate.mkNOT (sp_mant[22]!) not_sp_quiet,
    Gate.mkAND sp_is_nan not_sp_quiet sp_is_snan,
    Gate.mkAND sp_exp_ones sp_mant_zeros sp_is_inf,
    Gate.mkAND sp_exp_zeros sp_mant_zeros sp_is_zero
  ]

  let norm_dp_exp := makeIndexedWires "norm_dpe" 11
  let norm_dpe_c := makeIndexedWires "norm_dpe_c" 12
  let norm_dpe_gates := [Gate.mkBUF zero (norm_dpe_c[0]!)] ++ (List.range 11).flatMap fun i =>
    let a := if i < 8 then sp_exp[i]! else zero
    let b := if i == 7 || i == 8 || i == 9 then one else zero
    let ab_xor := Wire.mk s!"ndpe_xor_{i}"
    let ab_and := Wire.mk s!"ndpe_and_{i}"
    let cin_and := Wire.mk s!"ndpe_ca_{i}"
    [Gate.mkXOR a b ab_xor,
     Gate.mkXOR ab_xor (norm_dpe_c[i]!) (norm_dp_exp[i]!),
     Gate.mkAND a b ab_and,
     Gate.mkAND ab_xor (norm_dpe_c[i]!) cin_and,
     Gate.mkOR ab_and cin_and (norm_dpe_c[i + 1]!)]

  let res_fcvt_d_s := makeIndexedWires "res_fcvt_d_s" 64
  let res_fcvt_d_s_gates := (List.range 64).flatMap fun i =>
    let w := res_fcvt_d_s[i]!
    let canon_bit := if i >= 51 && i <= 62 then one else zero
    let norm_bit :=
      if i < 29 then zero
      else if i < 52 then sp_mant[i - 29]!
      else if i < 63 then norm_dp_exp[i - 52]!
      else sp_sign
    let inf_bit :=
      if i < 52 then zero
      else if i < 63 then one
      else sp_sign
    let zero_bit := if i == 63 then sp_sign else zero
    let m0 := Wire.mk s!"fcds_m0_{i}"
    let m1 := Wire.mk s!"fcds_m1_{i}"
    let m2 := Wire.mk s!"fcds_m2_{i}"
    [Gate.mkMUX norm_bit zero_bit sp_is_zero m0,
     Gate.mkMUX m0 inf_bit sp_is_inf m1,
     Gate.mkMUX m1 canon_bit sp_is_nan m2,
     Gate.mkMUX canon_bit m2 is_boxed w]

  -- ══════════════════════════════════════════════
  -- 3. DP float to SP float: FCVT.S.D (op=48)
  -- ══════════════════════════════════════════════
  let dp_sign := src1[63]!
  let dp_exp := (List.range 11).map fun i => src1[52 + i]!
  let dp_mant := (List.range 52).map fun i => src1[i]!

  let (dp_exp_ones, dp_exp_ones_gates) := mkAndTree "dpe_ones" dp_exp
  let (dp_exp_any, dp_exp_any_gates) := mkOrTree "dpe_any" dp_exp
  let dp_exp_zeros := Wire.mk "dpe_zeros"
  let dp_exp_zeros_gate := Gate.mkNOT dp_exp_any dp_exp_zeros

  let (dp_mant_any, dp_mant_any_gates) := mkOrTree "dpm_any" dp_mant
  let dp_mant_zeros := Wire.mk "dpm_zeros"
  let dp_mant_zeros_gate := Gate.mkNOT dp_mant_any dp_mant_zeros

  let dp_is_nan := Wire.mk "dp_is_nan"
  let dp_is_snan := Wire.mk "dp_is_snan"
  let dp_is_inf := Wire.mk "dp_is_inf"
  let dp_is_zero := Wire.mk "dp_is_zero"
  let not_dp_quiet := Wire.mk "not_dp_quiet"

  let dp_class_gates := [
    Gate.mkAND dp_exp_ones dp_mant_any dp_is_nan,
    Gate.mkNOT (dp_mant[51]!) not_dp_quiet,
    Gate.mkAND dp_is_nan not_dp_quiet dp_is_snan,
    Gate.mkAND dp_exp_ones dp_mant_zeros dp_is_inf,
    Gate.mkAND dp_exp_zeros dp_mant_zeros dp_is_zero
  ]

  let sp_conv_exp := makeIndexedWires "sp_cexp" 11
  let sp_conv_borrow := makeIndexedWires "sp_cbor" 12
  let sp_cexp_gates := [Gate.mkBUF zero (sp_conv_borrow[0]!)] ++ (List.range 11).flatMap fun i =>
    let a := dp_exp[i]!
    let b := if i == 7 || i == 8 || i == 9 then one else zero
    let not_a := Wire.mk s!"spcb_na_{i}"
    let diff := Wire.mk s!"spcb_d_{i}"
    let t0 := Wire.mk s!"spcb_t0_{i}"
    let t1 := Wire.mk s!"spcb_t1_{i}"
    let t2 := Wire.mk s!"spcb_t2_{i}"
    [Gate.mkNOT a not_a,
     Gate.mkXOR a b diff,
     Gate.mkXOR diff (sp_conv_borrow[i]!) (sp_conv_exp[i]!),
     Gate.mkAND not_a b t0,
     Gate.mkAND not_a (sp_conv_borrow[i]!) t1,
     Gate.mkAND b (sp_conv_borrow[i]!) t2,
     Gate.mkOR t0 t1 (Wire.mk s!"spcb_o_{i}"),
     Gate.mkOR (Wire.mk s!"spcb_o_{i}") t2 (sp_conv_borrow[i + 1]!)]

  -- Subnormal shift amount: sub_val = 897 - dp_exp
  -- 897 = 11'b011_1000_0001 (bits 0, 7, 8, 9 are 1)
  let sp_sub_val := makeIndexedWires "sp_subv" 11
  let sp_sub_bor := makeIndexedWires "sp_subb" 12
  let sp_sub_gates := [Gate.mkBUF zero (sp_sub_bor[0]!)] ++ (List.range 11).flatMap fun i =>
    let a := if i == 0 || i == 7 || i == 8 || i == 9 then one else zero
    let b := dp_exp[i]!
    let not_a := Wire.mk s!"spsb_na_{i}"
    let diff := Wire.mk s!"spsb_d_{i}"
    let t0 := Wire.mk s!"spsb_t0_{i}"
    let t1 := Wire.mk s!"spsb_t1_{i}"
    let t2 := Wire.mk s!"spsb_t2_{i}"
    [Gate.mkNOT a not_a,
     Gate.mkXOR a b diff,
     Gate.mkXOR diff (sp_sub_bor[i]!) (sp_sub_val[i]!),
     Gate.mkAND not_a b t0,
     Gate.mkAND not_a (sp_sub_bor[i]!) t1,
     Gate.mkAND b (sp_sub_bor[i]!) t2,
     Gate.mkOR t0 t1 (Wire.mk s!"spsb_o_{i}"),
     Gate.mkOR (Wire.mk s!"spsb_o_{i}") t2 (sp_sub_bor[i + 1]!)]

  -- Subnormal if dp_exp < 897: sp_sub_bor[11] is 0 and sub_val != 0
  let (sub_val_any, sub_val_any_gates) := mkOrTree "sp_subv_any" sp_sub_val
  let not_sub_bor := Wire.mk "sp_nsub_bor"
  let is_subnormal_sp := Wire.mk "sp_is_subnormal"
  let is_subnormal_gates := sub_val_any_gates ++ [
    Gate.mkNOT (sp_sub_bor[11]!) not_sub_bor,
    Gate.mkAND not_sub_bor sub_val_any is_subnormal_sp
  ]

  -- Clamp shift amount: if any bit above bit 5 is set, clamp to 63
  let (sub_high_any, sub_high_any_gates) := mkOrTree "sp_sub_hi" ((List.range 5).map fun i => sp_sub_val[6 + i]!)
  let sp_sh_amt := makeIndexedWires "sp_sh_amt" 6
  let sp_sh_amt_gates := sub_high_any_gates ++ (List.range 6).flatMap fun i =>
    let clamped := Wire.mk s!"sp_sh_c_{i}"
    [Gate.mkOR (sp_sub_val[i]!) sub_high_any clamped,
     Gate.mkMUX zero clamped is_subnormal_sp (sp_sh_amt[i]!)]

  -- Base exponent: if subnormal, 0; else sp_conv_exp[7:0]
  let base_sp_exp := makeIndexedWires "sp_bexp" 8
  let base_sp_exp_gates := (List.range 8).map fun i =>
    Gate.mkMUX (sp_conv_exp[i]!) zero is_subnormal_sp (base_sp_exp[i]!)

  -- 56-bit mantissa: {3'b0, 1'b1, dp_mant[51:0]}
  let sig56 := dp_mant ++ [one, zero, zero, zero]
  let ((sp_bsr_out, sp_bsr_stk), sp_bsr_gates) := (List.range 6).foldl
    (fun (acc : (List Wire × Wire) × List Gate) step =>
      let (stageIn, prev_sticky) := acc.1
      let shiftVal := Nat.pow 2 step
      let stageOut := makeIndexedWires s!"sp_bsr_s{step}" 56
      let gates := (List.range 56).map fun i =>
        if i + shiftVal < 56 then
          Gate.mkMUX (stageIn[i]!) (stageIn[i + shiftVal]!) (sp_sh_amt[step]!) (stageOut[i]!)
        else
          Gate.mkMUX (stageIn[i]!) zero (sp_sh_amt[step]!) (stageOut[i]!)
      let lost_bits := (List.range (min shiftVal 56)).map fun i => stageIn[i]!
      let (lost_or, lost_or_gates) := mkOrTree s!"sp_lost_s{step}" lost_bits
      let stage_contrib := Wire.mk s!"sp_stk_c_{step}"
      let new_sticky := Wire.mk s!"sp_stk_{step}"
      let g_contrib := Gate.mkAND (sp_sh_amt[step]!) lost_or stage_contrib
      let g_sticky := Gate.mkOR prev_sticky stage_contrib new_sticky
      ((stageOut, new_sticky), acc.2 ++ gates ++ lost_or_gates ++ [g_contrib, g_sticky])
    ) ((sig56, zero), [])

  let top23 := (List.range 23).map fun i => sp_bsr_out[29 + i]!
  let round_bit := sp_bsr_out[28]!
  let (low28_any, low28_gates) := mkOrTree "sp_low28" (List.range 28 |>.map fun i => sp_bsr_out[i]!)
  let sticky_bit := Wire.mk "sp_final_stk"
  let sticky_gate := Gate.mkOR low28_any sp_bsr_stk sticky_bit

  let round_inexact := Wire.mk "sp_rnd_inexact"
  let round_inexact_gate := Gate.mkOR round_bit sticky_bit round_inexact

  let rne_up := Wire.mk "sp_rne_up"
  let rne_up_gates := [
    Gate.mkOR sticky_bit (top23[0]!) (Wire.mk "rne_t0"),
    Gate.mkAND round_bit (Wire.mk "rne_t0") rne_up
  ]

  let rounded_top23 := makeIndexedWires "rnd_top23" 23
  let rnd_carry := makeIndexedWires "rnd_c" 24
  let rnd_add_gates := [Gate.mkBUF rne_up (rnd_carry[0]!)] ++ (List.range 23).flatMap fun i =>
    [Gate.mkXOR (top23[i]!) (rnd_carry[i]!) (rounded_top23[i]!),
     Gate.mkAND (top23[i]!) (rnd_carry[i]!) (rnd_carry[i + 1]!)]

  let final_sp_exp := makeIndexedWires "fsp_exp" 8
  let exp_inc_c := makeIndexedWires "einc_c" 9
  let exp_inc_gates := [Gate.mkBUF (rnd_carry[23]!) (exp_inc_c[0]!)] ++ (List.range 8).flatMap fun i =>
    [Gate.mkXOR (base_sp_exp[i]!) (exp_inc_c[i]!) (final_sp_exp[i]!),
     Gate.mkAND (base_sp_exp[i]!) (exp_inc_c[i]!) (exp_inc_c[i + 1]!)]

  let res_fcvt_s_d := makeIndexedWires "res_fcvt_s_d" 64
  let res_fcvt_s_d_gates := (List.range 64).flatMap fun i =>
    if i >= 32 then
      [Gate.mkBUF one (res_fcvt_s_d[i]!)]
    else
      let w := res_fcvt_s_d[i]!
      let canon_sp := if i >= 22 && i <= 30 then one else zero
      let norm_sp :=
        if i < 23 then rounded_top23[i]!
        else if i < 31 then final_sp_exp[i - 23]!
        else dp_sign
      let inf_sp :=
        if i < 23 then zero
        else if i < 31 then one
        else dp_sign
      let zero_sp := if i == 31 then dp_sign else zero
      let m0 := Wire.mk s!"fcsd_m0_{i}"
      let m1 := Wire.mk s!"fcsd_m1_{i}"
      [Gate.mkMUX norm_sp zero_sp dp_is_zero m0,
       Gate.mkMUX m0 inf_sp dp_is_inf m1,
       Gate.mkMUX m1 canon_sp dp_is_nan w]

  -- ══════════════════════════════════════════════
  -- 4. DP float to Integer: FCVT.W.D / FCVT.WU.D (op=44/45)
  -- ══════════════════════════════════════════════
  let sig53 := dp_mant ++ [one]

  let sh_right_amt := makeIndexedWires "fcvt_sh_rt" 6
  let sh_borrow := makeIndexedWires "fcvt_sh_b" 7
  let fcvt_sh_gates := [Gate.mkBUF zero (sh_borrow[0]!)] ++ (List.range 6).flatMap fun i =>
    let a := if i == 0 || i == 1 || i == 4 || i == 5 then one else zero
    let b := dp_exp[i]!
    let not_a := Wire.mk s!"fsh_na_{i}"
    let diff := Wire.mk s!"fsh_d_{i}"
    let t0 := Wire.mk s!"fsh_t0_{i}"
    let t1 := Wire.mk s!"fsh_t1_{i}"
    let t2 := Wire.mk s!"fsh_t2_{i}"
    [Gate.mkNOT a not_a,
     Gate.mkXOR a b diff,
     Gate.mkXOR diff (sh_borrow[i]!) (sh_right_amt[i]!),
     Gate.mkAND not_a b t0,
     Gate.mkAND not_a (sh_borrow[i]!) t1,
     Gate.mkAND b (sh_borrow[i]!) t2,
     Gate.mkOR t0 t1 (Wire.mk s!"fsh_o_{i}"),
     Gate.mkOR (Wire.mk s!"fsh_o_{i}") t2 (sh_borrow[i + 1]!)]

  let sig64 := sig53 ++ (List.range 11 |>.map fun _ => zero)
  let ((bsr_out, bsr_sticky), bsr_gates) := (List.range 6).foldl
    (fun (acc : (List Wire × Wire) × List Gate) step =>
      let (stageIn, prev_sticky) := acc.1
      let shiftVal := Nat.pow 2 step
      let stageOut := makeIndexedWires s!"bsr_s{step}" 64
      let gates := (List.range 64).map fun i =>
        if i + shiftVal < 64 then
          Gate.mkMUX (stageIn[i]!) (stageIn[i + shiftVal]!) (sh_right_amt[step]!) (stageOut[i]!)
        else
          Gate.mkMUX (stageIn[i]!) zero (sh_right_amt[step]!) (stageOut[i]!)
      let lost_bits := (List.range (min shiftVal 64)).map fun i => stageIn[i]!
      let (lost_or, lost_or_gates) := mkOrTree s!"fcvt_lost_s{step}" lost_bits
      let stage_contrib := Wire.mk s!"fcvt_stk_c_{step}"
      let new_sticky := Wire.mk s!"fcvt_stk_{step}"
      let g_contrib := Gate.mkAND (sh_right_amt[step]!) lost_or stage_contrib
      let g_sticky := Gate.mkOR prev_sticky stage_contrib new_sticky
      ((stageOut, new_sticky), acc.2 ++ gates ++ lost_or_gates ++ [g_contrib, g_sticky])
    ) ((sig64, zero), [])

  -- Exponent range checks:
  -- exp_lt_1023: magnitude < 1.0
  let exp_low10 := (List.range 10).map fun i => dp_exp[i]!
  let (exp_low10_all, exp_low10_all_gates) := mkAndTree "exp_l10" exp_low10
  let not_exp_l10 := Wire.mk "not_exp_l10"
  let not_dp_exp10 := Wire.mk "not_dp_exp10"
  let exp_lt_1023 := Wire.mk "exp_lt_1023"
  let exp_lt_1023_gates := exp_low10_all_gates ++ [
    Gate.mkNOT exp_low10_all not_exp_l10,
    Gate.mkNOT (dp_exp[10]!) not_dp_exp10,
    Gate.mkAND not_dp_exp10 not_exp_l10 exp_lt_1023
  ]

  -- Bits 5..9 of dp_exp (any set => dp_exp[9:0] >= 32):
  let exp_hi5 := (List.range 5).map fun i => dp_exp[5 + i]!
  let (exp_hi5_any, exp_hi5_any_gates) := mkOrTree "exp_hi5" exp_hi5

  -- Bits 1..4 all set (dp_exp[4:1] == 4'b1111):
  let exp_b14 := (List.range 4).map fun i => dp_exp[1 + i]!
  let (exp_b14_all, exp_b14_all_gates) := mkAndTree "exp_b14" exp_b14

  -- Bits 0..4 all set (dp_exp[4:0] == 5'b11111):
  let exp_b04_all := Wire.mk "exp_b04_all"
  let exp_b04_gate := Gate.mkAND exp_b14_all (dp_exp[0]!) exp_b04_all

  -- exp_gte_1054 = dp_exp[10] AND (exp_hi5_any OR exp_b14_all)
  let gte_1054_sub := Wire.mk "gte_1054_sub"
  let exp_gte_1054_val := Wire.mk "exp_gte_1054_val"
  let gte_1054_gates := exp_hi5_any_gates ++ exp_b14_all_gates ++ [
    exp_b04_gate,
    Gate.mkOR exp_hi5_any exp_b14_all gte_1054_sub,
    Gate.mkAND (dp_exp[10]!) gte_1054_sub exp_gte_1054_val
  ]

  -- exp_gte_1055 = dp_exp[10] AND (exp_hi5_any OR exp_b04_all)
  let gte_1055_sub := Wire.mk "gte_1055_sub"
  let exp_gte_1055 := Wire.mk "exp_gte_1055"
  let gte_1055_gates := [
    Gate.mkOR exp_hi5_any exp_b04_all gte_1055_sub,
    Gate.mkAND (dp_exp[10]!) gte_1055_sub exp_gte_1055
  ]

  -- exp_eq_1054 = exp_gte_1054 AND NOT(exp_gte_1055)
  let not_gte_1055 := Wire.mk "not_gte_1055"
  let exp_eq_1054 := Wire.mk "exp_eq_1054"
  let eq_1054_gates := [
    Gate.mkNOT exp_gte_1055 not_gte_1055,
    Gate.mkAND exp_gte_1054_val not_gte_1055 exp_eq_1054
  ]

  let not_exp_lt_1023 := Wire.mk "not_exp_lt_1023"
  let int_mag := makeIndexedWires "int_mag" 32
  let int_mag_gates := [Gate.mkNOT exp_lt_1023 not_exp_lt_1023] ++
    (List.range 32).map fun i =>
      Gate.mkAND (bsr_out[i]!) not_exp_lt_1023 (int_mag[i]!)

  let int_mag_neg := makeIndexedWires "imag_neg" 32
  let int_mag_c := makeIndexedWires "imag_c" 33
  let int_mag_neg_gates := [Gate.mkBUF one (int_mag_c[0]!)] ++ (List.range 32).flatMap fun i =>
    let nb := Wire.mk s!"imnb_{i}"
    [Gate.mkNOT (int_mag[i]!) nb,
     Gate.mkXOR nb (int_mag_c[i]!) (int_mag_neg[i]!),
     Gate.mkAND nb (int_mag_c[i]!) (int_mag_c[i + 1]!)]

  let fcvt_w_val := makeIndexedWires "fcvt_w_val" 32
  let fcvt_w_val_gates := (List.range 32).map fun i =>
    Gate.mkMUX (int_mag[i]!) (int_mag_neg[i]!) dp_sign (fcvt_w_val[i]!)

  let not_dp_sign := Wire.mk "not_dp_sign"
  let not_dp_sign_gate := Gate.mkNOT dp_sign not_dp_sign

  -- Invalid operation (NV) detection
  let is_nan_or_inf := Wire.mk "fcvt_w_nan_inf"
  let is_nan_or_inf_gate := Gate.mkOR dp_is_nan dp_is_inf is_nan_or_inf

  -- Negative overflow for fcvt.w.d:
  -- dp_sign AND (exp_gte_1055 OR (exp_eq_1054 AND dp_mant_any))
  let exp_eq_1054_mant := Wire.mk "exp_eq_1054_mant"
  let neg_w_ov_sub := Wire.mk "neg_w_ov_sub"
  let neg_w_ov := Wire.mk "neg_w_ov"
  let neg_w_ov_gates := [
    Gate.mkAND exp_eq_1054 dp_mant_any exp_eq_1054_mant,
    Gate.mkOR exp_gte_1055 exp_eq_1054_mant neg_w_ov_sub,
    Gate.mkAND dp_sign neg_w_ov_sub neg_w_ov
  ]

  -- Positive overflow for fcvt.w.d:
  -- not_dp_sign AND exp_gte_1054
  let pos_w_ov := Wire.mk "pos_w_ov"
  let pos_w_ov_gate := Gate.mkAND not_dp_sign exp_gte_1054_val pos_w_ov

  -- nv_w = is_nan_or_inf OR pos_w_ov OR neg_w_ov
  let nv_w := Wire.mk "nv_w"
  let nv_w_gates := [
    Gate.mkOR is_nan_or_inf pos_w_ov (Wire.mk "nv_w_t0"),
    Gate.mkOR (Wire.mk "nv_w_t0") neg_w_ov nv_w
  ]

  -- nv_wu:
  -- Positive overflow for fcvt.wu.d: not_dp_sign AND exp_gte_1055
  let pos_wu_ov := Wire.mk "pos_wu_ov"
  let pos_wu_ov_gate := Gate.mkAND not_dp_sign exp_gte_1055 pos_wu_ov

  -- Negative input with magnitude >= 1.0: dp_sign AND NOT(exp_lt_1023) AND NOT(dp_is_zero)
  let not_dp_zero := Wire.mk "not_dp_zero"
  let not_dp_zero_gate := Gate.mkNOT dp_is_zero not_dp_zero
  let neg_wu_ge1 := Wire.mk "neg_wu_ge1"
  let neg_wu_ge1_gates := [
    not_dp_zero_gate,
    Gate.mkAND dp_sign not_exp_lt_1023 (Wire.mk "neg_wu_t0"),
    Gate.mkAND (Wire.mk "neg_wu_t0") not_dp_zero neg_wu_ge1
  ]

  -- nv_wu = is_nan_or_inf OR pos_wu_ov OR neg_wu_ge1
  let nv_wu := Wire.mk "nv_wu"
  let nv_wu_gates := [
    Gate.mkOR is_nan_or_inf pos_wu_ov (Wire.mk "nv_wu_t0"),
    Gate.mkOR (Wire.mk "nv_wu_t0") neg_wu_ge1 nv_wu
  ]

  -- nv_fcvt_w: select between nv_w and nv_wu
  let nv_fcvt_w := Wire.mk "nv_fcvt_w"
  let nv_fcvt_w_gate := Gate.mkMUX nv_w nv_wu is_fcvt_wu_d nv_fcvt_w

  -- Clamping logic
  let not_dp_nan := Wire.mk "not_dp_nan"
  let not_dp_nan_gate := Gate.mkNOT dp_is_nan not_dp_nan
  let clamp_w_is_neg := Wire.mk "clamp_w_is_neg"
  let clamp_w_is_neg_gate := Gate.mkAND dp_sign not_dp_nan clamp_w_is_neg
  let not_clamp_w_is_neg := Wire.mk "not_clamp_w_is_neg"
  let not_clamp_w_is_neg_gate := Gate.mkNOT clamp_w_is_neg not_clamp_w_is_neg

  let clamp_wu_val := Wire.mk "clamp_wu_val"
  let clamp_wu_val_gate := Gate.mkOR dp_is_nan not_dp_sign clamp_wu_val

  let clamp_gates_pre := [not_dp_nan_gate, clamp_w_is_neg_gate, not_clamp_w_is_neg_gate, clamp_wu_val_gate]

  let res_fcvt_w := makeIndexedWires "res_fcvt_w" 64
  let res_fcvt_w_gates := (List.range 64).flatMap fun i =>
    if i >= 32 then
      [Gate.mkBUF (res_fcvt_w[31]!) (res_fcvt_w[i]!)]
    else
      let w := res_fcvt_w[i]!
      let clamp_w := if i == 31 then clamp_w_is_neg else not_clamp_w_is_neg
      let clamp_wu := clamp_wu_val
      let clamp_val := Wire.mk s!"clamp_val_{i}"
      let norm_val := Wire.mk s!"norm_val_{i}"
      [Gate.mkMUX clamp_w clamp_wu is_fcvt_wu_d clamp_val,
       Gate.mkMUX (fcvt_w_val[i]!) (int_mag[i]!) is_fcvt_wu_d norm_val,
       Gate.mkMUX norm_val clamp_val nv_fcvt_w w]

  -- Inexact (NX) detection for FCVT.W.D and FCVT.WU.D:
  let fcvt_w_nx_raw := Wire.mk "fcvt_w_nx_raw"
  let fcvt_w_nx := Wire.mk "fcvt_w_nx"
  let not_nv_fcvt_w := Wire.mk "not_nv_fcvt_w"
  let fcvt_w_nx_gates := [
    Gate.mkMUX bsr_sticky not_dp_zero exp_lt_1023 fcvt_w_nx_raw,
    Gate.mkNOT nv_fcvt_w not_nv_fcvt_w,
    Gate.mkAND fcvt_w_nx_raw not_nv_fcvt_w fcvt_w_nx
  ]

  -- ══════════════════════════════════════════════
  -- 5. Master Output Multiplexing
  -- ══════════════════════════════════════════════
  let is_any_fcvt_d_int := Wire.mk "is_any_fcvt_d_int"
  let is_any_fcvt_w := Wire.mk "is_any_fcvt_w"
  let sel_gates := [
    Gate.mkOR is_fcvt_d_w is_fcvt_d_wu is_any_fcvt_d_int,
    Gate.mkOR is_fcvt_w_d is_fcvt_wu_d is_any_fcvt_w
  ]

  let out_gates := (List.range 64).flatMap fun i =>
    let w := result[i]!
    let m0 := Wire.mk s!"out_m0_{i}"
    let m1 := Wire.mk s!"out_m1_{i}"
    let m2 := Wire.mk s!"out_m2_{i}"
    [Gate.mkMUX (res_fcvt_d_int[i]!) (res_fcvt_d_s[i]!) is_fcvt_d_s m0,
     Gate.mkMUX m0 (res_fcvt_s_d[i]!) is_fcvt_s_d m1,
     Gate.mkMUX m1 (res_fcvt_w[i]!) is_any_fcvt_w m2,
     Gate.mkMUX m2 (src1[i]!) is_any_fmv_d w]

  let nv_fcds := sp_is_snan
  let nv_fcsd := dp_is_snan
  let exc_nv := Wire.mk "exc_nv"
  let exc_nx := Wire.mk "exc_nx"
  let exc_nv_gates := [
    Gate.mkAND is_fcvt_d_s nv_fcds (Wire.mk "nv0"),
    Gate.mkAND is_fcvt_s_d nv_fcsd (Wire.mk "nv1"),
    Gate.mkAND is_any_fcvt_w nv_fcvt_w (Wire.mk "nv2"),
    Gate.mkOR (Wire.mk "nv0") (Wire.mk "nv1") (Wire.mk "nv_t0"),
    Gate.mkOR (Wire.mk "nv_t0") (Wire.mk "nv2") exc_nv,
    Gate.mkBUF exc_nv (exc[4]!),
    Gate.mkNOT (rm[2]!) (Wire.mk "not_dc_rm2"),
    Gate.mkAND (rm[2]!) (Wire.mk "not_dc_rm2") (exc[3]!),
    Gate.mkNOT (rm[1]!) (Wire.mk "not_dc_rm1"),
    Gate.mkAND (rm[1]!) (Wire.mk "not_dc_rm1") (exc[2]!),
    Gate.mkNOT (rm[0]!) (Wire.mk "not_dc_rm0"),
    Gate.mkAND (rm[0]!) (Wire.mk "not_dc_rm0") (exc[1]!),
    Gate.mkAND is_fcvt_s_d round_inexact (Wire.mk "nx_sd"),
    Gate.mkAND is_any_fcvt_w fcvt_w_nx (Wire.mk "nx_w"),
    Gate.mkOR (Wire.mk "nx_sd") (Wire.mk "nx_w") exc_nx,
    Gate.mkBUF exc_nx (exc[0]!)
  ]

  let all_gates :=
    op_inv_gates ++ dec_44 ++ dec_45 ++ dec_46 ++ dec_47 ++ dec_48 ++ dec_49 ++
    dec_fmv ++ result_is_int_gates ++
    [int_sign_gate] ++ int_neg_gates ++ int_abs_gates ++
    int_abs_any_gates ++ [int_is_zero_gate] ++ pe_init_gates ++ pe_fold_gates ++
    norm_shamt_gates ++ bsl_s0_gates ++ bsl_s1_gates ++ bsl_s2_gates ++
    bsl_s3_gates ++ bsl_s4_gates ++ pos_any_gates ++ pos_m1_gates ++
    fcvt_d_exp_gates ++ res_fcvt_d_int_gates ++ [not_int_zero_gate] ++ res_fcvt_d_sign_gate ++
    box_and_gates ++ sp_exp_ones_gates ++ sp_exp_any_gates ++ [sp_exp_zeros_gate] ++
    sp_mant_any_gates ++ [sp_mant_zeros_gate] ++ sp_class_gates ++ norm_dpe_gates ++
    res_fcvt_d_s_gates ++ dp_exp_ones_gates ++ dp_exp_any_gates ++ [dp_exp_zeros_gate] ++
    dp_mant_any_gates ++ [dp_mant_zeros_gate] ++ dp_class_gates ++ sp_cexp_gates ++
    sp_sub_gates ++ is_subnormal_gates ++ sp_sh_amt_gates ++ base_sp_exp_gates ++
    sp_bsr_gates ++ low28_gates ++ [sticky_gate] ++ [round_inexact_gate] ++ rne_up_gates ++ rnd_add_gates ++
    exp_inc_gates ++ res_fcvt_s_d_gates ++ fcvt_sh_gates ++ bsr_gates ++
    exp_lt_1023_gates ++ gte_1054_gates ++ gte_1055_gates ++ eq_1054_gates ++
    int_mag_gates ++ int_mag_neg_gates ++ fcvt_w_val_gates ++ [not_dp_sign_gate] ++
    [is_nan_or_inf_gate] ++ neg_w_ov_gates ++ [pos_w_ov_gate] ++ nv_w_gates ++
    [pos_wu_ov_gate] ++ neg_wu_ge1_gates ++ nv_wu_gates ++ [nv_fcvt_w_gate] ++
    clamp_gates_pre ++ res_fcvt_w_gates ++ fcvt_w_nx_gates ++
    sel_gates ++ out_gates ++ exc_nv_gates

  { name := "FPDoubleConverter"
    inputs := src1 ++ op ++ rm ++ [zero, one]
    outputs := result ++ exc ++ [result_is_int]
    gates := all_gates
    instances := []
    signalGroups := [
      { name := "src1", width := 64, wires := src1 },
      { name := "op", width := 6, wires := op },
      { name := "rm", width := 3, wires := rm },
      { name := "result", width := 64, wires := result },
      { name := "exc", width := 5, wires := exc }
    ]
  }

/-- Convenience alias -/
def fpDoubleConverter : Circuit := fpDoubleConverterCircuit

end Shoumei.Circuits.Combinational
