/-
Circuits/Combinational/FPToInt64.lean - 64-Bit Float to Integer Conversion Submodule

Submodule of FPLongConverter implementing:
- FCVT.L.S  (SP float -> signed 64-bit int)
- FCVT.LU.S (SP float -> unsigned 64-bit int)
- FCVT.L.D  (DP float -> signed 64-bit int)
- FCVT.LU.D (DP float -> unsigned 64-bit int)

Interface:
- Inputs:
  * src1[63:0]: Float operand (SP in bits [31:0] or DP in bits [63:0])
  * is_dp: High for double-precision float input, low for single-precision
  * is_unsigned: High for unsigned integer result, low for signed integer
  * rm[2:0]: Rounding mode (0=RNE, 1=RTZ, 2=RDN, 3=RUP, 4=RMM)
  * zero, one: Constant wires
- Outputs:
  * result[63:0]: Converted 64-bit integer
  * exc_nv: Invalid operation exception
  * exc_nx: Inexact exception
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.KoggeStoneAdder

namespace Shoumei.Circuits.Combinational

open Shoumei

private def mkOrTree (pfx : String) (inputs : List Wire) : Wire × List Gate :=
  match inputs with
  | [] => (Wire.mk s!"{pfx}_empty", [])
  | [w] => (w, [])
  | _ =>
    let buildLevel (ws : List Wire) (lvl : Nat) : List Wire × List Gate :=
      let rec go (remaining : List Wire) (acc_w : List Wire) (acc_g : List Gate) :=
        match remaining with
        | [] => (acc_w.reverse, acc_g)
        | [w] => ((w :: acc_w).reverse, acc_g)
        | w1 :: w2 :: rest =>
          let intermediate := Wire.mk s!"{pfx}_l{lvl}_{acc_w.length}"
          let gate := Gate.mkOR w1 w2 intermediate
          go rest (intermediate :: acc_w) (acc_g ++ [gate])
      go ws [] []
    let rec reduceTree (ws : List Wire) (lvl : Nat) (acc : List Gate) (fuel : Nat) : Wire × List Gate :=
      match fuel with
      | 0 => (ws.head!, acc)
      | fuel' + 1 =>
        match ws with
        | [] => (Wire.mk s!"{pfx}_empty", acc)
        | [w] => (w, acc)
        | _ =>
          let (next_ws, next_gates) := buildLevel ws lvl
          reduceTree next_ws (lvl + 1) (acc ++ next_gates) fuel'
    reduceTree inputs 0 [] (inputs.length + 1)

private def mkAndTree (pfx : String) (inputs : List Wire) : Wire × List Gate :=
  match inputs with
  | [] => (Wire.mk s!"{pfx}_empty", [])
  | [w] => (w, [])
  | _ =>
    let buildLevel (ws : List Wire) (lvl : Nat) : List Wire × List Gate :=
      let rec go (remaining : List Wire) (acc_w : List Wire) (acc_g : List Gate) :=
        match remaining with
        | [] => (acc_w.reverse, acc_g)
        | [w] => ((w :: acc_w).reverse, acc_g)
        | w1 :: w2 :: rest =>
          let intermediate := Wire.mk s!"{pfx}_l{lvl}_{acc_w.length}"
          let gate := Gate.mkAND w1 w2 intermediate
          go rest (intermediate :: acc_w) (acc_g ++ [gate])
      go ws [] []
    let rec reduceTree (ws : List Wire) (lvl : Nat) (acc : List Gate) (fuel : Nat) : Wire × List Gate :=
      match fuel with
      | 0 => (ws.head!, acc)
      | fuel' + 1 =>
        match ws with
        | [] => (Wire.mk s!"{pfx}_empty", acc)
        | [w] => (w, acc)
        | _ =>
          let (next_ws, next_gates) := buildLevel ws lvl
          reduceTree next_ws (lvl + 1) (acc ++ next_gates) fuel'
    reduceTree inputs 0 [] (inputs.length + 1)

/-- 64-bit Float to Integer Converter Circuit -/
def mkFPToInt64 : Circuit :=
  let src1 := makeIndexedWires "src1" 64
  let is_dp := Wire.mk "is_dp"
  let is_unsigned := Wire.mk "is_unsigned"
  let rm := makeIndexedWires "rm" 3
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  let result := makeIndexedWires "result" 64
  let exc_nv := Wire.mk "exc_nv"
  let exc_nx := Wire.mk "exc_nx"

  -- Rounding mode decodes
  let not_rm0 := Wire.mk "not_rm0"
  let not_rm1 := Wire.mk "not_rm1"
  let not_rm2 := Wire.mk "not_rm2"
  let rm_inv_gates := [
    Gate.mkNOT (rm[0]!) not_rm0,
    Gate.mkNOT (rm[1]!) not_rm1,
    Gate.mkNOT (rm[2]!) not_rm2
  ]
  let rm_is_rne := Wire.mk "rm_is_rne" -- 000
  let rm_is_rtz := Wire.mk "rm_is_rtz" -- 001
  let rm_is_rdn := Wire.mk "rm_is_rdn" -- 010
  let rm_is_rup := Wire.mk "rm_is_rup" -- 011
  let rm_is_rmm := Wire.mk "rm_is_rmm" -- 100
  let rm_dec_gates := [
    Gate.mkAND not_rm2 not_rm1 (Wire.mk "rm_t0"),
    Gate.mkAND (Wire.mk "rm_t0") not_rm0 rm_is_rne,
    Gate.mkAND (Wire.mk "rm_t0") (rm[0]!) rm_is_rtz,
    Gate.mkAND not_rm2 (rm[1]!) (Wire.mk "rm_t1"),
    Gate.mkAND (Wire.mk "rm_t1") not_rm0 rm_is_rdn,
    Gate.mkAND (Wire.mk "rm_t1") (rm[0]!) rm_is_rup,
    Gate.mkAND (rm[2]!) not_rm1 (Wire.mk "rm_t2"),
    Gate.mkAND (Wire.mk "rm_t2") not_rm0 rm_is_rmm
  ]

  -- For SP float inputs (is_dp == 0): losslessly expand SP to DP float
  -- SP fields: sign=src1[31], exp=src1[30:23], mant=src1[22:0]
  let sp_in_sign := src1[31]!
  let sp_in_exp := (List.range 8).map fun i => src1[23 + i]!
  let sp_in_mant := (List.range 23).map fun i => src1[i]!

  let (sp_in_exp_ones, sp_in_exp_ones_gates) := mkAndTree "spin_e1" sp_in_exp
  let (sp_in_exp_any, sp_in_exp_any_gates) := mkOrTree "spin_ea" sp_in_exp
  let sp_in_exp_zeros := Wire.mk "spin_ez"
  let sp_in_exp_zeros_gate := Gate.mkNOT sp_in_exp_any sp_in_exp_zeros

  let (sp_in_mant_any, sp_in_mant_any_gates) := mkOrTree "spin_ma" sp_in_mant
  let sp_in_mant_zeros := Wire.mk "spin_mz"
  let sp_in_mant_zeros_gate := Gate.mkNOT sp_in_mant_any sp_in_mant_zeros

  let sp_in_is_nan := Wire.mk "spin_is_nan"
  let sp_in_is_inf := Wire.mk "spin_is_inf"
  let sp_in_is_zero := Wire.mk "spin_is_zero"
  let sp_in_class_gates := [
    Gate.mkAND sp_in_exp_ones sp_in_mant_any sp_in_is_nan,
    Gate.mkAND sp_in_exp_ones sp_in_mant_zeros sp_in_is_inf,
    Gate.mkAND sp_in_exp_zeros sp_in_mant_zeros sp_in_is_zero
  ]

  -- SP exp to DP exp: if normal, dp_exp = sp_exp + 896 (896 = 0b01110000000)
  let norm_sp_dp_exp := makeIndexedWires "nsp_dpe" 11
  let norm_sp_dp_exp_c := makeIndexedWires "nsp_dpe_c" 12
  let norm_sp_dp_exp_gates := [Gate.mkBUF zero (norm_sp_dp_exp_c[0]!)] ++ (List.range 11).flatMap fun i =>
    let a := if i < 8 then sp_in_exp[i]! else zero
    let b := if i == 7 || i == 8 || i == 9 then one else zero
    let ab_xor := Wire.mk s!"nsp_xor_{i}"
    let ab_and := Wire.mk s!"nsp_and_{i}"
    let cin_and := Wire.mk s!"nsp_ca_{i}"
    [Gate.mkXOR a b ab_xor,
     Gate.mkXOR ab_xor (norm_sp_dp_exp_c[i]!) (norm_sp_dp_exp[i]!),
     Gate.mkAND a b ab_and,
     Gate.mkAND ab_xor (norm_sp_dp_exp_c[i]!) cin_and,
     Gate.mkOR ab_and cin_and (norm_sp_dp_exp_c[i + 1]!)]

  -- Assemble expanded DP representation of SP input
  let sp_as_dp := makeIndexedWires "sp_as_dp" 64
  let sp_as_dp_gates := (List.range 64).flatMap fun i =>
    let norm_bit :=
      if i < 29 then zero
      else if i < 52 then sp_in_mant[i - 29]!
      else if i < 63 then norm_sp_dp_exp[i - 52]!
      else sp_in_sign
    let nan_bit := if i >= 51 && i <= 62 then one else zero
    let inf_bit := if i < 52 then zero else if i < 63 then one else sp_in_sign
    let zero_bit := if i == 63 then sp_in_sign else zero
    let m0 := Wire.mk s!"spdp_m0_{i}"
    let m1 := Wire.mk s!"spdp_m1_{i}"
    [Gate.mkMUX norm_bit zero_bit sp_in_is_zero m0,
     Gate.mkMUX m0 inf_bit sp_in_is_inf m1,
     Gate.mkMUX m1 nan_bit sp_in_is_nan (sp_as_dp[i]!)]

  -- Master Float Input to Int64 converter: select DP input or expanded SP input
  let flt_in := makeIndexedWires "flt_in" 64
  let flt_in_gates := (List.range 64).map fun i =>
    Gate.mkMUX (sp_as_dp[i]!) (src1[i]!) is_dp (flt_in[i]!)

  let flt_sign := flt_in[63]!
  let flt_exp := (List.range 11).map fun i => flt_in[52 + i]!
  let flt_mant := (List.range 52).map fun i => flt_in[i]!

  -- Classification of DP float input
  let (flt_exp_ones, flt_exp_ones_gates) := mkAndTree "flt_e1" flt_exp
  let (flt_exp_any, flt_exp_any_gates) := mkOrTree "flt_ea" flt_exp
  let flt_exp_zeros := Wire.mk "flt_ez"
  let flt_exp_zeros_gate := Gate.mkNOT flt_exp_any flt_exp_zeros

  let (flt_mant_any, flt_mant_any_gates) := mkOrTree "flt_ma" flt_mant
  let flt_mant_zeros := Wire.mk "flt_mz"
  let flt_mant_zeros_gate := Gate.mkNOT flt_mant_any flt_mant_zeros

  let flt_is_nan := Wire.mk "flt_is_nan"
  let flt_is_inf := Wire.mk "flt_is_inf"
  let flt_is_zero := Wire.mk "flt_is_zero"
  let flt_class_gates := [
    Gate.mkAND flt_exp_ones flt_mant_any flt_is_nan,
    Gate.mkAND flt_exp_ones flt_mant_zeros flt_is_inf,
    Gate.mkAND flt_exp_zeros flt_mant_zeros flt_is_zero
  ]

  -- Shift amount calculation for 128-bit barrel right shifter:
  -- shamt = 115 - (flt_exp - 1023) = 1138 - flt_exp (7 bits: 0..127)
  -- 1138 in 11-bit binary: 10001110010
  let const1138 := [zero, one, zero, zero, one, one, one, zero, zero, zero, one]
  let shamt_full := makeIndexedWires "shamt_full" 11
  let (shamt_sub_gates, shamt_borrow) := mkKoggeStoneSub const1138 flt_exp shamt_full "shamt_sub" one

  -- If shamt_borrow=1 or flt_exp >= 1139 (i.e. unbiased_exp >= 116): shift amount is 0 (huge overflow)
  let shamt7 := (List.range 7).map fun i =>
    Wire.mk s!"shamt7_{i}"
  let shamt7_gates := (List.range 7).map fun i =>
    Gate.mkMUX (shamt_full[i]!) zero shamt_borrow (shamt7[i]!)

  -- Form the 128-bit bus:
  -- bits [127:116] = 0 (12 zeros)
  -- bit 115 = 1 (implicit hidden 1)
  -- bits [114:63] = flt_mant (52 bits)
  -- bits [62:0] = 0 (63 zeros)
  let bus128_init :=
    (List.range 63 |>.map fun _ => zero) ++
    flt_mant ++
    [one] ++
    (List.range 12 |>.map fun _ => zero)

  -- 128-bit Barrel Right Shifter with sticky accumulator
  let ((bus128_out, bus_sticky), bus_shift_gates) := (List.range 7).foldl
    (fun (acc : (List Wire × Wire) × List Gate) step =>
      let (stageIn, prev_sticky) := acc.1
      let shiftVal := Nat.pow 2 step
      let stageOut := makeIndexedWires s!"b128_s{step}" 128
      let gates := (List.range 128).map fun i =>
        if i + shiftVal < 128 then
          Gate.mkMUX (stageIn[i]!) (stageIn[i + shiftVal]!) (shamt7[step]!) (stageOut[i]!)
        else
          Gate.mkMUX (stageIn[i]!) zero (shamt7[step]!) (stageOut[i]!)
      let lost_bits := (List.range (min shiftVal 128)).map fun i => stageIn[i]!
      let (lost_or, lost_or_gates) := mkOrTree s!"b128_lost_{step}" lost_bits
      let stage_contrib := Wire.mk s!"b128_stk_c_{step}"
      let new_sticky := Wire.mk s!"b128_stk_{step}"
      let g_contrib := Gate.mkAND (shamt7[step]!) lost_or stage_contrib
      let g_sticky := Gate.mkOR prev_sticky stage_contrib new_sticky
      ((stageOut, new_sticky), acc.2 ++ gates ++ lost_or_gates ++ [g_contrib, g_sticky])
    ) ((bus128_init, zero), [])

  -- Magnitude < 1.0 check: flt_exp < 1023
  let (exp_lo10_all, exp_lo10_all_gates) := mkAndTree "exp_lo10" (List.range 10 |>.map fun i => flt_exp[i]!)
  let not_exp_lo10_all := Wire.mk "not_exp_lo10_all"
  let not_flt_exp10 := Wire.mk "not_flt_exp10"
  let flt_exp_lt_1023 := Wire.mk "flt_exp_lt_1023"
  let exp_lt_1023_gates := [
    Gate.mkNOT exp_lo10_all not_exp_lo10_all,
    Gate.mkNOT (flt_exp[10]!) not_flt_exp10,
    Gate.mkAND not_flt_exp10 not_exp_lo10_all flt_exp_lt_1023
  ]

  -- Integer magnitude from shifted bus: bits [63:0]
  -- If flt_exp_lt_1023 or flt_is_zero, integer magnitude is 0
  let flt_int_mag := makeIndexedWires "flt_int_mag" 64
  let flt_int_mag_gates := (List.range 64).map fun i =>
    Gate.mkMUX (bus128_out[i]!) zero flt_exp_lt_1023 (flt_int_mag[i]!)

  -- Discarded fractional bits:
  -- If flt_exp_lt_1023:
  --   round bit is 1 iff flt_exp == 1022 (magnitude in [0.5, 1.0))
  --   sticky bit is 1 iff mantissa nonzero or flt_exp < 1022
  let flt_exp_is_1022 := Wire.mk "flt_exp_is_1022"
  let not_flt_exp0 := Wire.mk "not_flt_exp0"
  let (exp_bits1_9_all, exp_b19_gates) := mkAndTree "exp_b19" (List.range 9 |>.map fun i => flt_exp[1 + i]!)
  let exp_1022_gates := exp_b19_gates ++ [
    Gate.mkNOT (flt_exp[0]!) not_flt_exp0,
    Gate.mkAND not_flt_exp10 exp_bits1_9_all (Wire.mk "e1022_t0"),
    Gate.mkAND (Wire.mk "e1022_t0") not_flt_exp0 flt_exp_is_1022
  ]

  let flt_round_bit := Wire.mk "flt_round_bit"
  let flt_sticky_bit := Wire.mk "flt_sticky_bit"
  let not_flt_is_zero := Wire.mk "not_flt_is_zero"
  let flt_stk_sub1 := Wire.mk "flt_stk_sub1"
  let flt_frac_gates := [
    Gate.mkNOT flt_is_zero not_flt_is_zero,
    Gate.mkMUX (bus128_out[127]!) flt_exp_is_1022 flt_exp_lt_1023 flt_round_bit,
    Gate.mkOR flt_mant_any (Wire.mk "not_e1022_nz") flt_stk_sub1,
    Gate.mkNOT flt_exp_is_1022 (Wire.mk "not_e1022"),
    Gate.mkAND (Wire.mk "not_e1022") not_flt_is_zero (Wire.mk "not_e1022_nz"),
    Gate.mkMUX bus_sticky flt_stk_sub1 flt_exp_lt_1023 flt_sticky_bit
  ]

  let flt_inexact := Wire.mk "flt_inexact"
  let flt_inexact_gate := Gate.mkOR flt_round_bit flt_sticky_bit flt_inexact

  -- Round up logic for Float -> Int64
  let flt_lsb := flt_int_mag[0]!
  let flt_stk_or_lsb := Wire.mk "flt_stk_lsb"
  let flt_rne_up := Wire.mk "flt_rne_up"
  let flt_rdn_up := Wire.mk "flt_rdn_up"
  let flt_rup_up := Wire.mk "flt_rup_up"
  let not_flt_sign := Wire.mk "not_flt_sign"
  let flt_round_up_raw := Wire.mk "flt_rnd_up_raw"
  let flt_round_up := Wire.mk "flt_rnd_up"

  let flt_round_gates := [
    Gate.mkNOT flt_sign not_flt_sign,
    Gate.mkOR flt_sticky_bit flt_lsb flt_stk_or_lsb,
    Gate.mkAND flt_round_bit flt_stk_or_lsb flt_rne_up,
    Gate.mkAND flt_sign flt_inexact flt_rdn_up,
    Gate.mkAND not_flt_sign flt_inexact flt_rup_up,
    Gate.mkAND rm_is_rne flt_rne_up (Wire.mk "flt_ru0"),
    Gate.mkAND rm_is_rdn flt_rdn_up (Wire.mk "flt_ru1"),
    Gate.mkAND rm_is_rup flt_rup_up (Wire.mk "flt_ru2"),
    Gate.mkAND rm_is_rmm flt_round_bit (Wire.mk "flt_ru3"),
    Gate.mkOR (Wire.mk "flt_ru0") (Wire.mk "flt_ru1") (Wire.mk "flt_ru_t0"),
    Gate.mkOR (Wire.mk "flt_ru2") (Wire.mk "flt_ru3") (Wire.mk "flt_ru_t1"),
    Gate.mkOR (Wire.mk "flt_ru_t0") (Wire.mk "flt_ru_t1") flt_round_up_raw,
    Gate.mkAND flt_round_up_raw flt_inexact flt_round_up
  ]

  -- Increment integer magnitude by flt_round_up
  let flt_int_mag_inc := makeIndexedWires "fimag_inc" 64
  let zeros64 := (List.range 64).map fun _ => zero
  let (fimag_add_gates, flt_mag_ovf) := mkKoggeStoneAdd (List.range 64 |>.map fun i => flt_int_mag[i]!) zeros64 flt_round_up flt_int_mag_inc "fimag_add"

  -- 2's complement negation if signed and negative: -flt_int_mag_inc
  let flt_int_neg := makeIndexedWires "flt_int_neg" 64
  let (fint_neg_gates, _) := mkKoggeStoneSub zeros64 (List.range 64 |>.map fun i => flt_int_mag_inc[i]!) flt_int_neg "fint_neg" one

  -- Un-clamped normal integer result
  let flt_int_norm := makeIndexedWires "flt_int_norm" 64
  let flt_int_norm_gates := (List.range 64).flatMap fun i =>
    let signed_val := Wire.mk s!"fint_sval_{i}"
    [Gate.mkMUX (flt_int_mag_inc[i]!) (flt_int_neg[i]!) flt_sign signed_val,
     Gate.mkMUX signed_val (flt_int_mag_inc[i]!) is_unsigned (flt_int_norm[i]!)]

  -- Overflow and Invalid Operation (NV) Detection:
  -- Exponent threshold checks:
  -- 1023 + 63 = 1086 (max signed exponent)
  -- 1023 + 64 = 1087 (max unsigned exponent)
  -- Let's detect if flt_exp >= 1086, >= 1087, >= 1088:
  -- 1088 = 0b10001000000 (bit 10=1, bit 6=1)
  -- Bits [9:6]: any bit set means flt_exp[9:0] >= 64, so flt_exp >= 1088
  let (exp_hi4_any, exp_hi4_any_gates) := mkOrTree "fexp_hi4" (List.range 4 |>.map fun i => flt_exp[6 + i]!)
  let exp_gte_1088 := Wire.mk "exp_gte_1088"
  let exp_gte_1088_gate := Gate.mkAND (flt_exp[10]!) exp_hi4_any exp_gte_1088

  -- Bits [5:0]: 1086 is 1024 + 62 = 0b10000111110
  -- 1087 is 1024 + 63 = 0b10000111111
  let (exp_lo6_all, exp_lo6_gates) := mkAndTree "exp_lo6" (List.range 6 |>.map fun i => flt_exp[i]!)
  let (exp_bits1_5_all, exp_b15_gates) := mkAndTree "exp_b15" (List.range 5 |>.map fun i => flt_exp[1 + i]!)

  let exp_gte_1087 := Wire.mk "exp_gte_1087"
  let exp_gte_1086 := Wire.mk "exp_gte_1086"
  let exp_ovf_gates := exp_hi4_any_gates ++ exp_lo6_gates ++ exp_b15_gates ++ [
    exp_gte_1088_gate,
    Gate.mkAND (flt_exp[10]!) exp_lo6_all (Wire.mk "e1087_t"),
    Gate.mkOR exp_gte_1088 (Wire.mk "e1087_t") exp_gte_1087,
    Gate.mkAND (flt_exp[10]!) exp_bits1_5_all (Wire.mk "e1086_t"),
    Gate.mkOR exp_gte_1088 (Wire.mk "e1086_t") exp_gte_1086
  ]

  -- Signed overflow:
  -- Positive overflow: not_flt_sign AND (exp_gte_1086 OR flt_int_mag_inc[63])
  let pos_signed_ovf := Wire.mk "pos_s_ovf"
  let pos_signed_ovf_gates := [
    Gate.mkOR exp_gte_1086 (flt_int_mag_inc[63]!) (Wire.mk "pso_t"),
    Gate.mkAND not_flt_sign (Wire.mk "pso_t") pos_signed_ovf
  ]

  -- Negative overflow: flt_sign AND (exp_gte_1087 OR (exp_gte_1086 AND mantissa_nonzero))
  let neg_signed_ovf := Wire.mk "neg_s_ovf"
  let neg_signed_ovf_gates := [
    Gate.mkAND exp_gte_1086 flt_mant_any (Wire.mk "nso_t0"),
    Gate.mkOR exp_gte_1087 (Wire.mk "nso_t0") (Wire.mk "nso_t1"),
    Gate.mkAND flt_sign (Wire.mk "nso_t1") neg_signed_ovf
  ]

  let signed_nv := Wire.mk "signed_nv"
  let signed_nv_gate := Gate.mkOR pos_signed_ovf neg_signed_ovf signed_nv

  -- Unsigned overflow:
  -- Positive: not_flt_sign AND (exp_gte_1087 OR flt_mag_ovf)
  let pos_unsigned_ovf := Wire.mk "pos_u_ovf"
  let pos_unsigned_ovf_gates := [
    Gate.mkOR exp_gte_1087 flt_mag_ovf (Wire.mk "puo_t"),
    Gate.mkAND not_flt_sign (Wire.mk "puo_t") pos_unsigned_ovf
  ]

  -- Negative input to unsigned:
  -- If negative and magnitude >= 1.0 (NOT exp_lt_1023): NV!
  -- If negative and magnitude < 1.0 and rounds to -1 (flt_round_up): NV!
  let neg_unsigned_ovf := Wire.mk "neg_u_ovf"
  let not_exp_lt_1023 := Wire.mk "not_exp_lt_1023"
  let neg_unsigned_ovf_gates := [
    Gate.mkNOT flt_exp_lt_1023 not_exp_lt_1023,
    Gate.mkAND not_exp_lt_1023 not_flt_is_zero (Wire.mk "nuo_ge1"),
    Gate.mkAND flt_round_up not_flt_is_zero (Wire.mk "nuo_rup"),
    Gate.mkOR (Wire.mk "nuo_ge1") (Wire.mk "nuo_rup") (Wire.mk "nuo_any"),
    Gate.mkAND flt_sign (Wire.mk "nuo_any") neg_unsigned_ovf
  ]

  let unsigned_nv := Wire.mk "unsigned_nv"
  let unsigned_nv_gate := Gate.mkOR pos_unsigned_ovf neg_unsigned_ovf unsigned_nv

  -- Master NV for Float -> Int64
  let flt_nv_raw := Wire.mk "flt_nv_raw"
  let flt_nv := Wire.mk "flt_nv"
  let flt_nv_gates := [
    Gate.mkMUX signed_nv unsigned_nv is_unsigned flt_nv_raw,
    Gate.mkOR flt_is_nan flt_is_inf (Wire.mk "nan_inf"),
    Gate.mkOR flt_nv_raw (Wire.mk "nan_inf") flt_nv,
    Gate.mkBUF flt_nv exc_nv
  ]

  -- Clamping logic on NV:
  -- Signed: if negative and NOT NaN -> 0x8000000000000000; else 0x7FFFFFFFFFFFFFFF
  -- Unsigned: if negative and NOT NaN -> 0x0000000000000000; else 0xFFFFFFFFFFFFFFFF
  let not_flt_nan := Wire.mk "not_flt_nan"
  let clamp_is_neg := Wire.mk "clamp_is_neg"
  let not_clamp_is_neg := Wire.mk "not_clamp_is_neg"
  let clamp_u_val := Wire.mk "clamp_u_val"
  let clamp_gates := [
    Gate.mkNOT flt_is_nan not_flt_nan,
    Gate.mkAND flt_sign not_flt_nan clamp_is_neg,
    Gate.mkNOT clamp_is_neg not_clamp_is_neg,
    Gate.mkOR flt_is_nan not_flt_sign clamp_u_val
  ]

  let res_flt_to_int_gates := (List.range 64).flatMap fun i =>
    let clamp_bit_signed :=
      if i == 63 then clamp_is_neg
      else not_clamp_is_neg
    let clamp_bit_unsigned := clamp_u_val
    let clamp_bit := Wire.mk s!"clamp_bit_{i}"
    let norm_bit := flt_int_norm[i]!
    [Gate.mkMUX clamp_bit_signed clamp_bit_unsigned is_unsigned clamp_bit,
     Gate.mkMUX norm_bit clamp_bit flt_nv (result[i]!)]

  -- Inexact for Float -> Int: flt_inexact AND NOT flt_nv
  let not_flt_nv := Wire.mk "not_flt_nv"
  let exc_nx_flt_to_int_gates := [
    Gate.mkNOT flt_nv not_flt_nv,
    Gate.mkAND flt_inexact not_flt_nv exc_nx
  ]

  let all_gates :=
    rm_inv_gates ++ rm_dec_gates ++
    sp_in_exp_ones_gates ++ sp_in_exp_any_gates ++ [sp_in_exp_zeros_gate] ++
    sp_in_mant_any_gates ++ [sp_in_mant_zeros_gate] ++ sp_in_class_gates ++
    norm_sp_dp_exp_gates ++ sp_as_dp_gates ++ flt_in_gates ++
    flt_exp_ones_gates ++ flt_exp_any_gates ++ [flt_exp_zeros_gate] ++
    flt_mant_any_gates ++ [flt_mant_zeros_gate] ++ flt_class_gates ++
    shamt_sub_gates ++ shamt7_gates ++ bus_shift_gates ++
    exp_lo10_all_gates ++ exp_lt_1023_gates ++ flt_int_mag_gates ++
    exp_1022_gates ++ flt_frac_gates ++ [flt_inexact_gate] ++
    flt_round_gates ++ fimag_add_gates ++ fint_neg_gates ++ flt_int_norm_gates ++
    exp_ovf_gates ++ pos_signed_ovf_gates ++ neg_signed_ovf_gates ++ [signed_nv_gate] ++
    pos_unsigned_ovf_gates ++ neg_unsigned_ovf_gates ++ [unsigned_nv_gate] ++
    flt_nv_gates ++ clamp_gates ++ res_flt_to_int_gates ++ exc_nx_flt_to_int_gates

  { name := "FPToInt64",
    inputs := src1 ++ [is_dp, is_unsigned] ++ rm ++ [zero, one],
    outputs := result ++ [exc_nv, exc_nx],
    gates := all_gates,
    instances := [],
    signalGroups := [
      { name := "src1", width := 64, wires := src1 },
      { name := "rm", width := 3, wires := rm },
      { name := "result", width := 64, wires := result }
    ],
    keepHierarchy := true }

def fpToInt64Circuit : Circuit := mkFPToInt64

end Shoumei.Circuits.Combinational
