/-
Circuits/Combinational/FPLongConverter.lean - 64-Bit FP/Integer Conversion Circuit

Implements all 64-bit integer conversion operations for RV64D/RV64F:
- FCVT.L.S  (op=0): SP float -> signed 64-bit int
- FCVT.LU.S (op=1): SP float -> unsigned 64-bit int
- FCVT.S.L  (op=2): signed 64-bit int -> SP float (NaN-boxed)
- FCVT.S.LU (op=3): unsigned 64-bit int -> SP float (NaN-boxed)
- FCVT.L.D  (op=4): DP float -> signed 64-bit int
- FCVT.LU.D (op=5): DP float -> unsigned 64-bit int
- FCVT.D.L  (op=6): signed 64-bit int -> DP float
- FCVT.D.LU (op=7): unsigned 64-bit int -> DP float

Interface:
- Inputs:
  * src1[63:0]: Operand
  * op[2:0]: Sub-op (bit2=DP, bit1=Int->FP, bit0=unsigned)
  * rm[2:0]: Rounding mode (0=RNE, 1=RTZ, 2=RDN, 3=RUP, 4=RMM)
  * zero, one: Constant wires
- Outputs:
  * result[63:0]: Converted value
  * exc[4:0]: Exceptions (NV, DZ, OF, UF, NX)
  * result_is_int: High when targeting INT PRF (Float -> Int)
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.KoggeStoneAdder

namespace Shoumei.Circuits.Combinational

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

/-- 64-bit FP/Integer Converter Circuit -/
def fpLongConverterCircuit : Circuit :=
  let src1 := makeIndexedWires "src1" 64
  let op := makeIndexedWires "op" 3
  let rm := makeIndexedWires "rm" 3
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  let result := makeIndexedWires "result" 64
  let exc := makeIndexedWires "exc" 5
  let result_is_int := Wire.mk "result_is_int"

  -- Opcode bit decoding
  let is_dp := op[2]!
  let is_int_to_fp := op[1]!
  let is_unsigned := op[0]!

  let not_is_dp := Wire.mk "not_is_dp"
  let not_is_int_to_fp := Wire.mk "not_is_int_to_fp"
  let not_is_unsigned := Wire.mk "not_is_unsigned"
  let op_inv_gates := [
    Gate.mkNOT is_dp not_is_dp,
    Gate.mkNOT is_int_to_fp not_is_int_to_fp,
    Gate.mkNOT is_unsigned not_is_unsigned,
    Gate.mkBUF not_is_int_to_fp result_is_int
  ]

  -- ══════════════════════════════════════════════
  -- PART 1: INT64 -> FLOAT (op[1] == 1)
  -- ══════════════════════════════════════════════

  -- Sign of integer input
  let int_is_signed := not_is_unsigned
  let int_sign := Wire.mk "int_sign"
  let int_sign_gate := Gate.mkAND (src1[63]!) int_is_signed int_sign

  -- Negation of integer input: 0 - src1
  let zeros64 := (List.range 64).map fun _ => zero
  let int_neg := makeIndexedWires "int_neg" 64
  let (int_neg_sub_gates, _) := mkKoggeStoneSub zeros64 (List.range 64 |>.map fun i => src1[i]!) int_neg "int_neg" one

  -- Absolute value of integer input
  let int_abs := makeIndexedWires "int_abs" 64
  let int_abs_gates := (List.range 64).map fun i =>
    Gate.mkMUX (src1[i]!) (int_neg[i]!) int_sign (int_abs[i]!)

  -- Check if int_abs is zero
  let (int_abs_any, int_abs_any_gates) := mkOrTree "int_abs_any" (List.range 64 |>.map fun i => int_abs[i]!)
  let int_is_zero := Wire.mk "int_is_zero"
  let int_is_zero_gate := Gate.mkNOT int_abs_any int_is_zero

  -- 64-bit Priority Encoder: find leading 1 in int_abs (63 down to 0)
  -- lead_pos: 6 bits (0..63)
  let pe_init := makeIndexedWires "pe_init" 6
  let pe_init_gates := (List.range 6).map fun k => Gate.mkBUF zero (pe_init[k]!)
  let (_, _, pe_fold_gates) := (List.range 64).foldl
    (fun (acc : Wire × (List Wire × List Gate)) idx =>
      let i := 63 - idx
      let old_found := acc.1
      let old_pos := acc.2.1
      let gates_acc := acc.2.2
      let nf := Wire.mk s!"pe_nf_{i}"
      let take := Wire.mk s!"pe_take_{i}"
      let g_nf := Gate.mkNOT old_found nf
      let g_take := Gate.mkAND (int_abs[i]!) nf take
      let new_found := Wire.mk s!"pe_found_{i}"
      let g_found := Gate.mkOR old_found (int_abs[i]!) new_found
      let new_pos := makeIndexedWires s!"pe_pos_{i}" 6
      let pos_gates := (List.range 6).map fun k =>
        let bit_k := if (i &&& (1 <<< k)) != 0 then one else zero
        Gate.mkMUX (old_pos[k]!) bit_k take (new_pos[k]!)
      (new_found, (new_pos, gates_acc ++ [g_nf, g_take, g_found] ++ pos_gates))
    ) (zero, (pe_init, []))

  let lead_pos_wires := makeIndexedWires "pe_pos_0" 6

  -- Shift left amount to normalize: shamt = 63 - lead_pos = ~lead_pos
  let norm_shamt := makeIndexedWires "norm_shamt" 6
  let norm_shamt_gates := (List.range 6).map fun i =>
    Gate.mkNOT (lead_pos_wires[i]!) (norm_shamt[i]!)

  -- 64-bit Barrel Left Shifter: int_abs << norm_shamt
  let (norm64, norm_shift_gates) := (List.range 6).foldl
    (fun (acc : List Wire × List Gate) step =>
      let stageIn := acc.1
      let shiftVal := Nat.pow 2 step
      let stageOut := makeIndexedWires s!"nsh_s{step}" 64
      let gates := (List.range 64).map fun i =>
        if i >= shiftVal then
          Gate.mkMUX (stageIn[i]!) (stageIn[i - shiftVal]!) (norm_shamt[step]!) (stageOut[i]!)
        else
          Gate.mkMUX (stageIn[i]!) zero (norm_shamt[step]!) (stageOut[i]!)
      (stageOut, acc.2 ++ gates)
    ) ((List.range 64 |>.map fun i => int_abs[i]!), [])

  -- Rounding mode decoding
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

  -- ── Subpart 1A: Int64 -> DP Float (FCVT.D.L / FCVT.D.LU) ──
  -- norm64[63] = hidden 1
  -- norm64[62:11] = 52 mantissa bits
  let dp_raw_mant := (List.range 52).map fun i => norm64[11 + i]!
  let dp_round_bit := norm64[10]!
  let (dp_sticky_bit, dp_sticky_gates) := mkOrTree "dp_stk" (List.range 10 |>.map fun i => norm64[i]!)

  let dp_inexact := Wire.mk "dp_inexact"
  let dp_inexact_gate := Gate.mkOR dp_round_bit dp_sticky_bit dp_inexact

  -- Round up logic for DP
  let dp_lsb := norm64[11]!
  let dp_stk_or_lsb := Wire.mk "dp_stk_lsb"
  let dp_rne_up := Wire.mk "dp_rne_up"
  let dp_rdn_up := Wire.mk "dp_rdn_up"
  let dp_rup_up := Wire.mk "dp_rup_up"
  let not_int_sign := Wire.mk "not_int_sign"
  let dp_round_up_raw := Wire.mk "dp_rnd_up_raw"
  let dp_round_up := Wire.mk "dp_rnd_up"

  let dp_round_gates := [
    Gate.mkNOT int_sign not_int_sign,
    Gate.mkOR dp_sticky_bit dp_lsb dp_stk_or_lsb,
    Gate.mkAND dp_round_bit dp_stk_or_lsb dp_rne_up,
    Gate.mkAND int_sign dp_inexact dp_rdn_up,
    Gate.mkAND not_int_sign dp_inexact dp_rup_up,
    -- Combine rounding modes
    Gate.mkAND rm_is_rne dp_rne_up (Wire.mk "dp_ru0"),
    Gate.mkAND rm_is_rdn dp_rdn_up (Wire.mk "dp_ru1"),
    Gate.mkAND rm_is_rup dp_rup_up (Wire.mk "dp_ru2"),
    Gate.mkAND rm_is_rmm dp_round_bit (Wire.mk "dp_ru3"),
    Gate.mkOR (Wire.mk "dp_ru0") (Wire.mk "dp_ru1") (Wire.mk "dp_ru_t0"),
    Gate.mkOR (Wire.mk "dp_ru2") (Wire.mk "dp_ru3") (Wire.mk "dp_ru_t1"),
    Gate.mkOR (Wire.mk "dp_ru_t0") (Wire.mk "dp_ru_t1") dp_round_up_raw,
    Gate.mkAND dp_round_up_raw dp_inexact dp_round_up
  ]

  -- DP Mantissa increment: dp_raw_mant + dp_round_up
  let dp_mant_inc := makeIndexedWires "dp_mant_inc" 52
  let zeros52 := (List.range 52).map fun _ => zero
  let (dp_mant_add_gates, dp_mant_ovf) := mkKoggeStoneAdd dp_raw_mant zeros52 dp_round_up dp_mant_inc "dp_mant_add"

  -- If mantissa overflows, new mantissa is 0 and exponent increments
  let dp_mant_final := makeIndexedWires "dp_mant_fin" 52
  let dp_mant_fin_gates := (List.range 52).map fun i =>
    Gate.mkMUX (dp_mant_inc[i]!) zero dp_mant_ovf (dp_mant_final[i]!)

  -- DP Exponent: 1023 + lead_pos + dp_mant_ovf
  -- 1023 in 11-bit binary is: 01111111111 (bits 0..9 are 1, bit 10 is 0)
  let const1023 := (List.range 10 |>.map fun _ => one) ++ [zero]
  let lead_pos_ext11 := (List.range 6 |>.map fun i => lead_pos_wires[i]!) ++ (List.range 5 |>.map fun _ => zero)
  let dp_exp_base := makeIndexedWires "dp_exp_base" 11
  let (dp_exp_add_gates, _) := mkKoggeStoneAdd const1023 lead_pos_ext11 dp_mant_ovf dp_exp_base "dp_exp_add"

  -- Assemble DP Float output: {int_sign, dp_exp_base[10:0], dp_mant_final[51:0]}
  let res_int_to_dp := makeIndexedWires "res_int_to_dp" 64
  let res_int_to_dp_gates := (List.range 64).map fun i =>
    let bit :=
      if i < 52 then dp_mant_final[i]!
      else if i < 63 then dp_exp_base[i - 52]!
      else int_sign
    Gate.mkMUX bit zero int_is_zero (res_int_to_dp[i]!)

  -- ── Subpart 1B: Int64 -> SP Float (FCVT.S.L / FCVT.S.LU) ──
  -- norm64[63] = hidden 1
  -- norm64[62:40] = 23 mantissa bits
  let sp_raw_mant := (List.range 23).map fun i => norm64[40 + i]!
  let sp_round_bit := norm64[39]!
  let (sp_sticky_bit, sp_sticky_gates) := mkOrTree "sp_stk" (List.range 39 |>.map fun i => norm64[i]!)

  let sp_inexact := Wire.mk "sp_inexact"
  let sp_inexact_gate := Gate.mkOR sp_round_bit sp_sticky_bit sp_inexact

  -- Round up logic for SP
  let sp_lsb := norm64[40]!
  let sp_stk_or_lsb := Wire.mk "sp_stk_lsb"
  let sp_rne_up := Wire.mk "sp_rne_up"
  let sp_rdn_up := Wire.mk "sp_rdn_up"
  let sp_rup_up := Wire.mk "sp_rup_up"
  let sp_round_up_raw := Wire.mk "sp_rnd_up_raw"
  let sp_round_up := Wire.mk "sp_rnd_up"

  let sp_round_gates := [
    Gate.mkOR sp_sticky_bit sp_lsb sp_stk_or_lsb,
    Gate.mkAND sp_round_bit sp_stk_or_lsb sp_rne_up,
    Gate.mkAND int_sign sp_inexact sp_rdn_up,
    Gate.mkAND not_int_sign sp_inexact sp_rup_up,
    Gate.mkAND rm_is_rne sp_rne_up (Wire.mk "sp_ru0"),
    Gate.mkAND rm_is_rdn sp_rdn_up (Wire.mk "sp_ru1"),
    Gate.mkAND rm_is_rup sp_rup_up (Wire.mk "sp_ru2"),
    Gate.mkAND rm_is_rmm sp_round_bit (Wire.mk "sp_ru3"),
    Gate.mkOR (Wire.mk "sp_ru0") (Wire.mk "sp_ru1") (Wire.mk "sp_ru_t0"),
    Gate.mkOR (Wire.mk "sp_ru2") (Wire.mk "sp_ru3") (Wire.mk "sp_ru_t1"),
    Gate.mkOR (Wire.mk "sp_ru_t0") (Wire.mk "sp_ru_t1") sp_round_up_raw,
    Gate.mkAND sp_round_up_raw sp_inexact sp_round_up
  ]

  -- SP Mantissa increment: sp_raw_mant + sp_round_up
  let sp_mant_inc := makeIndexedWires "sp_mant_inc" 23
  let zeros23 := (List.range 23).map fun _ => zero
  let (sp_mant_add_gates, sp_mant_ovf) := mkKoggeStoneAdd sp_raw_mant zeros23 sp_round_up sp_mant_inc "sp_mant_add"

  let sp_mant_final := makeIndexedWires "sp_mant_fin" 23
  let sp_mant_fin_gates := (List.range 23).map fun i =>
    Gate.mkMUX (sp_mant_inc[i]!) zero sp_mant_ovf (sp_mant_final[i]!)

  -- SP Exponent: 127 + lead_pos + sp_mant_ovf
  -- 127 in 8-bit binary is: 01111111 (bits 0..6 are 1, bit 7 is 0)
  let const127 := (List.range 7 |>.map fun _ => one) ++ [zero]
  let lead_pos_ext8 := (List.range 6 |>.map fun i => lead_pos_wires[i]!) ++ [zero, zero]
  let sp_exp_base := makeIndexedWires "sp_exp_base" 8
  let (sp_exp_add_gates, _) := mkKoggeStoneAdd const127 lead_pos_ext8 sp_mant_ovf sp_exp_base "sp_exp_add"

  -- Assemble SP Float output (NaN-boxed: upper 32 bits all 1s)
  let res_int_to_sp := makeIndexedWires "res_int_to_sp" 64
  let res_int_to_sp_gates := (List.range 64).map fun i =>
    if i >= 32 then
      Gate.mkBUF one (res_int_to_sp[i]!)
    else
      let bit :=
        if i < 23 then sp_mant_final[i]!
        else if i < 31 then sp_exp_base[i - 23]!
        else int_sign
      Gate.mkMUX bit zero int_is_zero (res_int_to_sp[i]!)

  -- Inexact flag for Int -> FP
  let exc_nx_int_to_fp := Wire.mk "exc_nx_int_to_fp"
  let exc_nx_int_to_fp_gate := Gate.mkMUX sp_inexact dp_inexact is_dp exc_nx_int_to_fp

  -- ══════════════════════════════════════════════
  -- PART 2: FLOAT -> INT64 (op[1] == 0)
  -- ══════════════════════════════════════════════

  -- For SP float inputs (op[2] == 0): losslessly expand SP to DP float
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
  let (fimag_add_gates, flt_mag_ovf) := mkKoggeStoneAdd (List.range 64 |>.map fun i => flt_int_mag[i]!) zeros64 flt_round_up flt_int_mag_inc "fimag_add"

  -- 2's complement negation if signed and negative: -flt_int_mag_inc
  let flt_int_neg := makeIndexedWires "flt_int_neg" 64
  let (fint_neg_gates, _) := mkKoggeStoneSub zeros64 (List.range 64 |>.map fun i => flt_int_mag_inc[i]!) flt_int_neg "fint_neg" one

  -- Un-clamped normal integer result
  let flt_int_norm := makeIndexedWires "flt_int_norm" 64
  let flt_int_norm_gates := (List.range 64).map fun i =>
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
    Gate.mkOR flt_nv_raw (Wire.mk "nan_inf") flt_nv
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

  let res_flt_to_int := makeIndexedWires "res_flt_to_int" 64
  let res_flt_to_int_gates := (List.range 64).flatMap fun i =>
    let clamp_bit_signed :=
      if i == 63 then clamp_is_neg
      else not_clamp_is_neg
    let clamp_bit_unsigned := clamp_u_val
    let clamp_bit := Wire.mk s!"clamp_bit_{i}"
    let norm_bit := flt_int_norm[i]!
    [Gate.mkMUX clamp_bit_signed clamp_bit_unsigned is_unsigned clamp_bit,
     Gate.mkMUX norm_bit clamp_bit flt_nv (res_flt_to_int[i]!)]

  -- Inexact for Float -> Int: flt_inexact AND NOT flt_nv
  let not_flt_nv := Wire.mk "not_flt_nv"
  let exc_nx_flt_to_int := Wire.mk "exc_nx_flt_to_int"
  let exc_nx_flt_to_int_gates := [
    Gate.mkNOT flt_nv not_flt_nv,
    Gate.mkAND flt_inexact not_flt_nv exc_nx_flt_to_int
  ]

  -- ══════════════════════════════════════════════
  -- PART 3: MASTER MULTIPLEXING AND EXCEPTIONS
  -- ══════════════════════════════════════════════

  -- Select between Float -> Int and Int -> Float outputs
  let res_int_to_fp := makeIndexedWires "res_int_to_fp" 64
  let res_int_to_fp_gates := (List.range 64).map fun i =>
    Gate.mkMUX (res_int_to_sp[i]!) (res_int_to_dp[i]!) is_dp (res_int_to_fp[i]!)

  let master_result_gates := (List.range 64).map fun i =>
    Gate.mkMUX (res_flt_to_int[i]!) (res_int_to_fp[i]!) is_int_to_fp (result[i]!)

  -- Exceptions:
  -- exc[4] = NV: active only for Float -> Int (flt_nv)
  -- exc[3] = DZ: always 0
  -- exc[2] = OF: always 0
  -- exc[1] = UF: always 0
  -- exc[0] = NX: active for both
  let master_exc_nv := Wire.mk "m_exc_nv"
  let master_exc_nx := Wire.mk "m_exc_nx"
  let master_exc_gates := [
    Gate.mkAND flt_nv not_is_int_to_fp master_exc_nv,
    Gate.mkMUX exc_nx_flt_to_int exc_nx_int_to_fp is_int_to_fp master_exc_nx,
    Gate.mkBUF master_exc_nv (exc[4]!),
    Gate.mkBUF zero (exc[3]!),
    Gate.mkBUF zero (exc[2]!),
    Gate.mkBUF zero (exc[1]!),
    Gate.mkBUF master_exc_nx (exc[0]!)
  ]

  let all_gates :=
    op_inv_gates ++
    [int_sign_gate] ++ int_neg_sub_gates ++ int_abs_gates ++
    int_abs_any_gates ++ [int_is_zero_gate] ++
    pe_init_gates ++ pe_fold_gates ++ norm_shamt_gates ++ norm_shift_gates ++
    rm_inv_gates ++ rm_dec_gates ++
    dp_sticky_gates ++ [dp_inexact_gate] ++ dp_round_gates ++ dp_mant_add_gates ++ dp_mant_fin_gates ++
    dp_exp_add_gates ++ res_int_to_dp_gates ++
    sp_sticky_gates ++ [sp_inexact_gate] ++ sp_round_gates ++ sp_mant_add_gates ++ sp_mant_fin_gates ++
    sp_exp_add_gates ++ res_int_to_sp_gates ++ [exc_nx_int_to_fp_gate] ++
    sp_in_exp_ones_gates ++ sp_in_exp_any_gates ++ [sp_in_exp_zeros_gate] ++
    sp_in_mant_any_gates ++ [sp_in_mant_zeros_gate] ++ sp_in_class_gates ++
    norm_sp_dp_exp_gates ++ sp_as_dp_gates ++ flt_in_gates ++
    flt_exp_ones_gates ++ flt_exp_any_gates ++ [flt_exp_zeros_gate] ++
    flt_mant_any_gates ++ [flt_mant_zeros_gate] ++ flt_class_gates ++
    shamt_sub_gates ++ shamt7_gates ++ bus_shift_gates ++
    exp_lo10_all_gates ++ exp_lt_1023_gates ++ flt_int_mag_gates ++
    exp_1022_gates ++ flt_frac_gates ++ [flt_inexact_gate] ++
    flt_round_gates ++ fimag_add_gates ++ fint_neg_gates ++ flt_int_norm_gates.flatten ++
    exp_ovf_gates ++ pos_signed_ovf_gates ++ neg_signed_ovf_gates ++ [signed_nv_gate] ++
    pos_unsigned_ovf_gates ++ neg_unsigned_ovf_gates ++ [unsigned_nv_gate] ++
    flt_nv_gates ++ clamp_gates ++ res_flt_to_int_gates ++ exc_nx_flt_to_int_gates ++
    res_int_to_fp_gates ++ master_result_gates ++ master_exc_gates

  { name := "FPLongConverter",
    inputs := src1 ++ op ++ rm ++ [zero, one],
    outputs := result ++ exc ++ [result_is_int],
    gates := all_gates,
    instances := [] }

end Shoumei.Circuits.Combinational
