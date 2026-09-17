/-
Circuits/Combinational/Int64ToFP.lean - 64-Bit Integer to Float Conversion Submodule

Submodule of FPLongConverter implementing:
- FCVT.S.L  (signed 64-bit int -> SP float, NaN-boxed)
- FCVT.S.LU (unsigned 64-bit int -> SP float, NaN-boxed)
- FCVT.D.L  (signed 64-bit int -> DP float)
- FCVT.D.LU (unsigned 64-bit int -> DP float)

Interface:
- Inputs:
  * src1[63:0]: Integer operand
  * is_dp: High for double-precision float output, low for single-precision
  * is_unsigned: High for unsigned integer, low for signed integer
  * rm[2:0]: Rounding mode (0=RNE, 1=RTZ, 2=RDN, 3=RUP, 4=RMM)
  * zero, one: Constant wires
- Outputs:
  * result[63:0]: Converted float value (NaN-boxed for SP)
  * exc_nx: Inexact exception flag
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

/-- 64-bit Integer to Float Converter Circuit -/
def mkInt64ToFP : Circuit :=
  let src1 := makeIndexedWires "src1" 64
  let is_dp := Wire.mk "is_dp"
  let is_unsigned := Wire.mk "is_unsigned"
  let rm := makeIndexedWires "rm" 3
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  let result := makeIndexedWires "result" 64
  let exc_nx := Wire.mk "exc_nx"

  let not_is_unsigned := Wire.mk "not_is_unsigned"
  let not_is_unsigned_gate := Gate.mkNOT is_unsigned not_is_unsigned

  -- Sign of integer input
  let int_is_signed := not_is_unsigned
  let int_sign := Wire.mk "int_sign"
  let int_sign_gate := Gate.mkAND (src1[63]!) int_is_signed int_sign
  let not_int_sign := Wire.mk "not_int_sign"
  let not_int_sign_gate := Gate.mkNOT int_sign not_int_sign

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
  let rm_is_rne := Wire.mk "rm_is_rne"
  let rm_is_rtz := Wire.mk "rm_is_rtz"
  let rm_is_rdn := Wire.mk "rm_is_rdn"
  let rm_is_rup := Wire.mk "rm_is_rup"
  let rm_is_rmm := Wire.mk "rm_is_rmm"
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

  -- ── Subpart 1A: Int64 -> DP Float ──
  let dp_raw_mant := (List.range 52).map fun i => norm64[11 + i]!
  let dp_round_bit := norm64[10]!
  let (dp_sticky_bit, dp_sticky_gates) := mkOrTree "dp_stk" (List.range 10 |>.map fun i => norm64[i]!)
  let dp_inexact := Wire.mk "dp_inexact"
  let dp_inexact_gate := Gate.mkOR dp_round_bit dp_sticky_bit dp_inexact

  let dp_lsb := norm64[11]!
  let dp_stk_or_lsb := Wire.mk "dp_stk_lsb"
  let dp_rne_up := Wire.mk "dp_rne_up"
  let dp_rdn_up := Wire.mk "dp_rdn_up"
  let dp_rup_up := Wire.mk "dp_rup_up"
  let dp_round_up_raw := Wire.mk "dp_rnd_up_raw"
  let dp_round_up := Wire.mk "dp_rnd_up"
  let dp_round_gates := [
    Gate.mkOR dp_sticky_bit dp_lsb dp_stk_or_lsb,
    Gate.mkAND dp_round_bit dp_stk_or_lsb dp_rne_up,
    Gate.mkAND int_sign dp_inexact dp_rdn_up,
    Gate.mkAND not_int_sign dp_inexact dp_rup_up,
    Gate.mkAND rm_is_rne dp_rne_up (Wire.mk "dp_ru0"),
    Gate.mkAND rm_is_rdn dp_rdn_up (Wire.mk "dp_ru1"),
    Gate.mkAND rm_is_rup dp_rup_up (Wire.mk "dp_ru2"),
    Gate.mkAND rm_is_rmm dp_round_bit (Wire.mk "dp_ru3"),
    Gate.mkOR (Wire.mk "dp_ru0") (Wire.mk "dp_ru1") (Wire.mk "dp_ru_t0"),
    Gate.mkOR (Wire.mk "dp_ru2") (Wire.mk "dp_ru3") (Wire.mk "dp_ru_t1"),
    Gate.mkOR (Wire.mk "dp_ru_t0") (Wire.mk "dp_ru_t1") dp_round_up_raw,
    Gate.mkAND dp_round_up_raw dp_inexact dp_round_up
  ]

  let dp_mant_inc := makeIndexedWires "dp_mant_inc" 52
  let zeros52 := (List.range 52).map fun _ => zero
  let (dp_mant_add_gates, dp_mant_ovf) := mkKoggeStoneAdd dp_raw_mant zeros52 dp_round_up dp_mant_inc "dp_mant_add"

  let dp_mant_final := makeIndexedWires "dp_mant_fin" 52
  let dp_mant_fin_gates := (List.range 52).map fun i =>
    Gate.mkMUX (dp_mant_inc[i]!) zero dp_mant_ovf (dp_mant_final[i]!)

  let const1023 := (List.range 10 |>.map fun _ => one) ++ [zero]
  let lead_pos_ext11 := (List.range 6 |>.map fun i => lead_pos_wires[i]!) ++ (List.range 5 |>.map fun _ => zero)
  let dp_exp_base := makeIndexedWires "dp_exp_base" 11
  let (dp_exp_add_gates, _) := mkKoggeStoneAdd const1023 lead_pos_ext11 dp_mant_ovf dp_exp_base "dp_exp_add"

  let res_int_to_dp := makeIndexedWires "res_int_to_dp" 64
  let res_int_to_dp_gates := (List.range 64).map fun i =>
    let bit :=
      if i < 52 then dp_mant_final[i]!
      else if i < 63 then dp_exp_base[i - 52]!
      else int_sign
    Gate.mkMUX bit zero int_is_zero (res_int_to_dp[i]!)

  -- ── Subpart 1B: Int64 -> SP Float ──
  let sp_raw_mant := (List.range 23).map fun i => norm64[40 + i]!
  let sp_round_bit := norm64[39]!
  let (sp_sticky_bit, sp_sticky_gates) := mkOrTree "sp_stk" (List.range 39 |>.map fun i => norm64[i]!)
  let sp_inexact := Wire.mk "sp_inexact"
  let sp_inexact_gate := Gate.mkOR sp_round_bit sp_sticky_bit sp_inexact

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

  let sp_mant_inc := makeIndexedWires "sp_mant_inc" 23
  let zeros23 := (List.range 23).map fun _ => zero
  let (sp_mant_add_gates, sp_mant_ovf) := mkKoggeStoneAdd sp_raw_mant zeros23 sp_round_up sp_mant_inc "sp_mant_add"

  let sp_mant_final := makeIndexedWires "sp_mant_fin" 23
  let sp_mant_fin_gates := (List.range 23).map fun i =>
    Gate.mkMUX (sp_mant_inc[i]!) zero sp_mant_ovf (sp_mant_final[i]!)

  let const127 := (List.range 7 |>.map fun _ => one) ++ [zero]
  let lead_pos_ext8 := (List.range 6 |>.map fun i => lead_pos_wires[i]!) ++ [zero, zero]
  let sp_exp_base := makeIndexedWires "sp_exp_base" 8
  let (sp_exp_add_gates, _) := mkKoggeStoneAdd const127 lead_pos_ext8 sp_mant_ovf sp_exp_base "sp_exp_add"

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

  let exc_nx_int_to_fp := Wire.mk "exc_nx_int_to_fp"
  let exc_nx_int_to_fp_gate := Gate.mkMUX sp_inexact dp_inexact is_dp exc_nx_int_to_fp
  let exc_nx_out_gate := Gate.mkBUF exc_nx_int_to_fp exc_nx

  -- Select between DP and SP float result
  let res_out_gates := (List.range 64).map fun i =>
    Gate.mkMUX (res_int_to_sp[i]!) (res_int_to_dp[i]!) is_dp (result[i]!)

  let all_gates :=
    [not_is_unsigned_gate, int_sign_gate, not_int_sign_gate] ++
    int_neg_sub_gates ++ int_abs_gates ++
    int_abs_any_gates ++ [int_is_zero_gate] ++
    pe_init_gates ++ pe_fold_gates ++ norm_shamt_gates ++ norm_shift_gates ++
    rm_inv_gates ++ rm_dec_gates ++
    dp_sticky_gates ++ [dp_inexact_gate] ++ dp_round_gates ++ dp_mant_add_gates ++ dp_mant_fin_gates ++
    dp_exp_add_gates ++ res_int_to_dp_gates ++
    sp_sticky_gates ++ [sp_inexact_gate] ++ sp_round_gates ++ sp_mant_add_gates ++ sp_mant_fin_gates ++
    sp_exp_add_gates ++ res_int_to_sp_gates ++ [exc_nx_int_to_fp_gate, exc_nx_out_gate] ++
    res_out_gates

  { name := "Int64ToFP",
    inputs := src1 ++ [is_dp, is_unsigned] ++ rm ++ [zero, one],
    outputs := result ++ [exc_nx],
    gates := all_gates,
    instances := [],
    signalGroups := [
      { name := "src1", width := 64, wires := src1 },
      { name := "rm", width := 3, wires := rm },
      { name := "result", width := 64, wires := result }
    ],
    keepHierarchy := true }

def int64ToFPCircuit : Circuit := mkInt64ToFP

end Shoumei.Circuits.Combinational
