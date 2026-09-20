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
import Shoumei.Components.Select
import Shoumei.Circuits.Combinational.KoggeStoneAdder

namespace Shoumei.Circuits.Combinational

open Shoumei
open Shoumei.Components

private def mkBalancedOrTree (pfx : String) (inputs : List Wire) : Wire × List Gate :=
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

/-- 8-bit Priority Encoder: finds leading 1 (b7 down to b0), returns (has_1, pos[2:0], gates) -/
private def mkPE8 (pfx : String) (b : List Wire) : Wire × List Wire × List Gate :=
  let b0 := b[0]!
  let b1 := b[1]!
  let b2 := b[2]!
  let b3 := b[3]!
  let b4 := b[4]!
  let b5 := b[5]!
  let b6 := b[6]!
  let b7 := b[7]!
  let hi_pair := Wire.mk s!"{pfx}_hipair"
  let g_hipair := Gate.mkOR b7 b6 hi_pair
  let hi_lo := Wire.mk s!"{pfx}_hilo"
  let g_hilo := Gate.mkOR b5 b4 hi_lo
  let hi4 := Wire.mk s!"{pfx}_hi4"
  let g_hi4 := Gate.mkOR hi_pair hi_lo hi4

  let lo_pair := Wire.mk s!"{pfx}_lopair"
  let g_lopair := Gate.mkOR b3 b2 lo_pair
  let lo_lo := Wire.mk s!"{pfx}_lolo"
  let g_lolo := Gate.mkOR b1 b0 lo_lo
  let lo4 := Wire.mk s!"{pfx}_lo4"
  let g_lo4 := Gate.mkOR lo_pair lo_lo lo4

  let has_1 := Wire.mk s!"{pfx}_has1"
  let g_has1 := Gate.mkOR hi4 lo4 has_1

  let pos2 := hi4

  let pos1 := Wire.mk s!"{pfx}_pos1"
  let g_pos1 := Gate.mkMUX lo_pair hi_pair hi4 pos1

  let not_b6 := Wire.mk s!"{pfx}_nb6"
  let g_nb6 := Gate.mkNOT b6 not_b6
  let b65 := Wire.mk s!"{pfx}_b65"
  let g_b65 := Gate.mkAND not_b6 b5 b65
  let hi_b0 := Wire.mk s!"{pfx}_hib0"
  let g_hib0 := Gate.mkOR b7 b65 hi_b0

  let not_b2 := Wire.mk s!"{pfx}_nb2"
  let g_nb2 := Gate.mkNOT b2 not_b2
  let b21 := Wire.mk s!"{pfx}_b21"
  let g_b21 := Gate.mkAND not_b2 b1 b21
  let lo_b0 := Wire.mk s!"{pfx}_lob0"
  let g_lob0 := Gate.mkOR b3 b21 lo_b0

  let pos0 := Wire.mk s!"{pfx}_pos0"
  let g_pos0 := Gate.mkMUX lo_b0 hi_b0 hi4 pos0

  let gates := [g_hipair, g_hilo, g_hi4, g_lopair, g_lolo, g_lo4, g_has1,
                g_pos1, g_nb6, g_b65, g_hib0, g_nb2, g_b21, g_lob0, g_pos0]
  (has_1, [pos0, pos1, pos2], gates)

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
  let (int_neg_sub_gates, _) := mkSubFor (AdderSpec.minArea 64 .one) zeros64 (List.range 64 |>.map fun i => src1[i]!) int_neg "int_neg" one

  -- Absolute value of integer input
  let int_abs := makeIndexedWires "int_abs" 64
  let int_abs_gates := (List.range 64).map fun i =>
    Gate.mkMUX (src1[i]!) (int_neg[i]!) int_sign (int_abs[i]!)

  -- Check if int_abs is zero and find leading 1 (63 down to 0) via 8x8 tree priority encoder
  let group_pe_results := (List.range 8).map fun g =>
    let group_bits := (List.range 8).map fun j => int_abs[8 * g + j]!
    mkPE8 s!"grp_pe_{g}" group_bits

  let grp_has_1 := group_pe_results.map (·.1)
  let grp_pos3 := group_pe_results.map (·.2.1)
  let grp_pe_gates := group_pe_results.flatMap (·.2.2)

  let (int_abs_any, top_pos3, top_pe_gates) := mkPE8 "top_pe" grp_has_1
  let int_is_zero := Wire.mk "int_is_zero"
  let int_is_zero_gate := Gate.mkNOT int_abs_any int_is_zero

  let lead_pos_wires := makeIndexedWires "pe_lead_pos" 6
  let lead_pos_hi_gates := [
    Gate.mkBUF (top_pos3[0]!) (lead_pos_wires[3]!),
    Gate.mkBUF (top_pos3[1]!) (lead_pos_wires[4]!),
    Gate.mkBUF (top_pos3[2]!) (lead_pos_wires[5]!)
  ]

  let mux8_low_gates := (List.range 3).flatMap fun bit_idx =>
    let m01 := Wire.mk s!"lp_m01_{bit_idx}"
    let m23 := Wire.mk s!"lp_m23_{bit_idx}"
    let m45 := Wire.mk s!"lp_m45_{bit_idx}"
    let m67 := Wire.mk s!"lp_m67_{bit_idx}"
    let g01 := Gate.mkMUX ((grp_pos3[0]!)[bit_idx]!) ((grp_pos3[1]!)[bit_idx]!) (top_pos3[0]!) m01
    let g23 := Gate.mkMUX ((grp_pos3[2]!)[bit_idx]!) ((grp_pos3[3]!)[bit_idx]!) (top_pos3[0]!) m23
    let g45 := Gate.mkMUX ((grp_pos3[4]!)[bit_idx]!) ((grp_pos3[5]!)[bit_idx]!) (top_pos3[0]!) m45
    let g67 := Gate.mkMUX ((grp_pos3[6]!)[bit_idx]!) ((grp_pos3[7]!)[bit_idx]!) (top_pos3[0]!) m67
    let m0123 := Wire.mk s!"lp_m0123_{bit_idx}"
    let m4567 := Wire.mk s!"lp_m4567_{bit_idx}"
    let g0123 := Gate.mkMUX m01 m23 (top_pos3[1]!) m0123
    let g4567 := Gate.mkMUX m45 m67 (top_pos3[1]!) m4567
    let g_final := Gate.mkMUX m0123 m4567 (top_pos3[2]!) (lead_pos_wires[bit_idx]!)
    [g01, g23, g45, g67, g0123, g4567, g_final]

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
  let (dp_sticky_bit, dp_sticky_gates) := mkBalancedOrTree "dp_stk" (List.range 10 |>.map fun i => norm64[i]!)
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
  let (dp_mant_add_gates, dp_mant_ovf) := mkAddFor (AdderSpec.minArea dp_raw_mant.length .input) dp_raw_mant zeros52 dp_round_up dp_mant_inc "dp_mant_add"

  let dp_mant_final := makeIndexedWires "dp_mant_fin" 52
  let dp_mant_fin_gates := (List.range 52).map fun i =>
    Gate.mkMUX (dp_mant_inc[i]!) zero dp_mant_ovf (dp_mant_final[i]!)

  let const1023 := (List.range 10 |>.map fun _ => one) ++ [zero]
  let lead_pos_ext11 := (List.range 6 |>.map fun i => lead_pos_wires[i]!) ++ (List.range 5 |>.map fun _ => zero)
  let dp_exp_base := makeIndexedWires "dp_exp_base" 11
  let (dp_exp_add_gates, _) := mkAddFor (AdderSpec.minArea const1023.length .input) const1023 lead_pos_ext11 dp_mant_ovf dp_exp_base "dp_exp_add"

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
  let (sp_sticky_bit, sp_sticky_gates) := mkBalancedOrTree "sp_stk" (List.range 39 |>.map fun i => norm64[i]!)
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
  let (sp_mant_add_gates, sp_mant_ovf) := mkAddFor (AdderSpec.minArea sp_raw_mant.length .input) sp_raw_mant zeros23 sp_round_up sp_mant_inc "sp_mant_add"

  let sp_mant_final := makeIndexedWires "sp_mant_fin" 23
  let sp_mant_fin_gates := (List.range 23).map fun i =>
    Gate.mkMUX (sp_mant_inc[i]!) zero sp_mant_ovf (sp_mant_final[i]!)

  let const127 := (List.range 7 |>.map fun _ => one) ++ [zero]
  let lead_pos_ext8 := (List.range 6 |>.map fun i => lead_pos_wires[i]!) ++ [zero, zero]
  let sp_exp_base := makeIndexedWires "sp_exp_base" 8
  let (sp_exp_add_gates, _) := mkAddFor (AdderSpec.minArea const127.length .input) const127 lead_pos_ext8 sp_mant_ovf sp_exp_base "sp_exp_add"

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
    grp_pe_gates ++ top_pe_gates ++ [int_is_zero_gate] ++
    lead_pos_hi_gates ++ mux8_low_gates ++
    norm_shamt_gates ++ norm_shift_gates ++
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
