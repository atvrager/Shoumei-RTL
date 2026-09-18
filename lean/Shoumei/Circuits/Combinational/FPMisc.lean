/-
Circuits/Combinational/FPMisc.lean - FP Miscellaneous Operations Circuit

Implements single-cycle FP bit-manipulation operations for RV32F:
  FSGNJ, FSGNJN, FSGNJX, FMV.X.W, FMV.W.X,
  FEQ.S, FLT.S, FLE.S, FCVT.W.S, FMIN.S, FMAX.S, FCVT.S.W, FCLASS.S

Hierarchical decomposition into 4 modular sub-units:
  - FPSgnj: Sign injection and moves (FSGNJ, FSGNJN, FSGNJX, FMV.X.W, FMV.W.X)
  - FPCompare: Comparisons and min/max (FEQ.S, FLT.S, FLE.S, FMIN.S, FMAX.S)
  - FPClass: Floating-point classification (FCLASS.S)
  - FPCvtInt: Float/integer conversions (FCVT.W.S, FCVT.WU.S, FCVT.S.W, FCVT.S.WU)

Inputs:
  - src1[31:0], src2[31:0] - source operands
  - op[4:0] - operation select
  - rm[2:0] - rounding mode (RNE=0, RTZ=1, RDN=2, RUP=3, RMM=4)
  - zero, one - constant wires

Outputs:
  - result[31:0] - operation result
  - exc[4:0] - exception flags (NV, DZ, OF, UF, NX)
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.KoggeStoneAdder

namespace Shoumei.Circuits.Combinational

set_option maxRecDepth 8192

open Shoumei

/-- OR-reduce: returns (wire, gates) where wire = OR of all input wires.
    Requires inputs.length >= 1. -/
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

/-- N-bit subtractor: a - b, returns (diff wires, borrow_out wire, gates).
    borrow_out=1 means a < b (unsigned). -/
private def mkRippleSub (pfx : String) (a b : List Wire) (n : Nat) (borrowIn : Wire) :
    List Wire × Wire × List Gate :=
  let diff := makeIndexedWires s!"{pfx}_d" n
  let (_, gates) := (List.range n).foldl (fun (acc : Wire × List Gate) i =>
    let bin := acc.1
    let xor1 := Wire.mk s!"{pfx}_xor1_{i}"
    let g_xor1 := Gate.mkXOR (a[i]!) (b[i]!) xor1
    let g_diff := Gate.mkXOR xor1 bin (diff[i]!)
    let na := Wire.mk s!"{pfx}_na_{i}"
    let t0 := Wire.mk s!"{pfx}_bt0_{i}"
    let t1 := Wire.mk s!"{pfx}_bt1_{i}"
    let t2 := Wire.mk s!"{pfx}_bt2_{i}"
    let or0 := Wire.mk s!"{pfx}_bor0_{i}"
    let bout := Wire.mk s!"{pfx}_bo_{i}"
    let g_na := Gate.mkNOT (a[i]!) na
    let g_t0 := Gate.mkAND na (b[i]!) t0
    let g_t1 := Gate.mkAND na bin t1
    let g_t2 := Gate.mkAND (b[i]!) bin t2
    let g_or0 := Gate.mkOR t0 t1 or0
    let g_bout := Gate.mkOR or0 t2 bout
    (bout, acc.2 ++ [g_xor1, g_diff, g_na, g_t0, g_t1, g_t2, g_or0, g_bout])
  ) (borrowIn, [])
  let borrowOut := Wire.mk s!"{pfx}_bo_{n - 1}"
  (diff, borrowOut, gates)

/-- Right barrel shifter: shift data right by amount (log2 n bits).
    Returns (result wires, gates). Only uses lower shBits of shift amount. -/
private def mkBarrelShiftRight (pfx : String) (data : List Wire) (n : Nat)
    (shiftAmt : List Wire) (shBits : Nat) (zeroW : Wire) : List Wire × List Gate :=
  let (finalData, allGates) := (List.range shBits).foldl (fun (acc : List Wire × List Gate) stage =>
    let prev := acc.1
    let shift := Nat.pow 2 stage
    let cur := makeIndexedWires s!"{pfx}_s{stage}" n
    let stageGates := (List.range n).map fun i =>
      if i + shift < n then
        Gate.mkMUX (prev[i]!) (prev[i + shift]!) (shiftAmt[stage]!) (cur[i]!)
      else
        Gate.mkMUX (prev[i]!) zeroW (shiftAmt[stage]!) (cur[i]!)
    (cur, acc.2 ++ stageGates)
  ) (data, [])
  (finalData, allGates)

/-- Left barrel shifter: shift data left by amount (log2 n bits).
    Returns (result wires, gates). -/
private def mkBarrelShiftLeft (pfx : String) (data : List Wire) (n : Nat)
    (shiftAmt : List Wire) (shBits : Nat) (zeroW : Wire) : List Wire × List Gate :=
  let (finalData, allGates) := (List.range shBits).foldl (fun (acc : List Wire × List Gate) stage =>
    let prev := acc.1
    let shift := Nat.pow 2 stage
    let cur := makeIndexedWires s!"{pfx}_s{stage}" n
    let stageGates := (List.range n).map fun i =>
      if i ≥ shift then
        Gate.mkMUX (prev[i]!) (prev[i - shift]!) (shiftAmt[stage]!) (cur[i]!)
      else
        Gate.mkMUX (prev[i]!) zeroW (shiftAmt[stage]!) (cur[i]!)
    (cur, acc.2 ++ stageGates)
  ) (data, [])
  (finalData, allGates)

/-- AND-reduce: returns (wire, gates) where wire = AND of all input wires.
    Requires inputs.length >= 1. -/
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

-- ============================================================
-- 1. FPSgnj: Sign injection and register move circuit
-- ============================================================

/-- Floating-point sign injection and move operations:
    FSGNJ (21), FSGNJN (22), FSGNJX (23), FMV.X.W (16), FMV.W.X (17) -/
def fpSgnjCircuit : Circuit :=
  let src1 := makeIndexedWires "src1" 32
  let src2_sign := Wire.mk "src2_sign"
  let op := makeIndexedWires "op" 5
  let result := makeIndexedWires "result" 32

  -- Sign bits for FSGNJ variants
  let fsgnj_bit31 := Wire.mk "fsgnj_bit31"
  let g_fsgnj := Gate.mkBUF src2_sign fsgnj_bit31

  let fsgnjn_bit31 := Wire.mk "fsgnjn_bit31"
  let g_fsgnjn := Gate.mkNOT src2_sign fsgnjn_bit31

  let fsgnjx_bit31 := Wire.mk "fsgnjx_bit31"
  let g_fsgnjx := Gate.mkXOR (src1[31]!) src2_sign fsgnjx_bit31

  -- Inverted op bits for decoding
  let nop := makeIndexedWires "nop" 5
  let inv_gates := (List.range 5).map fun i => Gate.mkNOT (op[i]!) (nop[i]!)

  -- FSGNJ = 21 = 10101 -> op4=1, op3=0, op2=1, op1=0, op0=1
  let fsgnj_t0 := Wire.mk "fsgnj_t0"
  let fsgnj_t1 := Wire.mk "fsgnj_t1"
  let fsgnj_t2 := Wire.mk "fsgnj_t2"
  let fsgnj_t3 := Wire.mk "fsgnj_t3"
  let is_fsgnj := Wire.mk "is_fsgnj"
  let dec_fsgnj := [
    Gate.mkAND (op[4]!) (nop[3]!) fsgnj_t0,
    Gate.mkAND (op[2]!) (nop[1]!) fsgnj_t1,
    Gate.mkAND fsgnj_t0 fsgnj_t1 fsgnj_t2,
    Gate.mkAND fsgnj_t2 (op[0]!) fsgnj_t3,
    Gate.mkBUF fsgnj_t3 is_fsgnj
  ]

  -- FSGNJN = 22 = 10110 -> op4=1, op3=0, op2=1, op1=1, op0=0
  let fsgnjn_t0 := Wire.mk "fsgnjn_t0"
  let fsgnjn_t1 := Wire.mk "fsgnjn_t1"
  let fsgnjn_t2 := Wire.mk "fsgnjn_t2"
  let is_fsgnjn := Wire.mk "is_fsgnjn"
  let dec_fsgnjn := [
    Gate.mkAND (op[4]!) (nop[3]!) fsgnjn_t0,
    Gate.mkAND (op[2]!) (op[1]!) fsgnjn_t1,
    Gate.mkAND fsgnjn_t0 fsgnjn_t1 fsgnjn_t2,
    Gate.mkAND fsgnjn_t2 (nop[0]!) is_fsgnjn
  ]

  -- FSGNJX = 23 = 10111 -> op4=1, op3=0, op2=1, op1=1, op0=1
  let fsgnjx_t0 := Wire.mk "fsgnjx_t0"
  let fsgnjx_t1 := Wire.mk "fsgnjx_t1"
  let fsgnjx_t2 := Wire.mk "fsgnjx_t2"
  let is_fsgnjx := Wire.mk "is_fsgnjx"
  let dec_fsgnjx := [
    Gate.mkAND (op[4]!) (nop[3]!) fsgnjx_t0,
    Gate.mkAND (op[2]!) (op[1]!) fsgnjx_t1,
    Gate.mkAND fsgnjx_t0 fsgnjx_t1 fsgnjx_t2,
    Gate.mkAND fsgnjx_t2 (op[0]!) is_fsgnjx
  ]

  -- is_sgnj_any = is_fsgnj | is_fsgnjn | is_fsgnjx
  let sgnj_or0 := Wire.mk "sgnj_or0"
  let is_sgnj_any := Wire.mk "is_sgnj_any"
  let dec_sgnj_any := [
    Gate.mkOR is_fsgnj is_fsgnjn sgnj_or0,
    Gate.mkOR sgnj_or0 is_fsgnjx is_sgnj_any
  ]

  -- sgnj_sign = MUX(is_fsgnjx, fsgnjx_bit31, MUX(is_fsgnjn, fsgnjn_bit31, fsgnj_bit31))
  let sgnj_sign_inner := Wire.mk "sgnj_sign_inner"
  let sgnj_sign := Wire.mk "sgnj_sign"
  let sgnj_sign_gates := [
    Gate.mkMUX fsgnj_bit31 fsgnjn_bit31 is_fsgnjn sgnj_sign_inner,
    Gate.mkMUX sgnj_sign_inner fsgnjx_bit31 is_fsgnjx sgnj_sign
  ]

  -- Result: bits [30:0] pass src1 directly, bit 31 is sgnj_sign if sgnj else src1[31] (FMV)
  let low_gates := (List.range 31).map fun i => Gate.mkBUF (src1[i]!) (result[i]!)
  let bit31_gate := Gate.mkMUX (src1[31]!) sgnj_sign is_sgnj_any (result[31]!)

  { name := "FPSgnj"
    inputs := src1 ++ [src2_sign] ++ op
    outputs := result
    gates :=
      [g_fsgnj, g_fsgnjn, g_fsgnjx] ++
      inv_gates ++
      dec_fsgnj ++ dec_fsgnjn ++ dec_fsgnjx ++
      dec_sgnj_any ++ sgnj_sign_gates ++
      low_gates ++ [bit31_gate]
    instances := []
    signalGroups := [
      { name := "src1",   width := 32, wires := src1 },
      { name := "src2_sign", width := 1, wires := [src2_sign] },
      { name := "op",     width := 5,  wires := op },
      { name := "result", width := 32, wires := result }
    ]
  }

-- ============================================================
-- 2. FPCompare: FP comparisons and min/max circuit
-- ============================================================

/-- Floating-point comparison and min/max operations:
    FEQ.S (9), FLT.S (10), FLE.S (11), FMIN.S (19), FMAX.S (20) -/
def fpCompareCircuit : Circuit :=
  let src1 := makeIndexedWires "src1" 32
  let src2 := makeIndexedWires "src2" 32
  let op := makeIndexedWires "op" 5
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"
  let result := makeIndexedWires "result" 32
  let nv := Wire.mk "nv"

  -- src1 NaN detection
  let nan1_exp_bits := (List.range 8).map fun i => src1[23 + i]!
  let (nan1_exp_ones, nan1_exp_ones_gates) := mkAndTree "nan1_eao" nan1_exp_bits
  let nan1_mant_bits := (List.range 23).map fun i => src1[i]!
  let (nan1_mant_nz, nan1_mant_nz_gates) := mkOrTree "nan1_mnz" nan1_mant_bits
  let is_nan_src1 := Wire.mk "is_nan_src1"
  let is_snan_src1 := Wire.mk "is_snan_src1"
  let nan1_not_quiet := Wire.mk "nan1_not_quiet"
  let nan1_detect_gates := [
    Gate.mkAND nan1_exp_ones nan1_mant_nz is_nan_src1,
    Gate.mkNOT (src1[22]!) nan1_not_quiet,
    Gate.mkAND is_nan_src1 nan1_not_quiet is_snan_src1
  ]

  -- src2 NaN detection
  let nan2_exp_bits := (List.range 8).map fun i => src2[23 + i]!
  let (nan2_exp_ones, nan2_exp_ones_gates) := mkAndTree "nan2_eao" nan2_exp_bits
  let nan2_mant_bits := (List.range 23).map fun i => src2[i]!
  let (nan2_mant_nz, nan2_mant_nz_gates) := mkOrTree "nan2_mnz" nan2_mant_bits
  let is_nan_src2 := Wire.mk "is_nan_src2"
  let is_snan_src2 := Wire.mk "is_snan_src2"
  let nan2_not_quiet := Wire.mk "nan2_not_quiet"
  let nan2_detect_gates := [
    Gate.mkAND nan2_exp_ones nan2_mant_nz is_nan_src2,
    Gate.mkNOT (src2[22]!) nan2_not_quiet,
    Gate.mkAND is_nan_src2 nan2_not_quiet is_snan_src2
  ]

  -- Combined NaN signals
  let either_nan := Wire.mk "either_nan"
  let both_nan := Wire.mk "both_nan"
  let either_snan := Wire.mk "either_snan"
  let nan_combined_gates := [
    Gate.mkOR is_nan_src1 is_nan_src2 either_nan,
    Gate.mkAND is_nan_src1 is_nan_src2 both_nan,
    Gate.mkOR is_snan_src1 is_snan_src2 either_snan
  ]

  -- Inverted op bits for decoding
  let nop := makeIndexedWires "nop" 5
  let inv_gates := (List.range 5).map fun i => Gate.mkNOT (op[i]!) (nop[i]!)

  -- FEQ_S = 9 = 01001
  let feq_t0 := Wire.mk "feq_t0"
  let feq_t1 := Wire.mk "feq_t1"
  let feq_t2 := Wire.mk "feq_t2"
  let is_feq := Wire.mk "is_feq"
  let dec_feq := [
    Gate.mkAND (nop[4]!) (op[3]!) feq_t0,
    Gate.mkAND (nop[2]!) (nop[1]!) feq_t1,
    Gate.mkAND feq_t0 feq_t1 feq_t2,
    Gate.mkAND feq_t2 (op[0]!) is_feq
  ]

  -- FLT_S = 10 = 01010
  let flt_t0 := Wire.mk "flt_t0"
  let flt_t1 := Wire.mk "flt_t1"
  let flt_t2 := Wire.mk "flt_t2"
  let is_flt := Wire.mk "is_flt"
  let dec_flt := [
    Gate.mkAND (nop[4]!) (op[3]!) flt_t0,
    Gate.mkAND (nop[2]!) (op[1]!) flt_t1,
    Gate.mkAND flt_t0 flt_t1 flt_t2,
    Gate.mkAND flt_t2 (nop[0]!) is_flt
  ]

  -- FLE_S = 11 = 01011
  let fle_t0 := Wire.mk "fle_t0"
  let fle_t1 := Wire.mk "fle_t1"
  let fle_t2 := Wire.mk "fle_t2"
  let is_fle := Wire.mk "is_fle"
  let dec_fle := [
    Gate.mkAND (nop[4]!) (op[3]!) fle_t0,
    Gate.mkAND (nop[2]!) (op[1]!) fle_t1,
    Gate.mkAND fle_t0 fle_t1 fle_t2,
    Gate.mkAND fle_t2 (op[0]!) is_fle
  ]

  -- FMIN_S = 19 = 10011
  let fmin_t0 := Wire.mk "fmin_t0"
  let fmin_t1 := Wire.mk "fmin_t1"
  let fmin_t2 := Wire.mk "fmin_t2"
  let is_fmin := Wire.mk "is_fmin"
  let dec_fmin := [
    Gate.mkAND (op[4]!) (nop[3]!) fmin_t0,
    Gate.mkAND (nop[2]!) (op[1]!) fmin_t1,
    Gate.mkAND fmin_t0 fmin_t1 fmin_t2,
    Gate.mkAND fmin_t2 (op[0]!) is_fmin
  ]

  -- FMAX_S = 20 = 10100
  let fmax_t0 := Wire.mk "fmax_t0"
  let fmax_t1 := Wire.mk "fmax_t1"
  let fmax_t2 := Wire.mk "fmax_t2"
  let is_fmax := Wire.mk "is_fmax"
  let dec_fmax := [
    Gate.mkAND (op[4]!) (nop[3]!) fmax_t0,
    Gate.mkAND (op[2]!) (nop[1]!) fmax_t1,
    Gate.mkAND fmax_t0 fmax_t1 fmax_t2,
    Gate.mkAND fmax_t2 (nop[0]!) is_fmax
  ]

  -- FEQ logic
  let feq_xor := makeIndexedWires "feq_xor" 32
  let feq_xor_gates := (List.range 32).map fun i =>
    Gate.mkXOR (src1[i]!) (src2[i]!) (feq_xor[i]!)
  let (feq_or_out, feq_or_gates) := mkOrTree "feq_or" feq_xor
  let feq_raw := Wire.mk "feq_raw"
  let g_feq_inv := Gate.mkNOT feq_or_out feq_raw
  let not_either_nan := Wire.mk "not_either_nan"
  let feq_result := Wire.mk "feq_result"
  let feq_nan_gates := [
    Gate.mkNOT either_nan not_either_nan,
    Gate.mkAND feq_raw not_either_nan feq_result
  ]

  -- FLT logic
  let mag1 := (List.range 31).map fun i => src1[i]!
  let mag2 := (List.range 31).map fun i => src2[i]!
  let (_, flt_borrow, flt_sub_gates) := mkRippleSub "flt" mag1 mag2 31 zero
  let flt_signs_differ := Wire.mk "flt_signs_differ"
  let g_flt_sd := Gate.mkXOR (src1[31]!) (src2[31]!) flt_signs_differ
  let flt_not_borrow := Wire.mk "flt_not_borrow"
  let g_flt_nb := Gate.mkNOT flt_borrow flt_not_borrow
  let flt_not_eq := Wire.mk "flt_not_eq"
  let g_flt_neq := Gate.mkNOT feq_result flt_not_eq
  let flt_neg_lt := Wire.mk "flt_neg_lt"
  let g_flt_neg_lt := Gate.mkAND flt_not_borrow flt_not_eq flt_neg_lt
  let flt_same_result2 := Wire.mk "flt_same_result2"
  let g_flt_same2 := Gate.mkMUX flt_borrow flt_neg_lt (src1[31]!) flt_same_result2
  let flt_raw := Wire.mk "flt_raw"
  let g_flt_final := Gate.mkMUX flt_same_result2 (src1[31]!) flt_signs_differ flt_raw
  let flt_result := Wire.mk "flt_result"
  let flt_nan_gate := Gate.mkAND flt_raw not_either_nan flt_result

  -- FLE logic
  let fle_result := Wire.mk "fle_result"
  let g_fle := Gate.mkOR flt_result feq_result fle_result

  -- FMIN logic
  let fmin_base := makeIndexedWires "fmin_base" 32
  let fmin_nan1 := makeIndexedWires "fmin_nan1" 32
  let fmin_nan2 := makeIndexedWires "fmin_nan2" 32
  let fmin_res := makeIndexedWires "fmin_res" 32
  let fmin_res_gates :=
    (List.range 32).map (fun i =>
      Gate.mkMUX (src2[i]!) (src1[i]!) flt_raw (fmin_base[i]!)) ++
    (List.range 32).map (fun i =>
      Gate.mkMUX (fmin_base[i]!) (src2[i]!) is_nan_src1 (fmin_nan1[i]!)) ++
    (List.range 32).map (fun i =>
      Gate.mkMUX (fmin_nan1[i]!) (src1[i]!) is_nan_src2 (fmin_nan2[i]!)) ++
    (List.range 32).map (fun i =>
      let canon_bit := if i == 22 || (i >= 23 && i <= 30) then one else zero
      Gate.mkMUX (fmin_nan2[i]!) canon_bit both_nan (fmin_res[i]!))

  -- FMAX logic
  let fmax_base := makeIndexedWires "fmax_base" 32
  let fmax_nan1 := makeIndexedWires "fmax_nan1" 32
  let fmax_nan2 := makeIndexedWires "fmax_nan2" 32
  let fmax_res := makeIndexedWires "fmax_res" 32
  let fmax_res_gates :=
    (List.range 32).map (fun i =>
      Gate.mkMUX (src1[i]!) (src2[i]!) flt_raw (fmax_base[i]!)) ++
    (List.range 32).map (fun i =>
      Gate.mkMUX (fmax_base[i]!) (src2[i]!) is_nan_src1 (fmax_nan1[i]!)) ++
    (List.range 32).map (fun i =>
      Gate.mkMUX (fmax_nan1[i]!) (src1[i]!) is_nan_src2 (fmax_nan2[i]!)) ++
    (List.range 32).map (fun i =>
      let canon_bit := if i == 22 || (i >= 23 && i <= 30) then one else zero
      Gate.mkMUX (fmax_nan2[i]!) canon_bit both_nan (fmax_res[i]!))

  -- Result multiplexing
  let after_feq := makeIndexedWires "after_feq" 32
  let after_feq_gates := (List.range 32).map fun i =>
    if i == 0 then Gate.mkMUX zero feq_result is_feq (after_feq[0]!)
    else Gate.mkBUF zero (after_feq[i]!)

  let after_flt := makeIndexedWires "after_flt" 32
  let after_flt_gates := (List.range 32).map fun i =>
    if i == 0 then Gate.mkMUX (after_feq[0]!) flt_result is_flt (after_flt[0]!)
    else Gate.mkMUX (after_feq[i]!) zero is_flt (after_flt[i]!)

  let after_fle := makeIndexedWires "after_fle" 32
  let after_fle_gates := (List.range 32).map fun i =>
    if i == 0 then Gate.mkMUX (after_flt[0]!) fle_result is_fle (after_fle[0]!)
    else Gate.mkMUX (after_flt[i]!) zero is_fle (after_fle[i]!)

  let after_fmin := makeIndexedWires "after_fmin" 32
  let after_fmin_gates := (List.range 32).map fun i =>
    Gate.mkMUX (after_fle[i]!) (fmin_res[i]!) is_fmin (after_fmin[i]!)

  let after_fmax_gates := (List.range 32).map fun i =>
    Gate.mkMUX (after_fmin[i]!) (fmax_res[i]!) is_fmax (result[i]!)

  -- Exception: NV generation
  let is_flt_or_fle := Wire.mk "is_flt_or_fle"
  let cmp_nan_nv := Wire.mk "cmp_nan_nv"
  let feq_snan_nv := Wire.mk "feq_snan_nv"
  let minmax_snan_nv := Wire.mk "minmax_snan_nv"
  let is_fmin_or_fmax := Wire.mk "is_fmin_or_fmax"
  let nv_t0 := Wire.mk "cmp_nv_t0"
  let nv_gates := [
    Gate.mkOR is_flt is_fle is_flt_or_fle,
    Gate.mkAND is_flt_or_fle either_nan cmp_nan_nv,
    Gate.mkAND is_feq either_snan feq_snan_nv,
    Gate.mkOR is_fmin is_fmax is_fmin_or_fmax,
    Gate.mkAND is_fmin_or_fmax either_snan minmax_snan_nv,
    Gate.mkOR cmp_nan_nv feq_snan_nv nv_t0,
    Gate.mkOR nv_t0 minmax_snan_nv nv
  ]

  { name := "FPCompare"
    inputs := src1 ++ src2 ++ op ++ [zero, one]
    outputs := result ++ [nv]
    gates :=
      nan1_exp_ones_gates ++ nan1_mant_nz_gates ++ nan1_detect_gates ++
      nan2_exp_ones_gates ++ nan2_mant_nz_gates ++ nan2_detect_gates ++
      nan_combined_gates ++
      inv_gates ++
      dec_feq ++ dec_flt ++ dec_fle ++ dec_fmin ++ dec_fmax ++
      feq_xor_gates ++ feq_or_gates ++ [g_feq_inv] ++ feq_nan_gates ++
      flt_sub_gates ++
      [g_flt_sd, g_flt_nb, g_flt_neq, g_flt_neg_lt, g_flt_same2, g_flt_final, flt_nan_gate] ++
      [g_fle] ++
      fmin_res_gates ++ fmax_res_gates ++
      after_feq_gates ++ after_flt_gates ++ after_fle_gates ++
      after_fmin_gates ++ after_fmax_gates ++
      nv_gates
    instances := []
    signalGroups := [
      { name := "src1",   width := 32, wires := src1 },
      { name := "src2",   width := 32, wires := src2 },
      { name := "op",     width := 5,  wires := op },
      { name := "result", width := 32, wires := result }
    ]
  }

-- ============================================================
-- 3. FPClass: Floating-point classify circuit
-- ============================================================

/-- Floating-point classify operation: FCLASS.S (18) -/
def fpClassCircuit : Circuit :=
  let src1 := makeIndexedWires "src1" 32
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"
  let result := makeIndexedWires "result" 32

  -- Helper signals for classification
  let fclass_exp_bits := (List.range 8).map fun i => src1[23 + i]!
  let (fclass_exp_ones, fclass_exp_ones_gates) := mkAndTree "fclass_eao" fclass_exp_bits
  let (fclass_exp_or, fclass_exp_or_gates) := mkOrTree "fclass_eaz_or" fclass_exp_bits
  let fclass_exp_zeros := Wire.mk "fclass_exp_zeros"
  let g_fclass_eaz := Gate.mkNOT fclass_exp_or fclass_exp_zeros
  let fclass_mant_bits := (List.range 23).map fun i => src1[i]!
  let (fclass_mant_nz, fclass_mant_nz_gates) := mkOrTree "fclass_mnz" fclass_mant_bits
  let fclass_mant_zero := Wire.mk "fclass_mant_zero"
  let g_fclass_mz := Gate.mkNOT fclass_mant_nz fclass_mant_zero
  let fclass_not_sign := Wire.mk "fclass_not_sign"
  let g_fclass_ns := Gate.mkNOT (src1[31]!) fclass_not_sign
  let fclass_not_eao := Wire.mk "fclass_not_eao"
  let g_fclass_neao := Gate.mkNOT fclass_exp_ones fclass_not_eao
  let fclass_not_eaz := Wire.mk "fclass_not_eaz"
  let g_fclass_neaz := Gate.mkNOT fclass_exp_zeros fclass_not_eaz

  -- bit 0: neg inf
  let fclass_b0_t := Wire.mk "fclass_b0_t"
  let fclass_b0 := Wire.mk "fclass_b0"
  let fclass_b0_gates := [
    Gate.mkAND (src1[31]!) fclass_exp_ones fclass_b0_t,
    Gate.mkAND fclass_b0_t fclass_mant_zero fclass_b0
  ]
  -- bit 1: neg normal
  let fclass_b1_t := Wire.mk "fclass_b1_t"
  let fclass_b1 := Wire.mk "fclass_b1"
  let fclass_b1_gates := [
    Gate.mkAND (src1[31]!) fclass_not_eao fclass_b1_t,
    Gate.mkAND fclass_b1_t fclass_not_eaz fclass_b1
  ]
  -- bit 2: neg subnormal
  let fclass_b2_t := Wire.mk "fclass_b2_t"
  let fclass_b2 := Wire.mk "fclass_b2"
  let fclass_b2_gates := [
    Gate.mkAND (src1[31]!) fclass_exp_zeros fclass_b2_t,
    Gate.mkAND fclass_b2_t fclass_mant_nz fclass_b2
  ]
  -- bit 3: neg zero
  let fclass_b3_t := Wire.mk "fclass_b3_t"
  let fclass_b3 := Wire.mk "fclass_b3"
  let fclass_b3_gates := [
    Gate.mkAND (src1[31]!) fclass_exp_zeros fclass_b3_t,
    Gate.mkAND fclass_b3_t fclass_mant_zero fclass_b3
  ]
  -- bit 4: pos zero
  let fclass_b4_t := Wire.mk "fclass_b4_t"
  let fclass_b4 := Wire.mk "fclass_b4"
  let fclass_b4_gates := [
    Gate.mkAND fclass_not_sign fclass_exp_zeros fclass_b4_t,
    Gate.mkAND fclass_b4_t fclass_mant_zero fclass_b4
  ]
  -- bit 5: pos subnormal
  let fclass_b5_t := Wire.mk "fclass_b5_t"
  let fclass_b5 := Wire.mk "fclass_b5"
  let fclass_b5_gates := [
    Gate.mkAND fclass_not_sign fclass_exp_zeros fclass_b5_t,
    Gate.mkAND fclass_b5_t fclass_mant_nz fclass_b5
  ]
  -- bit 6: pos normal
  let fclass_b6_t := Wire.mk "fclass_b6_t"
  let fclass_b6 := Wire.mk "fclass_b6"
  let fclass_b6_gates := [
    Gate.mkAND fclass_not_sign fclass_not_eao fclass_b6_t,
    Gate.mkAND fclass_b6_t fclass_not_eaz fclass_b6
  ]
  -- bit 7: pos inf
  let fclass_b7_t := Wire.mk "fclass_b7_t"
  let fclass_b7 := Wire.mk "fclass_b7"
  let fclass_b7_gates := [
    Gate.mkAND fclass_not_sign fclass_exp_ones fclass_b7_t,
    Gate.mkAND fclass_b7_t fclass_mant_zero fclass_b7
  ]
  -- bit 8: signaling NaN
  let fclass_not_m22 := Wire.mk "fclass_not_m22"
  let g_fclass_nm22 := Gate.mkNOT (src1[22]!) fclass_not_m22
  let fclass_b8_t := Wire.mk "fclass_b8_t"
  let fclass_b8 := Wire.mk "fclass_b8"
  let fclass_b8_gates := [
    Gate.mkAND fclass_exp_ones fclass_mant_nz fclass_b8_t,
    Gate.mkAND fclass_b8_t fclass_not_m22 fclass_b8
  ]
  -- bit 9: quiet NaN
  let fclass_b9_t := Wire.mk "fclass_b9_t"
  let fclass_b9 := Wire.mk "fclass_b9"
  let fclass_b9_gates := [
    Gate.mkAND fclass_exp_ones fclass_mant_nz fclass_b9_t,
    Gate.mkAND fclass_b9_t (src1[22]!) fclass_b9
  ]

  let fclass_bits : List Wire := [fclass_b0, fclass_b1, fclass_b2, fclass_b3,
    fclass_b4, fclass_b5, fclass_b6, fclass_b7, fclass_b8, fclass_b9] ++
    (List.range 22).map (fun _ => zero)

  let out_gates := (List.range 32).map fun i =>
    Gate.mkBUF (fclass_bits[i]!) (result[i]!)

  { name := "FPClass"
    inputs := src1 ++ [zero, one]
    outputs := result
    gates :=
      fclass_exp_ones_gates ++ fclass_exp_or_gates ++ [g_fclass_eaz] ++
      fclass_mant_nz_gates ++ [g_fclass_mz, g_fclass_ns, g_fclass_neao, g_fclass_neaz] ++
      fclass_b0_gates ++ fclass_b1_gates ++ fclass_b2_gates ++ fclass_b3_gates ++
      fclass_b4_gates ++ fclass_b5_gates ++ fclass_b6_gates ++ fclass_b7_gates ++
      [g_fclass_nm22] ++ fclass_b8_gates ++ fclass_b9_gates ++
      out_gates
    instances := []
    signalGroups := [
      { name := "src1",   width := 32, wires := src1 },
      { name := "result", width := 32, wires := result }
    ]
  }

-- ============================================================
-- 4. FPCvtInt: Float/integer conversion circuit
-- ============================================================

/-- Floating-point integer conversion operations:
    FCVT.W.S (12), FCVT.WU.S (13), FCVT.S.W (14), FCVT.S.WU (15) -/
def fpCvtIntCircuit : Circuit :=
  let src1 := makeIndexedWires "src1" 32
  let op := makeIndexedWires "op" 5
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"
  let result := makeIndexedWires "result" 32
  let nv := Wire.mk "nv"
  let nx := Wire.mk "nx"

  -- src1 NaN detection
  let nan1_exp_bits := (List.range 8).map fun i => src1[23 + i]!
  let (nan1_exp_ones, nan1_exp_ones_gates) := mkAndTree "nan1_eao" nan1_exp_bits
  let nan1_mant_bits := (List.range 23).map fun i => src1[i]!
  let (nan1_mant_nz, nan1_mant_nz_gates) := mkOrTree "nan1_mnz" nan1_mant_bits
  let is_nan_src1 := Wire.mk "is_nan_src1"
  let is_snan_src1 := Wire.mk "is_snan_src1"
  let nan1_not_quiet := Wire.mk "nan1_not_quiet"
  let nan1_detect_gates := [
    Gate.mkAND nan1_exp_ones nan1_mant_nz is_nan_src1,
    Gate.mkNOT (src1[22]!) nan1_not_quiet,
    Gate.mkAND is_nan_src1 nan1_not_quiet is_snan_src1
  ]

  -- Inverted op bits for decoding
  let nop := makeIndexedWires "nop" 5
  let inv_gates := (List.range 5).map fun i => Gate.mkNOT (op[i]!) (nop[i]!)

  -- FCVT_W_S = 12 = 01100
  let fcvt_t0 := Wire.mk "fcvt_t0"
  let fcvt_t1 := Wire.mk "fcvt_t1"
  let fcvt_t2 := Wire.mk "fcvt_t2"
  let is_fcvt := Wire.mk "is_fcvt"
  let dec_fcvt := [
    Gate.mkAND (nop[4]!) (op[3]!) fcvt_t0,
    Gate.mkAND (op[2]!) (nop[1]!) fcvt_t1,
    Gate.mkAND fcvt_t0 fcvt_t1 fcvt_t2,
    Gate.mkAND fcvt_t2 (nop[0]!) is_fcvt
  ]

  -- FCVT_WU_S = 13 = 01101
  let fcvtwu_t0 := Wire.mk "fcvtwu_t0"
  let fcvtwu_t1 := Wire.mk "fcvtwu_t1"
  let fcvtwu_t2 := Wire.mk "fcvtwu_t2"
  let is_fcvt_wu := Wire.mk "is_fcvt_wu"
  let dec_fcvt_wu := [
    Gate.mkAND (nop[4]!) (op[3]!) fcvtwu_t0,
    Gate.mkAND (op[2]!) (nop[1]!) fcvtwu_t1,
    Gate.mkAND fcvtwu_t0 fcvtwu_t1 fcvtwu_t2,
    Gate.mkAND fcvtwu_t2 (op[0]!) is_fcvt_wu
  ]

  -- FCVT_S_W = 14 = 01110
  let fcvtsw_t0 := Wire.mk "fcvtsw_t0"
  let fcvtsw_t1 := Wire.mk "fcvtsw_t1"
  let fcvtsw_t2 := Wire.mk "fcvtsw_t2"
  let is_fcvt_s_w := Wire.mk "is_fcvt_s_w"
  let dec_fcvt_s_w := [
    Gate.mkAND (nop[4]!) (op[3]!) fcvtsw_t0,
    Gate.mkAND (op[2]!) (op[1]!) fcvtsw_t1,
    Gate.mkAND fcvtsw_t0 fcvtsw_t1 fcvtsw_t2,
    Gate.mkAND fcvtsw_t2 (nop[0]!) is_fcvt_s_w
  ]

  -- FCVT_S_WU = 15 = 01111
  let fcvtswu_t0 := Wire.mk "fcvtswu_t0"
  let fcvtswu_t1 := Wire.mk "fcvtswu_t1"
  let fcvtswu_t2 := Wire.mk "fcvtswu_t2"
  let is_fcvt_s_wu := Wire.mk "is_fcvt_s_wu"
  let dec_fcvt_s_wu := [
    Gate.mkAND (nop[4]!) (op[3]!) fcvtswu_t0,
    Gate.mkAND (op[2]!) (op[1]!) fcvtswu_t1,
    Gate.mkAND fcvtswu_t0 fcvtswu_t1 fcvtswu_t2,
    Gate.mkAND fcvtswu_t2 (op[0]!) is_fcvt_s_wu
  ]

  -- ────────────────────────────────────────────────────────────
  -- FCVT.W.S Datapath
  -- ────────────────────────────────────────────────────────────
  let expBits := (List.range 8).map fun i => src1[23 + i]!
  let mant := (List.range 23).map (fun i => src1[i]!) ++ [one]

  let const150 := [zero, one, one, zero, one, zero, zero, one]
  let (shiftAmt, shiftBorrow, fcvt_sub_gates) :=
    mkRippleSub "fcvt_sh" const150 expBits 8 zero

  let fcvt_big_or0 := Wire.mk "fcvt_big_or0"
  let fcvt_big_or1 := Wire.mk "fcvt_big_or1"
  let fcvt_big_and := Wire.mk "fcvt_big_and"
  let fcvt_shift_too_big := Wire.mk "fcvt_shift_too_big"
  let fcvt_underflow := Wire.mk "fcvt_underflow"
  let fcvt_big_gates := [
    Gate.mkOR (shiftAmt[7]!) (shiftAmt[6]!) fcvt_big_or0,
    Gate.mkOR fcvt_big_or0 (shiftAmt[5]!) fcvt_big_or1,
    Gate.mkAND (shiftAmt[4]!) (shiftAmt[3]!) fcvt_big_and,
    Gate.mkOR fcvt_big_or1 fcvt_big_and fcvt_shift_too_big,
    Gate.mkOR fcvt_shift_too_big shiftBorrow fcvt_underflow
  ]

  let mant32 := mant ++ (List.range 8).map (fun _ => zero)
  let shiftCtrl := (List.range 5).map fun i => shiftAmt[i]!
  let (fcvt_shifted, fcvt_shift_gates) :=
    mkBarrelShiftRight "fcvt_bsh" mant32 32 shiftCtrl 5 zero

  let fcvt_mag := makeIndexedWires "fcvt_mag" 32
  let fcvt_mag_gates := (List.range 32).map fun i =>
    Gate.mkMUX (fcvt_shifted[i]!) zero fcvt_underflow (fcvt_mag[i]!)

  let fcvt_mag_bits := (List.range 32).map fun i => fcvt_mag[i]!
  let (fcvt_mag_nz, fcvt_mag_nz_gates) := mkOrTree "fcvt_mag_nz" fcvt_mag_bits

  let fcvt_inv := makeIndexedWires "fcvt_inv" 32
  let fcvt_inv_gates := (List.range 32).map fun i =>
    Gate.mkNOT (fcvt_mag[i]!) (fcvt_inv[i]!)

  let fcvt_neg := makeIndexedWires "fcvt_neg" 32
  let zeros32 := (List.range 32).map fun _ => zero
  let (fcvt_neg_gates, _fcvt_neg_cout) :=
    mkKoggeStoneAdd fcvt_inv zeros32 one fcvt_neg "fcvt_neg"

  let fcvt_normal := makeIndexedWires "fcvt_normal" 32
  let fcvt_sel_gates := (List.range 32).map fun i =>
    Gate.mkMUX (fcvt_mag[i]!) (fcvt_neg[i]!) (src1[31]!) (fcvt_normal[i]!)

  let nan1_mant_zero := Wire.mk "nan1_mant_zero"
  let is_inf_src1 := Wire.mk "is_inf_src1"
  let nan1_mant_z_gate := Gate.mkNOT nan1_mant_nz nan1_mant_zero
  let inf1_gate := Gate.mkAND nan1_exp_ones nan1_mant_zero is_inf_src1

  let fcvt_overflow := Wire.mk "fcvt_overflow"
  let fcvt_special_gates := [Gate.mkBUF shiftBorrow fcvt_overflow]

  let fcvt_is_special := Wire.mk "fcvt_is_special"
  let fcvt_neg_special := Wire.mk "fcvt_neg_special"
  let fcvt_not_nan := Wire.mk "fcvt_not_nan"
  let fcvt_special_det := [
    Gate.mkOR is_nan_src1 fcvt_overflow fcvt_is_special,
    Gate.mkNOT is_nan_src1 fcvt_not_nan,
    Gate.mkAND (src1[31]!) fcvt_not_nan (Wire.mk "fcvt_neg_and_nn"),
    Gate.mkAND (Wire.mk "fcvt_neg_and_nn") fcvt_is_special fcvt_neg_special
  ]

  let fcvt_res := makeIndexedWires "fcvt_res" 32
  let fcvt_result_gates := (List.range 32).map fun i =>
    if i == 31 then
      Gate.mkMUX (fcvt_normal[i]!) fcvt_neg_special fcvt_is_special (fcvt_res[i]!)
    else
      let special_bit := Wire.mk s!"fcvt_sb_{i}"
      Gate.mkMUX (fcvt_normal[i]!) special_bit fcvt_is_special (fcvt_res[i]!)
  let fcvt_not_neg_special := Wire.mk "fcvt_not_neg_special"
  let fcvt_special_bit_gates := [Gate.mkNOT fcvt_neg_special fcvt_not_neg_special] ++
    (List.range 31).map fun i =>
      Gate.mkBUF fcvt_not_neg_special (Wire.mk s!"fcvt_sb_{i}")

  let fcvt_sticky := Wire.mk "fcvt_sticky_out"
  let (_, fcvt_sticky_gates) :=
    (List.range 5).foldl (fun (acc : (List Wire × Wire) × List Gate) stage =>
      let (prev_data, prev_sticky) := acc.1
      let shift := Nat.pow 2 stage
      let lost_bits := (List.range (min shift 32)).map fun i => prev_data[i]!
      let (lost_or, lost_or_gates) := mkOrTree s!"fcvt_lost_s{stage}" lost_bits
      let stage_contrib := Wire.mk s!"fcvt_sticky_contrib_{stage}"
      let new_sticky := Wire.mk s!"fcvt_sticky_{stage}"
      let g_contrib := Gate.mkAND (shiftCtrl[stage]!) lost_or stage_contrib
      let g_sticky := Gate.mkOR prev_sticky stage_contrib new_sticky
      let new_data := makeIndexedWires s!"fcvt_bsh2_s{stage}" 32
      let data_gates := (List.range 32).map fun i =>
        if i + shift < 32 then
          Gate.mkMUX (prev_data[i]!) (prev_data[i + shift]!) (shiftCtrl[stage]!) (new_data[i]!)
        else
          Gate.mkMUX (prev_data[i]!) zero (shiftCtrl[stage]!) (new_data[i]!)
      ((new_data, new_sticky), acc.2 ++ lost_or_gates ++ [g_contrib, g_sticky] ++ data_gates)
    ) ((mant32, zero), [])
  let fcvt_sticky_final := Wire.mk "fcvt_sticky_4"
  let fcvt_sticky_buf := [Gate.mkBUF fcvt_sticky_final fcvt_sticky]

  let fcvt_src1_mag := (List.range 31).map fun i => src1[i]!
  let (fcvt_src1_nz, fcvt_src1_nz_gates) := mkOrTree "fcvt_s1nz" fcvt_src1_mag
  let fcvt_underflow_nx := Wire.mk "fcvt_underflow_nx"
  let not_shiftBorrow := Wire.mk "fcvt_not_shiftBorrow"
  let fcvt_uflow_real := Wire.mk "fcvt_uflow_real"
  let g_underflow_nx_gates := [
    Gate.mkNOT shiftBorrow not_shiftBorrow,
    Gate.mkAND fcvt_shift_too_big not_shiftBorrow fcvt_uflow_real,
    Gate.mkAND fcvt_uflow_real fcvt_src1_nz fcvt_underflow_nx
  ]
  let fcvt_nx_pre := Wire.mk "fcvt_nx_pre"
  let fcvt_nx := Wire.mk "fcvt_nx"
  let fcvt_nx_gates := [
    Gate.mkAND fcvt_sticky (Wire.mk "fcvt_not_special") fcvt_nx_pre,
    Gate.mkOR fcvt_nx_pre fcvt_underflow_nx fcvt_nx
  ]
  let fcvt_not_special_gate := [Gate.mkNOT fcvt_is_special (Wire.mk "fcvt_not_special")]
  let fcvt_nv := Wire.mk "fcvt_nv"
  let fcvt_nv_gate := [Gate.mkBUF fcvt_is_special fcvt_nv]

  -- ────────────────────────────────────────────────────────────
  -- FCVT.WU.S Datapath
  -- ────────────────────────────────────────────────────────────
  let fcvtwu_lsa := makeIndexedWires "fcvtwu_lsa" 4
  let fcvtwu_lsa_inv := (List.range 4).map fun i => Wire.mk s!"fcvtwu_lsa_inv_{i}"
  let fcvtwu_lsa_inv_gates := (List.range 4).map fun i =>
    Gate.mkNOT (shiftAmt[i]!) (fcvtwu_lsa_inv[i]!)
  let fcvtwu_lsa_carry := (List.range 5).map fun i => Wire.mk s!"fcvtwu_lsa_c_{i}"
  let fcvtwu_lsa_add_gates :=
    [Gate.mkBUF one (fcvtwu_lsa_carry[0]!)] ++
    (List.range 4).map (fun i =>
      Gate.mkXOR (fcvtwu_lsa_inv[i]!) (fcvtwu_lsa_carry[i]!) (fcvtwu_lsa[i]!)) ++
    (List.range 4).map (fun i =>
      Gate.mkAND (fcvtwu_lsa_inv[i]!) (fcvtwu_lsa_carry[i]!) (fcvtwu_lsa_carry[i+1]!))

  let mant32_list := (List.range 32).map fun i => mant32[i]!
  let (fcvtwu_lsh, fcvtwu_lsh_gates) :=
    mkBarrelShiftLeft "fcvtwu_lsh" mant32_list 32 fcvtwu_lsa 4 zero

  let fcvtwu_ov_t0 := Wire.mk "fcvtwu_ov_t0"
  let fcvtwu_ov_t1 := Wire.mk "fcvtwu_ov_t1"
  let fcvtwu_overflow := Wire.mk "fcvtwu_overflow"
  let fcvtwu_ov_gates := [
    Gate.mkAND (shiftAmt[7]!) (shiftAmt[6]!) fcvtwu_ov_t0,
    Gate.mkAND (shiftAmt[5]!) (shiftAmt[4]!) fcvtwu_ov_t1,
    Gate.mkAND fcvtwu_ov_t0 fcvtwu_ov_t1 (Wire.mk "fcvtwu_upper_ok"),
    Gate.mkNOT (Wire.mk "fcvtwu_upper_ok") fcvtwu_overflow
  ]

  let fcvtwu_lsh_or_ov := makeIndexedWires "fcvtwu_lsh_ov" 32
  let fcvtwu_lsh_ov_gates := (List.range 32).map fun i =>
    Gate.mkOR (fcvtwu_lsh[i]!) fcvtwu_overflow (fcvtwu_lsh_or_ov[i]!)

  let fcvtwu_unsigned_mag := makeIndexedWires "fcvtwu_umag" 32
  let fcvtwu_umag_gates := (List.range 32).map fun i =>
    Gate.mkMUX (fcvt_mag[i]!) (fcvtwu_lsh_or_ov[i]!) shiftBorrow (fcvtwu_unsigned_mag[i]!)

  let fcvtwu_neg_clamp := Wire.mk "fcvtwu_neg_clamp"
  let fcvtwu_neg_clamp_gate := [
    Gate.mkNOT is_nan_src1 (Wire.mk "fcvtwu_not_nan"),
    Gate.mkAND (src1[31]!) (Wire.mk "fcvtwu_not_nan") fcvtwu_neg_clamp
  ]
  let fcvtwu_res := makeIndexedWires "fcvtwu_res" 32
  let fcvtwu_res_gates := (List.range 32).map fun i =>
    Gate.mkMUX (fcvtwu_unsigned_mag[i]!) zero fcvtwu_neg_clamp (fcvtwu_res[i]!)

  -- ────────────────────────────────────────────────────────────
  -- FCVT.S.W Datapath
  -- ────────────────────────────────────────────────────────────
  let (fcvtsw_or_out, fcvtsw_or_gates) := mkOrTree "fcvtsw_nz" src1
  let fcvtsw_is_zero := Wire.mk "fcvtsw_is_zero"
  let g_fcvtsw_iz := Gate.mkNOT fcvtsw_or_out fcvtsw_is_zero

  let fcvtsw_inv := makeIndexedWires "fcvtsw_inv" 32
  let fcvtsw_inv_gates := (List.range 32).map fun i =>
    Gate.mkNOT (src1[i]!) (fcvtsw_inv[i]!)

  let fcvtsw_neg := makeIndexedWires "fcvtsw_neg" 32
  let fcvtsw_zeros32 := (List.range 32).map fun _ => zero
  let (fcvtsw_neg_gates, _fcvtsw_neg_cout) :=
    mkKoggeStoneAdd fcvtsw_inv fcvtsw_zeros32 one fcvtsw_neg "fcvtsw_neg"

  let fcvtsw_mag := makeIndexedWires "fcvtsw_mag" 32
  let fcvtsw_mag_gates := (List.range 32).map fun i =>
    Gate.mkMUX (src1[i]!) (fcvtsw_neg[i]!) (src1[31]!) (fcvtsw_mag[i]!)

  let fcvtsw_lpos := makeIndexedWires "fcvtsw_lpos" 5
  let fcvtsw_pe_init := makeIndexedWires "fcvtsw_pe_pos_init" 5
  let fcvtsw_pe_init_gates := (List.range 5).map fun k =>
    Gate.mkBUF zero (fcvtsw_pe_init[k]!)
  let (_, _, fcvtsw_penc_fold_gates) := (List.range 32).foldl
    (fun (acc : Wire × (List Wire × List Gate)) idx =>
      let i := 31 - idx
      let old_found := acc.1
      let old_pos := acc.2.1
      let gates_acc := acc.2.2
      let nf := Wire.mk s!"fcvtsw_pe_nf_{i}"
      let take := Wire.mk s!"fcvtsw_pe_take_{i}"
      let g_nf := Gate.mkNOT old_found nf
      let g_take := Gate.mkAND (fcvtsw_mag[i]!) nf take
      let new_found := Wire.mk s!"fcvtsw_pe_found_{i}"
      let g_found := Gate.mkOR old_found (fcvtsw_mag[i]!) new_found
      let new_pos := makeIndexedWires s!"fcvtsw_pe_pos_{i}" 5
      let pos_gates := (List.range 5).map fun k =>
        let bit_val := if (i / Nat.pow 2 k) % 2 == 1 then one else zero
        Gate.mkMUX (old_pos[k]!) bit_val take (new_pos[k]!)
      (new_found, (new_pos, gates_acc ++ [g_nf, g_take, g_found] ++ pos_gates))
    ) (zero, (fcvtsw_pe_init, []))
  let fcvtsw_penc_gates := fcvtsw_pe_init_gates ++ fcvtsw_penc_fold_gates

  let fcvtsw_final_pos := makeIndexedWires "fcvtsw_pe_pos_0" 5
  let fcvtsw_lpos_gates := (List.range 5).map fun k =>
    Gate.mkBUF (fcvtsw_final_pos[k]!) (fcvtsw_lpos[k]!)

  let fcvtsw_shamt := makeIndexedWires "fcvtsw_shamt" 5
  let fcvtsw_shamt_gates := (List.range 5).map fun k =>
    Gate.mkNOT (fcvtsw_lpos[k]!) (fcvtsw_shamt[k]!)

  let (fcvtsw_shifted, fcvtsw_bsl_gates) :=
    mkBarrelShiftLeft "fcvtsw_bsl" fcvtsw_mag 32 fcvtsw_shamt 5 zero

  let const127 := [one, one, one, one, one, one, one, zero]
  let fcvtsw_lpos8 := (List.range 5).map (fun k => fcvtsw_lpos[k]!) ++
    [zero, zero, zero]
  let fcvtsw_exp := makeIndexedWires "fcvtsw_exp" 8
  let (fcvtsw_exp_gates, _fcvtsw_exp_cout) :=
    mkKoggeStoneAdd const127 fcvtsw_lpos8 zero fcvtsw_exp "fcvtsw_exp"

  let fcvtsw_round_bit := fcvtsw_shifted[7]!
  let fcvtsw_guard_bit := fcvtsw_shifted[8]!
  let fcvtsw_sticky_bits := (List.range 7).map fun i => fcvtsw_shifted[i]!
  let (fcvtsw_sticky_or, fcvtsw_sticky_gates) := mkOrTree "fcvtsw_sticky" fcvtsw_sticky_bits
  let fcvtsw_sticky_or_guard := Wire.mk "fcvtsw_sticky_or_guard"
  let fcvtsw_round_up := Wire.mk "fcvtsw_round_up"
  let fcvtsw_round_gates := [
    Gate.mkOR fcvtsw_sticky_or fcvtsw_guard_bit fcvtsw_sticky_or_guard,
    Gate.mkAND fcvtsw_round_bit fcvtsw_sticky_or_guard fcvtsw_round_up
  ]
  let fcvtsw_nx := Wire.mk "fcvtsw_nx"
  let fcvtsw_nx_gate := Gate.mkOR fcvtsw_round_bit fcvtsw_sticky_or fcvtsw_nx

  let fcvtsw_unrounded := makeIndexedWires "fcvtsw_unrnd" 31
  let fcvtsw_unrounded_gates := (List.range 31).map fun i =>
    if i < 23 then Gate.mkBUF (fcvtsw_shifted[i + 8]!) (fcvtsw_unrounded[i]!)
    else Gate.mkBUF (fcvtsw_exp[i - 23]!) (fcvtsw_unrounded[i]!)
  let fcvtsw_zeros31 := (List.range 31).map fun _ => zero
  let fcvtsw_rounded := makeIndexedWires "fcvtsw_rnded" 31
  let (fcvtsw_rnd_add_gates, _fcvtsw_rnd_cout) :=
    mkKoggeStoneAdd fcvtsw_unrounded fcvtsw_zeros31 fcvtsw_round_up fcvtsw_rounded "fcvtsw_rnd"

  let fcvtsw_not_zero := Wire.mk "fcvtsw_not_zero"
  let g_fcvtsw_nz := Gate.mkNOT fcvtsw_is_zero fcvtsw_not_zero

  let fcvtsw_res := makeIndexedWires "fcvtsw_res" 32
  let fcvtsw_pack_gates := (List.range 32).map fun i =>
    if i < 31 then
      Gate.mkMUX (fcvtsw_rounded[i]!) zero fcvtsw_is_zero (fcvtsw_res[i]!)
    else
      Gate.mkMUX (src1[31]!) zero fcvtsw_is_zero (fcvtsw_res[i]!)

  -- ────────────────────────────────────────────────────────────
  -- FCVT.S.WU Datapath
  -- ────────────────────────────────────────────────────────────
  let fcvtswu_lpos := makeIndexedWires "fcvtswu_lpos" 5
  let fcvtswu_pe_init := makeIndexedWires "fcvtswu_pe_pos_init" 5
  let fcvtswu_pe_init_gates := (List.range 5).map fun k =>
    Gate.mkBUF zero (fcvtswu_pe_init[k]!)
  let (_, _, fcvtswu_penc_fold_gates) := (List.range 32).foldl
    (fun (acc : Wire × (List Wire × List Gate)) idx =>
      let i := 31 - idx
      let old_found := acc.1
      let old_pos := acc.2.1
      let gates_acc := acc.2.2
      let nf := Wire.mk s!"fcvtswu_pe_nf_{i}"
      let take := Wire.mk s!"fcvtswu_pe_take_{i}"
      let g_nf := Gate.mkNOT old_found nf
      let g_take := Gate.mkAND (src1[i]!) nf take
      let new_found := Wire.mk s!"fcvtswu_pe_found_{i}"
      let g_found := Gate.mkOR old_found (src1[i]!) new_found
      let new_pos := makeIndexedWires s!"fcvtswu_pe_pos_{i}" 5
      let pos_gates := (List.range 5).map fun k =>
        let bit_val := if (i / Nat.pow 2 k) % 2 == 1 then one else zero
        Gate.mkMUX (old_pos[k]!) bit_val take (new_pos[k]!)
      (new_found, (new_pos, gates_acc ++ [g_nf, g_take, g_found] ++ pos_gates))
    ) (zero, (fcvtswu_pe_init, []))
  let fcvtswu_penc_gates := fcvtswu_pe_init_gates ++ fcvtswu_penc_fold_gates

  let fcvtswu_final_pos := makeIndexedWires "fcvtswu_pe_pos_0" 5
  let fcvtswu_lpos_gates := (List.range 5).map fun k =>
    Gate.mkBUF (fcvtswu_final_pos[k]!) (fcvtswu_lpos[k]!)

  let fcvtswu_shamt := makeIndexedWires "fcvtswu_shamt" 5
  let fcvtswu_shamt_gates := (List.range 5).map fun k =>
    Gate.mkNOT (fcvtswu_lpos[k]!) (fcvtswu_shamt[k]!)

  let (fcvtswu_shifted, fcvtswu_bsl_gates) :=
    mkBarrelShiftLeft "fcvtswu_bsl" src1 32 fcvtswu_shamt 5 zero

  let fcvtswu_lpos8 := (List.range 5).map (fun k => fcvtswu_lpos[k]!) ++
    [zero, zero, zero]
  let fcvtswu_exp := makeIndexedWires "fcvtswu_exp" 8
  let (fcvtswu_exp_gates, _fcvtswu_exp_cout) :=
    mkKoggeStoneAdd const127 fcvtswu_lpos8 zero fcvtswu_exp "fcvtswu_exp"

  let fcvtswu_round_bit := fcvtswu_shifted[7]!
  let fcvtswu_guard_bit := fcvtswu_shifted[8]!
  let fcvtswu_sticky_bits := (List.range 7).map fun i => fcvtswu_shifted[i]!
  let (fcvtswu_sticky_or, fcvtswu_sticky_gates) := mkOrTree "fcvtswu_sticky" fcvtswu_sticky_bits
  let fcvtswu_sticky_or_guard := Wire.mk "fcvtswu_sticky_or_guard"
  let fcvtswu_round_up := Wire.mk "fcvtswu_round_up"
  let fcvtswu_round_gates := [
    Gate.mkOR fcvtswu_sticky_or fcvtswu_guard_bit fcvtswu_sticky_or_guard,
    Gate.mkAND fcvtswu_round_bit fcvtswu_sticky_or_guard fcvtswu_round_up
  ]
  let fcvtswu_nx := Wire.mk "fcvtswu_nx"
  let fcvtswu_nx_gate := Gate.mkOR fcvtswu_round_bit fcvtswu_sticky_or fcvtswu_nx

  let fcvtswu_unrounded := makeIndexedWires "fcvtswu_unrnd" 31
  let fcvtswu_unrounded_gates := (List.range 31).map fun i =>
    if i < 23 then Gate.mkBUF (fcvtswu_shifted[i + 8]!) (fcvtswu_unrounded[i]!)
    else Gate.mkBUF (fcvtswu_exp[i - 23]!) (fcvtswu_unrounded[i]!)
  let fcvtswu_zeros31 := (List.range 31).map fun _ => zero
  let fcvtswu_rounded := makeIndexedWires "fcvtswu_rnded" 31
  let (fcvtswu_rnd_add_gates, _fcvtswu_rnd_cout) :=
    mkKoggeStoneAdd fcvtswu_unrounded fcvtswu_zeros31 fcvtswu_round_up fcvtswu_rounded "fcvtswu_rnd"

  let fcvtswu_res := makeIndexedWires "fcvtswu_res" 32
  let fcvtswu_pack_gates := (List.range 32).map fun i =>
    if i < 31 then
      Gate.mkMUX (fcvtswu_rounded[i]!) zero fcvtsw_is_zero (fcvtswu_res[i]!)
    else
      Gate.mkBUF zero (fcvtswu_res[i]!)

  -- ────────────────────────────────────────────────────────────
  -- Conversion Result Multiplexing
  -- ────────────────────────────────────────────────────────────
  let cvt_after_w := makeIndexedWires "cvt_after_w" 32
  let cvt_after_w_gates := (List.range 32).map fun i =>
    Gate.mkMUX zero (fcvt_res[i]!) is_fcvt (cvt_after_w[i]!)

  let cvt_after_wu := makeIndexedWires "cvt_after_wu" 32
  let cvt_after_wu_gates := (List.range 32).map fun i =>
    Gate.mkMUX (cvt_after_w[i]!) (fcvtwu_res[i]!) is_fcvt_wu (cvt_after_wu[i]!)

  let cvt_after_sw := makeIndexedWires "cvt_after_sw" 32
  let cvt_after_sw_gates := (List.range 32).map fun i =>
    Gate.mkMUX (cvt_after_wu[i]!) (fcvtsw_res[i]!) is_fcvt_s_w (cvt_after_sw[i]!)

  let cvt_out_gates := (List.range 32).map fun i =>
    Gate.mkMUX (cvt_after_sw[i]!) (fcvtswu_res[i]!) is_fcvt_s_wu (result[i]!)

  -- ────────────────────────────────────────────────────────────
  -- Exception Generation (NV & NX)
  -- ────────────────────────────────────────────────────────────
  let fcvt_is_fcvt_any := Wire.mk "fcvt_is_fcvt_any"
  let fcvt_ws_nv := Wire.mk "fcvt_ws_nv"
  let nv_gates := [
    Gate.mkOR is_fcvt is_fcvt_wu fcvt_is_fcvt_any,
    Gate.mkAND is_fcvt fcvt_nv fcvt_ws_nv,
    Gate.mkOR is_nan_src1 is_inf_src1 (Wire.mk "fcvtwu_nan_inf"),
    Gate.mkAND is_fcvt_wu (Wire.mk "fcvtwu_nan_inf") (Wire.mk "fcvtwu_nan_inf_nv"),
    Gate.mkAND (src1[31]!) fcvt_mag_nz (Wire.mk "fcvtwu_neg_nz"),
    Gate.mkAND is_fcvt_wu (Wire.mk "fcvtwu_neg_nz") (Wire.mk "fcvtwu_neg_nv"),
    Gate.mkAND is_fcvt_wu fcvtwu_overflow (Wire.mk "fcvtwu_pos_ov_t"),
    Gate.mkAND (Wire.mk "fcvtwu_pos_ov_t") shiftBorrow (Wire.mk "fcvtwu_pos_ov_nv"),
    Gate.mkAND is_fcvt_wu shiftBorrow (Wire.mk "fcvtwu_sb_t"),
    Gate.mkAND (Wire.mk "fcvtwu_sb_t") (src1[31]!) (Wire.mk "fcvtwu_neg_sb_nv"),
    Gate.mkOR (Wire.mk "fcvtwu_nan_inf_nv") (Wire.mk "fcvtwu_neg_nv") (Wire.mk "fcvtwu_nv_t0"),
    Gate.mkOR (Wire.mk "fcvtwu_pos_ov_nv") (Wire.mk "fcvtwu_neg_sb_nv") (Wire.mk "fcvtwu_nv_t1"),
    Gate.mkOR (Wire.mk "fcvtwu_nv_t0") (Wire.mk "fcvtwu_nv_t1") (Wire.mk "fcvtwu_all_nv"),
    Gate.mkOR fcvt_ws_nv (Wire.mk "fcvtwu_all_nv") nv
  ]

  let fcvt_ws_nx := Wire.mk "fcvt_ws_nx"
  let total_nx := Wire.mk "total_nx"
  let nx_gates := [
    Gate.mkAND fcvt_is_fcvt_any fcvt_nx fcvt_ws_nx,
    Gate.mkOR fcvt_ws_nx (Wire.mk "fcvtsw_nx_contrib") (Wire.mk "nx_t0"),
    Gate.mkOR (Wire.mk "nx_t0") (Wire.mk "fcvtswu_nx_contrib") total_nx,
    Gate.mkAND is_fcvt_s_w fcvtsw_nx (Wire.mk "fcvtsw_nx_contrib"),
    Gate.mkAND is_fcvt_s_wu fcvtswu_nx (Wire.mk "fcvtswu_nx_contrib"),
    Gate.mkBUF total_nx nx
  ]

  { name := "FPCvtInt"
    inputs := src1 ++ op ++ [zero, one]
    outputs := result ++ [nv, nx]
    gates :=
      nan1_exp_ones_gates ++ nan1_mant_nz_gates ++ nan1_detect_gates ++
      inv_gates ++
      dec_fcvt ++ dec_fcvt_wu ++ dec_fcvt_s_w ++ dec_fcvt_s_wu ++
      fcvt_sub_gates ++ fcvt_big_gates ++ fcvt_shift_gates ++
      fcvt_mag_gates ++ fcvt_mag_nz_gates ++ fcvt_inv_gates ++ fcvt_neg_gates ++ fcvt_sel_gates ++
      [nan1_mant_z_gate, inf1_gate] ++ fcvt_special_gates ++ fcvt_special_det ++
      fcvt_special_bit_gates ++ fcvt_result_gates ++
      fcvt_sticky_gates ++ fcvt_sticky_buf ++ fcvt_src1_nz_gates ++ g_underflow_nx_gates ++
      fcvt_not_special_gate ++ fcvt_nx_gates ++ fcvt_nv_gate ++
      fcvtwu_lsa_inv_gates ++ fcvtwu_lsa_add_gates ++ fcvtwu_lsh_gates ++
      fcvtwu_ov_gates ++ fcvtwu_lsh_ov_gates ++ fcvtwu_umag_gates ++
      fcvtwu_neg_clamp_gate ++ fcvtwu_res_gates ++
      fcvtsw_or_gates ++ [g_fcvtsw_iz] ++
      fcvtsw_inv_gates ++ fcvtsw_neg_gates ++ fcvtsw_mag_gates ++
      fcvtsw_penc_gates ++ fcvtsw_lpos_gates ++ fcvtsw_shamt_gates ++
      fcvtsw_bsl_gates ++ fcvtsw_exp_gates ++
      fcvtsw_sticky_gates ++ fcvtsw_round_gates ++ [fcvtsw_nx_gate] ++
      fcvtsw_unrounded_gates ++ fcvtsw_rnd_add_gates ++
      [g_fcvtsw_nz] ++ fcvtsw_pack_gates ++
      fcvtswu_penc_gates ++ fcvtswu_lpos_gates ++ fcvtswu_shamt_gates ++
      fcvtswu_bsl_gates ++ fcvtswu_exp_gates ++
      fcvtswu_sticky_gates ++ fcvtswu_round_gates ++ [fcvtswu_nx_gate] ++
      fcvtswu_unrounded_gates ++ fcvtswu_rnd_add_gates ++
      fcvtswu_pack_gates ++
      cvt_after_w_gates ++ cvt_after_wu_gates ++ cvt_after_sw_gates ++ cvt_out_gates ++
      nv_gates ++ nx_gates
    instances := []
    signalGroups := [
      { name := "src1",   width := 32, wires := src1 },
      { name := "op",     width := 5,  wires := op },
      { name := "result", width := 32, wires := result }
    ]
  }

-- ============================================================
-- 5. FPMisc: Top-level hierarchical module
-- ============================================================

/-- FP miscellaneous operations: sign injection, FMV, FEQ, FLT, FLE, FCVT.W.S,
    FMIN.S, FMAX.S, FCVT.S.W, FCLASS.S -/
def fpMiscCircuit : Circuit :=
  let src1 := makeIndexedWires "src1" 32
  let src2 := makeIndexedWires "src2" 32
  let op := makeIndexedWires "op" 5
  let rm := makeIndexedWires "rm" 3
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"
  let result := makeIndexedWires "result" 32
  let exc := makeIndexedWires "exc" 5

  -- Submodule output wires
  let sgnj_res := makeIndexedWires "sgnj_res" 32
  let cmp_res := makeIndexedWires "cmp_res" 32
  let cmp_nv := Wire.mk "cmp_nv"
  let class_res := makeIndexedWires "class_res" 32
  let cvt_res := makeIndexedWires "cvt_res" 32
  let cvt_nv := Wire.mk "cvt_nv"
  let cvt_nx := Wire.mk "cvt_nx"

  -- Instances
  let sgnj_inst : CircuitInstance := {
    moduleName := "FPSgnj"
    instName := "u_sgnj"
    portMap :=
      ((List.range 32).map fun i => (s!"src1_{i}", src1[i]!)) ++
      [("src2_sign", src2[31]!)] ++
      ((List.range 5).map fun i => (s!"op_{i}", op[i]!)) ++
      ((List.range 32).map fun i => (s!"result_{i}", sgnj_res[i]!))
  }

  let cmp_inst : CircuitInstance := {
    moduleName := "FPCompare"
    instName := "u_cmp"
    portMap :=
      ((List.range 32).map fun i => (s!"src1_{i}", src1[i]!)) ++
      ((List.range 32).map fun i => (s!"src2_{i}", src2[i]!)) ++
      ((List.range 5).map fun i => (s!"op_{i}", op[i]!)) ++
      [("zero", zero), ("one", one)] ++
      ((List.range 32).map fun i => (s!"result_{i}", cmp_res[i]!)) ++
      [("nv", cmp_nv)]
  }

  let class_inst : CircuitInstance := {
    moduleName := "FPClass"
    instName := "u_class"
    portMap :=
      ((List.range 32).map fun i => (s!"src1_{i}", src1[i]!)) ++
      [("zero", zero), ("one", one)] ++
      ((List.range 32).map fun i => (s!"result_{i}", class_res[i]!))
  }

  let cvt_inst : CircuitInstance := {
    moduleName := "FPCvtInt"
    instName := "u_cvt"
    portMap :=
      ((List.range 32).map fun i => (s!"src1_{i}", src1[i]!)) ++
      ((List.range 5).map fun i => (s!"op_{i}", op[i]!)) ++
      [("zero", zero), ("one", one)] ++
      ((List.range 32).map fun i => (s!"result_{i}", cvt_res[i]!)) ++
      [("nv", cvt_nv), ("nx", cvt_nx)]
  }

  -- Inverted op bits
  let nop := makeIndexedWires "nop" 5
  let inv_gates := (List.range 5).map fun i => Gate.mkNOT (op[i]!) (nop[i]!)

  -- is_class: op == 18 = 10010
  let class_t0 := Wire.mk "class_t0"
  let class_t1 := Wire.mk "class_t1"
  let class_t2 := Wire.mk "class_t2"
  let is_class := Wire.mk "is_class"
  let dec_class := [
    Gate.mkAND (op[4]!) (nop[3]!) class_t0,
    Gate.mkAND (nop[2]!) (op[1]!) class_t1,
    Gate.mkAND class_t0 class_t1 class_t2,
    Gate.mkAND class_t2 (nop[0]!) is_class
  ]

  -- is_cvt: op in 12..15 = 011xx
  let is_cvt := Wire.mk "is_cvt"
  let cvt_t0 := Wire.mk "cvt_t0"
  let dec_cvt := [
    Gate.mkAND (nop[4]!) (op[3]!) cvt_t0,
    Gate.mkAND cvt_t0 (op[2]!) is_cvt
  ]

  -- is_cmp: op in 9..11, 19, 20
  let cmp_rel := Wire.mk "cmp_rel"
  let dec_cmp_rel := [
    Gate.mkAND cvt_t0 (nop[2]!) cmp_rel
  ]

  let fmin_t0 := Wire.mk "fmin_t0"
  let fmin_t1 := Wire.mk "fmin_t1"
  let fmin_t2 := Wire.mk "fmin_t2"
  let is_fmin := Wire.mk "is_fmin"
  let dec_fmin := [
    Gate.mkAND (op[4]!) (nop[3]!) fmin_t0,
    Gate.mkAND (nop[2]!) (op[1]!) fmin_t1,
    Gate.mkAND fmin_t0 fmin_t1 fmin_t2,
    Gate.mkAND fmin_t2 (op[0]!) is_fmin
  ]

  let fmax_t0 := Wire.mk "fmax_t0"
  let fmax_t1 := Wire.mk "fmax_t1"
  let fmax_t2 := Wire.mk "fmax_t2"
  let is_fmax := Wire.mk "is_fmax"
  let dec_fmax := [
    Gate.mkAND (op[4]!) (nop[3]!) fmax_t0,
    Gate.mkAND (op[2]!) (nop[1]!) fmax_t1,
    Gate.mkAND fmax_t0 fmax_t1 fmax_t2,
    Gate.mkAND fmax_t2 (nop[0]!) is_fmax
  ]

  let cmp_or0 := Wire.mk "cmp_or0"
  let is_cmp := Wire.mk "is_cmp"
  let dec_cmp := [
    Gate.mkOR cmp_rel is_fmin cmp_or0,
    Gate.mkOR cmp_or0 is_fmax is_cmp
  ]

  -- Result selection
  let res_cmp_sgnj := makeIndexedWires "res_cmp_sgnj" 32
  let res_cmp_sgnj_gates := (List.range 32).map fun i =>
    Gate.mkMUX (sgnj_res[i]!) (cmp_res[i]!) is_cmp (res_cmp_sgnj[i]!)

  let res_cvt := makeIndexedWires "res_cvt" 32
  let res_cvt_gates := (List.range 32).map fun i =>
    Gate.mkMUX (res_cmp_sgnj[i]!) (cvt_res[i]!) is_cvt (res_cvt[i]!)

  let result_gates := (List.range 32).map fun i =>
    Gate.mkMUX (res_cvt[i]!) (class_res[i]!) is_class (result[i]!)

  -- Connect rm[0..2] to drive exc[1..3] as Boolean zero terms: rm[i] AND NOT(rm[i]) = 0.
  -- This ensures rm input ports are connected (no LINT-28), exc[1..3] have independent
  -- drivers (no LINT-31 shorted outputs), and exc[1..3] are not tied directly to logic 0 (no LINT-52).
  let not_rm0 := Wire.mk "not_rm0"
  let not_rm1 := Wire.mk "not_rm1"
  let not_rm2 := Wire.mk "not_rm2"
  let exc_gates := [
    Gate.mkBUF cvt_nx (exc[0]!),
    Gate.mkNOT (rm[0]!) not_rm0,
    Gate.mkAND (rm[0]!) not_rm0 (exc[1]!),
    Gate.mkNOT (rm[1]!) not_rm1,
    Gate.mkAND (rm[1]!) not_rm1 (exc[2]!),
    Gate.mkNOT (rm[2]!) not_rm2,
    Gate.mkAND (rm[2]!) not_rm2 (exc[3]!),
    Gate.mkOR cmp_nv cvt_nv (exc[4]!)
  ]

  { name := "FPMisc"
    inputs := src1 ++ src2 ++ op ++ rm ++ [zero, one]
    outputs := result ++ exc
    gates :=
      inv_gates ++
      dec_class ++ dec_cvt ++ dec_cmp_rel ++ dec_fmin ++ dec_fmax ++ dec_cmp ++
      res_cmp_sgnj_gates ++ res_cvt_gates ++ result_gates ++
      exc_gates
    instances := [sgnj_inst, cmp_inst, class_inst, cvt_inst]
    signalGroups := [
      { name := "src1",   width := 32, wires := src1 },
      { name := "src2",   width := 32, wires := src2 },
      { name := "op",     width := 5,  wires := op },
      { name := "rm",     width := 3,  wires := rm },
      { name := "result", width := 32, wires := result },
      { name := "exc",    width := 5,  wires := exc }
    ]
  }

end Shoumei.Circuits.Combinational
