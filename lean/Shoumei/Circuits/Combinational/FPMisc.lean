/-
Circuits/Combinational/FPMisc.lean - FP Miscellaneous Operations Circuit

Implements single-cycle FP bit-manipulation operations for RV32F:
  FSGNJ, FSGNJN, FSGNJX, FMV.X.W, FMV.W.X,
  FEQ.S, FLT.S, FLE.S, FCVT.W.S, FMIN.S, FMAX.S, FCVT.S.W, FCLASS.S

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
  | [] => (Wire.mk s!"{pfx}_empty", [])  -- should not happen
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

/-- N-bit 2:1 MUX bank: out[i] = sel ? b[i] : a[i] -/
private def mkMuxBank (pfx : String) (a b : List Wire) (sel : Wire) (n : Nat) :
    List Wire × List Gate :=
  let out := makeIndexedWires pfx n
  let gates := (List.range n).map fun i =>
    Gate.mkMUX (a[i]!) (b[i]!) sel (out[i]!)
  (out, gates)

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

  -- ============================================================
  -- NaN DETECTION (shared by comparisons, min/max, FCVT)
  -- ============================================================
  -- A float is NaN if exponent == 0xFF and mantissa != 0
  -- is_nan = exp_all_ones & mant_nonzero
  -- is_snan = is_nan & !src[22] (bit 22 = quiet bit; 0 = signaling)

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

  -- Canonical NaN: 0x7FC00000 = {0, 0xFF, 1, 0...0}
  -- bit 31=0, bits 30:23=0xFF, bit 22=1, bits 21:0=0

  -- ============================================================
  -- FSGNJ / FSGNJN / FSGNJX (existing)
  -- ============================================================

  -- Sign bits for FSGNJ variants
  -- fsgnj_bit31 = src2[31]
  let fsgnj_bit31 := Wire.mk "fsgnj_bit31"
  let g_fsgnj := Gate.mkBUF (src2[31]!) fsgnj_bit31

  -- fsgnjn_bit31 = NOT src2[31]
  let fsgnjn_bit31 := Wire.mk "fsgnjn_bit31"
  let g_fsgnjn := Gate.mkNOT (src2[31]!) fsgnjn_bit31

  -- fsgnjx_bit31 = src1[31] XOR src2[31]
  let fsgnjx_bit31 := Wire.mk "fsgnjx_bit31"
  let g_fsgnjx := Gate.mkXOR (src1[31]!) (src2[31]!) fsgnjx_bit31

  -- Op decoding: match specific encodings
  -- FSGNJ  = 21 = 10101  -> op4=1, op3=0, op2=1, op1=0, op0=1
  -- FSGNJN = 22 = 10110  -> op4=1, op3=0, op2=1, op1=1, op0=0
  -- FSGNJX = 23 = 10111  -> op4=1, op3=0, op2=1, op1=1, op0=1
  -- FMV_X_W= 16 = 10000  -> op4=1, op3=0, op2=0, op1=0, op0=0
  -- FMV_W_X= 17 = 10001  -> op4=1, op3=0, op2=0, op1=0, op0=1
  -- FEQ_S  = 9  = 01001  -> op4=0, op3=1, op2=0, op1=0, op0=1
  -- FLT_S  = 10 = 01010  -> op4=0, op3=1, op2=0, op1=1, op0=0
  -- FLE_S  = 11 = 01011  -> op4=0, op3=1, op2=0, op1=1, op0=1
  -- FCVT_W_S=12 = 01100  -> op4=0, op3=1, op2=1, op1=0, op0=0
  -- FCVT_S_W=14 = 01110  -> op4=0, op3=1, op2=1, op1=1, op0=0
  -- FCLASS =18 = 10010  -> op4=1, op3=0, op2=0, op1=1, op0=0
  -- FMIN_S =19 = 10011  -> op4=1, op3=0, op2=0, op1=1, op0=1
  -- FMAX_S =20 = 10100  -> op4=1, op3=0, op2=1, op1=0, op0=0

  -- Inverted op bits for decoding
  let nop := makeIndexedWires "nop" 5
  let inv_gates := (List.range 5).map fun i =>
    Gate.mkNOT (op[i]!) (nop[i]!)

  -- is_fsgnj  = op4 & !op3 & op2 & !op1 & op0
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

  -- is_fsgnjn = op4 & !op3 & op2 & op1 & !op0
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

  -- is_fsgnjx = op4 & !op3 & op2 & op1 & op0
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

  -- is_fmv = op4 & !op3 & !op2 & !op1  (covers both FMV_X_W and FMV_W_X)
  let fmv_t0 := Wire.mk "fmv_t0"
  let fmv_t1 := Wire.mk "fmv_t1"
  let is_fmv := Wire.mk "is_fmv"
  let dec_fmv := [
    Gate.mkAND (op[4]!) (nop[3]!) fmv_t0,
    Gate.mkAND (nop[2]!) (nop[1]!) fmv_t1,
    Gate.mkAND fmv_t0 fmv_t1 is_fmv
  ]

  -- is_sgnj_any = is_fsgnj | is_fsgnjn | is_fsgnjx
  let sgnj_or0 := Wire.mk "sgnj_or0"
  let is_sgnj_any := Wire.mk "is_sgnj_any"
  let dec_sgnj_any := [
    Gate.mkOR is_fsgnj is_fsgnjn sgnj_or0,
    Gate.mkOR sgnj_or0 is_fsgnjx is_sgnj_any
  ]

  -- Compute sign bit for sgnj group:
  -- sgnj_sign = MUX(is_fsgnjx, fsgnjx_bit31, MUX(is_fsgnjn, fsgnjn_bit31, fsgnj_bit31))
  let sgnj_sign_inner := Wire.mk "sgnj_sign_inner"
  let sgnj_sign := Wire.mk "sgnj_sign"
  let sgnj_sign_gates := [
    Gate.mkMUX fsgnj_bit31 fsgnjn_bit31 is_fsgnjn sgnj_sign_inner,
    Gate.mkMUX sgnj_sign_inner fsgnjx_bit31 is_fsgnjx sgnj_sign
  ]

  -- ============================================================
  -- FEQ.S (op=9 = 01001): !op4 & op3 & !op2 & !op1 & op0
  -- ============================================================
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

  -- XOR each bit pair
  let feq_xor := makeIndexedWires "feq_xor" 32
  let feq_xor_gates := (List.range 32).map fun i =>
    Gate.mkXOR (src1[i]!) (src2[i]!) (feq_xor[i]!)

  -- OR-reduce all XOR bits, then NOT -> equality (before NaN masking)
  let (feq_or_out, feq_or_gates) := mkOrTree "feq_or" feq_xor
  let feq_raw := Wire.mk "feq_raw"
  let g_feq_inv := Gate.mkNOT feq_or_out feq_raw
  -- If either input is NaN, FEQ returns 0
  let not_either_nan := Wire.mk "not_either_nan"
  let feq_result := Wire.mk "feq_result"
  let feq_nan_gates := [
    Gate.mkNOT either_nan not_either_nan,
    Gate.mkAND feq_raw not_either_nan feq_result
  ]

  -- ============================================================
  -- FLT.S (op=10 = 01010): !op4 & op3 & !op2 & op1 & !op0
  -- ============================================================
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

  -- 31-bit magnitude compare: src1[30:0] < src2[30:0]
  -- Use subtractor: src1[30:0] - src2[30:0], borrow_out=1 means src1 < src2
  let mag1 := (List.range 31).map fun i => src1[i]!
  let mag2 := (List.range 31).map fun i => src2[i]!
  let (_, flt_borrow, flt_sub_gates) := mkRippleSub "flt" mag1 mag2 31 zero

  -- Handle sign bits:
  -- If signs differ: result = src1[31] & !src2[31]  (negative < positive)
  -- If both same sign & both positive: result = borrow (mag1 < mag2)
  -- If both same sign & both negative: result = !borrow (mag1 > mag2 means more negative)
  -- signs_differ = src1[31] XOR src2[31]
  let flt_signs_differ := Wire.mk "flt_signs_differ"
  let g_flt_sd := Gate.mkXOR (src1[31]!) (src2[31]!) flt_signs_differ

  -- diff_result = src1[31] (if signs differ, negative one is less)
  -- same_sign_result: if src1[31]=0 (positive), borrow; if src1[31]=1 (negative), !borrow
  let flt_not_borrow := Wire.mk "flt_not_borrow"
  let g_flt_nb := Gate.mkNOT flt_borrow flt_not_borrow

  -- Also need to exclude equal case for same-sign: if equal, not less than
  -- flt_mag_eq: check if borrow=0 and all diff bits are 0
  -- Actually the subtractor gives borrow=0 when a>=b. We need strict less than.
  -- borrow=1 means a<b (unsigned). borrow=0 means a>=b. This is already correct for same positive.
  -- For same negative: !borrow means a>=b unsigned which means a<=b in magnitude, i.e., a is "more positive" = greater. Hmm.
  -- Actually for negative: larger magnitude = more negative = less.
  -- If both negative: src1 < src2 iff |src1| > |src2| iff mag1 > mag2 iff NOT(mag1 < mag2) iff NOT borrow
  -- But we also need mag1 != mag2 (strict). NOT borrow means mag1 >= mag2. We need mag1 > mag2.
  -- mag1 > mag2 iff mag2 < mag1 iff we'd need reverse subtraction...
  -- Simpler: for negative, lt = !borrow AND !equal
  -- For positive, lt = borrow (borrow=1 implies not equal)
  -- Let's just handle it: flt_same_result is correct for strict < when not equal.
  -- Actually borrow=1 means strict a<b (in unsigned subtraction with no borrow in). So for positive it's fine.
  -- For negative: we want !borrow but only when not equal. !borrow when equal is wrong (would say lt=true).
  -- So: neg_lt = !borrow AND !feq_result... wait feq checks all 32 bits. Let me use mag equality.
  -- Actually if magnitudes are equal AND signs are equal, feq_result=1 (full equality). So:
  -- flt_same_neg = !borrow AND !feq_result  ... but feq includes sign bit too. If signs are same and mags are same, feq=1. Good.
  -- Let's use: flt_same_neg = flt_not_borrow AND NOT(feq_result)
  -- But for positive: flt_same_pos = borrow (already strict)
  -- So: flt_same_result = src1[31] ? (flt_not_borrow AND !feq_result) : flt_borrow
  let flt_not_eq := Wire.mk "flt_not_eq"
  let g_flt_neq := Gate.mkNOT feq_result flt_not_eq
  let flt_neg_lt := Wire.mk "flt_neg_lt"
  let g_flt_neg_lt := Gate.mkAND flt_not_borrow flt_not_eq flt_neg_lt
  let flt_same_result2 := Wire.mk "flt_same_result2"
  let g_flt_same2 := Gate.mkMUX flt_borrow flt_neg_lt (src1[31]!) flt_same_result2

  -- raw FLT result (before NaN masking)
  let flt_raw := Wire.mk "flt_raw"
  let g_flt_final := Gate.mkMUX flt_same_result2 (src1[31]!) flt_signs_differ flt_raw
  -- If either input is NaN, FLT returns 0
  let flt_result := Wire.mk "flt_result"
  let flt_nan_gate := Gate.mkAND flt_raw not_either_nan flt_result

  -- ============================================================
  -- FLE.S (op=11 = 01011): !op4 & op3 & !op2 & op1 & op0
  -- ============================================================
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

  -- FLE = FLT OR FEQ
  let fle_result := Wire.mk "fle_result"
  let g_fle := Gate.mkOR flt_result feq_result fle_result

  -- ============================================================
  -- FCVT.W.S (op=12 = 01100): !op4 & op3 & op2 & !op1 & !op0
  -- ============================================================
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

  -- Extract exponent: exp[7:0] = src1[30:23]
  let expBits := (List.range 8).map fun i => src1[23 + i]!

  -- Mantissa with implicit 1: mant[23:0] = {1'b1, src1[22:0]}
  let mant := (List.range 23).map (fun i => src1[i]!) ++ [one]
  -- mant[0..22] = src1[0..22], mant[23] = 1

  -- Compute shift_amount = 150 - exp = 0x96 - exp (8-bit subtraction)
  -- 150 = 10010110
  -- Encode 150 as constant wires
  let const150 := [zero, one, one, zero, one, zero, zero, one]
  -- 150 = bit0=0, bit1=1, bit2=1, bit3=0, bit4=1, bit5=0, bit6=0, bit7=1
  let (shiftAmt, shiftBorrow, fcvt_sub_gates) :=
    mkRippleSub "fcvt_sh" const150 expBits 8 zero
  -- shiftBorrow=1 means 150 < exp, i.e., exp > 150 (overflow / shift left case)

  -- Check if exp < 127: shift_amount > 23
  -- If shiftAmt >= 24 (or borrow), result is 0
  -- For simplicity: use bits [5,6,7] of shiftAmt OR shiftBorrow to detect large shift
  -- shiftAmt[5] | shiftAmt[6] | shiftAmt[7] means shift >= 32
  -- Also need shift >= 24: that's shiftAmt >= 24 = 011000. Bit4 & bit3 would catch 24+.
  -- Actually let's check: if any of bits 7,6,5 are set, shift >= 32.
  -- Bit 4 set means shift >= 16. Combined with bit 3: >= 24.
  -- For shift > 23 exactly: we need shiftAmt > 23. Since shiftAmt is unsigned 8-bit,
  -- shiftAmt > 23 iff shiftAmt >= 24 iff bit7|bit6|bit5 | (bit4 & bit3)
  -- When shift > 23 or borrow (exp > 150), clamp to 0 or overflow.
  -- For test purposes: exp=128 -> shift=22, exp=127 -> shift=23, exp=126 -> shift=24 (too big, result=0).
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
  -- fcvt_underflow: if 1, result magnitude is 0 (underflow) or overflow; we output 0 for underflow,
  -- and for overflow (shiftBorrow=1), we'd want 0x7FFFFFFF but let's just pass through (not tested).

  -- Barrel shift right: mant >> shiftAmt[4:0]  (we use 5 bits, max shift 31, mant is 24 bits padded to 32)
  -- Pad mant to 32 bits with zeros
  let mant32 := mant ++ (List.range 8).map (fun _ => zero)
  let shiftCtrl := (List.range 5).map fun i => shiftAmt[i]!
  let (fcvt_shifted, fcvt_shift_gates) :=
    mkBarrelShiftRight "fcvt_bsh" mant32 32 shiftCtrl 5 zero

  -- If underflow, clamp magnitude to 0
  let fcvt_mag := makeIndexedWires "fcvt_mag" 32
  let fcvt_mag_gates := (List.range 32).map fun i =>
    -- fcvt_mag[i] = underflow ? 0 : shifted[i]
    Gate.mkMUX (fcvt_shifted[i]!) zero fcvt_underflow (fcvt_mag[i]!)

  -- OR-reduce fcvt_mag to detect nonzero magnitude (for FCVT.WU.S NV)
  let fcvt_mag_bits := (List.range 32).map fun i => fcvt_mag[i]!
  let (fcvt_mag_nz, fcvt_mag_nz_gates) := mkOrTree "fcvt_mag_nz" fcvt_mag_bits

  -- If src1[31] (negative), negate: result = ~mag + 1 (2's complement)
  -- Invert
  let fcvt_inv := makeIndexedWires "fcvt_inv" 32
  let fcvt_inv_gates := (List.range 32).map fun i =>
    Gate.mkNOT (fcvt_mag[i]!) (fcvt_inv[i]!)

  -- Add 1 using Kogge-Stone adder (O(log n) carry delay instead of O(n) ripple)
  let fcvt_neg := makeIndexedWires "fcvt_neg" 32
  let zeros32 := (List.range 32).map fun _ => zero
  let (fcvt_neg_gates, _fcvt_neg_cout) :=
    mkKoggeStoneAdd fcvt_inv zeros32 one fcvt_neg "fcvt_neg"

  -- Select positive or negative based on src1[31]
  let fcvt_normal := makeIndexedWires "fcvt_normal" 32
  let fcvt_sel_gates := (List.range 32).map fun i =>
    Gate.mkMUX (fcvt_mag[i]!) (fcvt_neg[i]!) (src1[31]!) (fcvt_normal[i]!)

  -- FCVT.W.S special cases: NaN, Inf, overflow
  -- is_inf_src1 = exp_all_ones & mant_zero (reuse nan1_exp_ones, nan1_mant_nz)
  let nan1_mant_zero := Wire.mk "nan1_mant_zero"
  let is_inf_src1 := Wire.mk "is_inf_src1"
  let nan1_mant_z_gate := Gate.mkNOT nan1_mant_nz nan1_mant_zero
  let inf1_gate := Gate.mkAND nan1_exp_ones nan1_mant_zero is_inf_src1

  -- fcvt_overflow = shiftBorrow AND NOT is_nan AND NOT is_inf (exp > 150 but finite)
  let fcvt_overflow := Wire.mk "fcvt_overflow"
  let _fcvt_special := Wire.mk "fcvt_special"  -- NaN or Inf or overflow
  let fcvt_special_gates := [
    -- overflow: exp > 150 (shiftBorrow=1) and not NaN/Inf
    -- Actually shiftBorrow=1 covers all exp > 150, including Inf/NaN. Let's just use shiftBorrow.
    Gate.mkBUF shiftBorrow fcvt_overflow
  ]

  -- For NaN or +overflow: return 0x7FFFFFFF (INT32_MAX)
  -- For -Inf or -overflow: return 0x80000000 (INT32_MIN)
  -- NaN always returns INT32_MAX
  -- Negative Inf/overflow: bit31=1, rest=0 (0x80000000)
  -- Positive Inf/overflow or NaN: bit31=0, rest=1 (0x7FFFFFFF)
  let fcvt_is_special := Wire.mk "fcvt_is_special"  -- NaN, Inf, or overflow
  let fcvt_neg_special := Wire.mk "fcvt_neg_special"  -- negative & special & not NaN
  let fcvt_not_nan := Wire.mk "fcvt_not_nan"
  let fcvt_special_det := [
    Gate.mkOR is_nan_src1 fcvt_overflow fcvt_is_special,
    Gate.mkNOT is_nan_src1 fcvt_not_nan,
    -- neg_special = sign & not_nan & special (negative overflow or -Inf)
    Gate.mkAND (src1[31]!) fcvt_not_nan (Wire.mk "fcvt_neg_and_nn"),
    Gate.mkAND (Wire.mk "fcvt_neg_and_nn") fcvt_is_special fcvt_neg_special
  ]

  -- Special result: 0x80000000 if neg_special, else 0x7FFFFFFF
  let fcvt_res := makeIndexedWires "fcvt_res" 32
  let fcvt_result_gates := (List.range 32).map fun i =>
    if i == 31 then
      -- bit 31: 1 if neg_special, 0 otherwise (for special case)
      -- normal: fcvt_normal[31]; special: neg_special
      Gate.mkMUX (fcvt_normal[i]!) fcvt_neg_special fcvt_is_special (fcvt_res[i]!)
    else
      -- bits 30:0: 0 if neg_special, 1 otherwise (for special case)
      let _not_neg_special := Wire.mk s!"fcvt_nns_{i}"
      -- When special: result = neg_special ? 0 : 1 = NOT neg_special
      -- We need a wire for "special value bit"
      let special_bit := Wire.mk s!"fcvt_sb_{i}"
      -- special_bit = NOT neg_special (1 if positive overflow/NaN, 0 if negative overflow)
      Gate.mkMUX (fcvt_normal[i]!) special_bit fcvt_is_special (fcvt_res[i]!)
  -- Extra gates for special bits (NOT neg_special)
  let fcvt_not_neg_special := Wire.mk "fcvt_not_neg_special"
  let fcvt_special_bit_gates := [Gate.mkNOT fcvt_neg_special fcvt_not_neg_special] ++
    (List.range 31).map fun i =>
      Gate.mkBUF fcvt_not_neg_special (Wire.mk s!"fcvt_sb_{i}")

  -- NX flag for FCVT.W.S: lost bits during right shift
  -- If shift_amount > 0, check if any shifted-out bits are nonzero.
  -- The shifted-out bits are the lower `shiftAmt` bits of mant32.
  -- Simple approach: OR the lower bits of mant32 that get shifted out.
  -- Since we already have the shifted result, we can detect inexact by comparing:
  --   mant32 != (shifted << shiftAmt), but that's complex.
  -- Simpler: OR all bits of mant32 below the shift point.
  -- For any shiftAmt > 0 with nonzero fractional part, NX=1.
  -- Actually, the mantissa is 24 bits (bits 0-23 of mant32, rest are zero).
  -- After shifting right by S, the integer part is mant32[23:S] and fractional is mant32[S-1:0].
  -- NX = any bit in mant32[S-1:0] is nonzero = mant32 & ((1<<S) - 1) != 0.
  -- Since we don't have a dynamic mask, use: fcvt_mag != (shifted >> 0) comparison.
  -- Even simpler: if shiftAmt > 0 and the original mantissa has bits below the shift point.
  -- Approximate: check if shiftAmt > 0 (any shift loses the LSBs of fractional)
  -- For now, use the fact that shifted result << shiftAmt != mant32.
  -- Actually simplest correct approach: NX = shifted_out_bits != 0.
  -- shifted_out_bits = mant32 XOR (fcvt_shifted << shiftAmt)... too complex.
  -- Better: compute the sticky bits directly from the barrel shifter's "lost" bits.
  -- For a right shift by S: lost_bits = mant32 & ((1 << S) - 1).
  -- We can compute this as: OR(mant[0]..mant[S-1]).
  -- Since S varies, we need a dynamic OR. Use the barrel shifter stages:
  -- At stage k (shift by 2^k): if shiftAmt[k]=1, the bits that "fall off" are the bottom 2^k bits.
  -- After all stages, any bit that was shifted out contributes to sticky.
  -- For simplicity: check if fcvt_underflow==0 AND shiftAmt[0..4] != 0, then OR-reduce
  -- the lower bits of the unshifted mantissa.
  -- Actually, the simplest approach that works: NX = NOT(fcvt_underflow) AND (mant has any bit below shift point).
  -- Since the shift point is dynamic, let's just OR all 23 mantissa fraction bits (src1[22:0])
  -- when exp < 150 (i.e., shift > 0). This is an over-approximation (says NX even for exact conversions
  -- like 1.0 which has mantissa = 1.000...0). Wrong.
  -- Correct approach: build a 24-bit mask from shiftAmt and AND with mant, then OR-reduce.
  -- That's quite expensive in gates. Let me do it properly.

  -- NX detection: After right-shifting mant by shiftAmt, the lost bits are:
  -- lost = mant32[shiftAmt-1 : 0]. NX = (lost != 0) AND NOT fcvt_underflow AND NOT fcvt_overflow
  -- Build the lost-bits sticky bit using the barrel shifter's intermediate results.
  -- For each barrel shift stage k: if shift bit k is 1, the lower 2^k bits of the input to that stage
  -- "fall off". We can OR-reduce those bits as a sticky contribution.
  -- But this is complex. Let me use a simpler approach:
  -- fcvt_lost = OR(mant32[0..23]) masked by shift amount.
  -- For shiftAmt = S: lost bits are mant32[0..S-1].
  -- Create a cumulative mask: sticky_bit = (S>=1 & mant[0]) | (S>=2 & mant[1]) | ... | (S>=24 & mant[23])
  -- S >= k iff shiftAmt >= k. This requires 24 comparisons.
  -- Even simpler for now: just compare the reconstructed integer back.
  -- fcvt_lost = (mag != (mag_rounded_back_to_float)). Too complex.
  -- Let me use a practical shortcut that works for riscv-tests:
  -- fcvt_nx = NOT(is_special) AND NOT(fcvt_shift_too_big) AND NOT(shiftBorrow) AND (shiftAmt != 0)
  --           AND (src1 represents a non-integer float)
  -- The condition "src1 is non-integer" = exp < 150 AND mant has bits below decimal point.
  -- exp < 150 is already !shiftBorrow. shiftAmt != 0 means shift > 0 meaning there ARE fractional bits.
  -- But even with shiftAmt != 0, the fractional bits might all be zero (e.g., 2.0 = 1.0 * 2^1,
  -- exp=128, shift=22, mant=0x800000, shifted = 0x00000002, lost = mant[21:0] = 0 → exact).
  -- So we really do need to check the lost bits.

  -- Build sticky bit from barrel shifter stages (track OR of shifted-out bits)
  -- Initial: sticky = 0, data = mant32
  -- Stage k (shift by 2^k): if shiftAmt[k]=1, the lower 2^k bits of current data are lost.
  --   new_sticky = old_sticky | OR(data[0..2^k-1]) when shiftAmt[k]=1
  --   new_data = data >> 2^k when shiftAmt[k]=1
  -- Since we already have the barrel shifter stages, we can compute sticky in parallel.
  -- Actually, let's just compute: lost_or = OR of (mant32[i] for i where i < shiftAmt).
  -- Use: for each mant bit i (0..23), check if i < shiftAmt (i.e., shiftAmt > i).
  -- bit_lost_i = mant32[i] AND (shiftAmt > i)
  -- Then fcvt_sticky = OR of all bit_lost_i.
  -- To check shiftAmt > i for a 5-bit shiftAmt, we compare shiftAmt against (i+1).
  -- This is 24 comparisons × 5 bits each = expensive. Let me just build the sticky from the shifter.

  -- Simpler approach: reverse-shift the shifted result and XOR with original.
  -- If any bit differs, it was a lost bit. But reverse-shifting is as expensive as the shifter.

  -- Pragmatic approach: use the barrel shifter intermediate stages to accumulate sticky.
  -- For a 5-stage barrel shifter shifting mant32 right:
  -- Stage 0 (shift by 1): if sa[0], lost bit = mant32[0]
  -- Stage 1 (shift by 2): if sa[1], lost bits = prev_data[0..1]
  -- Stage 2 (shift by 4): if sa[2], lost bits = prev_data[0..3]
  -- Stage 3 (shift by 8): if sa[3], lost bits = prev_data[0..7]
  -- Stage 4 (shift by 16): if sa[4], lost bits = prev_data[0..15]
  -- At each stage, compute OR of lost bits and accumulate into sticky.
  -- This requires re-doing the barrel shifter with sticky tracking.
  -- But we already have the barrel shifter result. Let me build a separate sticky computation.

  -- Actually, the easiest correct approach: mant32 has known positions.
  -- After shifting right by S, bits mant32[S-1:0] are lost.
  -- The maximum meaningful shift is 23 (mant has 24 bits, position 0-23).
  -- For S > 23, all bits are lost (but that's the underflow case, result=0, NX=1 if mant!=0).
  -- For S = 0, no bits are lost (NX=0, exact).
  -- Let me build a 5-stage sticky accumulator:
  let fcvt_sticky := Wire.mk "fcvt_sticky_out"
  -- Build stage-by-stage sticky tracking alongside a copy of the barrel shift
  -- But this duplicates the barrel shifter. Let me use a different approach.
  -- Since mant32 bits 24-31 are always 0, and we shift right, the shifted-out bits are
  -- from the original mant32. We can just check: does the original mant have any bit set
  -- in positions 0 through (shiftAmt-1)?
  -- For shiftAmt 0-23, build a priority-OR structure:
  --   sticky_stage[k] = shiftAmt[k] ? OR(data_at_stage_k [0 .. 2^k-1]) : 0
  -- Let me compute the sticky per-stage from the barrel shift intermediates.

  -- Recompute barrel shift with sticky tracking
  let (_, fcvt_sticky_gates) :=
    (List.range 5).foldl (fun (acc : (List Wire × Wire) × List Gate) stage =>
      let (prev_data, prev_sticky) := acc.1
      let shift := Nat.pow 2 stage
      -- OR-reduce the lower `shift` bits of prev_data (these get shifted out if sa[stage]=1)
      let lost_bits := (List.range (min shift 32)).map fun i => prev_data[i]!
      let (lost_or, lost_or_gates) := mkOrTree s!"fcvt_lost_s{stage}" lost_bits
      -- new_sticky = sa[stage] ? (prev_sticky | lost_or) : prev_sticky
      let stage_contrib := Wire.mk s!"fcvt_sticky_contrib_{stage}"
      let new_sticky := Wire.mk s!"fcvt_sticky_{stage}"
      let g_contrib := Gate.mkAND (shiftCtrl[stage]!) lost_or stage_contrib
      let g_sticky := Gate.mkOR prev_sticky stage_contrib new_sticky
      -- Advance data (shift right by 2^stage if sa[stage]=1)
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

  -- FCVT.W.S NX: inexact if sticky != 0, not special, not zero
  -- is_zero_src1: exp=0 and mant=0 (actually check if src1[30:0] == 0)
  let fcvt_src1_mag := (List.range 31).map fun i => src1[i]!
  let (fcvt_src1_nz, fcvt_src1_nz_gates) := mkOrTree "fcvt_s1nz" fcvt_src1_mag
  -- Also NX when shift_too_big (underflow) and value was nonzero
  -- Must exclude overflow (shiftBorrow=1): overflow sets NV, not NX
  let fcvt_underflow_nx := Wire.mk "fcvt_underflow_nx"
  let not_shiftBorrow := Wire.mk "fcvt_not_shiftBorrow"
  let fcvt_uflow_real := Wire.mk "fcvt_uflow_real"
  let g_underflow_nx_gates := [
    Gate.mkNOT shiftBorrow not_shiftBorrow,
    Gate.mkAND fcvt_shift_too_big not_shiftBorrow fcvt_uflow_real,
    Gate.mkAND fcvt_uflow_real fcvt_src1_nz fcvt_underflow_nx
  ]
  -- fcvt_nx = (sticky AND NOT is_special) OR underflow_nx
  let fcvt_nx_pre := Wire.mk "fcvt_nx_pre"
  let fcvt_nx := Wire.mk "fcvt_nx"
  let fcvt_nx_gates := [
    Gate.mkAND fcvt_sticky (Wire.mk "fcvt_not_special") fcvt_nx_pre,
    Gate.mkOR fcvt_nx_pre fcvt_underflow_nx fcvt_nx
  ]
  let fcvt_not_special_gate := [Gate.mkNOT fcvt_is_special (Wire.mk "fcvt_not_special")]

  -- FCVT.W.S NV: NaN, Inf, or overflow
  let fcvt_nv := Wire.mk "fcvt_nv"
  let fcvt_nv_gate := [Gate.mkBUF fcvt_is_special fcvt_nv]

  -- ============================================================
  -- FCVT.WU.S (op=13 = 01101): !op4 & op3 & op2 & !op1 & op0
  -- Convert float32 to unsigned int32.
  -- Reuses fcvt_mag (barrel-shifted mantissa). If input is negative, clamp to 0.
  -- ============================================================
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

  -- For unsigned conversion with exp > 150 (shiftBorrow=1, positive):
  -- Need to LEFT-shift mant32 by (exp - 150) bits.
  -- Left shift amount = two's complement of shiftAmt[3:0] (since shiftAmt = 150 - exp < 0)
  -- lsa = (~shiftAmt[3:0]) + 1
  let fcvtwu_lsa := makeIndexedWires "fcvtwu_lsa" 4
  let fcvtwu_lsa_inv := (List.range 4).map fun i => Wire.mk s!"fcvtwu_lsa_inv_{i}"
  let fcvtwu_lsa_inv_gates := (List.range 4).map fun i =>
    Gate.mkNOT (shiftAmt[i]!) (fcvtwu_lsa_inv[i]!)
  -- 4-bit increment: inv + 1 using ripple carry
  let fcvtwu_lsa_carry := (List.range 5).map fun i => Wire.mk s!"fcvtwu_lsa_c_{i}"
  let fcvtwu_lsa_add_gates :=
    [Gate.mkBUF one (fcvtwu_lsa_carry[0]!)] ++
    (List.range 4).map (fun i =>
      -- sum[i] = inv[i] XOR carry[i], carry[i+1] = inv[i] AND carry[i]
      Gate.mkXOR (fcvtwu_lsa_inv[i]!) (fcvtwu_lsa_carry[i]!) (fcvtwu_lsa[i]!)) ++
    (List.range 4).map (fun i =>
      Gate.mkAND (fcvtwu_lsa_inv[i]!) (fcvtwu_lsa_carry[i]!) (fcvtwu_lsa_carry[i+1]!))

  -- Barrel shift left: mant32 << lsa[3:0]
  let mant32_list := (List.range 32).map fun i => mant32[i]!
  let (fcvtwu_lsh, fcvtwu_lsh_gates) :=
    mkBarrelShiftLeft "fcvtwu_lsh" mant32_list 32 fcvtwu_lsa 4 zero

  -- Detect unsigned overflow: exp >= 159 (left shift > 8)
  -- When shiftBorrow=1 and shiftAmt[3:0] indicates lsa > 8.
  -- lsa > 8 iff lsa[3]=1 AND lsa[2:0] != 0, OR lsa[3]=1 AND lsa[2]=0 AND lsa[1]=0 AND lsa[0]=1 means lsa=9.
  -- Simpler: overflow when lsa > 8, i.e., lsa >= 9.
  -- lsa[3]=1 means lsa >= 8. lsa=8 is ok (exp=158). lsa=9+ means overflow.
  -- So overflow = lsa[3] AND (lsa[2] OR lsa[1] OR lsa[0])
  -- Also overflow if shiftAmt upper bits indicate exp much larger (shiftAmt[7:4] != 1111)
  -- When shiftBorrow=1, shiftAmt = 256 - (exp-150). For exp 151-158: shiftAmt = 248-255, upper nibble = F.
  -- For exp >= 159: shiftAmt = 247 or less, upper nibble != F.
  -- Check: all of shiftAmt[7:4] must be 1 for exp <= 158.
  let fcvtwu_ov_t0 := Wire.mk "fcvtwu_ov_t0"
  let fcvtwu_ov_t1 := Wire.mk "fcvtwu_ov_t1"
  let fcvtwu_overflow := Wire.mk "fcvtwu_overflow"
  -- Upper nibble all 1s: shiftAmt[7] AND shiftAmt[6] AND shiftAmt[5] AND shiftAmt[4]
  -- If NOT all 1s, overflow.
  let fcvtwu_ov_gates := [
    Gate.mkAND (shiftAmt[7]!) (shiftAmt[6]!) fcvtwu_ov_t0,
    Gate.mkAND (shiftAmt[5]!) (shiftAmt[4]!) fcvtwu_ov_t1,
    Gate.mkAND fcvtwu_ov_t0 fcvtwu_ov_t1 (Wire.mk "fcvtwu_upper_ok"),
    Gate.mkNOT (Wire.mk "fcvtwu_upper_ok") fcvtwu_overflow
  ]

  -- FCVT.WU.S result MUX:
  -- If shiftBorrow=0: use fcvt_mag (right-shifted, normal case)
  -- If shiftBorrow=1 AND NOT overflow: use fcvtwu_lsh (left-shifted)
  -- If shiftBorrow=1 AND overflow: clamp to 0xFFFFFFFF
  -- If negative: clamp to 0
  let fcvtwu_lsh_or_ov := makeIndexedWires "fcvtwu_lsh_ov" 32
  let fcvtwu_lsh_ov_gates := (List.range 32).map fun i =>
    -- overflow ? 1 : lsh[i]
    Gate.mkOR (fcvtwu_lsh[i]!) fcvtwu_overflow (fcvtwu_lsh_or_ov[i]!)

  let fcvtwu_unsigned_mag := makeIndexedWires "fcvtwu_umag" 32
  let fcvtwu_umag_gates := (List.range 32).map fun i =>
    -- shiftBorrow ? lsh_or_ov : fcvt_mag
    Gate.mkMUX (fcvt_mag[i]!) (fcvtwu_lsh_or_ov[i]!) shiftBorrow (fcvtwu_unsigned_mag[i]!)

  -- Final: negative (and not NaN) ? 0 : unsigned_mag
  -- NaN always returns 0xFFFFFFFF regardless of sign bit
  let fcvtwu_neg_clamp := Wire.mk "fcvtwu_neg_clamp"
  let fcvtwu_neg_clamp_gate := [
    Gate.mkNOT is_nan_src1 (Wire.mk "fcvtwu_not_nan"),
    Gate.mkAND (src1[31]!) (Wire.mk "fcvtwu_not_nan") fcvtwu_neg_clamp
  ]
  let fcvtwu_res := makeIndexedWires "fcvtwu_res" 32
  let fcvtwu_res_gates := (List.range 32).map fun i =>
    Gate.mkMUX (fcvtwu_unsigned_mag[i]!) zero fcvtwu_neg_clamp (fcvtwu_res[i]!)

  -- ============================================================
  -- FMIN.S (op=19 = 10011): op4 & !op3 & !op2 & op1 & op0
  -- ============================================================
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

  -- FMIN result with NaN handling:
  -- If both NaN: canonical NaN (0x7FC00000)
  -- If src1 is NaN (only): return src2
  -- If src2 is NaN (only): return src1
  -- Else: flt_raw ? src1 : src2 (use raw FLT, not NaN-masked)
  let fmin_base := makeIndexedWires "fmin_base" 32
  let fmin_nan1 := makeIndexedWires "fmin_nan1" 32
  let fmin_nan2 := makeIndexedWires "fmin_nan2" 32
  let fmin_res := makeIndexedWires "fmin_res" 32
  let fmin_res_gates :=
    -- Base: flt_raw ? src1 : src2
    (List.range 32).map (fun i =>
      Gate.mkMUX (src2[i]!) (src1[i]!) flt_raw (fmin_base[i]!)) ++
    -- If src1 is NaN: use src2
    (List.range 32).map (fun i =>
      Gate.mkMUX (fmin_base[i]!) (src2[i]!) is_nan_src1 (fmin_nan1[i]!)) ++
    -- If src2 is NaN: use src1
    (List.range 32).map (fun i =>
      Gate.mkMUX (fmin_nan1[i]!) (src1[i]!) is_nan_src2 (fmin_nan2[i]!)) ++
    -- If both NaN: canonical NaN 0x7FC00000
    (List.range 32).map (fun i =>
      let canon_bit := if i == 22 || (i >= 23 && i <= 30) then one else zero
      Gate.mkMUX (fmin_nan2[i]!) canon_bit both_nan (fmin_res[i]!))

  -- ============================================================
  -- FMAX.S (op=20 = 10100): op4 & !op3 & op2 & !op1 & !op0
  -- ============================================================
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

  -- FMAX result with NaN handling (same pattern as FMIN)
  let fmax_base := makeIndexedWires "fmax_base" 32
  let fmax_nan1 := makeIndexedWires "fmax_nan1" 32
  let fmax_nan2 := makeIndexedWires "fmax_nan2" 32
  let fmax_res := makeIndexedWires "fmax_res" 32
  let fmax_res_gates :=
    -- Base: flt_raw ? src2 : src1
    (List.range 32).map (fun i =>
      Gate.mkMUX (src1[i]!) (src2[i]!) flt_raw (fmax_base[i]!)) ++
    -- If src1 is NaN: use src2
    (List.range 32).map (fun i =>
      Gate.mkMUX (fmax_base[i]!) (src2[i]!) is_nan_src1 (fmax_nan1[i]!)) ++
    -- If src2 is NaN: use src1
    (List.range 32).map (fun i =>
      Gate.mkMUX (fmax_nan1[i]!) (src1[i]!) is_nan_src2 (fmax_nan2[i]!)) ++
    -- If both NaN: canonical NaN 0x7FC00000
    (List.range 32).map (fun i =>
      let canon_bit := if i == 22 || (i >= 23 && i <= 30) then one else zero
      Gate.mkMUX (fmax_nan2[i]!) canon_bit both_nan (fmax_res[i]!))

  -- ============================================================
  -- FCVT.S.W (op=14 = 01110): !op4 & op3 & op2 & op1 & !op0
  -- Convert signed int32 (src1) to float32
  -- ============================================================
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

  -- Step 1: Check if src1 == 0 (OR-reduce all 32 bits)
  let (fcvtsw_or_out, fcvtsw_or_gates) := mkOrTree "fcvtsw_nz" src1
  let fcvtsw_is_zero := Wire.mk "fcvtsw_is_zero"
  let g_fcvtsw_iz := Gate.mkNOT fcvtsw_or_out fcvtsw_is_zero

  -- Step 2: Get magnitude (absolute value). If src1[31]=1, negate.
  -- Invert all bits
  let fcvtsw_inv := makeIndexedWires "fcvtsw_inv" 32
  let fcvtsw_inv_gates := (List.range 32).map fun i =>
    Gate.mkNOT (src1[i]!) (fcvtsw_inv[i]!)

  -- Add 1 using Kogge-Stone adder (O(log n) carry delay)
  let fcvtsw_neg := makeIndexedWires "fcvtsw_neg" 32
  let fcvtsw_zeros32 := (List.range 32).map fun _ => zero
  let (fcvtsw_neg_gates, _fcvtsw_neg_cout) :=
    mkKoggeStoneAdd fcvtsw_inv fcvtsw_zeros32 one fcvtsw_neg "fcvtsw_neg"

  -- Select magnitude: if src1[31]=1, use negated; else use src1
  let fcvtsw_mag := makeIndexedWires "fcvtsw_mag" 32
  let fcvtsw_mag_gates := (List.range 32).map fun i =>
    Gate.mkMUX (src1[i]!) (fcvtsw_neg[i]!) (src1[31]!) (fcvtsw_mag[i]!)

  -- Step 3: Priority encoder - find leading one position (from bit 31 down to 0)
  -- Output: lead_pos[4:0] and lead_found
  -- We scan from bit 31 downward. At each step, if not yet found and current bit is 1,
  -- capture the position.
  -- Implementation: cascade of MUXes. Start with found=0, pos=0.
  -- For bit i (31 down to 0):
  --   new_found = old_found OR mag[i]
  --   new_pos[k] = old_found ? old_pos[k] : (mag[i] ? encode(i)[k] : old_pos[k])
  --             = MUX(old_pos[k], encode(i)[k], mag[i] AND NOT old_found)
  let fcvtsw_lpos := makeIndexedWires "fcvtsw_lpos" 5
  let fcvtsw_pe_init := makeIndexedWires "fcvtsw_pe_pos_init" 5
  let fcvtsw_pe_init_gates := (List.range 5).map fun k =>
    Gate.mkBUF zero (fcvtsw_pe_init[k]!)
  let (_, _, fcvtsw_penc_fold_gates) := (List.range 32).foldl
    (fun (acc : Wire × (List Wire × List Gate)) idx =>
      let i := 31 - idx  -- scan from 31 down to 0
      let old_found := acc.1
      let old_pos := acc.2.1
      let gates_acc := acc.2.2
      -- take = mag[i] AND NOT old_found
      let nf := Wire.mk s!"fcvtsw_pe_nf_{i}"
      let take := Wire.mk s!"fcvtsw_pe_take_{i}"
      let g_nf := Gate.mkNOT old_found nf
      let g_take := Gate.mkAND (fcvtsw_mag[i]!) nf take
      -- new_found = old_found OR mag[i]
      let new_found := Wire.mk s!"fcvtsw_pe_found_{i}"
      let g_found := Gate.mkOR old_found (fcvtsw_mag[i]!) new_found
      -- Update position bits
      let new_pos := makeIndexedWires s!"fcvtsw_pe_pos_{i}" 5
      let pos_gates := (List.range 5).map fun k =>
        let bit_val := if (i / Nat.pow 2 k) % 2 == 1 then one else zero
        Gate.mkMUX (old_pos[k]!) bit_val take (new_pos[k]!)
      (new_found, (new_pos, gates_acc ++ [g_nf, g_take, g_found] ++ pos_gates))
    ) (zero, (fcvtsw_pe_init, []))
  let fcvtsw_penc_gates := fcvtsw_pe_init_gates ++ fcvtsw_penc_fold_gates

  -- Final lead position is in the last pos wires. Copy to fcvtsw_lpos.
  -- The final pos after scanning bit 0 is fcvtsw_pe_pos_0
  let fcvtsw_final_pos := makeIndexedWires "fcvtsw_pe_pos_0" 5
  let fcvtsw_lpos_gates := (List.range 5).map fun k =>
    Gate.mkBUF (fcvtsw_final_pos[k]!) (fcvtsw_lpos[k]!)

  -- Step 4: Compute shift amount = 31 - lead_pos.
  -- We need to left-shift magnitude by (31 - lead_pos) to normalize.
  -- 31 - lead_pos as 5-bit: invert lead_pos bits (31 - x = 31 XOR x for 5-bit when x <= 31,
  -- actually 31 - x = NOT(x) when x <= 31 in 5-bit unsigned, since 31 = 11111).
  -- ~x in 5 bits = 31 - x. Perfect!
  let fcvtsw_shamt := makeIndexedWires "fcvtsw_shamt" 5
  let fcvtsw_shamt_gates := (List.range 5).map fun k =>
    Gate.mkNOT (fcvtsw_lpos[k]!) (fcvtsw_shamt[k]!)

  -- Step 5: Barrel left shift magnitude by shamt
  let (fcvtsw_shifted, fcvtsw_bsl_gates) :=
    mkBarrelShiftLeft "fcvtsw_bsl" fcvtsw_mag 32 fcvtsw_shamt 5 zero

  -- After shifting, bit 31 is the leading 1. The mantissa is bits [30:8] (23 bits).
  -- Exponent = lead_pos + 127.
  -- 127 = 01111111. Add lead_pos[4:0] + 127 using ripple adder.
  let const127 := [one, one, one, one, one, one, one, zero]
  -- 127 = bits: 1,1,1,1,1,1,1,0 (bit0=1, bit1=1, ..., bit6=1, bit7=0)
  let fcvtsw_lpos8 := (List.range 5).map (fun k => fcvtsw_lpos[k]!) ++
    [zero, zero, zero]  -- zero-extend to 8 bits
  -- Exponent add using Kogge-Stone (O(log n) carry delay)
  let fcvtsw_exp := makeIndexedWires "fcvtsw_exp" 8
  let (fcvtsw_exp_gates, _fcvtsw_exp_cout) :=
    mkKoggeStoneAdd const127 fcvtsw_lpos8 zero fcvtsw_exp "fcvtsw_exp"

  -- Step 6: Rounding (RNE) and pack float result
  -- After shifting: bit 31 = hidden 1, bits [30:8] = mantissa, bit 7 = round, bits [6:0] = sticky
  -- RNE: round_up = round_bit AND (sticky OR guard_bit)
  --   guard_bit = shifted[8] (LSB of mantissa), round_bit = shifted[7], sticky = OR(shifted[6:0])
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
  -- NX flag: any lost bits (round_bit OR sticky)
  let fcvtsw_nx := Wire.mk "fcvtsw_nx"
  let fcvtsw_nx_gate := Gate.mkOR fcvtsw_round_bit fcvtsw_sticky_or fcvtsw_nx

  -- Pack unrounded: {0_placeholder_sign, exp[7:0], mantissa[22:0]} in bits [30:0]
  -- Then add round_up as carry-in to bits [30:0] using Kogge-Stone
  let fcvtsw_unrounded := makeIndexedWires "fcvtsw_unrnd" 31
  let fcvtsw_unrounded_gates := (List.range 31).map fun i =>
    if i < 23 then Gate.mkBUF (fcvtsw_shifted[i + 8]!) (fcvtsw_unrounded[i]!)
    else Gate.mkBUF (fcvtsw_exp[i - 23]!) (fcvtsw_unrounded[i]!)
  -- Add round_up using Kogge-Stone (31-bit add with carry-in)
  let fcvtsw_zeros31 := (List.range 31).map fun _ => zero
  let fcvtsw_rounded := makeIndexedWires "fcvtsw_rnded" 31
  let (fcvtsw_rnd_add_gates, _fcvtsw_rnd_cout) :=
    mkKoggeStoneAdd fcvtsw_unrounded fcvtsw_zeros31 fcvtsw_round_up fcvtsw_rounded "fcvtsw_rnd"

  let fcvtsw_not_zero := Wire.mk "fcvtsw_not_zero"
  let g_fcvtsw_nz := Gate.mkNOT fcvtsw_is_zero fcvtsw_not_zero

  let fcvtsw_res := makeIndexedWires "fcvtsw_res" 32
  let fcvtsw_pack_gates := (List.range 32).map fun i =>
    if i < 31 then
      -- mantissa+exponent bits from rounded result, zeroed if input was zero
      Gate.mkMUX (fcvtsw_rounded[i]!) zero fcvtsw_is_zero (fcvtsw_res[i]!)
    else
      -- bit 31 = sign = src1[31], gated by not_zero
      Gate.mkMUX (src1[31]!) zero fcvtsw_is_zero (fcvtsw_res[i]!)

  -- ============================================================
  -- FCVT.S.WU (op=15 = 01111): !op4 & op3 & op2 & op1 & op0
  -- Convert unsigned int32 (src1) to float32. Like FCVT.S.W but
  -- magnitude = src1 (no abs value), sign = 0.
  -- ============================================================
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

  -- Check if src1 == 0
  -- Reuse fcvtsw_is_zero from FCVT.S.W (already checks src1 for zero)

  -- Priority encoder on src1 directly (unsigned magnitude)
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

  -- Shift amount = 31 - lead_pos = NOT(lead_pos) in 5 bits
  let fcvtswu_shamt := makeIndexedWires "fcvtswu_shamt" 5
  let fcvtswu_shamt_gates := (List.range 5).map fun k =>
    Gate.mkNOT (fcvtswu_lpos[k]!) (fcvtswu_shamt[k]!)

  -- Barrel left shift src1 by shamt
  let (fcvtswu_shifted, fcvtswu_bsl_gates) :=
    mkBarrelShiftLeft "fcvtswu_bsl" src1 32 fcvtswu_shamt 5 zero

  -- Exponent = lead_pos + 127
  let fcvtswu_lpos8 := (List.range 5).map (fun k => fcvtswu_lpos[k]!) ++
    [zero, zero, zero]
  -- Exponent add using Kogge-Stone (O(log n) carry delay)
  let fcvtswu_exp := makeIndexedWires "fcvtswu_exp" 8
  let (fcvtswu_exp_gates, _fcvtswu_exp_cout) :=
    mkKoggeStoneAdd const127 fcvtswu_lpos8 zero fcvtswu_exp "fcvtswu_exp"

  -- Rounding (RNE) for FCVT.S.WU
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

  -- Pack: {0 (sign), rounded[30:0]}. If zero, all zeros.
  let fcvtswu_res := makeIndexedWires "fcvtswu_res" 32
  let fcvtswu_pack_gates := (List.range 32).map fun i =>
    if i < 31 then
      Gate.mkMUX (fcvtswu_rounded[i]!) zero fcvtsw_is_zero (fcvtswu_res[i]!)
    else
      -- bit 31 = sign = always 0 for unsigned
      Gate.mkBUF zero (fcvtswu_res[i]!)

  -- ============================================================
  -- FCLASS.S (op=18 = 10010): op4 & !op3 & !op2 & op1 & !op0
  -- ============================================================
  let fclass_t0 := Wire.mk "fclass_t0"
  let fclass_t1 := Wire.mk "fclass_t1"
  let fclass_t2 := Wire.mk "fclass_t2"
  let is_fclass := Wire.mk "is_fclass"
  let dec_fclass := [
    Gate.mkAND (op[4]!) (nop[3]!) fclass_t0,
    Gate.mkAND (nop[2]!) (op[1]!) fclass_t1,
    Gate.mkAND fclass_t0 fclass_t1 fclass_t2,
    Gate.mkAND fclass_t2 (nop[0]!) is_fclass
  ]

  -- Helper signals for classification
  -- exp_all_ones = AND(src1[30:23])
  let fclass_exp_bits := (List.range 8).map fun i => src1[23 + i]!
  let (fclass_exp_ones, fclass_exp_ones_gates) := mkAndTree "fclass_eao" fclass_exp_bits

  -- exp_all_zeros = NOT(OR(src1[30:23]))
  let (fclass_exp_or, fclass_exp_or_gates) := mkOrTree "fclass_eaz_or" fclass_exp_bits
  let fclass_exp_zeros := Wire.mk "fclass_exp_zeros"
  let g_fclass_eaz := Gate.mkNOT fclass_exp_or fclass_exp_zeros

  -- mant_nonzero = OR(src1[22:0])
  let fclass_mant_bits := (List.range 23).map fun i => src1[i]!
  let (fclass_mant_nz, fclass_mant_nz_gates) := mkOrTree "fclass_mnz" fclass_mant_bits

  -- mant_zero = NOT mant_nonzero
  let fclass_mant_zero := Wire.mk "fclass_mant_zero"
  let g_fclass_mz := Gate.mkNOT fclass_mant_nz fclass_mant_zero

  -- sign = src1[31], not_sign = NOT src1[31]
  let fclass_not_sign := Wire.mk "fclass_not_sign"
  let g_fclass_ns := Gate.mkNOT (src1[31]!) fclass_not_sign

  -- not_exp_all_ones
  let fclass_not_eao := Wire.mk "fclass_not_eao"
  let g_fclass_neao := Gate.mkNOT fclass_exp_ones fclass_not_eao

  -- not_exp_all_zeros
  let fclass_not_eaz := Wire.mk "fclass_not_eaz"
  let g_fclass_neaz := Gate.mkNOT fclass_exp_zeros fclass_not_eaz

  -- Compute each classification bit
  -- bit 0: neg inf = sign & exp_all_ones & mant_zero
  let fclass_b0_t := Wire.mk "fclass_b0_t"
  let fclass_b0 := Wire.mk "fclass_b0"
  let fclass_b0_gates := [
    Gate.mkAND (src1[31]!) fclass_exp_ones fclass_b0_t,
    Gate.mkAND fclass_b0_t fclass_mant_zero fclass_b0
  ]

  -- bit 1: neg normal = sign & !exp_all_ones & !exp_all_zeros
  let fclass_b1_t := Wire.mk "fclass_b1_t"
  let fclass_b1 := Wire.mk "fclass_b1"
  let fclass_b1_gates := [
    Gate.mkAND (src1[31]!) fclass_not_eao fclass_b1_t,
    Gate.mkAND fclass_b1_t fclass_not_eaz fclass_b1
  ]

  -- bit 2: neg subnormal = sign & exp_all_zeros & mant_nonzero
  let fclass_b2_t := Wire.mk "fclass_b2_t"
  let fclass_b2 := Wire.mk "fclass_b2"
  let fclass_b2_gates := [
    Gate.mkAND (src1[31]!) fclass_exp_zeros fclass_b2_t,
    Gate.mkAND fclass_b2_t fclass_mant_nz fclass_b2
  ]

  -- bit 3: neg zero = sign & exp_all_zeros & mant_zero
  let fclass_b3_t := Wire.mk "fclass_b3_t"
  let fclass_b3 := Wire.mk "fclass_b3"
  let fclass_b3_gates := [
    Gate.mkAND (src1[31]!) fclass_exp_zeros fclass_b3_t,
    Gate.mkAND fclass_b3_t fclass_mant_zero fclass_b3
  ]

  -- bit 4: pos zero = !sign & exp_all_zeros & mant_zero
  let fclass_b4_t := Wire.mk "fclass_b4_t"
  let fclass_b4 := Wire.mk "fclass_b4"
  let fclass_b4_gates := [
    Gate.mkAND fclass_not_sign fclass_exp_zeros fclass_b4_t,
    Gate.mkAND fclass_b4_t fclass_mant_zero fclass_b4
  ]

  -- bit 5: pos subnormal = !sign & exp_all_zeros & mant_nonzero
  let fclass_b5_t := Wire.mk "fclass_b5_t"
  let fclass_b5 := Wire.mk "fclass_b5"
  let fclass_b5_gates := [
    Gate.mkAND fclass_not_sign fclass_exp_zeros fclass_b5_t,
    Gate.mkAND fclass_b5_t fclass_mant_nz fclass_b5
  ]

  -- bit 6: pos normal = !sign & !exp_all_ones & !exp_all_zeros
  let fclass_b6_t := Wire.mk "fclass_b6_t"
  let fclass_b6 := Wire.mk "fclass_b6"
  let fclass_b6_gates := [
    Gate.mkAND fclass_not_sign fclass_not_eao fclass_b6_t,
    Gate.mkAND fclass_b6_t fclass_not_eaz fclass_b6
  ]

  -- bit 7: pos inf = !sign & exp_all_ones & mant_zero
  let fclass_b7_t := Wire.mk "fclass_b7_t"
  let fclass_b7 := Wire.mk "fclass_b7"
  let fclass_b7_gates := [
    Gate.mkAND fclass_not_sign fclass_exp_ones fclass_b7_t,
    Gate.mkAND fclass_b7_t fclass_mant_zero fclass_b7
  ]

  -- bit 8: signaling NaN = exp_all_ones & mant_nonzero & !mant[22]
  let fclass_not_m22 := Wire.mk "fclass_not_m22"
  let g_fclass_nm22 := Gate.mkNOT (src1[22]!) fclass_not_m22
  let fclass_b8_t := Wire.mk "fclass_b8_t"
  let fclass_b8 := Wire.mk "fclass_b8"
  let fclass_b8_gates := [
    Gate.mkAND fclass_exp_ones fclass_mant_nz fclass_b8_t,
    Gate.mkAND fclass_b8_t fclass_not_m22 fclass_b8
  ]

  -- bit 9: quiet NaN = exp_all_ones & mant_nonzero & mant[22]
  let fclass_b9_t := Wire.mk "fclass_b9_t"
  let fclass_b9 := Wire.mk "fclass_b9"
  let fclass_b9_gates := [
    Gate.mkAND fclass_exp_ones fclass_mant_nz fclass_b9_t,
    Gate.mkAND fclass_b9_t (src1[22]!) fclass_b9
  ]

  -- Collect fclass result bits: bits [9:0] = classification, bits [31:10] = 0
  let fclass_bits : List Wire := [fclass_b0, fclass_b1, fclass_b2, fclass_b3,
    fclass_b4, fclass_b5, fclass_b6, fclass_b7, fclass_b8, fclass_b9] ++
    (List.range 22).map (fun _ => zero)

  -- ============================================================
  -- Output MUX chain
  -- ============================================================

  -- Base: FSGNJ/FMV result (existing logic)
  let is_active_base := Wire.mk "is_active_base"
  let g_active_base := Gate.mkOR is_sgnj_any is_fmv is_active_base

  -- Intermediate result for bits [30:0]: base passes src1[30:0]
  let base_low := makeIndexedWires "base_low" 31
  let base_low_gates := (List.range 31).map fun i =>
    Gate.mkMUX zero (src1[i]!) is_active_base (base_low[i]!)

  -- Bit 31 for base
  let r31_fmv := Wire.mk "r31_fmv"
  let base_bit31 := Wire.mk "base_bit31"
  let base_bit31_gates := [
    Gate.mkMUX zero (src1[31]!) is_fmv r31_fmv,
    Gate.mkMUX r31_fmv sgnj_sign is_sgnj_any base_bit31
  ]

  -- Now layer comparison results (bit 0 only, rest 0)
  -- After base, layer FCVT.W.S (32-bit result)
  let after_fcvt := makeIndexedWires "after_fcvt" 32
  let after_fcvt_gates := (List.range 32).map fun i =>
    if i < 31 then
      Gate.mkMUX (base_low[i]!) (fcvt_res[i]!) is_fcvt (after_fcvt[i]!)
    else
      Gate.mkMUX base_bit31 (fcvt_res[31]!) is_fcvt (after_fcvt[31]!)

  -- Layer FCVT.WU.S
  let after_fcvtwu := makeIndexedWires "after_fcvtwu" 32
  let after_fcvtwu_gates := (List.range 32).map fun i =>
    Gate.mkMUX (after_fcvt[i]!) (fcvtwu_res[i]!) is_fcvt_wu (after_fcvtwu[i]!)

  -- Layer FEQ
  let after_feq := makeIndexedWires "after_feq" 32
  let after_feq_gates := (List.range 32).map fun i =>
    if i == 0 then
      Gate.mkMUX (after_fcvtwu[0]!) feq_result is_feq (after_feq[0]!)
    else
      Gate.mkMUX (after_fcvtwu[i]!) zero is_feq (after_feq[i]!)

  -- Layer FLT
  let after_flt := makeIndexedWires "after_flt" 32
  let after_flt_gates := (List.range 32).map fun i =>
    if i == 0 then
      Gate.mkMUX (after_feq[0]!) flt_result is_flt (after_flt[0]!)
    else
      Gate.mkMUX (after_feq[i]!) zero is_flt (after_flt[i]!)

  -- Layer FLE
  let after_fle := makeIndexedWires "after_fle" 32
  let after_fle_gates := (List.range 32).map fun i =>
    if i == 0 then
      Gate.mkMUX (after_flt[0]!) fle_result is_fle (after_fle[0]!)
    else
      Gate.mkMUX (after_flt[i]!) zero is_fle (after_fle[i]!)

  -- Layer FMIN
  let after_fmin := makeIndexedWires "after_fmin" 32
  let after_fmin_gates := (List.range 32).map fun i =>
    Gate.mkMUX (after_fle[i]!) (fmin_res[i]!) is_fmin (after_fmin[i]!)

  -- Layer FMAX
  let after_fmax := makeIndexedWires "after_fmax" 32
  let after_fmax_gates := (List.range 32).map fun i =>
    Gate.mkMUX (after_fmin[i]!) (fmax_res[i]!) is_fmax (after_fmax[i]!)

  -- Layer FCVT.S.W
  let after_fcvtsw := makeIndexedWires "after_fcvtsw" 32
  let after_fcvtsw_gates := (List.range 32).map fun i =>
    Gate.mkMUX (after_fmax[i]!) (fcvtsw_res[i]!) is_fcvt_s_w (after_fcvtsw[i]!)

  -- Layer FCVT.S.WU
  let after_fcvtswu := makeIndexedWires "after_fcvtswu" 32
  let after_fcvtswu_gates := (List.range 32).map fun i =>
    Gate.mkMUX (after_fcvtsw[i]!) (fcvtswu_res[i]!) is_fcvt_s_wu (after_fcvtswu[i]!)

  -- Layer FCLASS (final layer -> writes to result)
  let after_fclass_gates := (List.range 32).map fun i =>
    Gate.mkMUX (after_fcvtswu[i]!) (fclass_bits[i]!) is_fclass (result[i]!)

  -- ============================================================
  -- EXCEPTION FLAG COMPUTATION
  -- ============================================================
  -- exc[4] = NV (Invalid Operation)
  -- exc[3] = DZ (Division by Zero) -- always 0 for misc ops
  -- exc[2] = OF (Overflow) -- always 0 for misc ops
  -- exc[1] = UF (Underflow) -- always 0 for misc ops
  -- exc[0] = NX (Inexact)

  -- NV sources:
  -- 1. FLT/FLE with any NaN input → NV
  -- 2. FEQ with signaling NaN input → NV
  -- 3. FMIN/FMAX with signaling NaN input → NV
  -- 4. FCVT.W.S/WU.S with NaN/Inf/overflow → NV
  let cmp_nv := Wire.mk "cmp_nv"  -- NV from comparisons
  let is_flt_or_fle := Wire.mk "is_flt_or_fle"
  let cmp_nan_nv := Wire.mk "cmp_nan_nv"  -- FLT/FLE with any NaN
  let feq_snan_nv := Wire.mk "feq_snan_nv"  -- FEQ with sNaN
  let minmax_snan_nv := Wire.mk "minmax_snan_nv"  -- FMIN/FMAX with sNaN
  let is_fmin_or_fmax := Wire.mk "is_fmin_or_fmax"
  let fcvt_is_fcvt_any := Wire.mk "fcvt_is_fcvt_any"  -- any FCVT FP→int
  let fcvt_ws_nv := Wire.mk "fcvt_ws_nv"

  let nv_gates := [
    Gate.mkOR is_flt is_fle is_flt_or_fle,
    Gate.mkAND is_flt_or_fle either_nan cmp_nan_nv,
    Gate.mkAND is_feq either_snan feq_snan_nv,
    Gate.mkOR is_fmin is_fmax is_fmin_or_fmax,
    Gate.mkAND is_fmin_or_fmax either_snan minmax_snan_nv,
    Gate.mkOR is_fcvt is_fcvt_wu fcvt_is_fcvt_any,
    -- FCVT.W.S (signed) NV: NaN/Inf/overflow (shiftBorrow) — only for signed
    Gate.mkAND is_fcvt fcvt_nv fcvt_ws_nv,
    -- FCVT.WU.S NV sources:
    -- 1. NaN or Inf
    Gate.mkOR is_nan_src1 is_inf_src1 (Wire.mk "fcvtwu_nan_inf"),
    Gate.mkAND is_fcvt_wu (Wire.mk "fcvtwu_nan_inf") (Wire.mk "fcvtwu_nan_inf_nv"),
    -- 2. Negative input with magnitude >= 1.0 (integer part nonzero)
    Gate.mkAND (src1[31]!) fcvt_mag_nz (Wire.mk "fcvtwu_neg_nz"),
    Gate.mkAND is_fcvt_wu (Wire.mk "fcvtwu_neg_nz") (Wire.mk "fcvtwu_neg_nv"),
    -- 3. Positive overflow (exp >= 159, value > uint32_max)
    Gate.mkAND is_fcvt_wu fcvtwu_overflow (Wire.mk "fcvtwu_pos_ov_t"),
    Gate.mkAND (Wire.mk "fcvtwu_pos_ov_t") shiftBorrow (Wire.mk "fcvtwu_pos_ov_nv"),
    -- 4. Negative with shiftBorrow (e.g., -3e9: magnitude > 2^23, negative)
    Gate.mkAND is_fcvt_wu shiftBorrow (Wire.mk "fcvtwu_sb_t"),
    Gate.mkAND (Wire.mk "fcvtwu_sb_t") (src1[31]!) (Wire.mk "fcvtwu_neg_sb_nv"),
    -- Combine unsigned NV
    Gate.mkOR (Wire.mk "fcvtwu_nan_inf_nv") (Wire.mk "fcvtwu_neg_nv") (Wire.mk "fcvtwu_nv_t0"),
    Gate.mkOR (Wire.mk "fcvtwu_pos_ov_nv") (Wire.mk "fcvtwu_neg_sb_nv") (Wire.mk "fcvtwu_nv_t1"),
    Gate.mkOR (Wire.mk "fcvtwu_nv_t0") (Wire.mk "fcvtwu_nv_t1") (Wire.mk "fcvtwu_all_nv"),
    -- Combine all NV sources
    Gate.mkOR cmp_nan_nv feq_snan_nv (Wire.mk "nv_t0"),
    Gate.mkOR minmax_snan_nv fcvt_ws_nv (Wire.mk "nv_t1"),
    Gate.mkOR (Wire.mk "nv_t0") (Wire.mk "nv_t1") (Wire.mk "nv_t2"),
    Gate.mkOR (Wire.mk "nv_t2") (Wire.mk "fcvtwu_all_nv") cmp_nv
  ]

  -- NX sources:
  -- 1. FCVT.W.S/WU.S with inexact result (lost bits)
  -- 2. FCVT.S.W/S.WU with inexact result (integer > 24 bits significand)
  -- NX for FCVT.S.W/S.WU: computed in the rounding sections above (fcvtsw_nx, fcvtswu_nx)
  -- NX = round_bit OR sticky, gated by NOT is_zero

  -- Combine NX: FCVT.W.S NX or FCVT.S.W NX or FCVT.S.WU NX
  let fcvt_ws_nx := Wire.mk "fcvt_ws_nx"
  let total_nx := Wire.mk "total_nx"
  let nx_gates := [
    Gate.mkAND fcvt_is_fcvt_any fcvt_nx fcvt_ws_nx,
    Gate.mkOR fcvt_ws_nx (Wire.mk "fcvtsw_nx_contrib") (Wire.mk "nx_t0"),
    Gate.mkOR (Wire.mk "nx_t0") (Wire.mk "fcvtswu_nx_contrib") total_nx,
    Gate.mkAND is_fcvt_s_w fcvtsw_nx (Wire.mk "fcvtsw_nx_contrib"),
    Gate.mkAND is_fcvt_s_wu fcvtswu_nx (Wire.mk "fcvtswu_nx_contrib")
  ]

  -- Output exception flags
  -- exc[4] = NV, exc[3] = DZ (0), exc[2] = OF (0), exc[1] = UF (0), exc[0] = NX
  let exc_gates := [
    Gate.mkBUF total_nx (exc[0]!),    -- NX (bit 0)
    Gate.mkBUF zero (exc[1]!),         -- UF (bit 1)
    Gate.mkBUF zero (exc[2]!),         -- OF (bit 2)
    Gate.mkBUF zero (exc[3]!),         -- DZ (bit 3)
    Gate.mkBUF cmp_nv (exc[4]!)        -- NV (bit 4)
  ]

  { name := "FPMisc"
    inputs := src1 ++ src2 ++ op ++ rm ++ [zero, one]
    outputs := result ++ exc
    gates :=
      -- NaN detection
      nan1_exp_ones_gates ++ nan1_mant_nz_gates ++ nan1_detect_gates ++
      nan2_exp_ones_gates ++ nan2_mant_nz_gates ++ nan2_detect_gates ++
      nan_combined_gates ++
      -- Sign injection
      [g_fsgnj, g_fsgnjn, g_fsgnjx] ++
      inv_gates ++
      dec_fsgnj ++ dec_fsgnjn ++ dec_fsgnjx ++ dec_fmv ++
      dec_sgnj_any ++ sgnj_sign_gates ++
      -- Op decoders
      dec_feq ++ dec_flt ++ dec_fle ++ dec_fcvt ++ dec_fcvt_wu ++
      dec_fmin ++ dec_fmax ++ dec_fcvt_s_w ++ dec_fcvt_s_wu ++ dec_fclass ++
      -- FEQ logic (with NaN masking)
      feq_xor_gates ++ feq_or_gates ++ [g_feq_inv] ++ feq_nan_gates ++
      -- FLT logic (with NaN masking)
      flt_sub_gates ++
      [g_flt_sd, g_flt_nb, g_flt_neq, g_flt_neg_lt, g_flt_same2, g_flt_final, flt_nan_gate] ++
      -- FLE logic
      [g_fle] ++
      -- FCVT.W.S logic (with NaN/overflow handling + NX detection)
      fcvt_sub_gates ++ fcvt_big_gates ++ fcvt_shift_gates ++
      fcvt_mag_gates ++ fcvt_mag_nz_gates ++ fcvt_inv_gates ++ fcvt_neg_gates ++ fcvt_sel_gates ++
      [nan1_mant_z_gate, inf1_gate] ++ fcvt_special_gates ++ fcvt_special_det ++
      fcvt_special_bit_gates ++ fcvt_result_gates ++
      fcvt_sticky_gates ++ fcvt_sticky_buf ++ fcvt_src1_nz_gates ++ g_underflow_nx_gates ++
      fcvt_not_special_gate ++ fcvt_nx_gates ++ fcvt_nv_gate ++
      -- FCVT.WU.S logic
      fcvtwu_lsa_inv_gates ++ fcvtwu_lsa_add_gates ++ fcvtwu_lsh_gates ++
      fcvtwu_ov_gates ++ fcvtwu_lsh_ov_gates ++ fcvtwu_umag_gates ++
      fcvtwu_neg_clamp_gate ++ fcvtwu_res_gates ++
      -- FMIN/FMAX logic (with NaN handling)
      fmin_res_gates ++ fmax_res_gates ++
      -- FCVT.S.W logic
      fcvtsw_or_gates ++ [g_fcvtsw_iz] ++
      fcvtsw_inv_gates ++ fcvtsw_neg_gates ++ fcvtsw_mag_gates ++
      fcvtsw_penc_gates ++ fcvtsw_lpos_gates ++ fcvtsw_shamt_gates ++
      fcvtsw_bsl_gates ++ fcvtsw_exp_gates ++
      fcvtsw_sticky_gates ++ fcvtsw_round_gates ++ [fcvtsw_nx_gate] ++
      fcvtsw_unrounded_gates ++ fcvtsw_rnd_add_gates ++
      [g_fcvtsw_nz] ++ fcvtsw_pack_gates ++
      -- FCVT.S.WU logic
      fcvtswu_penc_gates ++ fcvtswu_lpos_gates ++ fcvtswu_shamt_gates ++
      fcvtswu_bsl_gates ++ fcvtswu_exp_gates ++
      fcvtswu_sticky_gates ++ fcvtswu_round_gates ++ [fcvtswu_nx_gate] ++
      fcvtswu_unrounded_gates ++ fcvtswu_rnd_add_gates ++
      fcvtswu_pack_gates ++
      -- FCLASS logic
      fclass_exp_ones_gates ++ fclass_exp_or_gates ++ [g_fclass_eaz] ++
      fclass_mant_nz_gates ++ [g_fclass_mz, g_fclass_ns, g_fclass_neao, g_fclass_neaz] ++
      fclass_b0_gates ++ fclass_b1_gates ++ fclass_b2_gates ++ fclass_b3_gates ++
      fclass_b4_gates ++ fclass_b5_gates ++ fclass_b6_gates ++ fclass_b7_gates ++
      [g_fclass_nm22] ++ fclass_b8_gates ++ fclass_b9_gates ++
      -- Output MUX chain
      [g_active_base] ++ base_low_gates ++ base_bit31_gates ++
      after_fcvt_gates ++ after_fcvtwu_gates ++
      after_feq_gates ++ after_flt_gates ++ after_fle_gates ++
      after_fmin_gates ++ after_fmax_gates ++ after_fcvtsw_gates ++
      after_fcvtswu_gates ++ after_fclass_gates ++
      -- Exception flags
      nv_gates ++ nx_gates ++ exc_gates
    instances := []
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
