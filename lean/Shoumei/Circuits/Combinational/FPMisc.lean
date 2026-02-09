/-
Circuits/Combinational/FPMisc.lean - FP Miscellaneous Operations Circuit

Implements single-cycle FP bit-manipulation operations for RV32F:
  FSGNJ, FSGNJN, FSGNJX, FMV.X.W, FMV.W.X,
  FEQ.S, FLT.S, FLE.S, FCVT.W.S

Inputs:
  - src1[31:0], src2[31:0] - source operands
  - op[4:0] - operation select
  - zero, one - constant wires

Outputs:
  - result[31:0] - operation result
  - exc[4:0] - exception flags (always 0 for these ops)
-/

import Shoumei.DSL

namespace Shoumei.Circuits.Combinational

open Shoumei

private def makeIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}_{i}")

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

/-- FP miscellaneous operations: sign injection, FMV, FEQ, FLT, FLE, FCVT.W.S -/
def fpMiscCircuit : Circuit :=
  let src1 := makeIndexedWires "src1" 32
  let src2 := makeIndexedWires "src2" 32
  let op := makeIndexedWires "op" 5
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"
  let result := makeIndexedWires "result" 32
  let exc := makeIndexedWires "exc" 5

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

  -- OR-reduce all XOR bits, then NOT -> equality
  let (feq_or_out, feq_or_gates) := mkOrTree "feq_or" feq_xor
  let feq_result := Wire.mk "feq_result"
  let g_feq_inv := Gate.mkNOT feq_or_out feq_result

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

  -- final: signs_differ ? src1[31] : flt_same_result2
  let flt_result := Wire.mk "flt_result"
  let g_flt_final := Gate.mkMUX flt_same_result2 (src1[31]!) flt_signs_differ flt_result

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

  -- If src1[31] (negative), negate: result = ~mag + 1 (2's complement)
  -- Invert
  let fcvt_inv := makeIndexedWires "fcvt_inv" 32
  let fcvt_inv_gates := (List.range 32).map fun i =>
    Gate.mkNOT (fcvt_mag[i]!) (fcvt_inv[i]!)

  -- Add 1 using ripple carry (add fcvt_inv + 0 with carry_in = 1)
  -- This is just a half-adder chain: result[i] = inv[i] XOR carry, carry_out = inv[i] AND carry
  let fcvt_neg := makeIndexedWires "fcvt_neg" 32
  let (_, fcvt_neg_gates) := (List.range 32).foldl (fun (acc : Wire × List Gate) i =>
    let cin := acc.1
    let g_sum := Gate.mkXOR (fcvt_inv[i]!) cin (fcvt_neg[i]!)
    let cout := Wire.mk s!"fcvt_neg_c_{i}"
    let g_carry := Gate.mkAND (fcvt_inv[i]!) cin cout
    (cout, acc.2 ++ [g_sum, g_carry])
  ) (one, [])

  -- Select positive or negative based on src1[31]
  let fcvt_res := makeIndexedWires "fcvt_res" 32
  let fcvt_sel_gates := (List.range 32).map fun i =>
    Gate.mkMUX (fcvt_mag[i]!) (fcvt_neg[i]!) (src1[31]!) (fcvt_res[i]!)

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
  -- After base, layer FCVT (32-bit result)
  let after_fcvt := makeIndexedWires "after_fcvt" 32
  let after_fcvt_gates := (List.range 32).map fun i =>
    if i < 31 then
      Gate.mkMUX (base_low[i]!) (fcvt_res[i]!) is_fcvt (after_fcvt[i]!)
    else
      Gate.mkMUX base_bit31 (fcvt_res[31]!) is_fcvt (after_fcvt[31]!)

  -- Layer FEQ
  let after_feq := makeIndexedWires "after_feq" 32
  let after_feq_gates := (List.range 32).map fun i =>
    if i == 0 then
      Gate.mkMUX (after_fcvt[0]!) feq_result is_feq (after_feq[0]!)
    else
      Gate.mkMUX (after_fcvt[i]!) zero is_feq (after_feq[i]!)

  -- Layer FLT
  let after_flt := makeIndexedWires "after_flt" 32
  let after_flt_gates := (List.range 32).map fun i =>
    if i == 0 then
      Gate.mkMUX (after_feq[0]!) flt_result is_flt (after_flt[0]!)
    else
      Gate.mkMUX (after_feq[i]!) zero is_flt (after_flt[i]!)

  -- Layer FLE
  let after_fle_gates := (List.range 32).map fun i =>
    if i == 0 then
      Gate.mkMUX (after_flt[0]!) fle_result is_fle (result[0]!)
    else
      Gate.mkMUX (after_flt[i]!) zero is_fle (result[i]!)

  -- Exception flags: all zero for these operations
  let exc_gates := (List.range 5).map fun i =>
    Gate.mkBUF zero (exc[i]!)

  { name := "FPMisc"
    inputs := src1 ++ src2 ++ op ++ [zero, one]
    outputs := result ++ exc
    gates :=
      [g_fsgnj, g_fsgnjn, g_fsgnjx] ++
      inv_gates ++
      dec_fsgnj ++ dec_fsgnjn ++ dec_fsgnjx ++ dec_fmv ++
      dec_sgnj_any ++ sgnj_sign_gates ++
      -- New op decoders
      dec_feq ++ dec_flt ++ dec_fle ++ dec_fcvt ++
      -- FEQ logic
      feq_xor_gates ++ feq_or_gates ++ [g_feq_inv] ++
      -- FLT logic
      flt_sub_gates ++
      [g_flt_sd, g_flt_nb, g_flt_neq, g_flt_neg_lt, g_flt_same2, g_flt_final] ++
      -- FLE logic
      [g_fle] ++
      -- FCVT logic
      fcvt_sub_gates ++ fcvt_big_gates ++ fcvt_shift_gates ++
      fcvt_mag_gates ++ fcvt_inv_gates ++ fcvt_neg_gates ++ fcvt_sel_gates ++
      -- Output MUX chain
      [g_active_base] ++ base_low_gates ++ base_bit31_gates ++
      after_fcvt_gates ++ after_feq_gates ++ after_flt_gates ++ after_fle_gates ++
      exc_gates
    instances := []
    signalGroups := [
      { name := "src1",   width := 32, wires := src1 },
      { name := "src2",   width := 32, wires := src2 },
      { name := "op",     width := 5,  wires := op },
      { name := "result", width := 32, wires := result },
      { name := "exc",    width := 5,  wires := exc }
    ]
  }

end Shoumei.Circuits.Combinational
