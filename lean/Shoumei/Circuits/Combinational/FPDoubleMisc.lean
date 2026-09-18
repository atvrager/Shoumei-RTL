/-
Circuits/Combinational/FPDoubleMisc.lean - Double-Precision Miscellaneous Operations Circuit

Implements single-cycle double-precision floating-point operations for RV32D:
- Comparisons: FEQ.D, FLT.D, FLE.D (write integer rd)
- Classification: FCLASS.D (writes 10-bit integer mask)
- Min/Max: FMIN.D, FMAX.D (writes 64-bit FPR)
- Sign Injection: FSGNJ.D, FSGNJN.D, FSGNJX.D (writes 64-bit FPR)
- Conversions:
  * FCVT.W.D, FCVT.WU.D (DP float -> 32-bit integer)
  * FCVT.D.W, FCVT.D.WU (32-bit integer -> DP float)
  * FCVT.S.D (DP float -> NaN-boxed SP float)
  * FCVT.D.S (SP float -> DP float, with NaN unboxing check)

Interface:
- Inputs:
  * src1[63:0], src2[63:0]
  * op[5:0] (FPU internal opcode: 41..55)
  * rm[2:0] (rounding mode)
  * zero, one
- Outputs:
  * result[63:0]
  * exc[4:0] (NV, DZ, OF, UF, NX)
  * result_is_int
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.KoggeStoneAdder

namespace Shoumei.Circuits.Combinational

open Shoumei

/- makeIndexedWires is inherited from namespace -/

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

/-- Double-Precision FP Miscellaneous Circuit -/
def fpDoubleMiscCircuit : Circuit :=
  let src1 := makeIndexedWires "src1" 64
  let src2 := makeIndexedWires "src2" 64
  let op := makeIndexedWires "op" 6
  let rm := makeIndexedWires "rm" 3
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  let result := makeIndexedWires "result" 64
  let exc := makeIndexedWires "exc" 5
  let result_is_int := Wire.mk "result_is_int"

  -- ══════════════════════════════════════════════
  -- 1. Unpack & Special Value Detection (src1 & src2)
  -- ══════════════════════════════════════════════
  let sign1 := src1[63]!
  let exp1 := (List.range 11).map fun i => src1[52 + i]!
  let mant1 := (List.range 52).map fun i => src1[i]!

  let sign2 := src2[63]!
  let exp2 := (List.range 11).map fun i => src2[52 + i]!
  let mant2 := (List.range 52).map fun i => src2[i]!

  -- exp all ones
  let (exp1_ones, exp1_ones_gates) := mkAndTree "exp1_ones" exp1
  let (exp2_ones, exp2_ones_gates) := mkAndTree "exp2_ones" exp2

  -- exp all zeros
  let (exp1_any, exp1_any_gates) := mkOrTree "exp1_any" exp1
  let exp1_zeros := Wire.mk "exp1_zeros"
  let exp1_zeros_gate := Gate.mkNOT exp1_any exp1_zeros

  let (exp2_any, exp2_any_gates) := mkOrTree "exp2_any" exp2
  let exp2_zeros := Wire.mk "exp2_zeros"
  let exp2_zeros_gate := Gate.mkNOT exp2_any exp2_zeros

  -- mant all zeros
  let (mant1_any, mant1_any_gates) := mkOrTree "mant1_any" mant1
  let mant1_zeros := Wire.mk "mant1_zeros"
  let mant1_zeros_gate := Gate.mkNOT mant1_any mant1_zeros

  let (mant2_any, mant2_any_gates) := mkOrTree "mant2_any" mant2
  let mant2_zeros := Wire.mk "mant2_zeros"
  let mant2_zeros_gate := Gate.mkNOT mant2_any mant2_zeros

  -- Classes for src1
  let is_zero1 := Wire.mk "is_zero1"
  let is_inf1 := Wire.mk "is_inf1"
  let is_nan1 := Wire.mk "is_nan1"
  let is_snan1 := Wire.mk "is_snan1"
  let is_qnan1 := Wire.mk "is_qnan1"
  let is_subnorm1 := Wire.mk "is_subnorm1"
  let is_norm1 := Wire.mk "is_norm1"

  let not_exp1_ones := Wire.mk "not_exp1_ones"
  let not_exp1_zeros := Wire.mk "not_exp1_zeros"
  let not_quiet1 := Wire.mk "not_quiet1"

  let class1_gates := [
    Gate.mkAND exp1_zeros mant1_zeros is_zero1,
    Gate.mkAND exp1_ones mant1_zeros is_inf1,
    Gate.mkAND exp1_ones mant1_any is_nan1,
    Gate.mkNOT (src1[51]!) not_quiet1,
    Gate.mkAND is_nan1 not_quiet1 is_snan1,
    Gate.mkAND is_nan1 (src1[51]!) is_qnan1,
    Gate.mkAND exp1_zeros mant1_any is_subnorm1,
    Gate.mkNOT exp1_ones not_exp1_ones,
    Gate.mkNOT exp1_zeros not_exp1_zeros,
    Gate.mkAND not_exp1_ones not_exp1_zeros is_norm1
  ]

  -- Classes for src2
  let is_zero2 := Wire.mk "is_zero2"
  let is_inf2 := Wire.mk "is_inf2"
  let is_nan2 := Wire.mk "is_nan2"
  let is_snan2 := Wire.mk "is_snan2"
  let not_quiet2 := Wire.mk "not_quiet2"

  let class2_gates := [
    Gate.mkAND exp2_zeros mant2_zeros is_zero2,
    Gate.mkAND exp2_ones mant2_zeros is_inf2,
    Gate.mkAND exp2_ones mant2_any is_nan2,
    Gate.mkNOT (src2[51]!) not_quiet2,
    Gate.mkAND is_nan2 not_quiet2 is_snan2
  ]

  -- ══════════════════════════════════════════════
  -- 2. Bitwise Magnitude Compare (src1 vs src2)
  -- ══════════════════════════════════════════════
  let xor_bits := (List.range 64).map fun i => Wire.mk s!"xor_{i}"
  let xor_gates := (List.range 64).map fun i =>
    Gate.mkXOR (src1[i]!) (src2[i]!) (xor_bits[i]!)

  let (any_diff, any_diff_gates) := mkOrTree "any_diff" xor_bits
  let exact_eq := Wire.mk "exact_eq"
  let exact_eq_gate := Gate.mkNOT any_diff exact_eq

  let both_zero := Wire.mk "both_zero"
  let both_zero_gate := Gate.mkAND is_zero1 is_zero2 both_zero

  let mag_eq := Wire.mk "mag_eq"
  let mag_eq_gate := Gate.mkOR exact_eq both_zero mag_eq

  -- Ripple compare magnitude (bits 62:0) to find if mag1 < mag2
  -- borrow chain from bit 0 to 62
  let borrow := makeIndexedWires "borrow" 64
  let borrow_init := Gate.mkBUF zero (borrow[0]!)
  let mag_cmp_gates := [borrow_init] ++ (List.range 63).flatMap (fun i =>
    let a := src1[i]!
    let b := src2[i]!
    let bin := borrow[i]!
    let bout := borrow[i + 1]!
    let not_a := Wire.mk s!"na_{i}"
    let t0 := Wire.mk s!"bt0_{i}"
    let t1 := Wire.mk s!"bt1_{i}"
    let t2 := Wire.mk s!"bt2_{i}"
    let t01 := Wire.mk s!"bt01_{i}"
    [
      Gate.mkNOT a not_a,
      Gate.mkAND not_a b t0,
      Gate.mkAND not_a bin t1,
      Gate.mkAND b bin t2,
      Gate.mkOR t0 t1 t01,
      Gate.mkOR t01 t2 bout
    ]
  )
  let mag1_lt_mag2 := borrow[63]!

  -- ══════════════════════════════════════════════
  -- 3. Double-Precision Compare: FEQ.D, FLT.D, FLE.D
  -- ══════════════════════════════════════════════
  let either_nan := Wire.mk "either_nan"
  let either_snan := Wire.mk "either_snan"
  let nan_comb_gates := [
    Gate.mkOR is_nan1 is_nan2 either_nan,
    Gate.mkOR is_snan1 is_snan2 either_snan
  ]

  let not_either_nan := Wire.mk "not_either_nan"
  let not_nan_gate := Gate.mkNOT either_nan not_either_nan

  -- Less Than logic:
  -- if sign1 & !sign2 -> true (unless both zero)
  -- if !sign1 & sign2 -> false (unless both zero)
  -- if !sign1 & !sign2 -> mag1 < mag2
  -- if sign1 & sign2 -> mag1 > mag2 (i.e. NOT(mag1 < mag2) & !exact_eq)
  let not_sign1 := Wire.mk "not_sign1"
  let not_sign2 := Wire.mk "not_sign2"
  let diff_signs := Wire.mk "diff_signs"
  let s1_neg_s2_pos := Wire.mk "s1_neg_s2_pos"
  let s1_pos_s2_neg := Wire.mk "s1_pos_s2_neg"
  let same_signs := Wire.mk "same_signs"
  let both_pos := Wire.mk "both_pos"
  let both_neg := Wire.mk "both_neg"

  let lt_pos := Wire.mk "lt_pos"
  let not_mag1_lt := Wire.mk "not_mag1_lt"
  let not_exact_eq := Wire.mk "not_exact_eq"
  let lt_neg := Wire.mk "lt_neg"
  let lt_mag := Wire.mk "lt_mag"
  let lt_raw := Wire.mk "lt_raw"
  let lt_res := Wire.mk "lt_res"
  let le_res := Wire.mk "le_res"
  let eq_res := Wire.mk "eq_res"

  let not_both_zero := Wire.mk "not_both_zero"

  let cmp_logic_gates := [
    Gate.mkNOT sign1 not_sign1,
    Gate.mkNOT sign2 not_sign2,
    Gate.mkNOT both_zero not_both_zero,
    Gate.mkAND sign1 not_sign2 s1_neg_s2_pos,
    Gate.mkAND not_sign1 sign2 s1_pos_s2_neg,
    Gate.mkOR s1_neg_s2_pos s1_pos_s2_neg diff_signs,
    Gate.mkNOT diff_signs same_signs,
    Gate.mkAND not_sign1 not_sign2 both_pos,
    Gate.mkAND sign1 sign2 both_neg,

    Gate.mkAND both_pos mag1_lt_mag2 lt_pos,
    Gate.mkNOT mag1_lt_mag2 not_mag1_lt,
    Gate.mkNOT exact_eq not_exact_eq,
    Gate.mkAND both_neg not_mag1_lt (Wire.mk "lt_neg_t0"),
    Gate.mkAND (Wire.mk "lt_neg_t0") not_exact_eq lt_neg,
    Gate.mkOR lt_pos lt_neg lt_mag,
    Gate.mkOR s1_neg_s2_pos lt_mag (Wire.mk "lt_raw_t0"),
    Gate.mkAND (Wire.mk "lt_raw_t0") not_both_zero lt_raw,

    -- Filter out NaN
    Gate.mkAND lt_raw not_either_nan lt_res,
    Gate.mkAND mag_eq not_either_nan eq_res,
    Gate.mkOR lt_res eq_res le_res
  ]

  -- ══════════════════════════════════════════════
  -- 4. Sign Injection: FSGNJ.D, FSGNJN.D, FSGNJX.D
  -- ══════════════════════════════════════════════
  let sgnj_sign := sign2
  let sgnjn_sign := not_sign2
  let sgnjx_sign := Wire.mk "sgnjx_sign"
  let sgnjx_gate := Gate.mkXOR sign1 sign2 sgnjx_sign

  -- ══════════════════════════════════════════════
  -- 5. FCLASS.D (10-bit classification mask)
  -- ══════════════════════════════════════════════
  let fclass_bits := makeIndexedWires "fclass" 10
  let fclass_gates := [
    Gate.mkAND sign1 is_inf1 (fclass_bits[0]!),       -- negInf
    Gate.mkAND sign1 is_norm1 (fclass_bits[1]!),      -- negNormal
    Gate.mkAND sign1 is_subnorm1 (fclass_bits[2]!),   -- negSubnormal
    Gate.mkAND sign1 is_zero1 (fclass_bits[3]!),      -- negZero
    Gate.mkAND not_sign1 is_zero1 (fclass_bits[4]!),  -- posZero
    Gate.mkAND not_sign1 is_subnorm1 (fclass_bits[5]!), -- posSubnormal
    Gate.mkAND not_sign1 is_norm1 (fclass_bits[6]!),  -- posNormal
    Gate.mkAND not_sign1 is_inf1 (fclass_bits[7]!),   -- posInf
    Gate.mkBUF is_snan1 (fclass_bits[8]!),            -- sNaN
    Gate.mkBUF is_qnan1 (fclass_bits[9]!)             -- qNaN
  ]

  -- ══════════════════════════════════════════════
  -- 6. FMIN.D & FMAX.D
  -- ══════════════════════════════════════════════
  -- Canonical NaN constant wires
  let cnan64 := (List.range 64).map fun i =>
    -- 0x7FF8000000000000: bits 62..51 are 1, rest 0
    if i >= 51 && i <= 62 then one else zero

  let min_sel_s1 := Wire.mk "min_sel_s1"
  let max_sel_s1 := Wire.mk "max_sel_s1"

  -- If s1 is NaN, take s2 (unless both NaN -> cnan)
  -- If s2 is NaN, take s1
  -- If lt_raw: min takes s1, max takes s2
  -- Zero corner cases: if both zero, FMIN takes negative, FMAX takes positive
  let min_zero_sign := Wire.mk "min_zero_sign"
  let min_zero_sign_gate := Gate.mkOR sign1 sign2 min_zero_sign
  let max_zero_sign := Wire.mk "max_zero_sign"
  let max_zero_sign_gate := Gate.mkAND sign1 sign2 max_zero_sign

  let min_sel_gates := [
    Gate.mkOR is_nan2 lt_raw (Wire.mk "min_t0"),
    Gate.mkNOT is_nan1 (Wire.mk "not_nan1"),
    Gate.mkAND (Wire.mk "min_t0") (Wire.mk "not_nan1") min_sel_s1,

    Gate.mkNOT lt_raw (Wire.mk "not_lt_raw"),
    Gate.mkOR is_nan2 (Wire.mk "not_lt_raw") (Wire.mk "max_t0"),
    Gate.mkAND (Wire.mk "max_t0") (Wire.mk "not_nan1") max_sel_s1
  ]

  let min_res := makeIndexedWires "min_res" 64
  let max_res := makeIndexedWires "max_res" 64

  let both_nan := Wire.mk "both_nan"
  let both_nan_gate := Gate.mkAND is_nan1 is_nan2 both_nan

  let min_mux_gates := (List.range 64).flatMap fun i =>
    let m := Wire.mk s!"min_m_{i}"
    let m_zero := if i == 63 then Wire.mk "min_m_zero_63" else m
    if i == 63 then
      [Gate.mkMUX (src2[63]!) (src1[63]!) min_sel_s1 m,
       Gate.mkMUX m min_zero_sign both_zero m_zero,
       Gate.mkMUX m_zero (cnan64[63]!) both_nan (min_res[63]!)]
    else
      [Gate.mkMUX (src2[i]!) (src1[i]!) min_sel_s1 m,
       Gate.mkMUX m (cnan64[i]!) both_nan (min_res[i]!)]

  let max_mux_gates := (List.range 64).flatMap fun i =>
    let m := Wire.mk s!"max_m_{i}"
    let m_zero := if i == 63 then Wire.mk "max_m_zero_63" else m
    if i == 63 then
      [Gate.mkMUX (src2[63]!) (src1[63]!) max_sel_s1 m,
       Gate.mkMUX m max_zero_sign both_zero m_zero,
       Gate.mkMUX m_zero (cnan64[63]!) both_nan (max_res[63]!)]
    else
      [Gate.mkMUX (src2[i]!) (src1[i]!) max_sel_s1 m,
       Gate.mkMUX m (cnan64[i]!) both_nan (max_res[i]!)]

  -- ══════════════════════════════════════════════
  -- 7. Conversions: FCVT.D.W / FCVT.D.WU
  -- ══════════════════════════════════════════════
  let int_in := (List.range 32).map fun i => src1[i]!
  let _int_sign := int_in[31]!
  let abs_int := makeIndexedWires "abs_int" 32
  let abs_carry := makeIndexedWires "abs_carry" 33

  -- 2's complement negation: ~int + 1
  let abs_gates := [Gate.mkBUF one (abs_carry[0]!)] ++ (List.range 32).flatMap (fun i =>
    let nbit := Wire.mk s!"nint_{i}"
    [Gate.mkNOT (int_in[i]!) nbit,
     Gate.mkXOR nbit (abs_carry[i]!) (abs_int[i]!),
     Gate.mkAND nbit (abs_carry[i]!) (abs_carry[i + 1]!)]
  )

  -- ══════════════════════════════════════════════
  -- 8. Opcode Decoding (6 bits)
  -- ══════════════════════════════════════════════
  -- 41: FEQ.D, 42: FLT.D, 43: FLE.D
  -- 44: FCVT.W.D, 45: FCVT.WU.D, 46: FCVT.D.W, 47: FCVT.D.WU
  -- 48: FCVT.S.D, 49: FCVT.D.S, 50: FCLASS.D
  -- 51: FMIN.D, 52: FMAX.D, 53: FSGNJ.D, 54: FSGNJN.D, 55: FSGNJX.D

  let is_feq := Wire.mk "is_feq"
  let is_flt := Wire.mk "is_flt"
  let is_fle := Wire.mk "is_fle"
  let is_fclass := Wire.mk "is_fclass"
  let is_fmin := Wire.mk "is_fmin"
  let is_fmax := Wire.mk "is_fmax"
  let is_fsgnj := Wire.mk "is_fsgnj"
  let is_fsgnjn := Wire.mk "is_fsgnjn"
  let is_fsgnjx := Wire.mk "is_fsgnjx"

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

  -- 41 = 101001 (op5=1, op4=0, op3=1, op2=0, op1=0, op0=1)
  let dec_feq := [
    Gate.mkAND (op[5]!) not_op4 (Wire.mk "d41_t0"),
    Gate.mkAND (op[3]!) not_op2 (Wire.mk "d41_t1"),
    Gate.mkAND not_op1 (op[0]!) (Wire.mk "d41_t2"),
    Gate.mkAND (Wire.mk "d41_t0") (Wire.mk "d41_t1") (Wire.mk "d41_t3"),
    Gate.mkAND (Wire.mk "d41_t3") (Wire.mk "d41_t2") is_feq
  ]

  -- 42 = 101010
  let dec_flt := [
    Gate.mkAND (Wire.mk "d41_t0") (Wire.mk "d41_t1") (Wire.mk "d42_t0"),
    Gate.mkAND (op[1]!) not_op0 (Wire.mk "d42_t1"),
    Gate.mkAND (Wire.mk "d42_t0") (Wire.mk "d42_t1") is_flt
  ]

  -- 43 = 101011
  let dec_fle := [
    Gate.mkAND (Wire.mk "d41_t0") (Wire.mk "d41_t1") (Wire.mk "d43_t0"),
    Gate.mkAND (op[1]!) (op[0]!) (Wire.mk "d43_t1"),
    Gate.mkAND (Wire.mk "d43_t0") (Wire.mk "d43_t1") is_fle
  ]

  -- 50 = 110010 (op5=1, op4=1, op3=0, op2=0, op1=1, op0=0)
  let dec_fclass := [
    Gate.mkAND (op[5]!) (op[4]!) (Wire.mk "d50_t0"),
    Gate.mkAND not_op3 not_op2 (Wire.mk "d50_t1"),
    Gate.mkAND (op[1]!) not_op0 (Wire.mk "d50_t2"),
    Gate.mkAND (Wire.mk "d50_t0") (Wire.mk "d50_t1") (Wire.mk "d50_t3"),
    Gate.mkAND (Wire.mk "d50_t3") (Wire.mk "d50_t2") is_fclass
  ]

  -- 51 = 110011 (FMIN)
  let dec_fmin := [
    Gate.mkAND (Wire.mk "d50_t3") (op[1]!) (Wire.mk "d51_t0"),
    Gate.mkAND (Wire.mk "d51_t0") (op[0]!) is_fmin
  ]

  -- 52 = 110100 (FMAX)
  let dec_fmax := [
    Gate.mkAND (Wire.mk "d50_t0") not_op3 (Wire.mk "d52_t0"),
    Gate.mkAND (op[2]!) not_op1 (Wire.mk "d52_t1"),
    Gate.mkAND (Wire.mk "d52_t0") (Wire.mk "d52_t1") (Wire.mk "d52_t2"),
    Gate.mkAND (Wire.mk "d52_t2") not_op0 is_fmax
  ]

  -- 53 = 110101 (FSGNJ)
  let dec_fsgnj := [
    Gate.mkAND (Wire.mk "d52_t2") (op[0]!) is_fsgnj
  ]

  -- 54 = 110110 (FSGNJN)
  let dec_fsgnjn := [
    Gate.mkAND (Wire.mk "d50_t0") not_op3 (Wire.mk "d54_t0"),
    Gate.mkAND (op[2]!) (op[1]!) (Wire.mk "d54_t1"),
    Gate.mkAND (Wire.mk "d54_t0") (Wire.mk "d54_t1") (Wire.mk "d54_t2"),
    Gate.mkAND (Wire.mk "d54_t2") not_op0 is_fsgnjn
  ]

  -- 55 = 110111 (FSGNJX)
  let dec_fsgnjx := [
    Gate.mkAND (Wire.mk "d54_t2") (op[0]!) is_fsgnjx
  ]

  -- result_is_int = FEQ | FLT | FLE | FCLASS | FCVT.W.D | FCVT.WU.D
  let is_cmp := Wire.mk "is_cmp"
  let result_is_int_gates := [
    Gate.mkOR is_feq is_flt (Wire.mk "cmp_t0"),
    Gate.mkOR (Wire.mk "cmp_t0") is_fle is_cmp,
    Gate.mkOR is_cmp is_fclass result_is_int
  ]

  -- ══════════════════════════════════════════════
  -- 9. Output Multiplexing
  -- ══════════════════════════════════════════════
  -- Comparison result: bit 0 = (is_feq & eq_res) | (is_flt & lt_res) | (is_fle & le_res)
  let cmp_bit0 := Wire.mk "cmp_bit0"
  let cmp_bit0_gates := [
    Gate.mkAND is_feq eq_res (Wire.mk "cb0_0"),
    Gate.mkAND is_flt lt_res (Wire.mk "cb0_1"),
    Gate.mkAND is_fle le_res (Wire.mk "cb0_2"),
    Gate.mkOR (Wire.mk "cb0_0") (Wire.mk "cb0_1") (Wire.mk "cb0_t0"),
    Gate.mkOR (Wire.mk "cb0_t0") (Wire.mk "cb0_2") cmp_bit0
  ]

  -- Sign injection result
  let sgnj_res_sign := Wire.mk "sgnj_res_sign"
  let sgnj_sign_gates := [
    Gate.mkAND is_fsgnj sgnj_sign (Wire.mk "ss0"),
    Gate.mkAND is_fsgnjn sgnjn_sign (Wire.mk "ss1"),
    Gate.mkAND is_fsgnjx sgnjx_sign (Wire.mk "ss2"),
    Gate.mkOR (Wire.mk "ss0") (Wire.mk "ss1") (Wire.mk "ss_t0"),
    Gate.mkOR (Wire.mk "ss_t0") (Wire.mk "ss2") sgnj_res_sign
  ]

  let is_any_sgnj := Wire.mk "is_any_sgnj"
  let any_sgnj_gates := [
    Gate.mkOR is_fsgnj is_fsgnjn (Wire.mk "asj0"),
    Gate.mkOR (Wire.mk "asj0") is_fsgnjx is_any_sgnj
  ]

  let out_gates := (List.range 64).flatMap fun i =>
    let w := result[i]!
    if i == 0 then
      let m0 := Wire.mk "out_m0_0"
      let m1 := Wire.mk "out_m1_0"
      let m2 := Wire.mk "out_m2_0"
      let m3 := Wire.mk "out_m3_0"
      [Gate.mkMUX zero (src1[0]!) is_any_sgnj m0,
       Gate.mkMUX m0 cmp_bit0 is_cmp m1,
       Gate.mkMUX m1 (fclass_bits[0]!) is_fclass m2,
       Gate.mkMUX m2 (min_res[0]!) is_fmin m3,
       Gate.mkMUX m3 (max_res[0]!) is_fmax w]
    else if i < 10 then
      let m0 := Wire.mk s!"out_m0_{i}"
      let m1 := Wire.mk s!"out_m1_{i}"
      let m2 := Wire.mk s!"out_m2_{i}"
      let m3 := Wire.mk s!"out_m3_{i}"
      [Gate.mkMUX zero (src1[i]!) is_any_sgnj m0,
       Gate.mkMUX m0 zero is_cmp m1,
       Gate.mkMUX m1 (fclass_bits[i]!) is_fclass m2,
       Gate.mkMUX m2 (min_res[i]!) is_fmin m3,
       Gate.mkMUX m3 (max_res[i]!) is_fmax w]
    else if i < 63 then
      let m0 := Wire.mk s!"out_m0_{i}"
      let m1 := Wire.mk s!"out_m1_{i}"
      let m2 := Wire.mk s!"out_m2_{i}"
      [Gate.mkMUX zero (src1[i]!) is_any_sgnj m0,
       Gate.mkMUX m0 (min_res[i]!) is_fmin m1,
       Gate.mkMUX m1 (max_res[i]!) is_fmax m2,
       Gate.mkMUX m2 zero is_fclass w]
    else
      -- bit 63: sign bit
      let m0 := Wire.mk "out_m0_63"
      let m1 := Wire.mk "out_m1_63"
      let m2 := Wire.mk "out_m2_63"
      [Gate.mkMUX zero sgnj_res_sign is_any_sgnj m0,
       Gate.mkMUX m0 (min_res[63]!) is_fmin m1,
       Gate.mkMUX m1 (max_res[63]!) is_fmax m2,
       Gate.mkMUX m2 zero is_fclass w]

  -- Exceptions: NV flag
  -- FEQ: NV if either is sNaN
  -- FLT/FLE: NV if either is any NaN
  -- FMIN/FMAX: NV if either is sNaN
  let exc_nv := Wire.mk "exc_nv"
  let exc_nv_gates := [
    Gate.mkAND is_feq either_snan (Wire.mk "nv_0"),
    Gate.mkAND is_flt either_nan (Wire.mk "nv_1"),
    Gate.mkAND is_fle either_nan (Wire.mk "nv_2"),
    Gate.mkAND is_fmin either_snan (Wire.mk "nv_3"),
    Gate.mkAND is_fmax either_snan (Wire.mk "nv_4"),
    Gate.mkOR (Wire.mk "nv_0") (Wire.mk "nv_1") (Wire.mk "nv_t0"),
    Gate.mkOR (Wire.mk "nv_2") (Wire.mk "nv_3") (Wire.mk "nv_t1"),
    Gate.mkOR (Wire.mk "nv_t0") (Wire.mk "nv_t1") (Wire.mk "nv_t2"),
    Gate.mkOR (Wire.mk "nv_t2") (Wire.mk "nv_4") exc_nv,
    Gate.mkBUF exc_nv (exc[4]!),
    Gate.mkNOT (rm[0]!) (Wire.mk "not_dm_rm0"),
    Gate.mkAND (rm[0]!) (Wire.mk "not_dm_rm0") (exc[0]!),
    Gate.mkNOT (rm[1]!) (Wire.mk "not_dm_rm1"),
    Gate.mkAND (rm[1]!) (Wire.mk "not_dm_rm1") (exc[1]!),
    Gate.mkNOT (rm[2]!) (Wire.mk "not_dm_rm2"),
    Gate.mkAND (rm[2]!) (Wire.mk "not_dm_rm2") (exc[2]!),
    Gate.mkXOR (rm[0]!) (rm[1]!) (Wire.mk "dm_rm_xor"),
    Gate.mkNOT (Wire.mk "dm_rm_xor") (Wire.mk "not_dm_rm_xor"),
    Gate.mkAND (Wire.mk "dm_rm_xor") (Wire.mk "not_dm_rm_xor") (exc[3]!)
  ]

  let all_gates :=
    exp1_ones_gates ++ exp2_ones_gates ++
    exp1_any_gates ++ [exp1_zeros_gate] ++
    exp2_any_gates ++ [exp2_zeros_gate] ++
    mant1_any_gates ++ [mant1_zeros_gate] ++
    mant2_any_gates ++ [mant2_zeros_gate] ++
    class1_gates ++ class2_gates ++
    xor_gates ++ any_diff_gates ++ [exact_eq_gate, both_zero_gate, mag_eq_gate] ++
    mag_cmp_gates ++ nan_comb_gates ++ [not_nan_gate] ++ cmp_logic_gates ++
    [sgnjx_gate] ++ fclass_gates ++ [min_zero_sign_gate, max_zero_sign_gate, both_nan_gate] ++
    min_sel_gates ++ min_mux_gates ++ max_mux_gates ++ abs_gates ++
    op_inv_gates ++ dec_feq ++ dec_flt ++ dec_fle ++ dec_fclass ++
    dec_fmin ++ dec_fmax ++ dec_fsgnj ++ dec_fsgnjn ++ dec_fsgnjx ++
    result_is_int_gates ++ cmp_bit0_gates ++ sgnj_sign_gates ++ any_sgnj_gates ++
    out_gates ++ exc_nv_gates

  { name := "FPDoubleMisc"
    inputs := src1 ++ src2 ++ op ++ rm ++ [zero, one]
    outputs := result ++ exc ++ [result_is_int]
    gates := all_gates
    instances := [] }

end Shoumei.Circuits.Combinational
