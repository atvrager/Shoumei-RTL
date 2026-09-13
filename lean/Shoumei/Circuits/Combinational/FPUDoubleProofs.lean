/-
FPUDoubleProofs.lean - Formal proofs and test properties for FPUDouble
-/

import Shoumei.Circuits.Combinational.FPUDouble

namespace Shoumei.Circuits.Combinational.FPUDoubleProofs

open Shoumei.Circuits.Combinational.FPU
open Shoumei.Circuits.Combinational.FPUDouble

/-! ## Bit patterns for tests -/
-- 1.0 = 0x3FF0000000000000
-- 2.0 = 0x4000000000000000
-- 3.0 = 0x4008000000000000
-- 4.0 = 0x4010000000000000
-- 6.0 = 0x4018000000000000
-- 7.0 = 0x401C000000000000
-- 9.0 = 0x4022000000000000
-- -1.0 = 0xBFF0000000000000

/-! ## Classification Proofs -/

theorem test_classify64_pos_zero :
    classify64 posZero64 = FPClass.PosZero := by native_decide

theorem test_classify64_neg_zero :
    classify64 negZero64 = FPClass.NegZero := by native_decide

theorem test_classify64_pos_inf :
    classify64 posInf64 = FPClass.PosInf := by native_decide

theorem test_classify64_neg_inf :
    classify64 negInf64 = FPClass.NegInf := by native_decide

theorem test_classify64_qnan :
    classify64 canonicalNaN64 = FPClass.QNaN := by native_decide

theorem test_classify64_snan :
    classify64 0x7FF0000000000001 = FPClass.SNaN := by native_decide

theorem test_classify64_pos_normal :
    classify64 0x3FF0000000000000 = FPClass.PosNormal := by native_decide

theorem test_classify64_neg_normal :
    classify64 0xBFF0000000000000 = FPClass.NegNormal := by native_decide

theorem test_classify64_pos_subnormal :
    classify64 0x0000000000000001 = FPClass.PosSubnormal := by native_decide

/-! ## FCLASS Proofs -/

theorem test_dpClassify_pos_zero :
    dpClassify posZero64 = 0x010 := by native_decide

theorem test_dpClassify_neg_zero :
    dpClassify negZero64 = 0x008 := by native_decide

theorem test_dpClassify_pos_inf :
    dpClassify posInf64 = 0x080 := by native_decide

theorem test_dpClassify_neg_inf :
    dpClassify negInf64 = 0x001 := by native_decide

theorem test_dpClassify_qnan :
    dpClassify canonicalNaN64 = 0x200 := by native_decide

theorem test_dpClassify_snan :
    dpClassify 0x7FF0000000000001 = 0x100 := by native_decide

theorem test_dpClassify_pos_normal :
    dpClassify 0x3FF0000000000000 = 0x040 := by native_decide

/-! ## Arithmetic Proofs -/

theorem test_dpAdd_1_plus_2 :
    (dpAddSub 0x3FF0000000000000 0x4000000000000000 false .RNE).value = 0x4008000000000000 := by native_decide

theorem test_dpSub_3_minus_1 :
    (dpAddSub 0x4008000000000000 0x3FF0000000000000 true .RNE).value = 0x4000000000000000 := by native_decide

theorem test_dpMul_2_times_3 :
    (dpMul 0x4000000000000000 0x4008000000000000 .RNE).value = 0x4018000000000000 := by native_decide

theorem test_dpFMA_2_times_3_plus_1 :
    (dpFMA 0x4000000000000000 0x4008000000000000 0x3FF0000000000000 .RNE).value = 0x401C000000000000 := by native_decide

theorem test_dpDiv_6_by_2 :
    (dpDiv 0x4018000000000000 0x4000000000000000 .RNE).value = 0x4008000000000000 := by native_decide

theorem test_dpSqrt_4 :
    (dpSqrt 0x4010000000000000 .RNE).value = 0x4000000000000000 := by native_decide

theorem test_dpSqrt_9 :
    (dpSqrt 0x4022000000000000 .RNE).value = 0x4008000000000000 := by native_decide

/-! ## Comparison Proofs -/

theorem test_dpCompare_eq :
    (dpCompare 0x3FF0000000000000 0x3FF0000000000000 true false false).value = 1 := by native_decide

theorem test_dpCompare_lt :
    (dpCompare 0x3FF0000000000000 0x4000000000000000 false true false).value = 1 := by native_decide

theorem test_dpCompare_le :
    (dpCompare 0x3FF0000000000000 0x3FF0000000000000 false false true).value = 1 := by native_decide

/-! ## Conversion Proofs -/

theorem test_int32ToDP_42 :
    (int32ToDP 42).value = 0x4045000000000000 := by native_decide

theorem test_dpToInt32_42 :
    (dpToInt32 0x4045000000000000 .RNE).value = 42 := by native_decide

theorem test_dpToSP_1 :
    (dpToSP 0x3FF0000000000000 .RNE).value = 0xFFFFFFFF3F800000 := by native_decide

theorem test_spToDP_boxed_1 :
    (spToDP 0xFFFFFFFF3F800000).value = 0x3FF0000000000000 := by native_decide

theorem test_spToDP_unboxed_nan :
    (spToDP 0x000000003F800000).value = canonicalNaN64 := by native_decide

end Shoumei.Circuits.Combinational.FPUDoubleProofs
