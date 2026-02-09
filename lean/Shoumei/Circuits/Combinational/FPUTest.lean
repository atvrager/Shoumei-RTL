/-
FPU Test - Verify IEEE 754 SP behavioral model against known values.
Uses native_decide for concrete test cases.
-/

import Shoumei.Circuits.Combinational.FPU

namespace Shoumei.Circuits.Combinational.FPUTest

open FPU

/-! ## Constant Tests -/

-- IEEE 754 SP bit patterns
-- 1.0  = 0x3F800000 (sign=0, exp=127, mant=0)
-- 2.0  = 0x40000000 (sign=0, exp=128, mant=0)
-- 3.0  = 0x40400000 (sign=0, exp=128, mant=0x400000)
-- 0.5  = 0x3F000000 (sign=0, exp=126, mant=0)
-- -1.0 = 0xBF800000 (sign=1, exp=127, mant=0)
-- +0   = 0x00000000
-- -0   = 0x80000000
-- +inf = 0x7F800000
-- -inf = 0xFF800000
-- NaN  = 0x7FC00000 (canonical quiet NaN)

/-! ## Classification Tests -/

theorem test_classify_pos_zero :
    classify 0x00000000 = FPClass.PosZero := by native_decide

theorem test_classify_neg_zero :
    classify 0x80000000 = FPClass.NegZero := by native_decide

theorem test_classify_pos_inf :
    classify 0x7F800000 = FPClass.PosInf := by native_decide

theorem test_classify_neg_inf :
    classify 0xFF800000 = FPClass.NegInf := by native_decide

theorem test_classify_qnan :
    classify 0x7FC00000 = FPClass.QNaN := by native_decide

theorem test_classify_snan :
    classify 0x7F800001 = FPClass.SNaN := by native_decide

theorem test_classify_pos_normal :
    classify 0x3F800000 = FPClass.PosNormal := by native_decide  -- 1.0

theorem test_classify_neg_normal :
    classify 0xBF800000 = FPClass.NegNormal := by native_decide  -- -1.0

theorem test_classify_pos_subnormal :
    classify 0x00000001 = FPClass.PosSubnormal := by native_decide  -- smallest subnormal

/-! ## FCLASS Tests -/

theorem test_fclass_pos_inf :
    fpClassify 0x7F800000 = 0x080 := by native_decide

theorem test_fclass_neg_inf :
    fpClassify 0xFF800000 = 0x001 := by native_decide

theorem test_fclass_qnan :
    fpClassify 0x7FC00000 = 0x200 := by native_decide

theorem test_fclass_snan :
    fpClassify 0x7F800001 = 0x100 := by native_decide

theorem test_fclass_pos_zero :
    fpClassify 0x00000000 = 0x010 := by native_decide

theorem test_fclass_neg_zero :
    fpClassify 0x80000000 = 0x008 := by native_decide

/-! ## Pack/Unpack Round-Trip -/

theorem test_pack_unpack_one :
    pack (unpack 0x3F800000) = 0x3F800000 := by native_decide

theorem test_pack_unpack_neg_one :
    pack (unpack 0xBF800000) = 0xBF800000 := by native_decide

theorem test_pack_unpack_zero :
    pack (unpack 0x00000000) = 0x00000000 := by native_decide

/-! ## Sign Injection Tests -/

theorem test_fsgnj_pos_pos :
    fpSgnj 0x3F800000 0x40000000 = 0x3F800000 := by native_decide  -- sgnj(1.0, 2.0) = 1.0

theorem test_fsgnj_pos_neg :
    fpSgnj 0x3F800000 0xBF800000 = 0xBF800000 := by native_decide  -- sgnj(1.0, -1.0) = -1.0

theorem test_fsgnjn_pos_pos :
    fpSgnjn 0x3F800000 0x40000000 = 0xBF800000 := by native_decide  -- sgnjn(1.0, 2.0) = -1.0

theorem test_fsgnjx_pos_neg :
    fpSgnjx 0x3F800000 0xBF800000 = 0xBF800000 := by native_decide  -- sgnjx(1.0, -1.0) = -1.0

theorem test_fsgnjx_neg_neg :
    fpSgnjx 0xBF800000 0xBF800000 = 0x3F800000 := by native_decide  -- sgnjx(-1.0, -1.0) = 1.0

/-! ## FMV Tests (bit-preserving moves) -/

theorem test_fmv_x_w :
    (executeFP .FMV_X_W 0x3F800000 0 0 .RNE).value = 0x3F800000 := by native_decide

theorem test_fmv_w_x :
    (executeFP .FMV_W_X 0x3F800000 0 0 .RNE).value = 0x3F800000 := by native_decide

/-! ## Arithmetic Tests -/

-- 1.0 + 1.0 = 2.0
theorem test_fadd_one_one :
    (fpAddSub 0x3F800000 0x3F800000 false .RNE).value = 0x40000000 := by native_decide

-- 2.0 - 1.0 = 1.0
theorem test_fsub_two_one :
    (fpAddSub 0x40000000 0x3F800000 true .RNE).value = 0x3F800000 := by native_decide

-- 2.0 * 3.0 = 6.0 (0x40C00000)
theorem test_fmul_two_three :
    (fpMul 0x40000000 0x40400000 .RNE).value = 0x40C00000 := by native_decide

-- 1.0 / 2.0 = 0.5 (0x3F000000)
theorem test_fdiv_one_two :
    (fpDiv 0x3F800000 0x40000000 .RNE).value = 0x3F000000 := by native_decide

/-! ## Special Value Arithmetic -/

-- inf + 1.0 = inf
theorem test_add_inf :
    (fpAddSub 0x7F800000 0x3F800000 false .RNE).value = 0x7F800000 := by native_decide

-- inf - inf = NaN (with NV flag)
theorem test_sub_inf_inf_is_nan :
    isNaN (fpAddSub 0x7F800000 0x7F800000 true .RNE).value = true := by native_decide

theorem test_sub_inf_inf_nv :
    (fpAddSub 0x7F800000 0x7F800000 true .RNE).exceptions.nv = true := by native_decide

-- 0 / 0 = NaN (with NV flag)
theorem test_div_zero_zero_nan :
    isNaN (fpDiv 0x00000000 0x00000000 .RNE).value = true := by native_decide

-- 1.0 / 0.0 = +inf (with DZ flag)
theorem test_div_by_zero :
    (fpDiv 0x3F800000 0x00000000 .RNE).value = 0x7F800000 := by native_decide

theorem test_div_by_zero_dz :
    (fpDiv 0x3F800000 0x00000000 .RNE).exceptions.dz = true := by native_decide

-- inf * 0 = NaN (with NV flag)
theorem test_mul_inf_zero :
    isNaN (fpMul 0x7F800000 0x00000000 .RNE).value = true := by native_decide

/-! ## Compare Tests -/

-- FEQ(1.0, 1.0) = 1
theorem test_feq_equal :
    (fpCompare 0x3F800000 0x3F800000 true false false).value = 1 := by native_decide

-- FEQ(1.0, 2.0) = 0
theorem test_feq_not_equal :
    (fpCompare 0x3F800000 0x40000000 true false false).value = 0 := by native_decide

-- FLT(1.0, 2.0) = 1
theorem test_flt_less :
    (fpCompare 0x3F800000 0x40000000 false true false).value = 1 := by native_decide

-- FLT(2.0, 1.0) = 0
theorem test_flt_greater :
    (fpCompare 0x40000000 0x3F800000 false true false).value = 0 := by native_decide

-- FLE(1.0, 1.0) = 1
theorem test_fle_equal :
    (fpCompare 0x3F800000 0x3F800000 false false true).value = 1 := by native_decide

-- FEQ(+0, -0) = 1 (positive and negative zero are equal)
theorem test_feq_pos_neg_zero :
    (fpCompare 0x00000000 0x80000000 true false false).value = 1 := by native_decide

/-! ## Conversion Tests -/

-- FCVT.W.S(1.0) = 1
theorem test_fcvt_w_s_one :
    (fpToInt32 0x3F800000 .RNE).value = 1 := by native_decide

-- FCVT.W.S(2.0) = 2
theorem test_fcvt_w_s_two :
    (fpToInt32 0x40000000 .RNE).value = 2 := by native_decide

-- FCVT.S.W(1) = 1.0
theorem test_fcvt_s_w_one :
    (int32ToFP 1 .RNE).value = 0x3F800000 := by native_decide

-- FCVT.S.W(0) = 0.0
theorem test_fcvt_s_w_zero :
    (int32ToFP 0 .RNE).value = 0x00000000 := by native_decide

-- FCVT.WU.S(1.0) = 1
theorem test_fcvt_wu_s_one :
    (fpToUInt32 0x3F800000 .RNE).value = 1 := by native_decide

-- FCVT.S.WU(1) = 1.0
theorem test_fcvt_s_wu_one :
    (uint32ToFP 1 .RNE).value = 0x3F800000 := by native_decide

end Shoumei.Circuits.Combinational.FPUTest
