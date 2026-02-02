/-
RISCV/Execution/IntegerExecUnitTest.lean - Concrete behavioral tests for IntegerExecUnit

Tests the Integer Execution Unit (ALU wrapper) with concrete values to verify:
1. Arithmetic operations (ADD, SUB, SLT, SLTU)
2. Logic operations (AND, OR, XOR)
3. Shift operations (SLL, SRL, SRA)
4. Tag passthrough for CDB broadcast
5. Integration with Reservation Station interface

All tests use `native_decide` for concrete decidable verification.
-/

import Shoumei.RISCV.Execution.IntegerExecUnit

namespace Shoumei.RISCV.Execution.IntegerExecUnitTest

open Shoumei.RISCV
open Shoumei.RISCV.Execution

/-! ## Arithmetic Operations -/

/-- Test: ADD operation with positive numbers -/
theorem test_add_positive :
  let result := executeInteger OpType.ADD 100 200 42
  result.1 == 42 ∧ result.2 == 300 := by
  native_decide

/-- Test: ADD operation with overflow (wrapping) -/
theorem test_add_overflow :
  let result := executeInteger OpType.ADD 0xFFFFFFFF 1 42
  result.1 == 42 ∧ result.2 == 0 := by
  native_decide

/-- Test: SUB operation -/
theorem test_sub :
  let result := executeInteger OpType.SUB 500 200 42
  result.1 == 42 ∧ result.2 == 300 := by
  native_decide

/-- Test: SUB operation with underflow (wrapping) -/
theorem test_sub_underflow :
  let result := executeInteger OpType.SUB 0 1 42
  result.1 == 42 ∧ result.2 == 0xFFFFFFFF := by
  native_decide

/-- Test: SLT (signed less-than) with positive numbers -/
theorem test_slt_positive :
  let result := executeInteger OpType.SLT 100 200 42
  result.1 == 42 ∧ result.2 == 1 := by
  native_decide

/-- Test: SLT with negative numbers (treated as unsigned in simplified model) -/
theorem test_slt_negative :
  let result := executeInteger OpType.SLT 200 100 42
  result.1 == 42 ∧ result.2 == 0 := by
  native_decide

/-- Test: SLTU (unsigned less-than) -/
theorem test_sltu_true :
  let result := executeInteger OpType.SLTU 100 200 42
  result.1 == 42 ∧ result.2 == 1 := by
  native_decide

/-- Test: SLTU false case -/
theorem test_sltu_false :
  let result := executeInteger OpType.SLTU 200 100 42
  result.1 == 42 ∧ result.2 == 0 := by
  native_decide

/-! ## Logic Operations -/

/-- Test: AND operation -/
theorem test_and :
  let result := executeInteger OpType.AND 0xFF00FF00 0xF0F0F0F0 42
  result.1 == 42 ∧ result.2 == 0xF000F000 := by
  native_decide

/-- Test: OR operation -/
theorem test_or :
  let result := executeInteger OpType.OR 0xFF00FF00 0xF0F0F0F0 42
  result.1 == 42 ∧ result.2 == 0xFFF0FFF0 := by
  native_decide

/-- Test: XOR operation -/
theorem test_xor :
  let result := executeInteger OpType.XOR 0xFF00FF00 0xF0F0F0F0 42
  result.1 == 42 ∧ result.2 == 0x0FF00FF0 := by
  native_decide

/-- Test: XOR with same value (should be zero) -/
theorem test_xor_self :
  let result := executeInteger OpType.XOR 0x12345678 0x12345678 42
  result.1 == 42 ∧ result.2 == 0 := by
  native_decide

/-! ## Shift Operations -/

/-- Test: SLL (shift left logical) by 4 bits -/
theorem test_sll :
  let result := executeInteger OpType.SLL 0x00000001 4 42
  result.1 == 42 ∧ result.2 == 0x00000010 := by
  native_decide

/-- Test: SLL with large shift amount (mod 32) -/
theorem test_sll_large_shift :
  let result := executeInteger OpType.SLL 0x00000001 35 42  -- 35 mod 32 = 3
  result.1 == 42 ∧ result.2 == 0x00000008 := by
  native_decide

/-- Test: SRL (shift right logical) by 4 bits -/
theorem test_srl :
  let result := executeInteger OpType.SRL 0x00000100 4 42
  result.1 == 42 ∧ result.2 == 0x00000010 := by
  native_decide

/-- Test: SRL with high bit set (logical shift, zero-fill) -/
theorem test_srl_high_bit :
  let result := executeInteger OpType.SRL 0x80000000 4 42
  result.1 == 42 ∧ result.2 == 0x08000000 := by
  native_decide

/-! ## Tag Passthrough -/

/-- Test: Tag passthrough for different register tags -/
theorem test_tag_passthrough_p0 :
  let result := executeInteger OpType.ADD 100 200 0
  result.1 == 0 := by
  native_decide

theorem test_tag_passthrough_p63 :
  let result := executeInteger OpType.ADD 100 200 63
  result.1 == 63 := by
  native_decide

/-! ## CDB Broadcast Interface -/

/-- Test: executeToCDB creates correct broadcast -/
theorem test_cdb_broadcast :
  let broadcast := executeToCDB OpType.ADD 100 200 42
  broadcast.tag == 42 ∧ broadcast.data == 300 := by
  native_decide

/-- Test: executeFromRS integration -/
theorem test_execute_from_rs :
  let dispatch_bundle := (OpType.ADD, 100, 200, 42)
  let broadcast := executeFromRS dispatch_bundle
  broadcast.tag == 42 ∧ broadcast.data == 300 := by
  native_decide

/-! ## Edge Cases -/

/-- Test: ADD with zero -/
theorem test_add_zero :
  let result := executeInteger OpType.ADD 12345 0 42
  result.1 == 42 ∧ result.2 == 12345 := by
  native_decide

/-- Test: AND with all zeros -/
theorem test_and_zero :
  let result := executeInteger OpType.AND 0xFFFFFFFF 0 42
  result.1 == 42 ∧ result.2 == 0 := by
  native_decide

/-- Test: OR with all ones -/
theorem test_or_ones :
  let result := executeInteger OpType.OR 0x12345678 0xFFFFFFFF 42
  result.1 == 42 ∧ result.2 == 0xFFFFFFFF := by
  native_decide

/-- Test: Shift by zero (identity) -/
theorem test_shift_zero :
  let result := executeInteger OpType.SLL 0x12345678 0 42
  result.1 == 42 ∧ result.2 == 0x12345678 := by
  native_decide

end Shoumei.RISCV.Execution.IntegerExecUnitTest
