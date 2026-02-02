/-
RISCV/Execution/MemoryExecUnitTest.lean - Concrete behavioral tests for MemoryExecUnit

Tests the Memory Execution Unit (Address Generation Unit) with concrete values to verify:
1. Address calculation (base + offset)
2. Load operations (LB, LH, LW, LBU, LHU)
3. Store operations (SB, SH, SW)
4. Sign extension logic
5. Tag passthrough for CDB broadcast

All tests use `native_decide` for concrete decidable verification.
-/

import Shoumei.RISCV.Execution.MemoryExecUnit

namespace Shoumei.RISCV.Execution.MemoryExecUnitTest

open Shoumei.RISCV
open Shoumei.RISCV.Execution

/-! ## Address Calculation -/

/-- Test: Basic address calculation (positive offset) -/
theorem test_addr_calc_positive :
  let addr := calculateMemoryAddress 0x1000 100
  addr == 0x1064 := by
  native_decide

/-- Test: Address calculation with negative offset -/
theorem test_addr_calc_negative :
  let addr := calculateMemoryAddress 0x1000 (-100)
  addr == 0x0F9C := by
  native_decide

/-- Test: Address calculation with zero offset -/
theorem test_addr_calc_zero :
  let addr := calculateMemoryAddress 0x1000 0
  addr == 0x1000 := by
  native_decide

/-- Test: Address calculation with wraparound -/
theorem test_addr_calc_wraparound :
  let addr := calculateMemoryAddress 0xFFFFFFFF 1
  addr == 0 := by
  native_decide

/-! ## Load Operations -/

/-- Test: Load byte (LB) request format -/
theorem test_load_byte :
  let req := executeLoad OpType.LB 0x1000 4 42
  req.access_type == MemAccessType.Load ∧
  req.size == MemSize.Byte ∧
  req.sign_extend == true ∧
  req.address == 0x1004 ∧
  req.dest_tag == 42 := by
  native_decide

/-- Test: Load halfword (LH) request format -/
theorem test_load_halfword :
  let req := executeLoad OpType.LH 0x1000 8 42
  req.access_type == MemAccessType.Load ∧
  req.size == MemSize.Halfword ∧
  req.sign_extend == true ∧
  req.address == 0x1008 := by
  native_decide

/-- Test: Load word (LW) request format -/
theorem test_load_word :
  let req := executeLoad OpType.LW 0x1000 12 42
  req.access_type == MemAccessType.Load ∧
  req.size == MemSize.Word ∧
  req.sign_extend == false ∧  -- No extension needed for 32-bit load
  req.address == 0x100C := by
  native_decide

/-- Test: Load byte unsigned (LBU) - no sign extension -/
theorem test_load_byte_unsigned :
  let req := executeLoad OpType.LBU 0x1000 4 42
  req.access_type == MemAccessType.Load ∧
  req.size == MemSize.Byte ∧
  req.sign_extend == false ∧
  req.address == 0x1004 := by
  native_decide

/-- Test: Load halfword unsigned (LHU) - no sign extension -/
theorem test_load_halfword_unsigned :
  let req := executeLoad OpType.LHU 0x1000 8 42
  req.access_type == MemAccessType.Load ∧
  req.size == MemSize.Halfword ∧
  req.sign_extend == false ∧
  req.address == 0x1008 := by
  native_decide

/-! ## Store Operations -/

/-- Test: Store byte (SB) request format -/
theorem test_store_byte :
  let req := executeStore OpType.SB 0x1000 4 0x12345678 42
  req.access_type == MemAccessType.Store ∧
  req.size == MemSize.Byte ∧
  req.address == 0x1004 ∧
  req.write_data == 0x12345678 ∧
  req.dest_tag == 42 := by
  native_decide

/-- Test: Store halfword (SH) request format -/
theorem test_store_halfword :
  let req := executeStore OpType.SH 0x1000 8 0x12345678 42
  req.access_type == MemAccessType.Store ∧
  req.size == MemSize.Halfword ∧
  req.address == 0x1008 ∧
  req.write_data == 0x12345678 := by
  native_decide

/-- Test: Store word (SW) request format -/
theorem test_store_word :
  let req := executeStore OpType.SW 0x1000 12 0x12345678 42
  req.access_type == MemAccessType.Store ∧
  req.size == MemSize.Word ∧
  req.address == 0x100C ∧
  req.write_data == 0x12345678 := by
  native_decide

/-! ## Sign Extension Processing -/

/-- Test: Process byte with sign extension (negative) -/
theorem test_process_byte_sign_extend :
  let result := processLoadResponse 0x80 MemSize.Byte true
  result == 0xFFFFFF80 := by
  native_decide

/-- Test: Process byte without sign extension (positive) -/
theorem test_process_byte_no_sign_extend :
  let result := processLoadResponse 0x80 MemSize.Byte false
  result == 0x80 := by
  native_decide

/-- Test: Process halfword with sign extension (negative) -/
theorem test_process_halfword_sign_extend :
  let result := processLoadResponse 0x8000 MemSize.Halfword true
  result == 0xFFFF8000 := by
  native_decide

/-- Test: Process halfword without sign extension -/
theorem test_process_halfword_no_sign_extend :
  let result := processLoadResponse 0x8000 MemSize.Halfword false
  result == 0x8000 := by
  native_decide

/-- Test: Process word (no extension) -/
theorem test_process_word :
  let result := processLoadResponse 0x12345678 MemSize.Word false
  result == 0x12345678 := by
  native_decide

/-! ## Simple Memory Model Tests -/

/-- Test: Initialize empty memory -/
theorem test_memory_init :
  let mem := SimpleMemory.init
  SimpleMemory.readByte mem 0 == 0 := by
  native_decide

/-- Test: Write and read byte -/
theorem test_memory_write_read_byte :
  let mem := SimpleMemory.init
  let mem' := SimpleMemory.writeByte mem 0 0x42
  SimpleMemory.readByte mem' 0 == 0x42 := by
  native_decide

/-- Test: Write byte doesn't affect other addresses -/
theorem test_memory_write_isolation :
  let mem := SimpleMemory.init
  let mem' := SimpleMemory.writeByte mem 0 0x42
  SimpleMemory.readByte mem' 1 == 0 := by
  native_decide

/-! ## Edge Cases -/

/-- Test: Load with maximum address offset -/
theorem test_load_max_offset :
  let req := executeLoad OpType.LW 0x80000000 0x7FFFFFFF 42
  req.address == 0xFFFFFFFF := by
  native_decide

/-- Test: Store with negative offset -/
theorem test_store_negative_offset :
  let req := executeStore OpType.SW 0x1000 (-4) 0x12345678 42
  req.address == 0x0FFC := by
  native_decide

/-- Test: Address verification helpers -/
theorem test_verify_load_address :
  verifyLoadAddress 0x1000 100 == true := by
  native_decide

theorem test_verify_store_address :
  verifyStoreAddress 0x1000 100 == true := by
  native_decide

end Shoumei.RISCV.Execution.MemoryExecUnitTest
