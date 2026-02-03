/-
CPU Control Logic Tests

Comprehensive test suite for stall generation, stage enables, and flush detection.
Tests cover all structural hazard scenarios and config-aware behavior.

All tests use native_decide for concrete verification.
-/

import Shoumei.RISCV.CPUControl

namespace Shoumei.RISCV.CPUControlTest

open Shoumei.RISCV
open Shoumei.RISCV.Control
open Shoumei.RISCV.Execution

/-
Test 1: No Stall - All Resources Available
-/
theorem test_no_stall_all_available :
    let config := rv32imConfig
    let stall := generateStall config
      false  -- freeListEmpty
      false  -- robFull
      false  -- rsIntegerFull
      false  -- rsMemoryFull
      false  -- rsBranchFull
      false  -- rsMulDivFull
      true   -- lsuCanAcceptLoad
      true   -- lsuCanAcceptStore
      OpType.ADD  -- instrType
    stall = false
    := by native_decide

/-
Test 2: FreeList Empty Causes Stall
-/
theorem test_freelist_empty_stall :
    let config := rv32imConfig
    let stall := generateStall config
      true   -- freeListEmpty = TRUE
      false  -- robFull
      false  -- rsIntegerFull
      false  -- rsMemoryFull
      false  -- rsBranchFull
      false  -- rsMulDivFull
      true   -- lsuCanAcceptLoad
      true   -- lsuCanAcceptStore
      OpType.ADD
    stall = true
    := by native_decide

/-
Test 3: ROB Full Causes Stall
-/
theorem test_rob_full_stall :
    let config := rv32imConfig
    let stall := generateStall config
      false
      true   -- robFull = TRUE
      false
      false
      false
      false
      true
      true
      OpType.ADD
    stall = true
    := by native_decide

/-
Test 4: Integer RS Full Stalls Integer Instruction
-/
theorem test_integer_rs_full_stalls_integer_instr :
    let config := rv32imConfig
    let stall := generateStall config
      false
      false
      true   -- rsIntegerFull = TRUE
      false
      false
      false
      true
      true
      OpType.ADD  -- Integer instruction
    stall = true
    := by native_decide

/-
Test 5: Integer RS Full Does Not Stall Memory Instruction
-/
theorem test_integer_rs_full_no_stall_memory_instr :
    let config := rv32imConfig
    let stall := generateStall config
      false
      false
      true   -- rsIntegerFull = TRUE
      false  -- rsMemoryFull = FALSE
      false
      false
      true
      true
      OpType.LW  -- Memory instruction (should not stall)
    stall = false
    := by native_decide

/-
Test 6: Memory RS Full Stalls Load Instruction
-/
theorem test_memory_rs_full_stalls_load :
    let config := rv32imConfig
    let stall := generateStall config
      false
      false
      false
      true   -- rsMemoryFull = TRUE
      false
      false
      true
      true
      OpType.LW  -- Load instruction
    stall = true
    := by native_decide

/-
Test 7: Branch RS Full Stalls Branch Instruction
-/
theorem test_branch_rs_full_stalls_branch :
    let config := rv32imConfig
    let stall := generateStall config
      false
      false
      false
      false
      true   -- rsBranchFull = TRUE
      false
      true
      true
      OpType.BEQ  -- Branch instruction
    stall = true
    := by native_decide

/-
Test 8: MulDiv RS Full Stalls MulDiv Instruction (M Extension Enabled)
-/
theorem test_muldiv_rs_full_stalls_mul_with_m_ext :
    let config := rv32imConfig  -- M extension enabled
    let stall := generateStall config
      false
      false
      false
      false
      false
      true   -- rsMulDivFull = TRUE
      true
      true
      OpType.MUL  -- MulDiv instruction
    stall = true
    := by native_decide

/-
Test 9: MulDiv Instruction Does Not Stall (Classified as Illegal)
Note: When M extension is disabled, MulDiv instructions are classified
as Illegal by classifyToUnit, so needsMulDivRS returns false. The decoder
should mark these as illegal instructions before they reach the issue stage.
-/
theorem test_muldiv_instr_no_stall_without_m_ext :
    let config := rv32iConfig  -- M extension DISABLED
    let stall := generateStall config
      false
      false
      false
      false
      false
      false  -- rsMulDivFull = FALSE (doesn't matter)
      true
      true
      OpType.DIV  -- MulDiv instruction (classified as Illegal)
    stall = false  -- Does not stall (decoder handles illegal instructions)
    := by native_decide

/-
Test 10: LSU Cannot Accept Load Stalls Load Instruction
-/
theorem test_lsu_cannot_accept_load_stalls :
    let config := rv32imConfig
    let stall := generateStall config
      false
      false
      false
      false
      false
      false
      false  -- lsuCanAcceptLoad = FALSE
      true
      OpType.LW  -- Load instruction
    stall = true
    := by native_decide

/-
Test 11: LSU Cannot Accept Store Stalls Store Instruction
-/
theorem test_lsu_cannot_accept_store_stalls :
    let config := rv32imConfig
    let stall := generateStall config
      false
      false
      false
      false
      false
      false
      true
      false  -- lsuCanAcceptStore = FALSE
      OpType.SW  -- Store instruction
    stall = true
    := by native_decide

/-
Test 12: Multiple Stall Sources - Any Causes Stall
-/
theorem test_multiple_stall_sources :
    let config := rv32imConfig
    let stall := generateStall config
      true   -- freeListEmpty = TRUE
      true   -- robFull = TRUE
      false
      false
      false
      false
      true
      true
      OpType.ADD
    stall = true  -- Either source should cause stall
    := by native_decide

/-
Test 13: Stage Enables - Normal Operation
-/
theorem test_stage_enables_normal :
    let enables := generateStageEnables false false  -- no stall, no flush
    enables.fetchEnable = true ∧
    enables.decodeEnable = true ∧
    enables.renameEnable = true ∧
    enables.issueEnable = true
    := by native_decide

/-
Test 14: Stage Enables - Stall Disables All Stages
-/
theorem test_stage_enables_stall :
    let enables := generateStageEnables true false  -- stall = true
    enables.fetchEnable = false ∧
    enables.decodeEnable = false ∧
    enables.renameEnable = false ∧
    enables.issueEnable = false
    := by native_decide

/-
Test 15: Stage Enables - Flush Disables All Stages
-/
theorem test_stage_enables_flush :
    let enables := generateStageEnables false true  -- flushing = true
    enables.fetchEnable = false ∧
    enables.decodeEnable = false ∧
    enables.renameEnable = false ∧
    enables.issueEnable = false
    := by native_decide

/-
Test 16: Flush Detection - Branch Misprediction
-/
theorem test_flush_detect_branch_mispredict :
    let reason := detectFlush true false  -- branchMispredicted = true
    reason = FlushReason.BranchMisprediction
    := by native_decide

/-
Test 17: Flush Detection - Exception
-/
theorem test_flush_detect_exception :
    let reason := detectFlush false true  -- exceptionOccurred = true
    reason = FlushReason.Exception
    := by native_decide

/-
Test 18: Flush Detection - No Flush
-/
theorem test_flush_detect_none :
    let reason := detectFlush false false  -- no flush conditions
    reason = FlushReason.None
    := by native_decide

/-
Test 19: Flush Detection - Branch Priority Over Exception
-/
theorem test_flush_detect_branch_priority :
    let reason := detectFlush true true  -- both conditions
    reason = FlushReason.BranchMisprediction  -- branch has priority
    := by native_decide

/-
Test 20: Flush Target PC - Branch Misprediction
-/
theorem test_flush_target_branch :
    let target := getFlushTargetPC FlushReason.BranchMisprediction 0x80001234 0x80000000
    target = 0x80001234  -- Returns branch target
    := by native_decide

/-
Test 21: Flush Target PC - Exception
-/
theorem test_flush_target_exception :
    let target := getFlushTargetPC FlushReason.Exception 0x80001234 0x80000000
    target = 0x80000000  -- Returns trap handler
    := by native_decide

/-
Test 22: OpType Classification - Integer Operations
-/
theorem test_needs_integer_rs_add :
    needsIntegerRS OpType.ADD rv32imConfig = true
    := by native_decide

theorem test_needs_integer_rs_lui :
    needsIntegerRS OpType.LUI rv32imConfig = true
    := by native_decide

/-
Test 23: OpType Classification - Memory Operations
-/
theorem test_needs_memory_rs_load :
    needsMemoryRS OpType.LW rv32imConfig = true
    := by native_decide

theorem test_needs_memory_rs_store :
    needsMemoryRS OpType.SW rv32imConfig = true
    := by native_decide

/-
Test 24: OpType Classification - Branch Operations
-/
theorem test_needs_branch_rs_beq :
    needsBranchRS OpType.BEQ rv32imConfig = true
    := by native_decide

theorem test_needs_branch_rs_jal :
    needsBranchRS OpType.JAL rv32imConfig = true
    := by native_decide

/-
Test 25: OpType Classification - MulDiv Operations
-/
theorem test_needs_muldiv_rs_mul_with_m :
    needsMulDivRS OpType.MUL rv32imConfig = true
    := by native_decide

theorem test_needs_muldiv_rs_div_without_m :
    needsMulDivRS OpType.DIV rv32iConfig = false  -- Classified as Illegal
    := by native_decide

/-
Test 26: Load/Store Detection
-/
theorem test_is_load_lw :
    isLoad OpType.LW = true
    := by native_decide

theorem test_is_load_add :
    isLoad OpType.ADD = false
    := by native_decide

theorem test_is_store_sw :
    isStore OpType.SW = true
    := by native_decide

theorem test_is_store_add :
    isStore OpType.ADD = false
    := by native_decide

end Shoumei.RISCV.CPUControlTest
