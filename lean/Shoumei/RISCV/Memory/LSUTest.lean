/-
RISCV/Memory/LSUTest.lean - Load-Store Unit Test Suite

Comprehensive behavioral tests for LSU operations using native_decide.

Test Categories:
1. Store execution (enqueue into store buffer)
2. Load execution with forwarding hit (youngest match)
3. Load execution with forwarding miss (issue memory request)
4. Store commitment (mark committed in store buffer)
5. Store dequeue to memory (committed stores)
6. Load-store ordering (TSO semantics)
7. Flush handling (clear all state)
8. Edge cases (full buffer, pending load stall)
-/

import Shoumei.RISCV.Memory.LSU
import Shoumei.RISCV.ISA

namespace Shoumei.RISCV.Memory

open Shoumei.RISCV

/-! ## Test Helpers -/

/-- Create an LSU with a specific number of stores already enqueued. -/
def createLSUWithStores (n : Nat) : LSUState :=
  let rec enqueueN (lsu : LSUState) (count : Nat) : LSUState :=
    match count with
    | 0 => lsu
    | k + 1 =>
        let addr := (0x1000 + k * 4).toUInt32
        let data := (0x100 + k).toUInt32
        let (newLSU, success) := lsu.executeStore OpType.SW addr 0 data
        if success then enqueueN newLSU k else lsu
  enqueueN LSUState.empty n

/-! ## Test Category 1: Store Execution -/

/-- Test: Store to empty LSU succeeds. -/
theorem test_store_empty_success :
    let lsu := LSUState.empty
    let (newLSU, success) := lsu.executeStore OpType.SW 0x1000 0 0x42
    success = true ∧ newLSU.storeBufferCount = 1 := by
  native_decide

/-- Test: Store increments store buffer count. -/
theorem test_store_increments_count :
    let lsu := LSUState.empty
    let (lsu1, _) := lsu.executeStore OpType.SW 0x1000 0 0x10
    let (lsu2, _) := lsu1.executeStore OpType.SW 0x1004 0 0x20
    lsu2.storeBufferCount = 2 := by
  native_decide

/-- Test: Store buffer full causes stall. -/
theorem test_store_buffer_full_stall :
    let lsu := createLSUWithStores 8
    let (newLSU, success) := lsu.executeStore OpType.SW 0x2000 0 0xFF
    success = false ∧ newLSU.storeBufferCount = 8 := by
  native_decide

/-- Test: Store byte operation. -/
theorem test_store_byte :
    let lsu := LSUState.empty
    let (newLSU, success) := lsu.executeStore OpType.SB 0x1000 0 0xFF
    success = true ∧ newLSU.storeBufferCount = 1 := by
  native_decide

/-- Test: Store halfword operation. -/
theorem test_store_halfword :
    let lsu := LSUState.empty
    let (newLSU, success) := lsu.executeStore OpType.SH 0x1000 0 0xABCD
    success = true ∧ newLSU.storeBufferCount = 1 := by
  native_decide

/-! ## Test Category 2: Load Execution with Forwarding Hit -/

/-- Test: Load with forwarding hit (exact address match). -/
theorem test_load_forwarding_hit :
    let lsu := LSUState.empty
    -- Store to address 0x1000
    let (lsu1, _) := lsu.executeStore OpType.SW 0x1000 0 0x42
    -- Mark store as committed (needed for forwarding in some implementations)
    let lsu2 := lsu1.commitStore 0  -- Store buffer index 0
    -- Load from same address (should forward)
    let (_, result) := lsu2.executeLoad OpType.LW 0x1000 0 10
    result.isSome ∧ result.get!.1 = 10 ∧ result.get!.2 = 0x42 := by
  native_decide

/-- Test: Load with positive offset, forwarding hit. -/
theorem test_load_forwarding_positive_offset :
    let lsu := LSUState.empty
    -- Store to address 0x1000 + 100 = 0x1064
    let (lsu1, _) := lsu.executeStore OpType.SW 0x1000 100 0x99
    let lsu2 := lsu1.commitStore 0
    -- Load from same address (base=0x1000, offset=100)
    let (_, result) := lsu2.executeLoad OpType.LW 0x1000 100 20
    result.isSome ∧ result.get!.1 = 20 ∧ result.get!.2 = 0x99 := by
  native_decide

/-- Test: Load with negative offset, forwarding hit. -/
theorem test_load_forwarding_negative_offset :
    let lsu := LSUState.empty
    -- Store to address 0x1000 + (-100) = 0x0F9C
    let (lsu1, _) := lsu.executeStore OpType.SW 0x1000 (-100) 0x55
    let lsu2 := lsu1.commitStore 0
    -- Load from same address
    let (_, result) := lsu2.executeLoad OpType.LW 0x1000 (-100) 30
    result.isSome ∧ result.get!.1 = 30 ∧ result.get!.2 = 0x55 := by
  native_decide

/-! ## Test Category 3: Load Execution with Forwarding Miss -/

/-- Test: Load with forwarding miss (no matching store). -/
theorem test_load_forwarding_miss :
    let lsu := LSUState.empty
    -- Store to address 0x1000
    let (lsu1, _) := lsu.executeStore OpType.SW 0x1000 0 0x42
    let lsu2 := lsu1.commitStore 0
    -- Load from different address (should miss, create pending load)
    let (lsu3, result) := lsu2.executeLoad OpType.LW 0x2000 0 40
    result.isNone ∧ lsu3.hasPendingLoad := by
  native_decide

/-- Test: Load miss creates pending load with correct address. -/
theorem test_load_miss_pending_load_address :
    let lsu := LSUState.empty
    let (lsu1, result) := lsu.executeLoad OpType.LW 0x5000 0 50
    result.isNone ∧
    lsu1.pendingLoad.isSome ∧
    lsu1.pendingLoad.get!.address = 0x5000 ∧
    lsu1.pendingLoad.get!.dest_tag = 50 := by
  native_decide

/-- Test: Load stalls when another load is pending. -/
theorem test_load_stalls_on_pending_load :
    let lsu := LSUState.empty
    -- Issue first load (miss, creates pending load)
    let (lsu1, _) := lsu.executeLoad OpType.LW 0x1000 0 10
    -- Issue second load (should stall)
    let (lsu2, result2) := lsu1.executeLoad OpType.LW 0x2000 0 20
    result2.isNone ∧ lsu2.pendingLoad.isSome ∧
    lsu2.pendingLoad.get!.address = 0x1000  -- Still first load pending
    := by
  native_decide

/-! ## Test Category 4: Store Commitment -/

/-- Test: commitStore marks store as committed. -/
theorem test_commit_store_marks_committed :
    let lsu := LSUState.empty
    -- Enqueue a store at index 0
    let (lsu1, _) := lsu.executeStore OpType.SW 0x1000 0 0x42
    -- Commit the store
    let lsu2 := lsu1.commitStore 0
    -- Store buffer count unchanged (commit doesn't remove entry)
    lsu2.storeBufferCount = 1 := by
  native_decide

/-- Test: Multiple stores can be committed. -/
theorem test_commit_multiple_stores :
    let lsu := LSUState.empty
    let (lsu1, _) := lsu.executeStore OpType.SW 0x1000 0 0x10
    let (lsu2, _) := lsu1.executeStore OpType.SW 0x1004 0 0x20
    let lsu3 := lsu2.commitStore 0
    let lsu4 := lsu3.commitStore 1
    lsu4.storeBufferCount = 2 := by
  native_decide

/-! ## Test Category 5: Store Dequeue to Memory -/

/-- Test: dequeueStore with no committed stores returns none. -/
theorem test_dequeue_no_committed_stores :
    let lsu := LSUState.empty
    let (lsu1, _) := lsu.executeStore OpType.SW 0x1000 0 0x42
    -- Store not committed yet
    let (lsu2, result) := lsu1.dequeueStore
    result.isNone ∧ lsu2.storeBufferCount = 1 := by
  native_decide

/-- Test: dequeueStore with committed store succeeds. -/
theorem test_dequeue_committed_store_success :
    let lsu := LSUState.empty
    let (lsu1, _) := lsu.executeStore OpType.SW 0x1000 0 0x42
    let lsu2 := lsu1.commitStore 0  -- Commit store at index 0
    let (lsu3, result) := lsu2.dequeueStore
    result.isSome ∧
    result.get!.1 = 0x1000 ∧  -- Address
    result.get!.2.1 = 0x42 ∧  -- Data
    lsu3.storeBufferCount = 0  -- Entry removed
    := by
  native_decide

/-- Test: dequeueStore decrements count. -/
theorem test_dequeue_decrements_count :
    let lsu := LSUState.empty
    let (lsu1, _) := lsu.executeStore OpType.SW 0x1000 0 0x10
    let (lsu2, _) := lsu1.executeStore OpType.SW 0x1004 0 0x20
    let lsu3 := lsu2.commitStore 0  -- Commit first store
    let (lsu4, result) := lsu3.dequeueStore
    result.isSome ∧ lsu4.storeBufferCount = 1 := by
  native_decide

/-! ## Test Category 6: Load-Store Ordering (TSO) -/

/-- Test: Store then load to same address (forwarding). -/
theorem test_tso_store_then_load :
    let lsu := LSUState.empty
    -- Store
    let (lsu1, _) := lsu.executeStore OpType.SW 0x1000 0 0x42
    let lsu2 := lsu1.commitStore 0
    -- Load (should forward)
    let (_, result) := lsu2.executeLoad OpType.LW 0x1000 0 10
    result.isSome ∧ result.get!.2 = 0x42 := by
  native_decide

/-- Test: Multiple stores to same address (youngest wins). -/
theorem test_tso_youngest_store_wins :
    let lsu := LSUState.empty
    -- First store: addr=0x1000, data=0x10
    let (lsu1, _) := lsu.executeStore OpType.SW 0x1000 0 0x10
    let lsu2 := lsu1.commitStore 0
    -- Second store: addr=0x1000, data=0x20 (youngest)
    let (lsu3, _) := lsu2.executeStore OpType.SW 0x1000 0 0x20
    let lsu4 := lsu3.commitStore 1
    -- Load: should get youngest store data (0x20)
    let (_, result) := lsu4.executeLoad OpType.LW 0x1000 0 10
    result.isSome ∧ result.get!.2 = 0x20 := by
  native_decide

/-- Test: Load can bypass store to different address (TSO). -/
theorem test_tso_load_bypass_different_address :
    let lsu := LSUState.empty
    -- Store to 0x1000
    let (lsu1, _) := lsu.executeStore OpType.SW 0x1000 0 0x42
    -- Load from 0x2000 (different address, should miss and create pending load)
    let (lsu2, result) := lsu1.executeLoad OpType.LW 0x2000 0 10
    result.isNone ∧ lsu2.hasPendingLoad ∧ lsu2.storeBufferCount = 1 := by
  native_decide

/-! ## Test Category 7: Flush Handling -/

/-- Test: fullFlush clears store buffer. -/
theorem test_flush_clears_store_buffer :
    let lsu := createLSUWithStores 4
    let lsu2 := lsu.fullFlush
    lsu2.storeBufferEmpty := by
  native_decide

/-- Test: fullFlush clears pending load. -/
theorem test_flush_clears_pending_load :
    let lsu := LSUState.empty
    let (lsu1, _) := lsu.executeLoad OpType.LW 0x1000 0 10
    let lsu2 := lsu1.fullFlush
    !lsu2.hasPendingLoad := by
  native_decide

/-- Test: fullFlush clears both store buffer and pending load. -/
theorem test_flush_clears_all_state :
    let lsu := LSUState.empty
    let (lsu1, _) := lsu.executeStore OpType.SW 0x1000 0 0x42
    let (lsu2, _) := lsu1.executeLoad OpType.LW 0x2000 0 10
    let lsu3 := lsu2.fullFlush
    lsu3.storeBufferEmpty ∧ !lsu3.hasPendingLoad := by
  native_decide

/-! ## Test Category 8: Memory Response Processing -/

/-- Test: processMemoryResponse with pending load. -/
theorem test_process_memory_response_success :
    let lsu := LSUState.empty
    -- Issue load (miss, creates pending load)
    let (lsu1, _) := lsu.executeLoad OpType.LW 0x1000 0 10
    -- Memory responds with data
    let (lsu2, result) := lsu1.processMemoryResponse 0x99
    result.isSome ∧
    result.get!.1 = 10 ∧  -- dest_tag
    result.get!.2 = 0x99 ∧  -- data
    !lsu2.hasPendingLoad  -- Pending load cleared
    := by
  native_decide

/-- Test: processMemoryResponse with no pending load. -/
theorem test_process_memory_response_no_pending :
    let lsu := LSUState.empty
    let (lsu2, result) := lsu.processMemoryResponse 0x99
    result.isNone ∧ !lsu2.hasPendingLoad := by
  native_decide

/-- Test: Load byte with sign extension. -/
theorem test_load_byte_sign_extend :
    let lsu := LSUState.empty
    -- Store byte 0x80 (negative in signed interpretation)
    let (lsu1, _) := lsu.executeStore OpType.SB 0x1000 0 0x80
    let lsu2 := lsu1.commitStore 0
    -- Load byte signed (LB)
    let (_, result) := lsu2.executeLoad OpType.LB 0x1000 0 10
    -- After sign extension: 0x80 -> 0xFFFFFF80
    result.isSome ∧ result.get!.2 = 0xFFFFFF80 := by
  native_decide

/-- Test: Load byte unsigned (no sign extension). -/
theorem test_load_byte_unsigned :
    let lsu := LSUState.empty
    -- Store byte 0x80
    let (lsu1, _) := lsu.executeStore OpType.SB 0x1000 0 0x80
    let lsu2 := lsu1.commitStore 0
    -- Load byte unsigned (LBU)
    let (_, result) := lsu2.executeLoad OpType.LBU 0x1000 0 10
    -- No sign extension: 0x80 stays 0x80
    result.isSome ∧ result.get!.2 = 0x80 := by
  native_decide

/-! ## Test Category 9: Edge Cases -/

/-- Test: Zero offset store and load. -/
theorem test_zero_offset :
    let lsu := LSUState.empty
    let (lsu1, _) := lsu.executeStore OpType.SW 0x1000 0 0x42
    let lsu2 := lsu1.commitStore 0
    let (_, result) := lsu2.executeLoad OpType.LW 0x1000 0 10
    result.isSome ∧ result.get!.2 = 0x42 := by
  native_decide

/-- Test: Maximum positive offset wraparound. -/
theorem test_max_positive_offset :
    let lsu := LSUState.empty
    let (lsu1, _) := lsu.executeStore OpType.SW 0xFFFFFFFF 1 0x42
    -- Address wraps: 0xFFFFFFFF + 1 = 0
    let lsu2 := lsu1.commitStore 0
    let (_, result) := lsu2.executeLoad OpType.LW 0xFFFFFFFF 1 10
    result.isSome ∧ result.get!.2 = 0x42 := by
  native_decide

/-- Test: Store buffer queries (canAcceptStore). -/
theorem test_can_accept_store_empty :
    let lsu := LSUState.empty
    lsu.canAcceptStore = true := by
  native_decide

/-- Test: Store buffer queries (canAcceptStore full). -/
theorem test_cannot_accept_store_full :
    let lsu := createLSUWithStores 8
    lsu.canAcceptStore = false := by
  native_decide

/-- Test: Load queries (canAcceptLoad). -/
theorem test_can_accept_load_no_pending :
    let lsu := LSUState.empty
    lsu.canAcceptLoad = true := by
  native_decide

/-- Test: Load queries (canAcceptLoad with pending). -/
theorem test_cannot_accept_load_with_pending :
    let lsu := LSUState.empty
    let (lsu1, _) := lsu.executeLoad OpType.LW 0x1000 0 10
    lsu1.canAcceptLoad = false := by
  native_decide

end Shoumei.RISCV.Memory
