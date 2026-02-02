/-
RISCV/Memory/StoreBufferTest.lean - Concrete behavioral tests for Store Buffer

Tests the Store Buffer with concrete values to verify:
1. Enqueue (empty, tail index, pointer advance, field storage, full stall)
2. Commit (mark committed, uncommitted unchanged, idempotent)
3. Dequeue (committed head, pointer advance, count, skip uncommitted)
4. Forwarding (hit, miss, data, youngest-match, ignore invalid)
5. Flush (clear all, reset pointers)
6. FIFO ordering (in-order dequeue, wraparound)
7. Integration (concurrent ops, full sequences)

All tests use `native_decide` for concrete decidable verification.
-/

import Shoumei.RISCV.Memory.StoreBuffer

namespace Shoumei.RISCV.Memory.StoreBufferTest

open Shoumei.RISCV.Memory

/-! ## Enqueue Tests -/

/-- Test: Enqueue to empty buffer succeeds -/
theorem test_enqueue_to_empty :
  let (sb', idx) := StoreBufferState.empty.enqueue 0x1000 0xDEAD 2
  sb'.count == 1 ∧ idx == some 0 := by native_decide

/-- Test: Enqueue returns tail index -/
theorem test_enqueue_returns_tail :
  let (sb1, _) := StoreBufferState.empty.enqueue 0x1000 0xAA 2
  let (_, idx2) := sb1.enqueue 0x2000 0xBB 2
  idx2 == some 1 := by native_decide

/-- Test: Enqueue advances tail pointer -/
theorem test_enqueue_advances_tail :
  let (sb', _) := StoreBufferState.empty.enqueue 0x1000 0xDEAD 2
  sb'.tail == 1 ∧ sb'.head == 0 := by native_decide

/-- Test: Enqueued entry has correct fields -/
theorem test_enqueue_stores_fields :
  let (sb', _) := StoreBufferState.empty.enqueue 0x1000 0xDEAD 2
  let e := sb'.entries 0
  e.valid == true ∧ e.committed == false ∧
  e.address == 0x1000 ∧ e.data == 0xDEAD ∧ e.size.val == 2 := by native_decide

/-- Helper: fill all 8 store buffer entries. -/
private def filledSB8 : StoreBufferState :=
  let sb := StoreBufferState.empty
  let (sb, _) := sb.enqueue 0x1000 0x10 2
  let (sb, _) := sb.enqueue 0x1004 0x20 2
  let (sb, _) := sb.enqueue 0x1008 0x30 2
  let (sb, _) := sb.enqueue 0x100C 0x40 2
  let (sb, _) := sb.enqueue 0x1010 0x50 2
  let (sb, _) := sb.enqueue 0x1014 0x60 2
  let (sb, _) := sb.enqueue 0x1018 0x70 2
  let (sb, _) := sb.enqueue 0x101C 0x80 2
  sb

/-- Test: Full buffer stalls (returns none) -/
theorem test_full_stalls :
  let (_, idx) := filledSB8.enqueue 0x2000 0xFF 2
  idx == none := by native_decide

/-! ## Commit Tests -/

/-- Test: markCommitted sets committed flag -/
theorem test_mark_committed :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xAA 2
  let sb := sb.markCommitted 0
  (sb.entries 0).committed == true := by native_decide

/-- Test: Uncommitted entries unchanged after commit -/
theorem test_uncommitted_unchanged :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xAA 2
  let (sb, _) := sb.enqueue 0x2000 0xBB 2
  let sb := sb.markCommitted 0
  (sb.entries 1).committed == false := by native_decide

/-- Test: Commit specific index -/
theorem test_commit_specific_index :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xAA 2
  let (sb, _) := sb.enqueue 0x2000 0xBB 2
  let (sb, _) := sb.enqueue 0x3000 0xCC 2
  let sb := sb.markCommitted 1
  (sb.entries 0).committed == false ∧
  (sb.entries 1).committed == true ∧
  (sb.entries 2).committed == false := by native_decide

/-- Test: Double commit is idempotent -/
theorem test_double_commit_idempotent :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xAA 2
  let sb := sb.markCommitted 0
  let sb := sb.markCommitted 0
  (sb.entries 0).committed == true ∧ sb.count == 1 := by native_decide

/-! ## Dequeue Tests -/

/-- Test: Dequeue committed head entry -/
theorem test_dequeue_committed_head :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xDEAD 2
  let sb := sb.markCommitted 0
  let (_, entry) := sb.dequeue
  entry.isSome == true ∧
  (entry.get!).address == 0x1000 ∧
  (entry.get!).data == 0xDEAD ∧
  (entry.get!).size.val == 2 := by native_decide

/-- Test: Dequeue advances head pointer -/
theorem test_dequeue_advances_head :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xAA 2
  let sb := sb.markCommitted 0
  let (sb', _) := sb.dequeue
  sb'.head == 1 ∧ sb'.count == 0 := by native_decide

/-- Test: Dequeue decrements count -/
theorem test_dequeue_decrements_count :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xAA 2
  let (sb, _) := sb.enqueue 0x2000 0xBB 2
  let sb := sb.markCommitted 0
  let (sb', _) := sb.dequeue
  sb'.count == 1 := by native_decide

/-- Test: Dequeue skips uncommitted head -/
theorem test_dequeue_skips_uncommitted :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xAA 2
  let (_, entry) := sb.dequeue
  entry.isNone == true := by native_decide

/-- Test: Dequeue empty returns none -/
theorem test_dequeue_empty :
  let (_, entry) := StoreBufferState.empty.dequeue
  entry.isNone == true := by native_decide

/-! ## Forwarding Tests -/

/-- Test: Forward hit on exact address match -/
theorem test_fwd_hit_exact_address :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xDEAD 2
  sb.forwardCheck 0x1000 == some 0xDEAD := by native_decide

/-- Test: Forward miss on different address -/
theorem test_fwd_miss_different_address :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xDEAD 2
  sb.forwardCheck 0x2000 == none := by native_decide

/-- Test: Forward returns correct data -/
theorem test_fwd_returns_data :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0x12345678 2
  sb.forwardCheck 0x1000 == some 0x12345678 := by native_decide

/-- Test: Forward youngest-match (latest enqueued wins) -/
theorem test_fwd_youngest_match :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xAAAA 2
  let (sb, _) := sb.enqueue 0x2000 0xBBBB 2
  let (sb, _) := sb.enqueue 0x1000 0xCCCC 2  -- same address, newer data
  sb.forwardCheck 0x1000 == some 0xCCCC := by native_decide

/-- Test: Forward ignores invalid entries -/
theorem test_fwd_ignores_invalid :
  -- Enqueue, commit, dequeue (entry 0 becomes invalid), then forward check
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xAA 2
  let sb := sb.markCommitted 0
  let (sb, _) := sb.dequeue
  sb.forwardCheck 0x1000 == none := by native_decide

/-- Test: Forward after dequeue finds next match -/
theorem test_fwd_after_dequeue :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xAA 2
  let (sb, _) := sb.enqueue 0x1000 0xBB 2
  let sb := sb.markCommitted 0
  let (sb, _) := sb.dequeue
  sb.forwardCheck 0x1000 == some 0xBB := by native_decide

/-- Test: Forward matches both committed and uncommitted -/
theorem test_fwd_committed_and_uncommitted :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xAA 2  -- uncommitted
  let (sb, _) := sb.enqueue 0x1000 0xBB 2  -- uncommitted, younger
  let sb := sb.markCommitted 0
  -- Both entries match, youngest (0xBB) should win
  sb.forwardCheck 0x1000 == some 0xBB := by native_decide

/-- Test: Forward no valid entries returns none -/
theorem test_fwd_no_valid_entries :
  StoreBufferState.empty.forwardCheck 0x1000 == none := by native_decide

/-! ## Flush Tests -/

/-- Test: Flush clears all entries -/
theorem test_flush_clears_all :
  let sb := filledSB8
  let sb := sb.fullFlush
  sb.count == 0 ∧ sb.isEmpty := by native_decide

/-- Test: Flush resets pointers -/
theorem test_flush_resets_pointers :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xAA 2
  let (sb, _) := sb.enqueue 0x2000 0xBB 2
  let sb := sb.fullFlush
  sb.head == 0 ∧ sb.tail == 0 := by native_decide

/-- Test: Flush then enqueue works -/
theorem test_flush_then_enqueue :
  let sb := filledSB8
  let sb := sb.fullFlush
  let (sb, idx) := sb.enqueue 0x5000 0xFF 2
  sb.count == 1 ∧ idx == some 0 := by native_decide

/-! ## FIFO Ordering Tests -/

/-- Test: Enqueue A, B, C → dequeue in order A, B, C -/
theorem test_fifo_order :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xAA 2
  let (sb, _) := sb.enqueue 0x2000 0xBB 2
  let (sb, _) := sb.enqueue 0x3000 0xCC 2
  let sb := sb.markCommitted 0
  let sb := sb.markCommitted 1
  let sb := sb.markCommitted 2
  let (sb, e1) := sb.dequeue
  let (sb, e2) := sb.dequeue
  let (_, e3) := sb.dequeue
  e1.isSome == true ∧ e2.isSome == true ∧ e3.isSome == true ∧
  (e1.get!).data == 0xAA ∧ (e2.get!).data == 0xBB ∧ (e3.get!).data == 0xCC := by native_decide

/-- Test: Pointer wraparound (enqueue/dequeue past capacity) -/
theorem test_pointer_wraparound :
  -- Fill 4, commit and dequeue all, then enqueue 6 more (wraps past entry 7)
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0x10 2
  let (sb, _) := sb.enqueue 0x1004 0x20 2
  let (sb, _) := sb.enqueue 0x1008 0x30 2
  let (sb, _) := sb.enqueue 0x100C 0x40 2
  let sb := sb.markCommitted 0
  let sb := sb.markCommitted 1
  let sb := sb.markCommitted 2
  let sb := sb.markCommitted 3
  let (sb, _) := sb.dequeue
  let (sb, _) := sb.dequeue
  let (sb, _) := sb.dequeue
  let (sb, _) := sb.dequeue
  -- Now head=4, tail=4, count=0. Enqueue 6 to wrap around.
  let (sb, _) := sb.enqueue 0x2000 0x50 2
  let (sb, _) := sb.enqueue 0x2004 0x60 2
  let (sb, _) := sb.enqueue 0x2008 0x70 2
  let (sb, _) := sb.enqueue 0x200C 0x80 2
  let (sb, _) := sb.enqueue 0x2010 0x90 2  -- wraps to entry 1
  let (sb, _) := sb.enqueue 0x2014 0xA0 2  -- wraps to entry 2
  sb.count == 6 ∧ sb.head == 4 ∧ sb.tail == 2 := by native_decide

/-- Test: Commit out-of-order, dequeue still in FIFO order -/
theorem test_commit_ooo_dequeue_fifo :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xAA 2
  let (sb, _) := sb.enqueue 0x2000 0xBB 2
  let (sb, _) := sb.enqueue 0x3000 0xCC 2
  -- Commit out of order: 2, then 0, then 1
  let sb := sb.markCommitted 2
  let sb := sb.markCommitted 0
  let sb := sb.markCommitted 1
  -- Dequeue should still go head-first (entry 0, 1, 2)
  let (sb, e1) := sb.dequeue
  let (sb, e2) := sb.dequeue
  let (_, e3) := sb.dequeue
  e1.isSome == true ∧ e2.isSome == true ∧ e3.isSome == true ∧
  (e1.get!).data == 0xAA ∧ (e2.get!).data == 0xBB ∧ (e3.get!).data == 0xCC := by native_decide

/-- Test: Roundtrip preserves data -/
theorem test_roundtrip_preserves_data :
  let (sb, _) := StoreBufferState.empty.enqueue 0xCAFEBABE 0xDEADBEEF 2
  let sb := sb.markCommitted 0
  let (_, e) := sb.dequeue
  e.isSome == true ∧
  (e.get!).address == 0xCAFEBABE ∧ (e.get!).data == 0xDEADBEEF := by native_decide

/-! ## Integration Tests -/

/-- Test: Concurrent enqueue and dequeue -/
theorem test_concurrent_enq_deq :
  -- Enqueue 2 entries, commit and dequeue head, enqueue another
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xAA 2
  let (sb, _) := sb.enqueue 0x2000 0xBB 2
  let sb := sb.markCommitted 0
  let (sb, e) := sb.dequeue
  let (sb, idx) := sb.enqueue 0x3000 0xCC 2
  sb.count == 2 ∧
  idx == some 2 ∧
  e.isSome == true ∧ (e.get!).data == 0xAA := by native_decide

/-- Test: Forward during dequeue (uncommitted entry still forwarding) -/
theorem test_forward_during_dequeue :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xAA 2  -- committed
  let (sb, _) := sb.enqueue 0x2000 0xBB 2  -- uncommitted
  let sb := sb.markCommitted 0
  -- Forward should find 0x2000→0xBB (uncommitted but valid)
  -- Dequeue should give us entry 0 (0x1000→0xAA, committed)
  let fwd := sb.forwardCheck 0x2000
  let (_, deq) := sb.dequeue
  fwd == some 0xBB ∧
  deq.isSome == true ∧ (deq.get!).data == 0xAA := by native_decide

/-- Test: Full store-commit-forward-dequeue lifecycle -/
theorem test_full_lifecycle :
  let sb := StoreBufferState.empty
  -- 1. Enqueue store: sw x1, 0(x2) where address=0x1000, data=42
  let (sb, idx1) := sb.enqueue 0x1000 42 2
  -- 2. Forward check: load from 0x1000 should hit
  let fwd1 := sb.forwardCheck 0x1000
  -- 3. Commit (ROB retires store)
  let sb := sb.markCommitted 0
  -- 4. Forward still works after commit
  let fwd2 := sb.forwardCheck 0x1000
  -- 5. Dequeue (memory write)
  let (sb, deq) := sb.dequeue
  -- 6. Forward misses after dequeue
  let fwd3 := sb.forwardCheck 0x1000
  idx1 == some 0 ∧
  fwd1 == some 42 ∧
  fwd2 == some 42 ∧
  sb.count == 0 ∧
  fwd3 == none ∧
  deq.isSome == true ∧ (deq.get!).data == 42 := by native_decide

/-- Test: Full buffer forward still works -/
theorem test_full_buffer_forward :
  let sb := filledSB8
  -- Forward should find the entry at 0x1000 (entry 0)
  sb.forwardCheck 0x1000 == some 0x10 := by native_decide

/-- Test: Size field preserved through lifecycle -/
theorem test_size_field_lifecycle :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xAA 0  -- byte
  let (sb, _) := sb.enqueue 0x2000 0xBB 1  -- half
  let (sb, _) := sb.enqueue 0x3000 0xCC 2  -- word
  let sb := sb.markCommitted 0
  let sb := sb.markCommitted 1
  let sb := sb.markCommitted 2
  let (sb, e1) := sb.dequeue
  let (sb, e2) := sb.dequeue
  let (_, e3) := sb.dequeue
  e1.isSome == true ∧ e2.isSome == true ∧ e3.isSome == true ∧
  (e1.get!).size.val == 0 ∧ (e2.get!).size.val == 1 ∧ (e3.get!).size.val == 2 := by native_decide

/-! ## State Query Tests -/

/-- Test: isEmpty on empty buffer -/
theorem test_isEmpty_true : StoreBufferState.empty.isEmpty == true := by native_decide

/-- Test: isEmpty after enqueue -/
theorem test_isEmpty_after_enqueue :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xAA 2
  sb.isEmpty == false := by native_decide

/-- Test: isFull on full buffer -/
theorem test_isFull_true : filledSB8.isFull == true := by native_decide

/-- Test: isFull on non-full buffer -/
theorem test_isFull_false :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xAA 2
  sb.isFull == false := by native_decide

/-- Test: headReady false when uncommitted -/
theorem test_headReady_uncommitted :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xAA 2
  sb.headReady == false := by native_decide

/-- Test: headReady true when committed -/
theorem test_headReady_committed :
  let (sb, _) := StoreBufferState.empty.enqueue 0x1000 0xAA 2
  let sb := sb.markCommitted 0
  sb.headReady == true := by native_decide

end Shoumei.RISCV.Memory.StoreBufferTest
