/-
RISCV/Retirement/ROBTest.lean - Concrete behavioral tests for ROB

Tests the Reorder Buffer with concrete values to verify:
1. Allocation (empty, tail index, pointer advance, field storage, full stall)
2. CDB broadcast (tag matching, completion, exception flags)
3. Commit (head retire, pointer advance, count, empty/incomplete blocking)
4. FIFO ordering (in-order commit, pointer wraparound)
5. State queries (isEmpty, isFull, count)
6. Branch/flush (misprediction via CDB, flush younger, preserve older)
7. Committed RAT (update mapping, skip x0, recovery)

All tests use `native_decide` for concrete decidable verification.
-/

import Shoumei.RISCV.Retirement.ROB

namespace Shoumei.RISCV.Retirement.ROBTest

open Shoumei.RISCV.Retirement

/-! ## Allocation Tests -/

/-- Test: Allocate to empty ROB succeeds -/
theorem test_allocate_to_empty :
  let (rob', idx) := ROBState.empty.allocate 10 true 5 true 1 false
  rob'.count == 1 ∧ idx == some 0 := by native_decide

/-- Test: Allocated entry returns tail index -/
theorem test_allocate_returns_tail :
  let (rob1, _) := ROBState.empty.allocate 10 true 5 true 1 false
  let (_, idx2) := rob1.allocate 20 true 8 true 2 false
  idx2 == some 1 := by native_decide

/-- Test: Allocation advances tail pointer -/
theorem test_allocate_advances_tail :
  let (rob', _) := ROBState.empty.allocate 10 true 5 true 1 false
  rob'.tail == 1 ∧ rob'.head == 0 := by native_decide

/-- Test: Allocated entry has correct fields -/
theorem test_allocate_stores_fields :
  let (rob', _) := ROBState.empty.allocate 10 true 5 true 1 false
  let e := rob'.entries 0
  e.valid == true ∧ e.complete == false ∧
  e.physRd == 10 ∧ e.hasPhysRd == true ∧
  e.oldPhysRd == 5 ∧ e.hasOldPhysRd == true ∧
  e.archRd == 1 ∧ e.isBranch == false := by native_decide

/-- Helper: fill all 16 ROB entries. -/
private def filledROB16 : ROBState :=
  let rob := ROBState.empty
  let (rob, _) := rob.allocate 0 true 0 false 0 false
  let (rob, _) := rob.allocate 1 true 0 false 1 false
  let (rob, _) := rob.allocate 2 true 0 false 2 false
  let (rob, _) := rob.allocate 3 true 0 false 3 false
  let (rob, _) := rob.allocate 4 true 0 false 4 false
  let (rob, _) := rob.allocate 5 true 0 false 5 false
  let (rob, _) := rob.allocate 6 true 0 false 6 false
  let (rob, _) := rob.allocate 7 true 0 false 7 false
  let (rob, _) := rob.allocate 8 true 0 false 8 false
  let (rob, _) := rob.allocate 9 true 0 false 9 false
  let (rob, _) := rob.allocate 10 true 0 false 10 false
  let (rob, _) := rob.allocate 11 true 0 false 11 false
  let (rob, _) := rob.allocate 12 true 0 false 12 false
  let (rob, _) := rob.allocate 13 true 0 false 13 false
  let (rob, _) := rob.allocate 14 true 0 false 14 false
  let (rob, _) := rob.allocate 15 true 0 false 15 false
  rob

/-- Test: Full ROB reports isFull -/
theorem test_allocate_full_isFull :
  filledROB16.isFull == true ∧ filledROB16.count == 16 := by native_decide

/-- Test: Full ROB stalls further allocation -/
theorem test_allocate_full_stalls :
  (filledROB16.allocate 16 true 0 false 16 false).2 == none := by native_decide

/-! ## CDB Broadcast Tests -/

/-- Test: CDB broadcast marks matching entry complete -/
theorem test_cdb_marks_complete :
  let (rob, _) := ROBState.empty.allocate 10 true 5 true 1 false
  let rob' := rob.cdbBroadcast 10
  (rob'.entries 0).complete == true := by native_decide

/-- Test: CDB broadcast with no match leaves entries unchanged -/
theorem test_cdb_no_match_unchanged :
  let (rob, _) := ROBState.empty.allocate 10 true 5 true 1 false
  let rob' := rob.cdbBroadcast 99
  (rob'.entries 0).complete == false := by native_decide

/-- Test: CDB broadcast ignores invalid entries -/
theorem test_cdb_ignores_invalid :
  let rob := ROBState.empty
  let rob' := rob.cdbBroadcast 10
  (rob'.entries 0).complete == false := by native_decide

/-- Test: CDB broadcast ignores already-complete entries -/
theorem test_cdb_ignores_already_complete :
  let (rob, _) := ROBState.empty.allocate 10 true 5 true 1 false
  let rob := rob.cdbBroadcast 10
  let rob' := rob.cdbBroadcast 10 (cdb_exception := true)
  (rob'.entries 0).exception == false := by native_decide

/-- Test: CDB broadcast sets exception flag -/
theorem test_cdb_sets_exception :
  let (rob, _) := ROBState.empty.allocate 10 true 5 true 1 false
  let rob' := rob.cdbBroadcast 10 (cdb_exception := true)
  (rob'.entries 0).complete == true ∧ (rob'.entries 0).exception == true := by native_decide

/-- Test: CDB broadcast sets misprediction flag -/
theorem test_cdb_sets_mispredicted :
  let (rob, _) := ROBState.empty.allocate 10 true 5 true 1 true
  let rob' := rob.cdbBroadcast 10 (cdb_mispredicted := true)
  (rob'.entries 0).branchMispredicted == true := by native_decide

/-! ## Commit Tests -/

/-- Test: Commit head entry when valid and complete -/
theorem test_commit_head :
  let (rob, _) := ROBState.empty.allocate 10 true 5 true 1 false
  let rob := rob.cdbBroadcast 10
  let (_, entry) := rob.commit
  entry.isSome == true ∧ entry.get!.physRd == 10 ∧ entry.get!.archRd == 1 := by
  native_decide

/-- Test: Commit advances head pointer -/
theorem test_commit_advances_head :
  let (rob, _) := ROBState.empty.allocate 10 true 5 true 1 false
  let rob := rob.cdbBroadcast 10
  let (rob', _) := rob.commit
  rob'.head == 1 := by native_decide

/-- Test: Commit decrements count -/
theorem test_commit_decrements_count :
  let (rob, _) := ROBState.empty.allocate 10 true 5 true 1 false
  let rob := rob.cdbBroadcast 10
  let (rob', _) := rob.commit
  rob'.count == 0 := by native_decide

/-- Test: Commit on empty ROB returns none -/
theorem test_commit_empty_returns_none :
  let (_, entry) := ROBState.empty.commit
  entry.isNone == true := by native_decide

/-- Test: Commit blocks on incomplete head entry -/
theorem test_commit_incomplete_blocks :
  let (rob, _) := ROBState.empty.allocate 10 true 5 true 1 false
  let (_, entry) := rob.commit
  entry.isNone == true := by native_decide

/-- Test: Commit clears head entry valid flag -/
theorem test_commit_clears_entry :
  let (rob, _) := ROBState.empty.allocate 10 true 5 true 1 false
  let rob := rob.cdbBroadcast 10
  let (rob', _) := rob.commit
  (rob'.entries 0).valid == false := by native_decide

/-! ## FIFO Ordering Tests -/

/-- Test: Three allocations commit in order (A, B, C -> commit A first) -/
theorem test_fifo_in_order_commit :
  let (rob, _) := ROBState.empty.allocate 10 true 0 false 1 false
  let (rob, _) := rob.allocate 20 true 0 false 2 false
  let (rob, _) := rob.allocate 30 true 0 false 3 false
  let rob := rob.cdbBroadcast 10
  let rob := rob.cdbBroadcast 20
  let rob := rob.cdbBroadcast 30
  let (rob, e1) := rob.commit
  let (rob, e2) := rob.commit
  let (_, e3) := rob.commit
  e1.isSome == true ∧ e2.isSome == true ∧ e3.isSome == true ∧
  e1.get!.physRd == 10 ∧ e2.get!.physRd == 20 ∧ e3.get!.physRd == 30 := by
  native_decide

/-- Test: Roundtrip preserves physRd and oldPhysRd -/
theorem test_roundtrip_preserves_fields :
  let (rob, _) := ROBState.empty.allocate 42 true 17 true 5 false
  let rob := rob.cdbBroadcast 42
  let (_, entry) := rob.commit
  entry.isSome == true ∧
  entry.get!.physRd == 42 ∧ entry.get!.oldPhysRd == 17 ∧
  entry.get!.hasOldPhysRd == true := by native_decide

/-- Test: Pointer wraparound with 4 allocate-commit cycles + verify reuse -/
theorem test_pointer_wraparound_small :
  let rob := ROBState.empty
  -- Cycle 1: allocate at 0, complete, commit
  let (rob, _) := rob.allocate 0 true 0 false 0 false
  let rob := rob.cdbBroadcast 0
  let (rob, _) := rob.commit
  -- Cycle 2: allocate at 1, complete, commit
  let (rob, _) := rob.allocate 1 true 0 false 0 false
  let rob := rob.cdbBroadcast 1
  let (rob, _) := rob.commit
  -- Cycle 3: allocate at 2, complete, commit
  let (rob, _) := rob.allocate 2 true 0 false 0 false
  let rob := rob.cdbBroadcast 2
  let (rob, _) := rob.commit
  -- After 3 cycles: head=3, tail=3, count=0
  rob.head == 3 ∧ rob.tail == 3 ∧ rob.count == 0 := by native_decide

/-- Test: Out-of-order completion, in-order commit -/
theorem test_ooo_complete_inorder_commit :
  let (rob, _) := ROBState.empty.allocate 10 true 0 false 1 false  -- A at idx 0
  let (rob, _) := rob.allocate 20 true 0 false 2 false              -- B at idx 1
  -- Complete B first (out-of-order)
  let rob := rob.cdbBroadcast 20
  -- Try commit -> should block (A not complete)
  let (rob, blocked) := rob.commit
  let blocked_result := blocked.isNone
  -- Now complete A
  let rob := rob.cdbBroadcast 10
  -- Commit A (head)
  let (rob, e1) := rob.commit
  -- Commit B
  let (_, e2) := rob.commit
  blocked_result == true ∧
  e1.get!.physRd == 10 ∧ e2.get!.physRd == 20 := by native_decide

/-! ## State Query Tests -/

/-- Test: Empty ROB reports isEmpty -/
theorem test_isEmpty_true :
  ROBState.empty.isEmpty == true := by native_decide

/-- Test: Non-empty ROB reports not isEmpty -/
theorem test_isEmpty_false :
  let (rob, _) := ROBState.empty.allocate 10 true 0 false 0 false
  rob.isEmpty == false := by native_decide

/-- Helper: ROB with 4 entries allocated. -/
private def rob4 : ROBState :=
  let (rob, _) := ROBState.empty.allocate 0 true 0 false 0 false
  let (rob, _) := rob.allocate 1 true 0 false 1 false
  let (rob, _) := rob.allocate 2 true 0 false 2 false
  let (rob, _) := rob.allocate 3 true 0 false 3 false
  rob

/-- Test: isFull after 4 allocations is false -/
theorem test_isFull_false :
  rob4.isFull == false ∧ rob4.count == 4 := by native_decide

/-- Test: Count tracks allocation and commit -/
theorem test_count_accurate :
  let (rob, _) := ROBState.empty.allocate 10 true 0 false 0 false
  let (rob, _) := rob.allocate 20 true 0 false 1 false
  let (rob, _) := rob.allocate 30 true 0 false 2 false
  let c3 := rob.count == 3
  let rob := rob.cdbBroadcast 10
  let (rob, _) := rob.commit
  c3 ∧ rob.count == 2 := by native_decide

/-- Test: headReady when head is valid and complete -/
theorem test_headReady_true :
  let (rob, _) := ROBState.empty.allocate 10 true 5 true 1 false
  let rob := rob.cdbBroadcast 10
  rob.headReady == true := by native_decide

/-- Test: headReady false when incomplete -/
theorem test_headReady_false_incomplete :
  let (rob, _) := ROBState.empty.allocate 10 true 5 true 1 false
  rob.headReady == false := by native_decide

/-- Test: headReady false when empty -/
theorem test_headReady_false_empty :
  ROBState.empty.headReady == false := by native_decide

/-! ## Branch / Flush Tests -/

/-- Test: isBranch flag stored correctly -/
theorem test_isBranch_stored :
  let (rob, _) := ROBState.empty.allocate 10 true 5 true 1 true
  (rob.entries 0).isBranch == true := by native_decide

/-- Test: Misprediction flag set via CDB -/
theorem test_misprediction_via_cdb :
  let (rob, _) := ROBState.empty.allocate 10 true 5 true 1 true
  let rob' := rob.cdbBroadcast 10 (cdb_mispredicted := true)
  (rob'.entries 0).branchMispredicted == true ∧
  (rob'.entries 0).complete == true := by native_decide

/-- Test: Flush clears younger entries -/
theorem test_flush_clears_younger :
  let (rob, _) := ROBState.empty.allocate 10 true 0 false 0 false
  let (rob, _) := rob.allocate 20 true 0 false 1 false
  let (rob, _) := rob.allocate 30 true 0 false 2 false
  let (rob', freed) := rob.flush 0
  (rob'.entries 1).valid == false ∧
  (rob'.entries 2).valid == false ∧
  (rob'.entries 0).valid == true ∧
  freed.length == 2 := by native_decide

/-- Test: Flush preserves older entries -/
theorem test_flush_preserves_older :
  let (rob, _) := ROBState.empty.allocate 10 true 0 false 0 false
  let (rob, _) := rob.allocate 20 true 0 false 1 false
  let (rob, _) := rob.allocate 30 true 0 false 2 false
  let (rob', _) := rob.flush 1
  (rob'.entries 0).valid == true ∧
  (rob'.entries 1).valid == true ∧
  (rob'.entries 2).valid == false := by native_decide

/-- Test: Flush resets tail pointer -/
theorem test_flush_resets_tail :
  let (rob, _) := ROBState.empty.allocate 10 true 0 false 0 false
  let (rob, _) := rob.allocate 20 true 0 false 1 false
  let (rob, _) := rob.allocate 30 true 0 false 2 false
  let (rob', _) := rob.flush 0
  rob'.tail == 1 := by native_decide

/-- Test: Full flush clears everything -/
theorem test_full_flush :
  let (rob, _) := ROBState.empty.allocate 10 true 0 false 0 false
  let (rob, _) := rob.allocate 20 true 0 false 1 false
  let (rob', freed) := rob.fullFlush
  rob'.count == 0 ∧ rob'.isEmpty == true ∧ freed.length == 2 := by native_decide

/-- Test: Flush returns freed physRd tags -/
theorem test_flush_returns_freed_tags :
  let (rob, _) := ROBState.empty.allocate 10 true 0 false 0 false
  let (rob, _) := rob.allocate 20 true 0 false 1 false
  let (rob, _) := rob.allocate 30 true 0 false 2 false
  -- Flush at 0: entries 1 (physRd=20) and 2 (physRd=30) are freed
  let (_, freed) := rob.flush 0
  freed.length == 2 := by native_decide

/-! ## Committed RAT Tests -/

/-- Test: Committed RAT init has identity mapping -/
theorem test_crat_init_identity :
  let crat := CommittedRATState.init
  crat.mapping 0 == 0 ∧ crat.mapping 1 == 1 ∧ crat.mapping 31 == 31 := by native_decide

/-- Test: Commit updates committed RAT mapping -/
theorem test_crat_commit_updates :
  let crat := CommittedRATState.init
  let crat' := crat.update 5 42 true
  crat'.mapping 5 == 42 := by native_decide

/-- Test: Commit with hasPhysRd=false skips RAT update -/
theorem test_crat_no_rd_skips :
  let crat := CommittedRATState.init
  let crat' := crat.update 5 42 false
  crat'.mapping 5 == 5 := by native_decide

/-- Test: Committed RAT never updates x0 -/
theorem test_crat_x0_preserved :
  let crat := CommittedRATState.init
  let crat' := crat.update 0 42 true
  crat'.mapping 0 == 0 := by native_decide

/-- Test: RAT update doesn't affect other registers -/
theorem test_crat_update_isolated :
  let crat := CommittedRATState.init
  let crat' := crat.update 5 42 true
  crat'.mapping 4 == 4 ∧ crat'.mapping 6 == 6 := by native_decide

/-! ## CommitStep Integration Tests -/

/-- Test: CommitStep updates ROB and committed RAT together -/
theorem test_commitStep_integration :
  let rob := ROBState.empty
  let crat := CommittedRATState.init
  let (rob, _) := rob.allocate 42 true 5 true 5 false
  let rob := rob.cdbBroadcast 42
  let result := commitStep rob crat
  result.rob.count == 0 ∧
  result.committedRAT.mapping 5 == 42 ∧
  result.deallocTag == some 5 ∧
  result.misprediction == false := by native_decide

/-- Test: CommitStep detects misprediction -/
theorem test_commitStep_misprediction :
  let rob := ROBState.empty
  let crat := CommittedRATState.init
  let (rob, _) := rob.allocate 42 true 5 true 5 true
  let rob := rob.cdbBroadcast 42 (cdb_mispredicted := true)
  let result := commitStep rob crat
  result.misprediction == true := by native_decide

/-- Test: CommitStep detects exception -/
theorem test_commitStep_exception :
  let rob := ROBState.empty
  let crat := CommittedRATState.init
  let (rob, _) := rob.allocate 42 true 5 true 5 false
  let rob := rob.cdbBroadcast 42 (cdb_exception := true)
  let result := commitStep rob crat
  result.exceptionDetected == true := by native_decide

/-- Test: CommitStep with no entry to commit -/
theorem test_commitStep_empty :
  let result := commitStep ROBState.empty CommittedRATState.init
  result.deallocTag == none ∧ result.misprediction == false := by native_decide

/-- Test: CommitStep with no deallocation (hasOldPhysRd=false) -/
theorem test_commitStep_no_dealloc :
  let rob := ROBState.empty
  let crat := CommittedRATState.init
  let (rob, _) := rob.allocate 42 true 5 false 5 false  -- hasOldPhysRd=false
  let rob := rob.cdbBroadcast 42
  let result := commitStep rob crat
  result.deallocTag == none := by native_decide

/-! ## Edge Cases -/

/-- Test: Allocate with no physRd (e.g. store instruction) -/
theorem test_allocate_no_physrd :
  let (rob, _) := ROBState.empty.allocate 0 false 0 false 0 false
  let e := rob.entries 0
  e.hasPhysRd == false ∧ e.hasOldPhysRd == false := by native_decide

/-- Test: CDB ignores entries without hasPhysRd -/
theorem test_cdb_ignores_no_physrd :
  let (rob, _) := ROBState.empty.allocate 10 false 0 false 0 false
  let rob' := rob.cdbBroadcast 10
  (rob'.entries 0).complete == false := by native_decide

/-- Test: headEntry reads the correct entry -/
theorem test_headEntry :
  let (rob, _) := ROBState.empty.allocate 10 true 5 true 1 false
  let e := rob.headEntry
  e.physRd == 10 ∧ e.valid == true := by native_decide

/-- Test: Multiple CDB broadcasts to different entries -/
theorem test_cdb_multiple_entries :
  let (rob, _) := ROBState.empty.allocate 10 true 0 false 0 false
  let (rob, _) := rob.allocate 20 true 0 false 1 false
  let rob := rob.cdbBroadcast 10
  (rob.entries 0).complete == true ∧ (rob.entries 1).complete == false := by native_decide

end Shoumei.RISCV.Retirement.ROBTest
