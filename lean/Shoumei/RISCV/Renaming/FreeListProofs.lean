/-
RISCV/Renaming/FreeListProofs.lean - Proofs for Free Physical Register List

Structural proofs:
- Circuit name, gate counts, port counts, instance counts

Behavioral proofs:
- Initialization correctness (count, first tag, FIFO ordering)
- Allocation returns tags in FIFO order
- Deallocation adds tags back to the pool
- Underflow protection (allocate from empty returns None)
- FIFO ordering after deallocate (freed tags go to back of queue)
- Peek consistency with allocate
-/

import Shoumei.RISCV.Renaming.FreeList

namespace Shoumei.RISCV.Renaming.FreeListProofs

open Shoumei
open Shoumei.RISCV.Renaming

/-! ## Structural Proofs -/

/-- FreeList64 has the expected module name -/
theorem freelist64_name : mkFreeList64.name = "FreeList_64" := by native_decide

/-- FreeList64 input count:
    enq_data(6) + enq_valid(1) + deq_ready(1) + clock(1) + reset(1) + zero(1) + one(1) = 12 -/
theorem freelist64_input_count : mkFreeList64.inputs.length = 12 := by native_decide

/-- FreeList64 output count:
    enq_ready(1) + deq_data(6) + deq_valid(1) = 8 -/
theorem freelist64_output_count : mkFreeList64.outputs.length = 8 := by native_decide

/-- FreeList64 gate count:
    empty detection(14) + full detection(14) + handshaking(4) = 32 -/
theorem freelist64_gate_count : mkFreeList64.gates.length = 32 := by native_decide

/-- FreeList64 has 4 submodule instances (RAM + 2 pointers + counter) -/
theorem freelist64_instance_count : mkFreeList64.instances.length = 4 := by native_decide

/-! ## Behavioral Proofs: 4-register configuration -/

/-- Initial 4-reg free list has 2 available registers -/
theorem freelist4_init_count : mkFreeList4Init.count = 2 := by native_decide

/-- Initial 4-reg free list is not empty -/
theorem freelist4_init_not_empty : mkFreeList4Init.isEmpty = false := by native_decide

/-- Initial 4-reg free list is not full -/
theorem freelist4_init_not_full : mkFreeList4Init.isFull = false := by native_decide

/-- First allocation from 4-reg free list returns register 2 -/
theorem freelist4_first_alloc :
    mkFreeList4Init.allocate.2 = some ⟨2, by omega⟩ := by native_decide

/-- Second allocation returns register 3 (FIFO order) -/
theorem freelist4_second_alloc :
    let (fl1, _) := mkFreeList4Init.allocate
    fl1.allocate.2 = some ⟨3, by omega⟩ := by native_decide

/-- After two allocations, free list is empty -/
theorem freelist4_exhausted :
    let (fl1, _) := mkFreeList4Init.allocate
    let (fl2, _) := fl1.allocate
    fl2.isEmpty = true ∧ fl2.count = 0 := by native_decide

/-- Cannot allocate from exhausted free list (underflow protection) -/
theorem freelist4_underflow :
    let (fl1, _) := mkFreeList4Init.allocate
    let (fl2, _) := fl1.allocate
    fl2.allocate.2 = none := by native_decide

/-- Deallocate a tag, then allocate it back (roundtrip through empty queue) -/
theorem freelist4_dealloc_alloc_roundtrip :
    let (fl1, _) := mkFreeList4Init.allocate  -- alloc 2, queue = [3]
    let (fl2, _) := fl1.allocate              -- alloc 3, queue = []
    let fl3 := fl2.deallocate ⟨2, by omega⟩  -- free 2, queue = [2]
    fl3.allocate.2 = some ⟨2, by omega⟩ := by native_decide

/-- Deallocating increases count -/
theorem freelist4_dealloc_count :
    let (fl1, _) := mkFreeList4Init.allocate  -- count: 2 → 1
    let fl2 := fl1.deallocate ⟨0, by omega⟩  -- free reg 0, count: 1 → 2
    fl2.count = 2 := by native_decide

/-- FIFO ordering: deallocated tags go to the back of the queue -/
theorem freelist4_fifo_after_dealloc :
    let (fl1, _) := mkFreeList4Init.allocate  -- alloc 2, queue = [3]
    let fl2 := fl1.deallocate ⟨0, by omega⟩  -- free 0, queue = [3, 0]
    let (fl3, first) := fl2.allocate          -- alloc 3, queue = [0]
    let (_, second) := fl3.allocate           -- alloc 0, queue = []
    first = some ⟨3, by omega⟩ ∧ second = some ⟨0, by omega⟩ := by native_decide

/-- Peek returns same value as next allocation -/
theorem freelist4_peek_matches_alloc :
    mkFreeList4Init.peek = mkFreeList4Init.allocate.2 := by native_decide

/-! ## Behavioral Proofs: 8-register configuration -/

/-- Initial 8-reg free list has 4 available registers -/
theorem freelist8_init_count : mkFreeList8Init.count = 4 := by native_decide

/-- 8-reg free list allocations return registers 4, 5, 6, 7 in order -/
theorem freelist8_alloc_sequence :
    let (fl1, t1) := mkFreeList8Init.allocate
    let (fl2, t2) := fl1.allocate
    let (fl3, t3) := fl2.allocate
    let (_, t4) := fl3.allocate
    t1 = some ⟨4, by omega⟩ ∧
    t2 = some ⟨5, by omega⟩ ∧
    t3 = some ⟨6, by omega⟩ ∧
    t4 = some ⟨7, by omega⟩ := by native_decide

/-- 8-reg free list: deallocate then allocate preserves FIFO -/
theorem freelist8_dealloc_fifo :
    let (fl1, _) := mkFreeList8Init.allocate  -- alloc 4, queue = [5,6,7]
    let fl2 := fl1.deallocate ⟨4, by omega⟩  -- free 4, queue = [5,6,7,4]
    let (_, next) := fl2.allocate             -- alloc 5 (FIFO: 4 goes to back)
    next = some ⟨5, by omega⟩ := by native_decide

/-! ## Behavioral Proofs: 64-register standard configuration -/

/-- Initial 64-reg free list has 32 available registers (32-63) -/
theorem freelist64_init_count : mkFreeList64Init.count = 32 := by native_decide

/-- Initial 64-reg free list is not empty -/
theorem freelist64_init_not_empty : mkFreeList64Init.isEmpty = false := by native_decide

/-- Initial 64-reg free list is not full -/
theorem freelist64_init_not_full : mkFreeList64Init.isFull = false := by native_decide

/-- First allocation from 64-reg free list returns register 32 -/
theorem freelist64_first_alloc :
    mkFreeList64Init.allocate.2 = some ⟨32, by omega⟩ := by native_decide

/-- Peek returns same as first allocate -/
theorem freelist64_peek_matches_alloc :
    mkFreeList64Init.peek = mkFreeList64Init.allocate.2 := by native_decide

/-- After one allocation, count decreases to 31 -/
theorem freelist64_alloc_decrements_count :
    mkFreeList64Init.allocate.1.count = 31 := by native_decide

/-- Second allocation returns register 33 -/
theorem freelist64_second_alloc :
    let (fl1, _) := mkFreeList64Init.allocate
    fl1.allocate.2 = some ⟨33, by omega⟩ := by native_decide

end Shoumei.RISCV.Renaming.FreeListProofs
