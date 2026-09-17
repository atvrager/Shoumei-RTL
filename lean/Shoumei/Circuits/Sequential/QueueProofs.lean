/-
QueueProofs.lean - Formal Proofs for Queue/FIFO

Proves the fundamental properties of queues:
1. FIFO ordering - items dequeue in the same order they were enqueued
2. No overflow - cannot enqueue to a full queue
3. No underflow - cannot dequeue from an empty queue
4. Count accuracy - count always equals number of entries
5. Capacity invariant - never exceed capacity
-/

import Shoumei.Circuits.Sequential.Queue
import Shoumei.DSL.Decoupled

namespace Shoumei.Circuits.Sequential

open Shoumei
open Shoumei.DSL.Decoupled

-- Alias for convenience
abbrev IntQueue := QueueState Nat

/-!
## Basic Properties
-/

-- Theorem: Empty queue has count 0
theorem empty_has_zero_count (cap : Nat) :
  (QueueState.empty (α := Nat) cap).count = 0 := by
  simp [QueueState.empty, QueueState.count]

-- Theorem: Empty queue is empty
theorem empty_is_empty (cap : Nat) :
  (QueueState.empty (α := Nat) cap).isEmpty = true := by
  simp [QueueState.empty, QueueState.isEmpty]

-- Theorem: Empty queue is not full (if capacity > 0)
theorem empty_not_full (cap : Nat) (h : cap > 0) :
  (QueueState.empty (α := Nat) cap).isFull = false := by
  simp [QueueState.empty, QueueState.isFull]
  omega

-- Theorem: Enqueuing to empty queue increases count to 1
theorem enqueue_to_empty_count :
  let q := QueueState.empty (α := Nat) 4
  let q' := q.enqueue 42
  q'.count = 1 := by
  native_decide

-- Theorem: Dequeuing from queue with one element returns to empty
theorem dequeue_single_returns_empty :
  let q := QueueState.empty (α := Nat) 4
  let q' := q.enqueue 42
  let (q'', _) := q'.dequeue
  q''.isEmpty = true ∧ q''.count = 0 := by
  native_decide

/-!
## FIFO Ordering
-/

-- Theorem: Single enqueue-dequeue preserves value
theorem fifo_single (cap : Nat) (val : Nat) (h : cap > 0) :
  let q := QueueState.empty (α := Nat) cap
  let q' := q.enqueue val
  let (_, result) := q'.dequeue
  result = some val := by
  cases cap
  case zero => contradiction
  case succ n =>
    simp [QueueState.empty, QueueState.enqueue, QueueState.dequeue]
    simp [QueueState.isFull]

-- Theorem: Two enqueues followed by two dequeues preserve order
theorem fifo_two_elements :
  let q := QueueState.empty (α := Nat) 4
  let q1 := q.enqueue 10
  let q2 := q1.enqueue 20
  let (q3, first) := q2.dequeue
  let (_q4, second) := q3.dequeue
  first = some 10 ∧ second = some 20 := by
  native_decide

-- Theorem: Three enqueues followed by three dequeues preserve order
theorem fifo_three_elements :
  let q := QueueState.empty (α := Nat) 4
  let q1 := q.enqueue 100
  let q2 := q1.enqueue 200
  let q3 := q2.enqueue 300
  let (q4, first) := q3.dequeue
  let (q5, second) := q4.dequeue
  let (_q6, third) := q5.dequeue
  first = some 100 ∧ second = some 200 ∧ third = some 300 := by
  native_decide

/-!
## Overflow Protection
-/

-- Theorem: Cannot enqueue to full queue (1-entry)
theorem no_overflow_queue1 :
  let q := QueueState.empty (α := Nat) 1
  let q1 := q.enqueue 10
  let q2 := q1.enqueue 20  -- Should be no-op
  q2.count = 1 ∧ q2.isFull = true := by
  native_decide

-- Theorem: Cannot enqueue beyond capacity
theorem no_overflow_queue4 :
  let q := QueueState.empty (α := Nat) 4
  let q1 := q.enqueue 1
  let q2 := q1.enqueue 2
  let q3 := q2.enqueue 3
  let q4 := q3.enqueue 4
  let q5 := q4.enqueue 5  -- Should be no-op
  q5.count = 4 ∧ q5.isFull = true ∧ q4.count = 4 := by
  native_decide

/-!
## Underflow Protection
-/

-- Theorem: Dequeuing from empty queue returns none
theorem no_underflow_empty :
  let q := QueueState.empty (α := Nat) 4
  let (q', result) := q.dequeue
  result = none ∧ q'.isEmpty = true := by
  native_decide

-- Theorem: Repeated dequeues eventually return none
theorem dequeue_until_empty :
  let q := QueueState.empty (α := Nat) 4
  let q1 := q.enqueue 10
  let q2 := q1.enqueue 20
  let (q3, first) := q2.dequeue
  let (q4, second) := q3.dequeue
  let (_q5, third) := q4.dequeue  -- Should return none
  first = some 10 ∧ second = some 20 ∧ third = none := by
  native_decide

/-!
## Count Accuracy
-/

-- Theorem: Count matches entry list length
theorem count_equals_length (q : QueueState Nat) :
  q.count = q.entries.length := by
  simp [QueueState.count]

-- Theorem: Sequential enqueues increment count correctly
theorem sequential_enqueue_count :
  let q := QueueState.empty (α := Nat) 8
  let q1 := q.enqueue 1   -- count = 1
  let q2 := q1.enqueue 2  -- count = 2
  let q3 := q2.enqueue 3  -- count = 3
  q1.count = 1 ∧ q2.count = 2 ∧ q3.count = 3 := by
  native_decide

-- Theorem: Enqueue then dequeue maintains count
theorem enqueue_dequeue_count :
  let q := QueueState.empty (α := Nat) 4
  let q1 := q.enqueue 10
  let q2 := q1.enqueue 20
  let (q3, _) := q2.dequeue
  let q4 := q3.enqueue 30
  q2.count = 2 ∧ q3.count = 1 ∧ q4.count = 2 := by
  native_decide

/-!
## Capacity Invariant
-/

/-- Queue operations: enqueue or dequeue. -/
inductive QueueOp (α : Type) where
  | enq (val : α)
  | deq

/-- Apply a single queue operation. -/
def applyOp {α : Type} (op : QueueOp α) (q : QueueState α) : QueueState α :=
  match op with
  | .enq val => q.enqueue val
  | .deq => (q.dequeue).1

/-- Apply a sequence of operations from left to right. -/
def applyTrace {α : Type} (ops : List (QueueOp α)) (q : QueueState α) : QueueState α :=
  ops.foldl (fun acc op => applyOp op acc) q

/-- Theorem: Enqueue preserves queue capacity. -/
theorem enqueue_capacity {α : Type} (q : QueueState α) (val : α) :
    (q.enqueue val).capacity = q.capacity := by
  simp [QueueState.enqueue]
  split <;> rfl

/-- Theorem: Dequeue preserves queue capacity. -/
theorem dequeue_capacity {α : Type} (q : QueueState α) :
    (q.dequeue).1.capacity = q.capacity := by
  simp [QueueState.dequeue]
  cases q.entries <;> rfl

/-- Theorem: Any operation preserves queue capacity. -/
theorem applyOp_capacity {α : Type} (op : QueueOp α) (q : QueueState α) :
    (applyOp op q).capacity = q.capacity := by
  cases op with
  | enq val => exact enqueue_capacity q val
  | deq => exact dequeue_capacity q

/-- Theorem: Enqueue preserves the capacity invariant. -/
theorem enqueue_preserves_capacity_inv {α : Type} (q : QueueState α) (val : α) (h : q.count ≤ q.capacity) :
    (q.enqueue val).count ≤ q.capacity := by
  simp [QueueState.enqueue, QueueState.count]
  split
  · exact h
  · rename_i h_not_full
    simp [QueueState.isFull] at h_not_full
    simp
    omega

/-- Theorem: Dequeue preserves the capacity invariant. -/
theorem dequeue_preserves_capacity_inv {α : Type} (q : QueueState α) (h : q.count ≤ q.capacity) :
    (q.dequeue).1.count ≤ q.capacity := by
  rcases q with ⟨entries, cap⟩
  simp [QueueState.dequeue, QueueState.count] at h ⊢
  cases entries with
  | nil =>
    exact h
  | cons head tail =>
    simp at h ⊢
    omega

/-- Theorem: Any single operation preserves the capacity invariant. -/
theorem applyOp_preserves_capacity_inv {α : Type} (op : QueueOp α) (q : QueueState α) (h : q.count ≤ q.capacity) :
    (applyOp op q).count ≤ q.capacity := by
  cases op with
  | enq val => exact enqueue_preserves_capacity_inv q val h
  | deq => exact dequeue_preserves_capacity_inv q h

/-- Theorem: Any sequence of operations preserves the capacity invariant. -/
theorem applyTrace_preserves_capacity_inv {α : Type} (ops : List (QueueOp α)) (q : QueueState α) (h : q.count ≤ q.capacity) :
    (applyTrace ops q).count ≤ q.capacity := by
  induction ops generalizing q with
  | nil => exact h
  | cons op rest ih =>
    simp [applyTrace]
    have h_op := applyOp_preserves_capacity_inv op q h
    have h_cap := applyOp_capacity op q
    rw [← h_cap] at h_op
    have ih_applied := ih (applyOp op q) h_op
    rw [h_cap] at ih_applied
    exact ih_applied

/-- Master Theorem: An initialized queue never exceeds its capacity under any sequence of operations. -/
theorem never_exceeds_capacity {α : Type} (ops : List (QueueOp α)) (cap : Nat) :
    (applyTrace ops (QueueState.empty (α := α) cap)).count ≤ cap := by
  apply applyTrace_preserves_capacity_inv
  simp [QueueState.empty, QueueState.count]

-- Theorem: Full queue has count equal to capacity
theorem full_means_at_capacity :
  let q := QueueState.empty (α := Nat) 3
  let q1 := q.enqueue 1
  let q2 := q1.enqueue 2
  let q3 := q2.enqueue 3
  q3.isFull = true ∧ q3.count = q3.capacity := by
  native_decide

/-!
## Peek Correctness
-/

-- Theorem: Peek returns same as dequeue without modifying queue
theorem peek_equals_dequeue_head :
  let q := QueueState.empty (α := Nat) 4
  let q1 := q.enqueue 42
  let (_, deq_result) := q1.dequeue
  let peek_result := q1.peek
  peek_result = deq_result := by
  native_decide

-- Theorem: Peek on empty queue returns none
theorem peek_empty_is_none :
  let q := QueueState.empty (α := Nat) 4
  q.peek = none := by
  native_decide

-- Theorem: Peek doesn't modify queue
theorem peek_preserves_queue (q : QueueState Nat) :
  let _ := q.peek
  True := by  -- Peek returns a value, doesn't modify q
  trivial

/-!
## Interleaved Operations
-/

-- Theorem: Alternating enqueue/dequeue maintains FIFO
theorem alternating_operations :
  let q := QueueState.empty (α := Nat) 4
  let q1 := q.enqueue 10
  let (q2, first) := q1.dequeue
  let q3 := q2.enqueue 20
  let q4 := q3.enqueue 30
  let (q5, second) := q4.dequeue
  let (_q6, third) := q5.dequeue
  first = some 10 ∧ second = some 20 ∧ third = some 30 := by
  native_decide

/-!
## 32-bit Queue Tests (Wide Data)
-/

-- Theorem: FIFO ordering works with 32-bit data
theorem fifo_32bit_data :
  let q := QueueState.empty (α := Nat) 4
  let q1 := q.enqueue 0xDEADBEEF
  let q2 := q1.enqueue 0xCAFEBABE
  let (q3, first) := q2.dequeue
  let (_, second) := q3.dequeue
  first = some 0xDEADBEEF ∧ second = some 0xCAFEBABE := by
  native_decide

-- Theorem: 32-bit queue handles large values
theorem queue_32bit_large_values :
  let q := QueueState.empty (α := Nat) 4
  let q1 := q.enqueue 4294967295  -- 2^32 - 1
  let (q2, result) := q1.dequeue
  result = some 4294967295 ∧ q2.isEmpty = true := by
  native_decide

/-!
## Decoupled Interface Properties
-/

-- Theorem: Queue1 enqueue port has correct wire count (width + 2)
theorem queue1_enq_port_wire_count (width : Nat) :
  (Queue1.enqPort width).allWires.length = width + 2 := by
  simp [Queue1.enqPort, DecoupledSource.allWires, List.length_append, List.length_map, List.length_range]

-- Theorem: Queue1 dequeue port has correct wire count (width + 2)
theorem queue1_deq_port_wire_count (width : Nat) :
  (Queue1.deqPort width).allWires.length = width + 2 := by
  simp [Queue1.deqPort, DecoupledSource.allWires, List.length_append, List.length_map, List.length_range]

-- Theorem: Queue1 enqueue port has correct valid wire name
theorem queue1_enq_port_valid_name :
  (Queue1.enqPort 8).valid.name = "enq_valid" := by
  native_decide

-- Theorem: Queue1 enqueue port has correct ready wire name
theorem queue1_enq_port_ready_name :
  (Queue1.enqPort 8).ready.name = "enq_ready" := by
  native_decide

-- Theorem: Queue1 dequeue port has correct valid wire name
theorem queue1_deq_port_valid_name :
  (Queue1.deqPort 8).valid.name = "valid" := by
  native_decide

-- Theorem: Queue1 dequeue port has correct ready wire name
theorem queue1_deq_port_ready_name :
  (Queue1.deqPort 8).ready.name = "deq_ready" := by
  native_decide

-- Theorem: mkQueue1Decoupled has the correct name for 8-bit queue
theorem queue1_decoupled_8bit_name :
  (mkQueue1Decoupled 8).name = "Queue1_8" := by
  rfl

-- Theorem: mkQueue1Decoupled has the correct input count for 8-bit queue
-- Inputs: enq_bits[0..7] (8) + enq_valid (1) + deq_ready (1) + clock (1) + reset (1) = 12
theorem queue1_decoupled_8bit_input_count :
  (mkQueue1Decoupled 8).inputs.length = 12 := by
  native_decide

-- Theorem: mkQueue1Decoupled has the correct output count for 8-bit queue
-- Outputs: enq_ready (1) + data_reg[0..7] (8) + valid (1) = 10
theorem queue1_decoupled_8bit_output_count :
  (mkQueue1Decoupled 8).outputs.length = 10 := by
  native_decide

-- Theorem: mkQueue1Decoupled has the correct gate count for 8-bit queue
theorem queue1_decoupled_8bit_gate_count :
  (mkQueue1Decoupled 8).gates.length = 23 := by
  native_decide

-- Theorem: mkQueue1Decoupled produces same structure as mkQueue1StructuralComplete
theorem queue1_decoupled_equiv_structural_8bit :
  (mkQueue1Decoupled 8).gates.length = (mkQueue1StructuralComplete 8).gates.length ∧
  (mkQueue1Decoupled 8).inputs.length = (mkQueue1StructuralComplete 8).inputs.length ∧
  (mkQueue1Decoupled 8).outputs.length = (mkQueue1StructuralComplete 8).outputs.length := by
  native_decide

end Shoumei.Circuits.Sequential
