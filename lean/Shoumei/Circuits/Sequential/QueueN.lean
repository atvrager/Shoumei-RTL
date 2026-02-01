/-
Circuits/Sequential/QueueN.lean - Multi-Entry Circular Buffer Queue

Extends the single-entry Queue to support arbitrary depth N using a circular buffer
implementation with head/tail pointers.

This is needed for:
- Free List (Phase 3): 64-entry queue of physical register tags
- Reservation Stations (Phase 4): Multiple entry queues for instructions
- Reorder Buffer (Phase 6): Large circular buffer for in-order commit

Design:
- Storage: N registers, each width bits
- Head pointer: ceil(log2(N)) bits (points to next dequeue position)
- Tail pointer: ceil(log2(N)) bits (points to next enqueue position)
- Count register: ceil(log2(N))+1 bits (current number of entries)
- Empty when count == 0
- Full when count == N
-/

import Shoumei.DSL
import Shoumei.Circuits.Sequential.Queue
import Shoumei.Circuits.Sequential.Register

namespace Shoumei.Circuits.Sequential

open Shoumei

/-!
## Circular Buffer State

Extends QueueState to track head/tail pointers for efficient enqueue/dequeue.
-/

structure CircularBufferState (α : Type) (n : Nat) where
  storage : Fin n → Option α  -- Circular array storage
  head : Fin n                -- Read pointer (next dequeue)
  tail : Fin n                -- Write pointer (next enqueue)
  count : Nat                 -- Current number of entries
  h_count : count ≤ n         -- Invariant: count never exceeds capacity

namespace CircularBufferState

-- Is the circular buffer empty?
def isEmpty {α : Type} {n : Nat} (cb : CircularBufferState α n) : Bool :=
  cb.count == 0

-- Is the circular buffer full?
def isFull {α : Type} {n : Nat} (cb : CircularBufferState α n) : Bool :=
  cb.count >= n

-- Enqueue operation (add to tail, advance tail pointer)
def enqueue {α : Type} {n : Nat} (cb : CircularBufferState α n) (data : α)
    : CircularBufferState α n :=
  if h : cb.isFull then
    cb  -- No-op if full
  else
    let newStorage := fun i => if i = cb.tail then some data else cb.storage i
    let newTail := if h' : cb.tail.val + 1 < n then
                     ⟨cb.tail.val + 1, h'⟩
                   else
                     ⟨0, Nat.zero_lt_of_lt cb.tail.isLt⟩
    let newCount := cb.count + 1
    { storage := newStorage
      head := cb.head
      tail := newTail
      count := newCount
      h_count := by
        simp [isFull] at h
        omega }

-- Dequeue operation (remove from head, advance head pointer)
def dequeue {α : Type} {n : Nat} (cb : CircularBufferState α n)
    : CircularBufferState α n × Option α :=
  if h : cb.isEmpty then
    (cb, none)  -- Empty buffer
  else
    let data := cb.storage cb.head
    let newStorage := fun i => if i = cb.head then none else cb.storage i
    let newHead := if h' : cb.head.val + 1 < n then
                     ⟨cb.head.val + 1, h'⟩
                   else
                     ⟨0, Nat.zero_lt_of_lt cb.head.isLt⟩
    let newCount := cb.count - 1
    let newCb : CircularBufferState α n :=
      { storage := newStorage
        head := newHead
        tail := cb.tail
        count := newCount
        h_count := by
          simp [isEmpty] at h
          have : cb.count > 0 := by omega
          have : cb.count ≤ n := cb.h_count
          omega }
    (newCb, data)

-- Peek at head without removing
def peek {α : Type} {n : Nat} (cb : CircularBufferState α n) : Option α :=
  if cb.isEmpty then none else cb.storage cb.head

-- Create empty circular buffer with given depth
def empty {α : Type} (n : Nat) (h : n > 0) : CircularBufferState α n :=
  { storage := fun _ => none
    head := ⟨0, h⟩
    tail := ⟨0, h⟩
    count := 0
    h_count := Nat.zero_le n }

end CircularBufferState

/-!
## QueueN Circuit Definition

For code generation, we need a structural representation of multi-entry queues.
-/

structure QueueNCircuit where
  name : String
  width : Nat        -- Bit width of data
  depth : Nat        -- Number of entries (must be power of 2 for simple addressing)
  deriving Repr

-- Convenience constructor for multi-entry queues
def mkQueueN (depth width : Nat) : QueueNCircuit :=
  { name := s!"Queue{depth}_{width}", width := width, depth := depth }

-- Specific instances for common depths
def mkQueueN2 (width : Nat) : QueueNCircuit := mkQueueN 2 width
def mkQueueN4 (width : Nat) : QueueNCircuit := mkQueueN 4 width
def mkQueueN8 (width : Nat) : QueueNCircuit := mkQueueN 8 width
def mkQueueN16 (width : Nat) : QueueNCircuit := mkQueueN 16 width
def mkQueueN32 (width : Nat) : QueueNCircuit := mkQueueN 32 width
def mkQueueN64 (width : Nat) : QueueNCircuit := mkQueueN 64 width

-- Specific instance for Free List (Phase 3) - 64-entry, 6-bit wide
def mkQueue64x6 : QueueNCircuit := mkQueueN64 6

/-!
## Structural QueueN Implementation

Build an N-entry Queue from:
- N storage registers (each `width` bits)
- Head pointer register (ptrWidth bits)
- Tail pointer register (ptrWidth bits)
- Count register (ptrWidth+1 bits to represent 0..N)
- Decoder for write address (N-way one-hot)
- MUX for read data (N:1 selection)
- Incrementers for pointers (with wraparound)
- Comparators for empty/full detection

This is deferred to code generation as it requires complex structural composition.
For now, we define the behavioral semantics above.
-/

-- TODO: Implement mkQueueNStructural similar to mkQueue1Structural
-- This will require:
-- 1. Storage register array (N × width bits)
-- 2. Pointer registers (2 × ptrWidth bits)
-- 3. Count register (ptrWidth+1 bits)
-- 4. Address decoder for write enable
-- 5. MUX tree for read data
-- 6. Increment/wraparound logic for pointers
-- 7. Control logic for ready/valid handshaking

end Shoumei.Circuits.Sequential
