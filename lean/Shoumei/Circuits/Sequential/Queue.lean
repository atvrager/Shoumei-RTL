/-
Circuits/Sequential/Queue.lean - Queue/FIFO Implementation

Single-entry and multi-entry queues with ready/valid handshaking.

This extends our DSL with a higher-level Queue abstraction that has
built-in FIFO semantics, ready/valid handshaking, and state management.

Ready/Valid Protocol:
- Producer sets enq_valid high when data is available
- Consumer sets deq_ready high when ready to accept data
- Queue asserts enq_ready when it can accept data (not full)
- Queue asserts deq_valid when it has data (not empty)
- Transactions happen when valid && ready on same cycle
-/

import Shoumei.DSL

namespace Shoumei.Circuits.Sequential

open Shoumei

/-!
## Queue State Representation

A queue has:
- entries: List of data values (FIFO ordered)
- capacity: Maximum number of entries
-/

structure QueueState (α : Type) where
  entries : List α
  capacity : Nat
  deriving Repr

namespace QueueState

-- Is the queue empty?
def isEmpty {α : Type} (q : QueueState α) : Bool :=
  q.entries.isEmpty

-- Is the queue full?
def isFull {α : Type} (q : QueueState α) : Bool :=
  q.entries.length >= q.capacity

-- Current count
def count {α : Type} (q : QueueState α) : Nat :=
  q.entries.length

-- Enqueue operation (add to tail)
def enqueue {α : Type} (q : QueueState α) (data : α) : QueueState α :=
  if q.isFull then q  -- No-op if full
  else { q with entries := q.entries ++ [data] }

-- Dequeue operation (remove from head)
def dequeue {α : Type} (q : QueueState α) : QueueState α × Option α :=
  match q.entries with
  | [] => (q, none)  -- Empty queue
  | head :: tail => ({ q with entries := tail }, some head)

-- Peek at head without removing
def peek {α : Type} (q : QueueState α) : Option α :=
  q.entries.head?

-- Create empty queue with given capacity
def empty {α : Type} (capacity : Nat) : QueueState α :=
  { entries := [], capacity := capacity }

end QueueState

/-!
## Queue Circuit Definition

For code generation, we need a structural representation.
A Queue circuit with N entries storing width-bit data.
-/

structure QueueCircuit where
  name : String
  width : Nat        -- Bit width of data
  depth : Nat        -- Number of entries
  deriving Repr

-- Convenience constructors
def mkQueue1 (width : Nat) : QueueCircuit :=
  { name := s!"Queue1_{width}", width := width, depth := 1 }

def mkQueue2 (width : Nat) : QueueCircuit :=
  { name := s!"Queue2_{width}", width := width, depth := 2 }

def mkQueue4 (width : Nat) : QueueCircuit :=
  { name := s!"Queue4_{width}", width := width, depth := 4 }

def mkQueue8 (width : Nat) : QueueCircuit :=
  { name := s!"Queue8_{width}", width := width, depth := 8 }

-- Specific instances for testing
def queue1_1bit : QueueCircuit := mkQueue1 1
def queue1_4bit : QueueCircuit := mkQueue1 4
def queue1_8bit : QueueCircuit := mkQueue1 8
def queue1_32bit : QueueCircuit := mkQueue1 32

end Shoumei.Circuits.Sequential
