/-
RISCV/Renaming/FreeList.lean - Free Physical Register List

Manages a pool of available physical register tags for Tomasulo register renaming.
The Free List is a FIFO queue of physical register tags that can be allocated
to new instructions (dequeue) and freed when instructions retire (enqueue).

Design:
- Backed by an N-entry circular buffer queue (QueueN)
- Initially contains registers [firstFree, firstFree+1, ..., N-1]
  (first `firstFree` registers reserved for architectural identity mapping)
- allocate: dequeue next available physical register tag
- deallocate: enqueue a freed physical register tag back to the pool
- Ready/valid handshaking for flow control

Structural components:
- QueueRAM: N × tagWidth storage with decoder and mux
- QueuePointer × 2: Head and tail pointer registers
- QueueCounterUpDown: Count register for empty/full detection
-/

import Shoumei.DSL
import Shoumei.Circuits.Sequential.QueueN

namespace Shoumei.RISCV.Renaming

open Shoumei
open Shoumei.Circuits.Sequential

/-! ## Behavioral Model -/

/-- Free List state: A FIFO queue of available physical register tags.
    Wraps CircularBufferState with domain-specific operations. -/
structure FreeListState (numPhysRegs : Nat) where
  /-- Underlying circular buffer of physical register tags -/
  queue : CircularBufferState (Fin numPhysRegs) numPhysRegs

/-- Is the free list empty? (no physical registers available for allocation) -/
def FreeListState.isEmpty (fl : FreeListState n) : Bool :=
  fl.queue.isEmpty

/-- Is the free list full? (all physical registers are free) -/
def FreeListState.isFull (fl : FreeListState n) : Bool :=
  fl.queue.isFull

/-- Number of available physical registers -/
def FreeListState.count (fl : FreeListState n) : Nat :=
  fl.queue.count

/-- Allocate a physical register: dequeue the next available tag.
    Returns (updated state, Some tag) on success, or (unchanged state, None) if empty. -/
def FreeListState.allocate (fl : FreeListState n) : FreeListState n × Option (Fin n) :=
  let (queue', tag) := fl.queue.dequeue
  ({ queue := queue' }, tag)

/-- Deallocate (free) a physical register: enqueue the tag back to the pool.
    No-op if the free list is already full (all registers free). -/
def FreeListState.deallocate (fl : FreeListState n) (tag : Fin n) : FreeListState n :=
  { queue := fl.queue.enqueue tag }

/-- Peek at the next available physical register without removing it. -/
def FreeListState.peek (fl : FreeListState n) : Option (Fin n) :=
  fl.queue.peek

/-- Create initial free list with physical registers [firstFree, firstFree+1, ..., n-1].
    Registers 0 to firstFree-1 are reserved for the architectural identity mapping. -/
def FreeListState.init (n firstFree : Nat) (h_n : n > 0) (_h_first : firstFree ≤ n)
    : FreeListState n :=
  let empty := CircularBufferState.empty (α := Fin n) n h_n
  let filled := (List.range (n - firstFree)).foldl (fun cb i =>
    if h : firstFree + i < n then cb.enqueue ⟨firstFree + i, h⟩
    else cb  -- unreachable: i < n - firstFree implies firstFree + i < n
  ) empty
  { queue := filled }

/-- Initialize free list for 64 physical registers (standard configuration).
    Registers 0-31 reserved for identity mapping, 32-63 available for allocation. -/
def mkFreeList64Init : FreeListState 64 :=
  FreeListState.init 64 32 (by omega) (by omega)

/-- Initialize free list for 4 physical registers (test configuration).
    Registers 0-1 reserved, 2-3 available. -/
def mkFreeList4Init : FreeListState 4 :=
  FreeListState.init 4 2 (by omega) (by omega)

/-- Initialize free list for 8 physical registers (test configuration).
    Registers 0-3 reserved, 4-7 available. -/
def mkFreeList8Init : FreeListState 8 :=
  FreeListState.init 8 4 (by omega) (by omega)

/-! ## Structural Circuit -/

/-- Helper: Compute log2 ceiling -/
private def log2Ceil (n : Nat) : Nat :=
  if n <= 1 then 0
  else Nat.log2 n + (if 2^(Nat.log2 n) < n then 1 else 0)

/--
Build a Free List circuit.

The Free List is structurally a QueueN circular buffer with domain-specific naming.

Port interface:
- enq_data[tagWidth-1:0]: freed physical register tag (deallocate input)
- enq_valid: deallocation request
- enq_ready: free list can accept deallocation (not full)
- deq_data[tagWidth-1:0]: allocated physical register tag (allocate output)
- deq_ready: consumer ready to accept allocation
- deq_valid: allocation available (not empty)
- clock, reset, zero, one: control signals

Submodules:
- QueueRAM_{N}x{tagWidth}: Storage with decoder and mux
- QueuePointer_{ptrWidth} × 2: Head and tail pointer registers
- QueueCounterUpDown_{countWidth}: Count register
-/
def mkFreeList (numPhysRegs : Nat) : Circuit :=
  let tagWidth := log2Ceil numPhysRegs
  let queue := mkQueueNStructural numPhysRegs tagWidth
  let ptrWidth := log2Ceil numPhysRegs
  let countWidth := ptrWidth + 1
  { queue with
    name := s!"FreeList_{numPhysRegs}"
    -- V2 codegen annotations
    signalGroups := [
      { name := "enq_data", width := tagWidth, wires := (List.range tagWidth).map (fun i => Wire.mk s!"enq_data_{i}") },
      { name := "deq_data", width := tagWidth, wires := (List.range tagWidth).map (fun i => Wire.mk s!"deq_data_{i}") },
      { name := "head", width := ptrWidth, wires := (List.range ptrWidth).map (fun i => Wire.mk s!"head_{i}") },
      { name := "tail", width := ptrWidth, wires := (List.range ptrWidth).map (fun i => Wire.mk s!"tail_{i}") },
      { name := "count", width := countWidth, wires := (List.range countWidth).map (fun i => Wire.mk s!"count_{i}") }
    ]
  }

/-- Free List with 64 physical registers (6-bit tags) -/
def mkFreeList64 : Circuit := mkFreeList 64

end Shoumei.RISCV.Renaming
