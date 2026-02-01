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
import Shoumei.DSL.Decoupled

namespace Shoumei.Circuits.Sequential

open Shoumei
open Shoumei.DSL.Decoupled

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

/-!
## Structural Queue Implementation

Build a 1-entry Queue from DFFs and combinational logic.
This demonstrates DSL composability and enables structural proofs.
-/

-- Helper to create wire names with indices
def wireWithIndex (base : String) (idx : Nat) : Wire :=
  Wire.mk s!"{base}_{idx}"

-- Build a 1-entry Queue structurally from DFFs
-- For an N-bit queue:
--   - 1 DFF for valid bit
--   - N DFFs for data bits
--   - Combinational logic for ready/valid handshaking
def mkQueue1Structural (width : Nat) : Circuit :=
  let name := s!"Queue1_{width}"

  -- Input wires
  let enq_data := List.range width |>.map (wireWithIndex "enq_data")
  let enq_valid := Wire.mk "enq_valid"
  let deq_ready := Wire.mk "deq_ready"
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"

  -- Output wires
  let enq_ready := Wire.mk "enq_ready"
  let deq_data := List.range width |>.map (wireWithIndex "deq_data")
  let deq_valid := Wire.mk "deq_valid"

  -- Internal state wires
  let valid := Wire.mk "valid"           -- Current valid bit (DFF output)
  let valid_next := Wire.mk "valid_next" -- Next valid bit (DFF input)
  let data_reg := List.range width |>.map (wireWithIndex "data_reg")
  let data_next := List.range width |>.map (wireWithIndex "data_next")

  -- Control signals
  let enq_fire := Wire.mk "enq_fire"     -- enq_valid && enq_ready
  let deq_fire := Wire.mk "deq_fire"     -- deq_valid && deq_ready
  let not_deq_fire := Wire.mk "not_deq_fire"
  let valid_hold := Wire.mk "valid_hold" -- MUX output for hold vs dequeue

  -- Gates
  let gates := [
    -- Output combinational logic
    Gate.mkNOT valid enq_ready,                    -- enq_ready = !valid
    -- deq_valid = valid (direct wire connection handled by naming)
    -- deq_data[i] = data_reg[i] (direct wire connections)

    -- Control signal generation
    Gate.mkAND enq_valid enq_ready enq_fire,       -- enq_fire = enq_valid && enq_ready
    Gate.mkAND valid deq_ready deq_fire,           -- deq_fire = deq_valid && deq_ready (valid = deq_valid)
    Gate.mkNOT deq_fire not_deq_fire,              -- not_deq_fire = !deq_fire

    -- Valid next-state logic: valid_next = enq_fire ? 1 : (deq_fire ? 0 : valid)
    -- Implemented as: valid_next = MUX(MUX(valid, 0, deq_fire), 1, enq_fire)
    -- Since we don't have constant wires, we use: valid_next = enq_fire || (valid && !deq_fire)
    Gate.mkAND valid not_deq_fire valid_hold,      -- valid_hold = valid && !deq_fire
    Gate.mkOR enq_fire valid_hold valid_next,      -- valid_next = enq_fire || valid_hold

    -- Valid DFF
    Gate.mkDFF valid_next clock reset valid
  ] ++
  -- Data next-state logic: data_next[i] = enq_fire ? enq_data[i] : data_reg[i]
  -- Implemented as: data_next[i] = MUX(data_reg[i], enq_data[i], enq_fire)
  (List.range width).map (fun i =>
    Gate.mkMUX (data_reg[i]!) (enq_data[i]!) enq_fire (data_next[i]!)
  ) ++
  -- Data DFFs
  (List.range width).map (fun i =>
    Gate.mkDFF (data_next[i]!) clock reset (data_reg[i]!)
  ) ++
  -- Connect deq_data outputs to data_reg (using assignment gates)
  -- Note: In a real implementation, these would be handled by the code generator
  -- For now, we represent them as direct wire mappings in the outputs
  []

  { name := name
    inputs := enq_data ++ [enq_valid, deq_ready, clock, reset]
    outputs := [enq_ready] ++ deq_data ++ [deq_valid]
    gates := gates
    instances := []
  }

-- Helper: create structural queue with proper output connections
-- Map outputs to internal wires (deq_data -> data_reg, deq_valid -> valid)
def mkQueue1StructuralComplete (width : Nat) : Circuit :=
  let base := mkQueue1Structural width
  -- In the structural representation:
  -- - deq_data[i] should be data_reg[i]
  -- - deq_valid should be valid
  let valid_wire := Wire.mk "valid"
  let data_reg_wires := List.range width |>.map (wireWithIndex "data_reg")
  let updated_outputs :=
    [Wire.mk "enq_ready"] ++
    data_reg_wires ++  -- Use data_reg as deq_data outputs
    [valid_wire]       -- Use valid as deq_valid output
  { base with outputs := updated_outputs }

/-! ## Decoupled Interface Support

Extension: Expose Queue ports as Decoupled interfaces for composition.

The Queue1 circuit has two Decoupled interfaces:
- Enqueue port (DecoupledSink): producer → queue
- Dequeue port (DecoupledSource): queue → consumer

These helpers extract the Decoupled representation from the existing
structural circuit without modifying it - purely semantic annotations
for better composition and proofs.
-/

/-- Extract enqueue port as DecoupledSink.

    From Queue1 inputs: enq_data[width], enq_valid, (enq_ready is output)
    Creates: DecoupledSink with standard naming
-/
def Queue1.enqPort (width : Nat) : DecoupledSink width :=
  { bits := List.range width |>.map (wireWithIndex "enq_data")
    valid := Wire.mk "enq_valid"
    ready := Wire.mk "enq_ready"  -- This is an output of the queue
  }

/-- Extract dequeue port as DecoupledSource.

    From Queue1 outputs: deq_data[width], deq_valid, (deq_ready is input)
    Creates: DecoupledSource with standard naming
-/
def Queue1.deqPort (width : Nat) : DecoupledSource width :=
  { bits := List.range width |>.map (wireWithIndex "data_reg")  -- Internal data_reg exposed as deq_data
    valid := Wire.mk "valid"  -- Internal valid exposed as deq_valid
    ready := Wire.mk "deq_ready"  -- This is an input to the queue
  }

/-- Build Queue1 using Decoupled helpers for clarity.

    This variant explicitly constructs the circuit using DecoupledInput/Output
    helpers. It's functionally identical to mkQueue1StructuralComplete but
    demonstrates Decoupled-aware construction.

    The structural implementation is the same - we just use Decoupled helpers
    to make the interface contract explicit.
-/
def mkQueue1Decoupled (width : Nat) : Circuit :=
  let name := s!"Queue1_{width}"

  -- Create Decoupled interfaces using standard helpers
  let enq := mkDecoupledInput "enq" width
  let deq := mkDecoupledOutput "deq" width

  -- Control signals (same as mkQueue1Structural)
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"

  -- Internal state wires
  let valid := Wire.mk "valid"           -- Current valid bit (DFF output)
  let valid_next := Wire.mk "valid_next" -- Next valid bit (DFF input)
  let data_reg := List.range width |>.map (wireWithIndex "data_reg")
  let data_next := List.range width |>.map (wireWithIndex "data_next")

  -- Fire signals (using Decoupled helper)
  let enq_fire := enq.fireWire
  let deq_fire_wire := Wire.mk "deq_fire"
  let not_deq_fire := Wire.mk "not_deq_fire"
  let valid_hold := Wire.mk "valid_hold"

  -- Gates (same logic as mkQueue1Structural)
  let gates := [
    -- Output combinational logic
    Gate.mkNOT valid enq.ready,  -- enq_ready = !valid (queue full when valid)

    -- Fire signals
    mkDecoupledFireGate enq,  -- enq_fire = enq_valid && enq_ready
    Gate.mkAND valid deq.ready deq_fire_wire,  -- deq_fire = valid && deq_ready

    Gate.mkNOT deq_fire_wire not_deq_fire,

    -- Valid next-state logic
    Gate.mkAND valid not_deq_fire valid_hold,
    Gate.mkOR enq_fire valid_hold valid_next,

    -- Valid DFF
    Gate.mkDFF valid_next clock reset valid
  ] ++
  -- Data next-state logic
  (List.range width).map (fun i =>
    Gate.mkMUX (data_reg[i]!) (enq.bits[i]!) enq_fire (data_next[i]!)
  ) ++
  -- Data DFFs
  (List.range width).map (fun i =>
    Gate.mkDFF (data_next[i]!) clock reset (data_reg[i]!)
  )

  { name := name
    inputs := enq.bits ++ [enq.valid, deq.ready, clock, reset]
    outputs := [enq.ready] ++ data_reg ++ [valid]  -- data_reg = deq_data, valid = deq_valid
    gates := gates
    instances := []
  }

/-- Theorem: mkQueue1Decoupled produces same structure as mkQueue1StructuralComplete.

    This proves that using Decoupled helpers doesn't change the circuit structure,
    just makes the interface semantics explicit.

    TODO: Complete proof after establishing circuit equality
-/
axiom queue1_decoupled_equiv_structural (width : Nat)
    : (mkQueue1Decoupled width).gates.length = (mkQueue1StructuralComplete width).gates.length ∧
      (mkQueue1Decoupled width).inputs.length = (mkQueue1StructuralComplete width).inputs.length ∧
      (mkQueue1Decoupled width).outputs.length = (mkQueue1StructuralComplete width).outputs.length

end Shoumei.Circuits.Sequential
