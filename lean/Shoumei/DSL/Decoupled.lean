/-
DSL/Decoupled.lean - Decoupled Interface Abstraction

Provides types and helper functions for ready/valid handshaking interfaces.
A decoupled interface bundles data, valid, and ready signals following
industry-standard protocols (Chisel DecoupledIO, AXI-Stream, TileLink).

Key concepts:
- DecoupledSource: Producer side (asserts valid, observes ready)
- DecoupledSink: Consumer side (observes valid, asserts ready)
- Fire signal: Transfer occurs when valid && ready
- Backpressure: Consumer controls ready to throttle producer

This abstraction is lightweight - it doesn't change the DSL structure,
just provides semantic annotations and helper functions to generate
standard ready/valid patterns.
-/

-- Note: This module is Shoumei.DSL.Decoupled (file: lean/Shoumei/DSL/Decoupled.lean)
-- We need to import the parent DSL module which defines Wire, Gate, Circuit types
-- But actually, Lean 4 doesn't allow circular dependencies between Shoumei.DSL and Shoumei.DSL.Decoupled
-- The solution: Define Decoupled in its own namespace and import it from DSL.lean later

namespace Shoumei.DSL.Decoupled

-- Core types we use (must match DSL.lean definitions)
structure Wire where
  name : String
  deriving Repr, BEq, Hashable, Inhabited

inductive GateType where
  | AND | OR | NOT | XOR | BUF | MUX | DFF
  deriving Repr, BEq

structure Gate where
  gateType : GateType
  inputs : List Wire
  output : Wire
  deriving Repr

namespace Gate

def mkAND (a b : Wire) (out : Wire) : Gate :=
  { gateType := GateType.AND, inputs := [a, b], output := out }

def mkBUF (a : Wire) (out : Wire) : Gate :=
  { gateType := GateType.BUF, inputs := [a], output := out }

end Gate

/-! ## Decoupled Interface Types -/

/-- Decoupled source (producer side).

    The producer asserts `valid` when data is available.
    The consumer asserts `ready` when it can accept data.
    A transfer occurs when both `valid` and `ready` are high.

    Protocol rules:
    - Producer must hold `bits` and `valid` stable when valid && !ready
    - Producer can always assert or deassert `valid`
    - Consumer can always assert or deassert `ready`
    - No data loss: if valid && !ready, producer holds data until ready
-/
structure DecoupledSource (width : Nat) where
  /-- Data payload wires (width bits) -/
  bits : List Wire
  /-- Valid signal (producer asserts when data ready) -/
  valid : Wire
  /-- Ready signal (consumer asserts when accepting data) -/
  ready : Wire
  deriving Repr

/-- Decoupled sink (consumer side).

    Structurally identical to DecoupledSource, semantically opposite:
    - Consumer observes `valid` from producer
    - Consumer asserts `ready` to accept data
    - Consumer reads `bits` when valid && ready
-/
abbrev DecoupledSink := DecoupledSource

/-! ## Helper Functions for Wire Naming -/

/-- Create decoupled input port bundle (for module interface).

    Generates wires with standard naming:
    - {name}_bits_0, {name}_bits_1, ..., {name}_bits_{width-1}
    - {name}_valid
    - {name}_ready

    Example:
    ```lean
    let enq := mkDecoupledInput "enq" 8
    -- Creates: enq_bits_0..7, enq_valid, enq_ready
    ```
-/
def mkDecoupledInput (name : String) (width : Nat) : DecoupledSource width :=
  { bits := (List.range width).map (fun i => Wire.mk s!"{name}_bits_{i}")
    valid := Wire.mk s!"{name}_valid"
    ready := Wire.mk s!"{name}_ready"
  }

/-- Create decoupled output port bundle (for module interface).

    Identical to mkDecoupledInput, just semantic naming for clarity.
-/
def mkDecoupledOutput (name : String) (width : Nat) : DecoupledSink width :=
  mkDecoupledInput name width

/-- Get all wires in a decoupled interface (for port lists).

    Returns: bits ++ [valid, ready]
    Useful for concatenating into circuit input/output lists.
-/
def DecoupledSource.allWires {width : Nat} (d : DecoupledSource width) : List Wire :=
  d.bits ++ [d.valid, d.ready]

/-- Get data wires only (for connecting data paths). -/
def DecoupledSource.dataBits {width : Nat} (d : DecoupledSource width) : List Wire :=
  d.bits

/-! ## Fire Signal Generation -/

/-- Generate fire signal name.

    Fire signal indicates a transfer: valid && ready.
    Naming convention: {valid_name}_fire or {base_name}_fire

    Example: enq_valid_fire or enq_fire
-/
def DecoupledSource.fireName {width : Nat} (d : DecoupledSource width) : String :=
  -- Extract base name from valid signal (remove "_valid" suffix if present)
  let validName := d.valid.name
  if validName.endsWith "_valid" then
    validName.dropRight 6 ++ "_fire"  -- "enq_valid" → "enq_fire"
  else
    validName ++ "_fire"

/-- Create fire wire (doesn't generate gate, just the wire for naming). -/
def DecoupledSource.fireWire {width : Nat} (d : DecoupledSource width) : Wire :=
  Wire.mk d.fireName

/-- Generate fire signal gate: fire = valid AND ready.

    Returns gate: AND(valid, ready, fire)

    Example:
    ```lean
    let enq := mkDecoupledInput "enq" 8
    let gate := mkDecoupledFireGate enq
    -- Creates: enq_fire = enq_valid AND enq_ready
    ```
-/
def mkDecoupledFireGate {width : Nat} (d : DecoupledSource width) : Gate :=
  let fire := d.fireWire
  Gate.mkAND d.valid d.ready fire

/-! ## Interface Connection Helpers -/

/-- Connect two decoupled interfaces (producer → consumer).

    Generates gates to wire:
    - Data: src.bits[i] → sink.bits[i] (BUF gates)
    - Valid: src.valid → sink.valid (BUF gate)
    - Ready: sink.ready → src.ready (BUF gate, reverse direction!)

    Returns list of BUF gates for direct connection.

    Example:
    ```lean
    let producer := mkDecoupledOutput "producer" 8
    let consumer := mkDecoupledInput "consumer" 8
    let gates := connectDecoupled producer consumer
    -- Creates width+2 BUF gates connecting all signals
    ```

    Note: This is for direct connection. If buffering (queue) is desired,
    instantiate a Queue module between producer and consumer instead.
-/
def connectDecoupled {width : Nat}
    (src : DecoupledSource width)
    (sink : DecoupledSink width)
    : List Gate :=
  -- Wire data: src.bits → sink.bits
  (src.bits.zip sink.bits).map (fun (s, d) => Gate.mkBUF s d) ++
  -- Wire valid: src.valid → sink.valid
  [Gate.mkBUF src.valid sink.valid] ++
  -- Wire ready: sink.ready → src.ready (reverse direction!)
  [Gate.mkBUF sink.ready src.ready]

/-! ## Behavioral Semantics (for proofs) -/

/-- Decoupled transfer protocol rules.

    This structure captures the behavioral semantics of decoupled interfaces
    for theorem proving. It's not executable - just a specification.

    Key properties:
    1. Stability: Producer must hold data stable when valid && !ready
    2. Transfer condition: Data transfers iff valid && ready
    3. Valid freedom: Producer can always change valid
    4. Ready freedom: Consumer can always change ready

    These properties enable composition proofs:
    - Pipelining preserves semantics
    - Buffering (queue insertion) preserves semantics
    - Acyclic networks are deadlock-free
-/
structure DecoupledTransfer where
  /-- When valid && !ready, producer must hold data stable (no data loss).

      Formally: ∀ cycle, if valid(cycle) && !ready(cycle)
                then bits(cycle+1) = bits(cycle) && valid(cycle+1) = true

      This is a liveness property - prevents the producer from dropping data.
  -/
  stability : Bool  -- Placeholder for temporal logic formula

  /-- Transfer occurs iff valid && ready.

      Formally: transferred(cycle) ↔ (valid(cycle) && ready(cycle))

      This defines when data moves from producer to consumer.
  -/
  transfer_condition : Bool  -- Placeholder for formula

  /-- Producer can always assert or deassert valid (no restriction from protocol).

      Formally: ∀ cycle, valid(cycle+1) can be true or false

      The protocol doesn't constrain valid - producer has full control.
      (But stability rule requires holding valid=true until ready if data is present)
  -/
  valid_freedom : Bool  -- Placeholder for formula

  /-- Consumer can always assert or deassert ready (can apply backpressure).

      Formally: ∀ cycle, ready(cycle+1) can be true or false

      This allows backpressure - consumer controls throughput.
  -/
  ready_freedom : Bool  -- Placeholder for formula

  deriving Repr

/-- Default instance for DecoupledTransfer (all rules hold). -/
instance : Inhabited DecoupledTransfer where
  default := {
    stability := true
    transfer_condition := true
    valid_freedom := true
    ready_freedom := true
  }

/-! ## Composition Helpers -/

/-- Chain two decoupled modules with a direct connection.

    Connects producer.output → consumer.input using connectDecoupled.
    Returns gates list for the connection.

    This is for composition proofs - showing that connecting two
    decoupled-compliant modules preserves decoupled semantics.
-/
def chainDecoupled {width : Nat}
    (producer_out : DecoupledSource width)
    (consumer_in : DecoupledSink width)
    : List Gate :=
  connectDecoupled producer_out consumer_in

end Shoumei.DSL.Decoupled
