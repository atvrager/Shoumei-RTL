/-
DSL.lean - Core Hardware DSL Definitions

Defines the basic types for representing hardware circuits:
- Wire: Signal identifiers
- GateType: Supported logic gate types
- Gate: Logic gate with inputs and output
- Circuit: Complete circuit with inputs, outputs, and gates

This is a minimal combinational circuit DSL. Sequential elements
(registers, state machines) will be added in future phases.
-/

-- Wire: represents a signal in the circuit
-- Uses String identifier for simplicity
structure Wire where
  name : String
  deriving Repr, BEq, Hashable

namespace Wire

-- Note: Wire.mk is automatically provided by LEAN for structures
-- Usage: Wire.mk "name" or ⟨"name"⟩

end Wire

-- Gate types: basic combinational logic gates
inductive GateType where
  | AND   -- Logical AND
  | OR    -- Logical OR
  | NOT   -- Logical NOT (inverter)
  | XOR   -- Logical XOR (exclusive or)
  deriving Repr, BEq

-- Gate: represents a logic gate with inputs and output
structure Gate where
  gateType : GateType
  inputs : List Wire
  output : Wire
  deriving Repr

namespace Gate

-- Helper constructors for common gates
def mkAND (a b : Wire) (out : Wire) : Gate :=
  { gateType := GateType.AND, inputs := [a, b], output := out }

def mkOR (a b : Wire) (out : Wire) : Gate :=
  { gateType := GateType.OR, inputs := [a, b], output := out }

def mkNOT (a : Wire) (out : Wire) : Gate :=
  { gateType := GateType.NOT, inputs := [a], output := out }

def mkXOR (a b : Wire) (out : Wire) : Gate :=
  { gateType := GateType.XOR, inputs := [a, b], output := out }

end Gate

-- Circuit: a complete circuit with inputs, outputs, and gates
structure Circuit where
  name : String           -- Module/circuit name
  inputs : List Wire      -- Input signals
  outputs : List Wire     -- Output signals
  gates : List Gate       -- Internal gates
  deriving Repr

namespace Circuit

-- Helper to create empty circuit
def empty (name : String) : Circuit :=
  { name := name, inputs := [], outputs := [], gates := [] }

end Circuit

-- TODO: Add validation functions:
-- - Check that all gate inputs are either circuit inputs or outputs of previous gates
-- - Check that all gate outputs are unique (no wire driven by multiple gates)
-- - Check that circuit outputs are driven by some gate or are passthroughs
