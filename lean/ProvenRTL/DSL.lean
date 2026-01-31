/-
DSL.lean - Core Hardware DSL Definitions

Defines the basic types for representing hardware circuits:
- Wire: Signal identifiers
- GateType: Supported logic gate types (combinational and sequential)
- Gate: Logic gate with inputs and output
- Circuit: Complete circuit with inputs, outputs, and gates

Supports both combinational (AND, OR, NOT, XOR) and sequential (DFF) elements.
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

-- Gate types: combinational and sequential logic elements
inductive GateType where
  -- Combinational gates
  | AND   -- Logical AND
  | OR    -- Logical OR
  | NOT   -- Logical NOT (inverter)
  | XOR   -- Logical XOR (exclusive or)
  -- Sequential elements
  | DFF   -- D Flip-Flop (inputs: [d, clk, reset], output: q)
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

-- D Flip-Flop: captures data on rising edge of clock
-- Synchronous reset: when reset is high on clock edge, output goes to 0
def mkDFF (d clk reset : Wire) (q : Wire) : Gate :=
  { gateType := GateType.DFF, inputs := [d, clk, reset], output := q }

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

-- Classification: is a gate type combinational or sequential?
def GateType.isCombinational (gt : GateType) : Bool :=
  match gt with
  | GateType.AND | GateType.OR | GateType.NOT | GateType.XOR => true
  | GateType.DFF => false

def GateType.isSequential (gt : GateType) : Bool :=
  !gt.isCombinational

-- Check if a circuit has sequential elements
def Circuit.hasSequentialElements (c : Circuit) : Bool :=
  c.gates.any (fun g => g.gateType.isSequential)

-- Check if a circuit is purely combinational
def Circuit.isCombinational (c : Circuit) : Bool :=
  !c.hasSequentialElements

-- TODO: Add validation functions:
-- - Check that all gate inputs are either circuit inputs or outputs of previous gates
-- - Check that all gate outputs are unique (no wire driven by multiple gates)
-- - Check that circuit outputs are driven by some gate or are passthroughs
-- - Check that DFFs have exactly 3 inputs: [d, clk, reset]
-- - Check that clock and reset are properly connected
