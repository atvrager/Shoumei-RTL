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
  deriving Repr, BEq, Hashable, Inhabited

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
  | BUF   -- Buffer (pass-through)
          -- Semantics: out = in
  | MUX   -- 2-to-1 Multiplexer (inputs: [in0, in1, sel], output: out)
          -- Semantics: out = sel ? in1 : in0
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

def mkBUF (a : Wire) (out : Wire) : Gate :=
  { gateType := GateType.BUF, inputs := [a], output := out }

def mkMUX (in0 in1 sel : Wire) (out : Wire) : Gate :=
  { gateType := GateType.MUX, inputs := [in0, in1, sel], output := out }

-- D Flip-Flop: captures data on rising edge of clock
-- Synchronous reset: when reset is high on clock edge, output goes to 0
def mkDFF (d clk reset : Wire) (q : Wire) : Gate :=
  { gateType := GateType.DFF, inputs := [d, clk, reset], output := q }

end Gate



-- CircuitInstance: represents a submodule instantiation
structure CircuitInstance where
  moduleName : String     -- Name of the module being instantiated (e.g., "Ram64x32")
  instName : String       -- Name of this instance (e.g., "u_ram")
  portMap : List (String × Wire) -- Mapping from submodule port names to local wires
  deriving Repr

-- Circuit: a complete circuit with inputs, outputs, gates, and submodules
structure Circuit where
  name : String           -- Module/circuit name
  inputs : List Wire      -- Input signals
  outputs : List Wire     -- Output signals
  gates : List Gate       -- Internal gates
  instances : List CircuitInstance -- Submodule instances
  deriving Repr

namespace Circuit

-- Helper to create empty circuit
def empty (name : String) : Circuit :=
  { name := name, inputs := [], outputs := [], gates := [], instances := [] }

-- Inline a subcircuit with wire remapping
-- This allows hierarchical composition while keeping a flat gate structure
-- wireMap: maps subcircuit wires to parent circuit wires
-- Note: Submodule instances in subcircuit are conceptually flattened/lost in this operation,
-- similar to how gates are remapped. For now, we assume inlining is only used
-- for flattening combinational logic or when we deliberately want to remove hierarchy.
def inline (subcircuit : Circuit) (wireMap : Wire → Wire) : List Gate :=
  subcircuit.gates.map (fun g => {
    gateType := g.gateType
    inputs := g.inputs.map wireMap
    output := wireMap g.output
  })

end Circuit

-- Classification: is a gate type combinational or sequential?
def GateType.isCombinational (gt : GateType) : Bool :=
  match gt with
  | GateType.AND | GateType.OR | GateType.NOT | GateType.XOR | GateType.BUF | GateType.MUX => true
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
