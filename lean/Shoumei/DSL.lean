/-
DSL.lean - Core Hardware DSL Definitions

Defines the basic types for representing hardware circuits:
- Wire: Signal identifiers
- GateType: Supported logic gate types (combinational and sequential)
- Gate: Logic gate with inputs and output
- Circuit: Complete circuit with inputs, outputs, and gates

Supports both combinational (AND, OR, NOT, XOR) and sequential (DFF, DFF_SET) elements.
-/

-- Lean 4.27.0 compat: List.enum was removed in favor of List.zipIdx (which
-- returns (α × Nat) instead of (Nat × α)). Re-define with the original signature
-- to avoid a codebase-wide destructuring swap.
def List.enum (l : List α) : List (Nat × α) :=
  l.zipIdx.map (fun (a, i) => (i, a))

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
  | DFF       -- D Flip-Flop (inputs: [d, clk, reset], output: q) — resets to 0
  | DFF_SET   -- D Flip-Flop with preset (inputs: [d, clk, reset], output: q) — resets to 1
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
-- Async reset: when reset is high, output goes to 0
def mkDFF (d clk reset : Wire) (q : Wire) : Gate :=
  { gateType := GateType.DFF, inputs := [d, clk, reset], output := q }

-- D Flip-Flop with preset: captures data on rising edge of clock
-- Async reset: when reset is high, output goes to 1 (preset)
def mkDFF_SET (d clk reset : Wire) (q : Wire) : Gate :=
  { gateType := GateType.DFF_SET, inputs := [d, clk, reset], output := q }

end Gate



-- CircuitInstance: represents a submodule instantiation
structure CircuitInstance where
  moduleName : String     -- Name of the module being instantiated (e.g., "Ram64x32")
  instName : String       -- Name of this instance (e.g., "u_ram")
  portMap : List (String × Wire) -- Mapping from submodule port names to local wires
  deriving Repr

/-! ## Codegen V2: Signal Annotations

These types carry type information for code generators without affecting
proofs. All fields on Circuit default to [] so existing definitions are
unchanged.
-/

/-- Signal type annotation for codegen. Maps flat wires to typed signals. -/
inductive SignalType where
  | Bool
  | UInt (width : Nat)
  | SInt (width : Nat)
  deriving Repr, BEq, Inhabited

/-- Group of flat wires that form a single logical signal (e.g., a 32-bit bus). -/
structure SignalGroup where
  name  : String
  width : Nat
  wires : List Wire          -- the underlying flat wires
  stype : SignalType := .UInt width
  deriving Repr

/-- Interface bundle describing a structured port group (e.g., Decoupled). -/
structure InterfaceBundle where
  name     : String
  signals  : List (String × SignalType)  -- field name → type
  protocol : Option String := none       -- "decoupled" | "regport" | none
  deriving Repr

/-- RAM write port: enable + address + data wires. -/
structure RAMWritePort where
  en   : Wire
  addr : List Wire         -- log2(depth) wires
  data : List Wire         -- width wires
  deriving Repr

/-- RAM read port: address wires (inputs) + data wires (outputs). -/
structure RAMReadPort where
  addr : List Wire         -- log2(depth) wires
  data : List Wire         -- width wires (outputs)
  deriving Repr

/-- RAM primitive — opaque to proofs, known to codegen.
    Multi-port: configurable write/read port lists. -/
structure RAMPrimitive where
  name       : String
  depth      : Nat         -- number of entries
  width      : Nat         -- bits per entry
  writePorts : List RAMWritePort
  readPorts  : List RAMReadPort
  syncRead   : Bool := false  -- false → Mem (async), true → SyncReadMem (sync)
  clock      : Wire
  deriving Repr

-- Circuit: a complete circuit with inputs, outputs, gates, and submodules
structure Circuit where
  name       : String           -- Module/circuit name
  inputs     : List Wire        -- Input signals
  outputs    : List Wire        -- Output signals
  gates      : List Gate        -- Internal gates
  instances  : List CircuitInstance -- Submodule instances
  -- v2: codegen annotations (ignored by proofs, all default to [])
  signalGroups  : List SignalGroup      := []
  inputBundles  : List InterfaceBundle  := []
  outputBundles : List InterfaceBundle  := []
  rams          : List RAMPrimitive     := []
  keepHierarchy : Bool                  := false
  deriving Repr

namespace Circuit

-- Helper to create empty circuit
def empty (name : String) : Circuit :=
  { name := name, inputs := [], outputs := [], gates := [], instances := []
    signalGroups := [], inputBundles := [], outputBundles := [], rams := [] }

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
  | GateType.DFF | GateType.DFF_SET => false

def GateType.isSequential (gt : GateType) : Bool :=
  !gt.isCombinational

/-- Returns true for both DFF and DFF_SET gate types -/
def GateType.isDFF (gt : GateType) : Bool :=
  match gt with
  | GateType.DFF | GateType.DFF_SET => true
  | _ => false

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
