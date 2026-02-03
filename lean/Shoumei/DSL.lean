/-
DSL.lean - Core Hardware DSL Definitions

Defines the basic types for representing hardware circuits:
- Wire: Signal identifiers
- GateType: Supported logic gate types (combinational and sequential)
- Gate: Logic gate with inputs and output
- Circuit: Complete circuit with inputs, outputs, and gates

Supports both combinational (AND, OR, NOT, XOR) and sequential (DFF) elements.
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

/-! ## Codegen V2: Signal Type Annotations

These types provide optional metadata for code generators to produce
readable, type-aware output (buses, interfaces, RAMs) instead of
flat bit-level signals. They do NOT affect the proof core -- the
gate list remains the single source of truth for semantics.
-/

/-- Signal type annotation for codegen. Describes the logical type of a
    group of wires (e.g., 32 bits forming a UInt). -/
inductive SignalType where
  | Bool                    -- Single bit
  | UInt (width : Nat)      -- Unsigned multi-bit
  | SInt (width : Nat)      -- Signed multi-bit
  deriving Repr, BEq, Inhabited

/-- A group of wires that form a single logical signal (e.g., a 32-bit bus).
    Used by codegen to emit `logic [31:0] data_reg` instead of 32 individual wires. -/
structure SignalGroup where
  name  : String            -- Logical signal name (e.g., "data_reg")
  width : Nat               -- Bit width (should equal wires.length)
  wires : List Wire         -- The underlying flat wires, LSB first
  stype : SignalType := .UInt width
  deriving Repr

/-- An interface bundle groups signals into a named protocol-level interface
    (e.g., Decoupled with bits/valid/ready). Used by codegen to emit
    proper Chisel Bundles and SV struct types. -/
structure InterfaceBundle where
  name     : String                      -- Interface name (e.g., "enq", "cdb_0")
  signals  : List (String × SignalType)  -- Field name → type
  protocol : Option String := none       -- "decoupled" | "regwrite" | "regread" | none
  deriving Repr

/-- RAM write port descriptor. -/
structure RAMWritePort where
  en   : Wire              -- Write enable
  addr : List Wire         -- Address wires (log2(depth) bits)
  data : List Wire         -- Write data wires (width bits)
  deriving Repr

/-- RAM read port descriptor. -/
structure RAMReadPort where
  addr : List Wire         -- Address wires (log2(depth) bits)
  data : List Wire         -- Read data wires (width bits, outputs)
  deriving Repr

/-- RAM primitive -- opaque to proofs, known to codegen.
    Replaces thousands of DFFs + mux trees with a single semantic block. -/
structure RAMPrimitive where
  name       : String      -- Instance name (e.g., "u_mem")
  depth      : Nat         -- Number of entries (e.g., 64)
  width      : Nat         -- Bits per entry (e.g., 32)
  writePorts : List RAMWritePort
  readPorts  : List RAMReadPort
  syncRead   : Bool := false  -- false → Mem (async read), true → SyncReadMem (sync read)
  clock      : Wire
  deriving Repr

-- Circuit: a complete circuit with inputs, outputs, gates, and submodules
structure Circuit where
  name : String           -- Module/circuit name
  inputs : List Wire      -- Input signals
  outputs : List Wire     -- Output signals
  gates : List Gate       -- Internal gates
  instances : List CircuitInstance -- Submodule instances
  -- v2: codegen annotations (optional, default empty, ignored by proofs)
  signalGroups  : List SignalGroup     := []
  inputBundles  : List InterfaceBundle := []
  outputBundles : List InterfaceBundle := []
  rams          : List RAMPrimitive    := []
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
  | GateType.DFF => false

def GateType.isSequential (gt : GateType) : Bool :=
  !gt.isCombinational

-- Check if a circuit has sequential elements
def Circuit.hasSequentialElements (c : Circuit) : Bool :=
  c.gates.any (fun g => g.gateType.isSequential)

-- Check if a circuit is purely combinational
def Circuit.isCombinational (c : Circuit) : Bool :=
  !c.hasSequentialElements

/-! ## Signal Group Helpers -/

/-- Create a list of indexed wires: name_0, name_1, ..., name_{n-1}.
    Canonical version -- modules can use this instead of local redefinitions. -/
def mkIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}_{i}")

/-- Create a SignalGroup from a base name and width.
    Generates wires name_0..name_{width-1} and bundles them. -/
def SignalGroup.mk' (name : String) (width : Nat)
    (stype : SignalType := .UInt width) : SignalGroup :=
  { name := name, width := width, wires := mkIndexedWires name width, stype := stype }

-- TODO: Add validation functions:
-- - Check that all gate inputs are either circuit inputs or outputs of previous gates
-- - Check that all gate outputs are unique (no wire driven by multiple gates)
-- - Check that circuit outputs are driven by some gate or are passthroughs
-- - Check that DFFs have exactly 3 inputs: [d, clk, reset]
-- - Check that clock and reset are properly connected
