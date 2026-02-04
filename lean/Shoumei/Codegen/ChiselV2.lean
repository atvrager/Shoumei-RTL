/-
Codegen/ChiselV2.lean - Chisel V2 Code Generator (Hierarchical Mode)

Generates proper Chisel with Bundles, UInt, Decoupled interfaces from
annotated circuits. Uses signalGroups and interface bundles to produce
readable, typed Chisel output.

Design principles:
- Single-assign style (no when blocks)
- Typed signals (UInt, Bool, Bundles) from annotations
- ShoumeiReg wrapper for consistent register handling
- Bus reconstruction for vectorized operations
- Decoupled helper for ready/valid interfaces

Target: Chisel 7.x (Scala 2.13)
Output compiled to SystemVerilog via FIRRTL/CIRCT
-/

import Shoumei.DSL
import Shoumei.DSL.Interfaces
import Shoumei.Codegen.Common

namespace Shoumei.Codegen.ChiselV2

open Shoumei.Codegen

/-! ## Context and State -/

/-- Code generation context for ChiselV2.
    Tracks wire-to-signal mappings, bundle membership, and types. -/
structure Context where
  /-- Map wire to its parent signal group (if any) -/
  wireToGroup : List (Wire × SignalGroup)
  /-- Map wire to its bit index within the group -/
  wireToIndex : List (Wire × Nat)
  /-- Clock wires (implicit in Module) -/
  clockWires : List Wire
  /-- Reset wires (implicit in Module) -/
  resetWires : List Wire
  /-- Whether this is a sequential circuit (has DFFs) -/
  isSequential : Bool
  deriving Repr

/-! ## Bus Reconstruction Helpers -/

/-- Parse a wire name to extract base name and optional index.
    Examples: "data_31" → some ("data", 31), "valid" → none -/
def parseWireName (w : Wire) : Option (String × Nat) :=
  let name := w.name
  -- Find the last underscore
  match name.splitOn "_" with
  | [] => none
  | parts =>
      match parts.reverse with
      | [] => none
      | lastPart :: restReversed =>
          -- Check if last part is a number
          match lastPart.toNat? with
          | some idx =>
              let baseName := String.intercalate "_" restReversed.reverse
              some (baseName, idx)
          | none => none

/-- Group wires by base name (for bus reconstruction) -/
def groupWiresByBaseName (wires : List Wire) : List (String × List (Nat × Wire)) :=
  let parsed := wires.filterMap (fun w =>
    match parseWireName w with
    | some (base, idx) => some (base, idx, w)
    | none => none
  )
  -- Group by base name
  let grouped := parsed.foldl (fun acc (base, idx, w) =>
    match acc.find? (fun p => p.1 == base) with
    | some (_, existing) =>
        acc.filter (fun p => p.1 != base) ++ [(base, existing ++ [(idx, w)])]
    | none =>
        acc ++ [(base, [(idx, w)])]
  ) []
  grouped

/-- Check if a list of (index, wire) pairs forms a valid bus.
    Valid means: indices are contiguous from 0 to N-1 -/
def isValidBus (indexedWires : List (Nat × Wire)) : Bool :=
  if indexedWires.isEmpty then false
  else
    let indices := indexedWires.map (·.1)
    let sorted := indices.toArray.qsort (· < ·) |>.toList
    -- Check if sorted indices are [0, 1, 2, ..., n-1]
    sorted == List.range sorted.length

/-- Auto-detect signal groups from wire naming patterns -/
def autoDetectSignalGroups (wires : List Wire) : List SignalGroup :=
  let grouped := groupWiresByBaseName wires
  grouped.filterMap (fun (baseName, indexedWires) =>
    if isValidBus indexedWires then
      -- Sort wires by index to ensure correct order
      let sortedWires := indexedWires.toArray.qsort (fun a b => a.1 < b.1)
                         |>.toList.map (·.2)
      let width := sortedWires.length
      some { name := baseName, width := width, wires := sortedWires }
    else
      none
  )

/-- Find all internal wires (not inputs or outputs) -/
def findInternalWires (c : Circuit) : List Wire :=
  let gateOutputs := c.gates.map (fun g => g.output)
  let instanceWires := c.instances.flatMap (fun inst => inst.portMap.map (fun p => p.2))
  (gateOutputs ++ instanceWires).eraseDups.filter (fun w =>
    !c.inputs.contains w && !c.outputs.contains w
  )

/-- Build context from circuit -/
def mkContext (c : Circuit) : Context :=
  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let isSequential := c.gates.any (fun g => g.gateType == GateType.DFF)

  -- Auto-detect signal groups from internal wires
  let internalWires := findInternalWires c
  let autoDetectedGroups := autoDetectSignalGroups internalWires

  -- Combine explicit annotations with auto-detected groups
  -- Explicit annotations take precedence (come first)
  let allGroups := c.signalGroups ++ autoDetectedGroups

  -- Build wire-to-group mapping from all signal groups
  let wireToGroup := allGroups.flatMap (fun sg =>
    sg.wires.map (fun w => (w, sg))
  )

  -- Build wire-to-index mapping (bit index within bus)
  let wireToIndex := allGroups.flatMap (fun sg =>
    sg.wires.enum.map (fun (idx, w) => (w, idx))
  )

  { wireToGroup, wireToIndex, clockWires, resetWires, isSequential }

/-! ## Signal Type Helpers -/

/-- Convert SignalType to Chisel type string -/
def signalTypeToChisel (st : SignalType) : String :=
  match st with
  | .Bool => "Bool()"
  | .UInt w => s!"UInt({w}.W)"
  | .SInt w => s!"SInt({w}.W)"

/-- Get Chisel type for a signal group -/
def signalGroupToChisel (sg : SignalGroup) : String :=
  signalTypeToChisel sg.stype

/-! ## Wire Reference Generation -/

/-- Generate reference to a wire in generated Chisel code.

    For wires in signal groups: use group name
    For bundle fields: use io.bundle_name.field_name
    For standalone wires: use wire name directly -/
def wireRef (ctx : Context) (_c : Circuit) (w : Wire) : String :=
  -- Check if this is clock or reset (should be implicit)
  if ctx.clockWires.contains w then
    "clock"
  else if ctx.resetWires.contains w then
    "reset.asBool"
  else
    -- Check if wire belongs to a signal group
    match ctx.wireToGroup.find? (fun (w', _) => w'.name == w.name) with
    | some (_, sg) =>
        -- Wire is part of a bus - check if it's multi-bit or single-bit
        if sg.width > 1 then
          -- Multi-bit bus - use indexed reference
          match ctx.wireToIndex.find? (fun (w', _) => w'.name == w.name) with
          | some (_, idx) => s!"{sg.name}({idx})"
          | none => sg.name  -- Shouldn't happen
        else
          -- Single-bit signal, just use the name
          sg.name
    | none =>
        -- Check if it's a bundle field
        -- For now, just use the wire name
        -- TODO: Implement bundle field resolution
        w.name

/-! ## Bundle Generation -/

/-- Generate Chisel Bundle class definition from InterfaceBundle -/
def generateBundleClass (bundle : InterfaceBundle) : String :=
  let fields := bundle.signals.map (fun (fname, stype) =>
    s!"  val {fname} = {signalTypeToChisel stype}"
  )
  joinLines (["class " ++ bundle.name ++ "_bundle extends Bundle {"] ++ fields ++ ["}"])

/-- Generate Interfaces.scala file with all bundle definitions -/
def generateInterfacesFile (bundles : List InterfaceBundle) : String :=
  let header := joinLines [
    "// Auto-generated by Shoumei Codegen V2",
    "// Shared Bundle definitions for typed interfaces",
    "",
    "package generated",
    "",
    "import chisel3._",
    "import chisel3.util._",
    ""
  ]

  let bundleDefs := bundles.map generateBundleClass
  let bundlesStr := String.intercalate "\n\n" bundleDefs

  header ++ bundlesStr ++ "\n"

/-! ## Module IO Generation -/

/-- Generate IO declaration for a single wire with inferred type -/
def generateWireIO (ctx : Context) (c : Circuit) (w : Wire) (isInput : Bool) : Option String :=
  -- Skip implicit clock/reset
  if ctx.clockWires.contains w || ctx.resetWires.contains w then
    none
  else
    -- Skip DFF outputs when they're circuit outputs (registers handle these)
    let isDFFOutput := c.gates.any (fun g => g.gateType == GateType.DFF && g.output.name == w.name)
    if !isInput && isDFFOutput then
      none
    else
      -- Check if wire is part of a signal group
      match ctx.wireToGroup.find? (fun (w', _) => w'.name == w.name) with
      | some (_, sg) =>
          -- Only emit IO for the first wire in the group (we'll create one typed signal)
          if sg.wires.head? == some w then
            let chiselType := signalGroupToChisel sg
            let dir := if isInput then "Input" else "Output"
            some s!"  val {sg.name} = IO({dir}({chiselType}))"
          else
            none  -- Skip other wires in the group
      | none =>
          -- Standalone wire - emit as Bool
          let dir := if isInput then "Input" else "Output"
          some s!"  val {w.name} = IO({dir}(Bool()))"

/-- Generate IO declarations for all ports -/
def generateIO (ctx : Context) (c : Circuit) : String :=
  let inputDecls := c.inputs.filterMap (generateWireIO ctx c · true)
  let outputDecls := c.outputs.filterMap (generateWireIO ctx c · false)

  -- For sequential circuits (Module), clock and reset are implicit
  -- For combinational circuits (RawModule), they must be explicit
  -- But since combinational circuits don't have DFFs, they won't have clock/reset anyway
  -- So we can skip the implicit declarations entirely

  joinLines (inputDecls ++ outputDecls)

/-! ## Internal Signal Generation -/

/-- Generate Wire declaration for internal signals -/
def generateInternalWireDecl (ctx : Context) (_c : Circuit) (w : Wire) : Option String :=
  -- Check if wire is part of a signal group
  match ctx.wireToGroup.find? (fun (w', _) => w'.name == w.name) with
  | some (_, sg) =>
      -- Only emit for first wire in group
      if sg.wires.head? == some w then
        let chiselType := signalGroupToChisel sg
        some s!"  val {sg.name} = Wire({chiselType})"
      else
        none
  | none =>
      -- Standalone wire
      some s!"  val {w.name} = Wire(Bool())"

/-- Generate all internal wire declarations -/
def generateInternalWires (ctx : Context) (c : Circuit) : String :=
  let internalWires := findInternalWires c
  let decls := internalWires.filterMap (generateInternalWireDecl ctx c)
  joinLines decls

/-! ## Gate Emission (with Bus Reconstruction) -/

/-- Generate Chisel operator for a gate type -/
def gateTypeToOperator (gt : GateType) : String :=
  match gt with
  | GateType.AND => "&"
  | GateType.OR => "|"
  | GateType.NOT => "~"
  | GateType.XOR => "^"
  | GateType.BUF => ""
  | GateType.MUX => "Mux"
  | GateType.DFF => ""

/-- Generate assignment for a combinational gate -/
def generateCombGate (ctx : Context) (c : Circuit) (g : Gate) : String :=
  let op := gateTypeToOperator g.gateType
  let outRef := wireRef ctx c g.output

  match g.gateType with
  | GateType.NOT =>
      match g.inputs with
      | [i0] => s!"  {outRef} := {op}{wireRef ctx c i0}"
      | _ => "  // ERROR: NOT gate should have 1 input"
  | GateType.BUF =>
      match g.inputs with
      | [i0] => s!"  {outRef} := {wireRef ctx c i0}"
      | _ => "  // ERROR: BUF gate should have 1 input"
  | GateType.MUX =>
      match g.inputs with
      | [in0, in1, sel] =>
          s!"  {outRef} := Mux({wireRef ctx c sel}, {wireRef ctx c in1}, {wireRef ctx c in0})"
      | _ => "  // ERROR: MUX gate should have 3 inputs"
  | GateType.DFF =>
      ""  -- DFFs handled separately
  | _ =>
      match g.inputs with
      | [i0, i1] =>
          s!"  {outRef} := {wireRef ctx c i0} {op} {wireRef ctx c i1}"
      | _ => "  // ERROR: Binary gate should have 2 inputs"

/-- Generate all combinational gate logic -/
def generateCombGates (ctx : Context) (c : Circuit) : String :=
  let combGates := c.gates.filter (fun g => g.gateType != GateType.DFF)
  let assignments := combGates.map (generateCombGate ctx c)
  joinLines (assignments.filter (· != ""))

/-! ## Register Generation (ShoumeiReg) -/

/-- Find all DFF gates in circuit -/
def findDFFs (c : Circuit) : List Gate :=
  c.gates.filter (fun g => g.gateType == GateType.DFF)

/-- Generate register declaration using ShoumeiReg helper -/
def generateRegisterDecl (ctx : Context) (c : Circuit) (g : Gate) : String :=
  match g.inputs with
  | [_d, clk, _rst] =>
      -- Check if this register output is also a circuit output
      let isCircuitOutput := c.outputs.any (fun w => w.name == g.output.name)

      -- Check if this register is part of a signal group
      match ctx.wireToGroup.find? (fun (w', _) => w'.name == g.output.name) with
      | some (_, sg) =>
          -- Part of a bus - only emit for first register in group
          if sg.wires.head? == some g.output then
            let clockRef := wireRef ctx c clk
            let resetRef := if ctx.isSequential then
              -- Module has implicit reset (type Reset, need to cast to AsyncReset)
              "reset.asAsyncReset"
            else
              -- RawModule needs explicit reset (shouldn't happen for DFFs, but fallback)
              match ctx.resetWires.head? with
              | some rw => rw.name
              | none => "reset"
            -- If it's a circuit output, don't add _reg suffix
            let regName := if isCircuitOutput then sg.name else s!"{sg.name}_reg"
            s!"  val {regName} = ShoumeiReg({sg.width}, {clockRef}, {resetRef})"
          else
            ""
      | none =>
          -- Standalone register
          let clockRef := wireRef ctx c clk
          let resetRef := if ctx.isSequential then
            "reset.asAsyncReset"
          else
            match ctx.resetWires.head? with
            | some rw => rw.name
            | none => "reset"
          let regName := if isCircuitOutput then g.output.name else s!"{g.output.name}_reg"
          s!"  val {regName} = ShoumeiReg(1, {clockRef}, {resetRef})"
  | _ =>
      "  // ERROR: DFF should have 3 inputs [d, clk, reset]"

/-- Generate register update assignments (single-assign style) -/
def generateRegisterUpdate (ctx : Context) (c : Circuit) (g : Gate) : String :=
  match g.inputs with
  | [d, _clk, _rst] =>
      -- Check if this register output is also a circuit output
      let isCircuitOutput := c.outputs.any (fun w => w.name == g.output.name)

      -- Check if register output is part of a signal group
      match ctx.wireToGroup.find? (fun (w', _) => w'.name == g.output.name) with
      | some (_, outputGroup) =>
          -- Part of a bus - only emit for first register
          if outputGroup.wires.head? == some g.output then
            -- Find the D input's signal group (if any)
            let dName := match ctx.wireToGroup.find? (fun (w', _) => w'.name == d.name) with
              | some (_, inputGroup) => inputGroup.name
              | none => d.name  -- Fallback to wire name
            let regName := if isCircuitOutput then outputGroup.name else s!"{outputGroup.name}_reg"
            s!"  {regName} := {dName}"
          else
            ""
      | none =>
          -- Standalone register
          let dName := match ctx.wireToGroup.find? (fun (w', _) => w'.name == d.name) with
            | some (_, inputGroup) => inputGroup.name
            | none => d.name
          let regName := if isCircuitOutput then g.output.name else s!"{g.output.name}_reg"
          s!"  {regName} := {dName}"
  | _ =>
      ""

/-- Generate all register logic -/
def generateRegisters (ctx : Context) (c : Circuit) : String :=
  let dffs := findDFFs c
  let decls := dffs.map (generateRegisterDecl ctx c)
  let updates := dffs.map (generateRegisterUpdate ctx c)

  let declsStr := joinLines (decls.filter (· != ""))
  let updatesStr := joinLines (updates.filter (· != ""))

  if declsStr.isEmpty then
    ""
  else
    declsStr ++ "\n\n" ++ updatesStr

/-! ## Module Generation -/

/-- Generate complete Chisel module for a circuit -/
def generateModule (c : Circuit) : String :=
  let ctx := mkContext c

  -- Module or RawModule based on sequential/combinational
  let moduleType := if ctx.isSequential then "Module" else "RawModule"

  let header := joinLines [
    s!"// Auto-generated by Shoumei Codegen V2",
    s!"// Source: {c.name}",
    "",
    "package generated",
    "",
    "import chisel3._",
    "import chisel3.util._",
    "import shoumei.ShoumeiReg",
    "",
    "class " ++ c.name ++ " extends " ++ moduleType ++ " {"
  ]

  let io := generateIO ctx c
  let internalWires := generateInternalWires ctx c
  let combGates := generateCombGates ctx c
  let registers := generateRegisters ctx c

  let body := joinLines [
    io,
    "",
    internalWires,
    "",
    combGates,
    "",
    registers
  ]

  let footer := "}"

  joinLines [header, body, footer]

/-! ## Public API -/

/-- Generate Chisel V2 code for a circuit -/
def toChiselV2 (c : Circuit) : String :=
  generateModule c

end Shoumei.Codegen.ChiselV2
