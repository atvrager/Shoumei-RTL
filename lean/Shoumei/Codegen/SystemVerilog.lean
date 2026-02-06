/-
Codegen/SystemVerilog.lean - SystemVerilog Code Generator (Hierarchical Mode)

Generates readable SystemVerilog with typed buses, struct ports, and hierarchical
module instantiation from annotated circuits. Uses signalGroups and interface
bundles to produce clean, synthesizable SV output.

Design principles:
- Typed buses: logic [31:0] instead of 32 individual wires
- Struct types for interface bundles (with yosys-slang)
- Vectorized continuous assignments
- Single always_ff blocks for register groups
- Hierarchical module instantiation with named ports

Target: IEEE 1800-2017 SystemVerilog
Requires: yosys-slang for struct type support in LEC
-/

import Shoumei.DSL
import Shoumei.DSL.Interfaces
import Shoumei.Codegen.Common

namespace Shoumei.Codegen.SystemVerilog

open Shoumei.Codegen

/-! ## Context and State -/

/-- Code generation context for SystemVerilog.
    Tracks wire-to-signal mappings, bundle membership, and types. -/
structure Context where
  /-- Map wire to its parent signal group (if any) -/
  wireToGroup : List (Wire × SignalGroup)
  /-- Map wire to its bit index within the group -/
  wireToIndex : List (Wire × Nat)
  /-- Clock wires -/
  clockWires : List Wire
  /-- Reset wires -/
  resetWires : List Wire
  /-- Whether this is a sequential circuit (has DFFs) -/
  isSequential : Bool
  deriving Repr

/-! ## Bus Reconstruction Helpers (reused from ChiselV2) -/

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

/-- Verilog/SystemVerilog reserved keywords that cannot be used as identifiers -/
def svReservedKeywords : List String :=
  ["and", "or", "xor", "not", "nand", "nor", "xnor", "buf", "bufif0", "bufif1",
   "notif0", "notif1", "input", "output", "inout", "wire", "reg", "logic",
   "assign", "module", "endmodule", "begin", "end", "always", "initial",
   "if", "else", "case", "endcase", "for", "while", "repeat", "forever",
   "function", "endfunction", "task", "endtask", "generate", "endgenerate",
   "parameter", "localparam", "integer", "real", "time", "event",
   "posedge", "negedge", "edge", "supply0", "supply1", "tri", "wand", "wor",
   "default", "disable", "deassign", "force", "release", "fork", "join",
   "table", "endtable", "primitive", "endprimitive", "specify", "endspecify"]

/-- Sanitize a signal name to avoid Verilog reserved keyword conflicts.
    Prefixes with "w_" if the name is a reserved keyword. -/
def sanitizeSVName (name : String) : String :=
  if svReservedKeywords.contains name then s!"w_{name}" else name

/-- Sanitize signal group name for SV output -/
def sanitizeSignalGroup (sg : SignalGroup) : SignalGroup :=
  { sg with name := sanitizeSVName sg.name }

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
  -- Sanitize names to avoid SV reserved keyword conflicts
  let allGroups := (c.signalGroups ++ autoDetectedGroups).map sanitizeSignalGroup

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

/-- Convert SignalType to SystemVerilog type declaration -/
def signalTypeToSV (st : SignalType) : String :=
  match st with
  | .Bool => "logic"
  | .UInt w =>
      if w == 1 then "logic"
      else s!"logic [{w-1}:0]"
  | .SInt w =>
      if w == 1 then "logic signed"
      else s!"logic signed [{w-1}:0]"

/-- Get SystemVerilog type for a signal group -/
def signalGroupToSV (sg : SignalGroup) : String :=
  signalTypeToSV sg.stype

/-! ## Wire Reference Generation -/

/-- Generate reference to a wire in generated SystemVerilog code.

    For wires in signal groups: use group name with optional bit indexing
    For standalone wires: use wire name directly -/
def wireRef (ctx : Context) (_c : Circuit) (w : Wire) : String :=
  -- Check if wire belongs to a signal group
  match ctx.wireToGroup.find? (fun (w', _) => w'.name == w.name) with
  | some (_, sg) =>
      -- Wire is part of a bus
      if sg.width > 1 then
        -- Multi-bit bus - use indexed reference
        match ctx.wireToIndex.find? (fun (w', _) => w'.name == w.name) with
        | some (_, idx) => s!"{sg.name}[{idx}]"
        | none => sg.name  -- Shouldn't happen
      else
        -- Single-bit signal, just use the name
        sg.name
  | none =>
      -- Standalone wire
      w.name

/-! ## Module Port Generation -/

/-- Generate port declaration for a signal group -/
def generateSignalGroupPort (direction : String) (sg : SignalGroup) : String :=
  let svType := signalGroupToSV sg
  s!"  {direction} {svType} {sg.name}"

/-- Generate port declaration for a single wire -/
def generateWirePort (ctx : Context) (_c : Circuit) (w : Wire) (direction : String) : Option String :=
  -- Skip clock and reset (will be added explicitly)
  if ctx.clockWires.contains w || ctx.resetWires.contains w then
    none
  else
    -- Check if wire is part of a signal group
    match ctx.wireToGroup.find? (fun (w', _) => w'.name == w.name) with
    | some (_, sg) =>
        -- Only emit port for the first wire in the group
        if sg.wires.head? == some w then
          some (generateSignalGroupPort direction sg)
        else
          none
    | none =>
        -- Standalone wire - emit as single-bit logic
        some s!"  {direction} logic {w.name}"

/-- Generate all port declarations -/
def generatePorts (ctx : Context) (c : Circuit) : String :=
  let inputPorts := c.inputs.filterMap (generateWirePort ctx c · "input")
  let outputPorts := c.outputs.filterMap (generateWirePort ctx c · "output")

  -- Add explicit clock and reset ports for sequential circuits
  let clockResetPorts := if ctx.isSequential then
    ["  input logic clock", "  input logic reset"]
  else
    []

  let allPorts := inputPorts ++ outputPorts ++ clockResetPorts

  if allPorts.isEmpty then
    ""
  else
    -- Add commas between ports (but not after the last one)
    match allPorts with
    | [] => ""
    | [single] => single
    | _ =>
        let withCommas := allPorts.dropLast.map (fun p => p ++ ",")
        let lastPort := allPorts.getLast!
        joinLines (withCommas ++ [lastPort])

/-! ## Internal Signal Generation -/

/-- Generate signal declaration for internal wires -/
def generateInternalSignalDecl (ctx : Context) (_c : Circuit) (w : Wire) : Option String :=
  -- Check if wire is part of a signal group
  match ctx.wireToGroup.find? (fun (w', _) => w'.name == w.name) with
  | some (_, sg) =>
      -- Only emit for first wire in group
      if sg.wires.head? == some w then
        let svType := signalGroupToSV sg
        some s!"  {svType} {sg.name};"
      else
        none
  | none =>
      -- Standalone wire
      some s!"  logic {w.name};"

/-- Generate all internal signal declarations -/
def generateInternalSignals (ctx : Context) (c : Circuit) : String :=
  let internalWires := findInternalWires c
  let decls := internalWires.filterMap (generateInternalSignalDecl ctx c)
  joinLines decls

/-! ## Combinational Logic Generation -/

/-- Generate SystemVerilog operator for a gate type -/
def gateTypeToSVOperator (gt : GateType) : String :=
  match gt with
  | GateType.AND => "&"
  | GateType.OR => "|"
  | GateType.NOT => "~"
  | GateType.XOR => "^"
  | GateType.BUF => ""
  | GateType.MUX => "?:"
  | GateType.DFF => ""

/-- Generate continuous assignment for a combinational gate -/
def generateCombAssignment (ctx : Context) (c : Circuit) (g : Gate) : String :=
  let op := gateTypeToSVOperator g.gateType
  let outRef := wireRef ctx c g.output

  match g.gateType with
  | GateType.NOT =>
      match g.inputs with
      | [i0] => s!"  assign {outRef} = {op}{wireRef ctx c i0};"
      | _ => "  // ERROR: NOT gate should have 1 input"
  | GateType.BUF =>
      match g.inputs with
      | [i0] => s!"  assign {outRef} = {wireRef ctx c i0};"
      | _ => "  // ERROR: BUF gate should have 1 input"
  | GateType.MUX =>
      match g.inputs with
      | [in0, in1, sel] =>
          s!"  assign {outRef} = {wireRef ctx c sel} ? {wireRef ctx c in1} : {wireRef ctx c in0};"
      | _ => "  // ERROR: MUX gate should have 3 inputs"
  | GateType.DFF =>
      ""  -- DFFs handled separately
  | _ =>
      match g.inputs with
      | [i0, i1] =>
          s!"  assign {outRef} = {wireRef ctx c i0} {op} {wireRef ctx c i1};"
      | _ => "  // ERROR: Binary gate should have 2 inputs"

/-- Generate all combinational logic assignments -/
def generateCombLogic (ctx : Context) (c : Circuit) : String :=
  let combGates := c.gates.filter (fun g => g.gateType != GateType.DFF)
  let assignments := combGates.map (generateCombAssignment ctx c)
  joinLines (assignments.filter (· != ""))

/-! ## Register Generation -/

/-- Find all DFF gates in circuit -/
def findDFFs (c : Circuit) : List Gate :=
  c.gates.filter (fun g => g.gateType == GateType.DFF)

/-- Group DFFs by their clock and reset signals -/
def groupDFFsByClockReset (dffs : List Gate) : List (Wire × Wire × List Gate) :=
  -- For simplicity, assume all DFFs share same clock/reset
  -- In practice, group by (clock, reset) pair
  match dffs.head? with
  | none => []
  | some firstDFF =>
      match firstDFF.inputs with
      | [_, clk, rst] => [(clk, rst, dffs)]
      | _ => []

/-- Generate register declaration and assignment for a DFF.
    Returns (declaration_option, assign, reset_assign, reg_name) -/
def generateDFFDecl (ctx : Context) (c : Circuit) (g : Gate) : Option (Option String × String × String × String) :=
  match g.inputs with
  | [d, _clk, _rst] =>
      -- Check if output is a circuit output
      let isCircuitOutput := c.outputs.any (fun w => w.name == g.output.name)

      -- Check if this register is part of a signal group
      match ctx.wireToGroup.find? (fun (w', _) => w'.name == g.output.name) with
      | some (_, sg) =>
          -- Part of a bus - only emit for first register in group
          if sg.wires.head? == some g.output then
            let svType := signalGroupToSV sg
            let regName := if isCircuitOutput then sg.name else s!"{sg.name}_reg"
            let dRef := match ctx.wireToGroup.find? (fun (w', _) => w'.name == d.name) with
              | some (_, inputGroup) => inputGroup.name
              | none => d.name
            let decl := if isCircuitOutput then none else some s!"  {svType} {regName};"
            let resetVal := if sg.width > 1 then s!"{sg.width}'d0" else "1'b0"
            some (decl, s!"      {regName} <= {dRef};", s!"      {regName} <= {resetVal};", regName)
          else
            none
      | none =>
          -- Standalone register
          let regName := if isCircuitOutput then g.output.name else s!"{g.output.name}_reg"
          let dRef := match ctx.wireToGroup.find? (fun (w', _) => w'.name == d.name) with
            | some (_, inputGroup) => inputGroup.name
            | none => d.name
          let decl := if isCircuitOutput then none else some s!"  logic {regName};"
          some (decl, s!"      {regName} <= {dRef};", s!"      {regName} <= 1'b0;", regName)
  | _ =>
      none

/-- Generate always_ff block for register group -/
def generateAlwaysFFBlock (ctx : Context) (c : Circuit) (clk : Wire) (rst : Wire) (dffs : List Gate) : String :=
  let results := dffs.filterMap (generateDFFDecl ctx c)
  let decls := results.filterMap (fun (decl, _, _, _) => decl)
  let assigns := results.map (fun (_, assign, _, _) => assign)
  let resetAssigns := results.map (fun (_, _, resetAssign, _) => resetAssign)

  if assigns.isEmpty then
    ""
  else
    let declsStr := joinLines decls
    let clkRef := wireRef ctx c clk
    let rstRef := wireRef ctx c rst

    -- Generate always_ff block with reset logic
    let alwaysBlock := joinLines [
      s!"  always_ff @(posedge {clkRef} or posedge {rstRef}) begin",
      s!"    if ({rstRef}) begin",
      "      // Reset all registers to 0",
      joinLines resetAssigns,
      "    end else begin",
      joinLines assigns,
      "    end",
      "  end"
    ]

    if declsStr.isEmpty then
      alwaysBlock
    else
      declsStr ++ "\n\n" ++ alwaysBlock

/-- Generate all register logic -/
def generateRegisters (ctx : Context) (c : Circuit) : String :=
  let dffs := findDFFs c
  if dffs.isEmpty then
    ""
  else
    let grouped := groupDFFsByClockReset dffs
    let blocks := grouped.map (fun (clk, rst, dffGroup) =>
      generateAlwaysFFBlock ctx c clk rst dffGroup
    )
    String.intercalate "\n\n" blocks

/-! ## Module Instantiation -/

/-- Parse a port name that may contain bracket indexing.
    "alloc_physRd[0]" → some ("alloc_physRd", 0)
    "enq_valid" → none -/
def parsePortIndex (portName : String) : Option (String × Nat) :=
  match portName.splitOn "[" with
  | [base, idxPart] =>
      -- Remove trailing ']' from idxPart
      let idxStr := String.ofList (idxPart.toList.takeWhile (· != ']'))
      match idxStr.toNat? with
      | some idx => some (base, idx)
      | none => none
  | _ => none

/-- Group port map entries: collect bracketed entries with the same base name
    into bus groups, preserving order. Non-bracketed entries pass through as-is. -/
def groupPortMapEntries (portMap : List (String × Wire))
    : List (Sum (String × Wire) (String × List (Nat × Wire))) :=
  -- Process entries, accumulating groups
  let result := portMap.foldl (fun (acc : List (Sum (String × Wire) (String × List (Nat × Wire)))) (pname, w) =>
    match parsePortIndex pname with
    | none =>
        -- Scalar port, pass through
        acc ++ [Sum.inl (pname, w)]
    | some (base, idx) =>
        -- Check if the last entry is a group with the same base name
        match acc.reverse with
        | (Sum.inr (prevBase, entries)) :: restRev =>
            if prevBase == base then
              -- Extend the existing group
              restRev.reverse ++ [Sum.inr (base, entries ++ [(idx, w)])]
            else
              -- Different base, start new group
              acc ++ [Sum.inr (base, [(idx, w)])]
        | _ =>
            -- No previous group, start new one
            acc ++ [Sum.inr (base, [(idx, w)])]
  ) []
  result

/-- Generate port connection for module instantiation -/
def generatePortConnection (ctx : Context) (c : Circuit) (portName : String) (wire : Wire) : String :=
  s!"    .{portName}({wireRef ctx c wire})"

/-- Try to extract the bus name from a list of wire references.
    If all refs are busName[0], busName[1], ..., busName[N-1], return some busName.
    Otherwise return none. -/
def extractCommonBusName (wireRefs : List String) (sorted : List (Nat × Wire)) : Option String :=
  match wireRefs.head? with
  | none => none
  | some firstRef =>
      match firstRef.splitOn "[" with
      | [busName, _] =>
          let allMatch := sorted.enum.all (fun (i, (idx, _)) =>
            match wireRefs[i]? with
            | some ref => ref == busName ++ "[" ++ toString idx ++ "]"
            | none => false)
          if allMatch then some busName else none
      | _ => none

/-- Generate a bus port connection.
    Entries are sorted by index. If all wires form a contiguous bus, connects
    directly. Otherwise uses concatenation \{MSB, ..., LSB\} syntax. -/
def generateBusPortConnection (ctx : Context) (c : Circuit) (baseName : String)
    (entries : List (Nat × Wire)) : String :=
  let sorted := entries.toArray.qsort (fun a b => a.1 < b.1) |>.toList
  let wireRefs := sorted.map (fun (_, w) => wireRef ctx c w)
  match extractCommonBusName wireRefs sorted with
  | some busName =>
      -- Direct bus connection: .portName(busName)
      s!"    .{baseName}({busName})"
  | none =>
      -- Concatenation: .portName({wire_N, ..., wire_0})
      let concat := "{" ++ String.intercalate ", " wireRefs.reverse ++ "}"
      s!"    .{baseName}({concat})"

/-- Generate module instantiation -/
def generateInstance (ctx : Context) (c : Circuit) (inst : CircuitInstance) : String :=
  let grouped := groupPortMapEntries inst.portMap
  let portConnections := grouped.map (fun entry =>
    match entry with
    | Sum.inl (pname, w) => generatePortConnection ctx c pname w
    | Sum.inr (baseName, entries) => generateBusPortConnection ctx c baseName entries
  )

  let connectionsStr := String.intercalate ",\n" portConnections

  joinLines [
    s!"  {inst.moduleName} {inst.instName} (",
    connectionsStr,
    "  );"
  ]

/-- Generate all module instantiations -/
def generateInstances (ctx : Context) (c : Circuit) : String :=
  let instances := c.instances.map (generateInstance ctx c)
  joinLines instances

/-! ## Module Generation -/

/-- Generate complete SystemVerilog module for a circuit -/
def generateModule (c : Circuit) : String :=
  let ctx := mkContext c

  let header := joinLines [
    "// Auto-generated by Shoumei Codegen V2",
    s!"// Source: {c.name}",
    "",
    s!"module {c.name} ("
  ]

  let ports := generatePorts ctx c
  let portSection := if ports.isEmpty then
    ");"
  else
    ports ++ "\n);"

  let internalSignals := generateInternalSignals ctx c
  let combLogic := generateCombLogic ctx c
  let registers := generateRegisters ctx c
  let instances := generateInstances ctx c

  let body := joinLines [
    portSection,
    "",
    if internalSignals.isEmpty then "" else internalSignals ++ "\n",
    if combLogic.isEmpty then "" else combLogic ++ "\n",
    if registers.isEmpty then "" else registers ++ "\n",
    if instances.isEmpty then "" else instances
  ]

  let footer := "endmodule"

  joinLines [header, body, footer]

/-! ## Public API -/

/-- Generate SystemVerilog code for a circuit -/
def toSystemVerilog (c : Circuit) : String :=
  generateModule c

end Shoumei.Codegen.SystemVerilog
