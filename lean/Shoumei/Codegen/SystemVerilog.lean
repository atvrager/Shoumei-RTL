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
Requires: a SystemVerilog frontend that understands struct types (e.g. yosys-slang)
-/

import Shoumei.DSL
import Shoumei.DSL.Interfaces
import Shoumei.Codegen.Common
import Shoumei.Codegen.SVA
import Std.Data.HashMap
import Std.Data.HashSet

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

/-! ## Bus Reconstruction Helpers -/

/-- Parse a wire name to extract base name and optional index.
    Examples: "data_31" → some ("data", 31), "x[3]" → some ("x", 3), "valid" → none -/
def parseWireName (w : Wire) : Option (String × Nat) :=
  let name := w.name
  match name.splitOn "[" with
  | [base, idxPart] =>
      let idxStr := String.ofList (idxPart.toList.takeWhile (· != ']'))
      match idxStr.toNat? with
      | some idx => some (base, idx)
      | none => none
  | _ =>
      let parts := name.splitOn "_"
      if parts.length >= 2 then
        let lastPart := parts.getLast!
        match lastPart.toNat? with
        | some idx =>
            let base := String.intercalate "_" parts.dropLast
            if base.isEmpty then none else some (base, idx)
        | none => none
      else
        none

/-- Group wires by base name (for bus reconstruction) -/
def groupWiresByBaseName (wires : List Wire) : List (String × List (Nat × Wire)) := Id.run do
  let parsed := wires.filterMap (fun w =>
    match parseWireName w with
    | some (base, idx) => some (base, idx, w)
    | none => none
  )
  let mut map : Std.HashMap String (List (Nat × Wire)) := {}
  let mut order : List String := []
  for (base, idx, w) in parsed do
    match map[base]? with
    | some existing =>
        map := map.insert base (existing ++ [(idx, w)])
    | none =>
        map := map.insert base [(idx, w)]
        order := order ++ [base]
  let mut result : List (String × List (Nat × Wire)) := []
  for base in order do
    if let some entries := map[base]? then
      result := result ++ [(base, entries)]
  result

/-- Check if a list of (index, wire) pairs forms a valid bus.
    Valid means: at least 2 wires with contiguous indices [start, start+1, ..., start+N-1]. -/
def isValidBus (indexedWires : List (Nat × Wire)) : Bool :=
  if indexedWires.length <= 1 then false
  else
    let indices := indexedWires.map (·.1)
    let sorted := indices.toArray.qsort (· < ·) |>.toList
    match sorted.head? with
    | some h => sorted == (List.range sorted.length).map (· + h)
    | none => false

/-- Auto-detect signal groups from wire naming patterns -/
def autoDetectSignalGroups (wires : List Wire) : List SignalGroup :=
  let wireNameSet : Std.HashSet String := wires.foldl (fun s w => s.insert w.name) {}
  let grouped := groupWiresByBaseName wires
  grouped.filterMap (fun (baseName, indexedWires) =>
    if isValidBus indexedWires && !wireNameSet.contains baseName then
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
  let ramWires := c.rams.flatMap (fun ram =>
    let wpWires := ram.writePorts.flatMap (fun wp => [wp.en] ++ wp.addr ++ wp.data)
    let rpWires := ram.readPorts.flatMap (fun rp => rp.addr ++ rp.data)
    wpWires ++ rpWires)
  dedupWires (gateOutputs ++ instanceWires ++ ramWires) |>.filter (fun w =>
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
   "table", "endtable", "primitive", "endprimitive", "specify", "endspecify",
   "const", "type", "byte", "shortint", "int", "longint", "bit", "void",
   "shortreal", "struct", "union", "enum", "string", "chandle", "class",
   "interface", "package", "import", "export", "final", "return", "break", "continue"]

/-- Sanitize a signal name to avoid Verilog reserved keyword conflicts.
    Prefixes with "w_" if the name is a reserved keyword. -/
def sanitizeSVName (name : String) : String :=
  if svReservedKeywords.contains name then s!"w_{name}" else name

/-- Sanitize signal group name for SV output -/
def sanitizeSignalGroup (sg : SignalGroup) : SignalGroup :=
  { sg with name := sanitizeSVName sg.name }

/-- Extract base name from a wire name by stripping digit suffix.
    Examples: "addr_0" -> "addr", "sel_1" -> "sel", "data" -> "data" -/
private def extractBaseName (wireName : String) : String :=
  let parts := wireName.splitOn "_"
  if parts.length >= 2 then
    let lastPart := parts.getLast!
    if lastPart.toNat?.isSome then
      String.intercalate "_" (parts.dropLast)
    else
      wireName
  else
    wireName

/-- Check if an output signal group needs individual bit-level port declarations
    rather than a single vectorized port.
    Always returns false to ensure clean, human-readable SystemVerilog vector ports. -/
def outputNeedsIndividualPorts (_wireToGroup : List (Wire × SignalGroup))
    (_wireToIndex : List (Wire × Nat)) (_c : Circuit) (_sg : SignalGroup) : Bool :=
  false

/-- Build context from circuit -/
def mkContext (c : Circuit) : Context :=
  let clockWires := findClockWires c
  let resetWires := findResetWires c
  -- A circuit is sequential if it has DFF gates OR clock/reset wires
  -- (hierarchical modules may have no DFFs but pass clock/reset to instances)
  let isSequential := c.gates.any (fun g => g.gateType.isDFF) ||
                      !clockWires.isEmpty || !resetWires.isEmpty

  -- Auto-detect signal groups from all wires not explicitly grouped (inputs, outputs, and internal)
  let allCircuitWires := c.inputs ++ c.outputs ++ findInternalWires c
  let explicitWires := c.signalGroups.flatMap (·.wires) |>.map (·.name)
  let unassignedWires := allCircuitWires.filter (fun w => !explicitWires.contains w.name)
  let autoDetectedGroups := autoDetectSignalGroups unassignedWires

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
    For output signal group wires: use wire name directly (ports are individual)
    For standalone wires: use wire name directly -/
def wireRef (ctx : Context) (c : Circuit) (w : Wire) : String :=
  -- Check if wire belongs to a signal group
  match ctx.wireToGroup.find? (fun (w', _) => w'.name == w.name) with
  | some (_, sg) =>
      -- Output signal group wires with individual ports use wire names directly
      let isOutput := c.outputs.any (fun ow => ow.name == w.name)
      let outputSg := if isOutput then
        -- Find the signal group this output wire belongs to
        ctx.wireToGroup.find? (fun (w', _) => w'.name == w.name) |>.map (·.2)
      else none
      let needsIndividual := match outputSg with
        | some osg => outputNeedsIndividualPorts ctx.wireToGroup ctx.wireToIndex c osg
        | none => false
      if needsIndividual then
        w.name
      else if sg.width > 1 then
        -- Multi-bit bus - use indexed reference
        match ctx.wireToIndex.find? (fun (w', _) => w'.name == w.name) with
        | some (_, idx) => s!"{sg.name}[{idx}]"
        | none => sg.name  -- Shouldn't happen
      else
        -- Single-bit signal, just use the name
        sg.name
  | none =>
      -- Standalone wire
      sanitizeSVName w.name

/-! ## Module Port Generation -/

/-- Generate port declaration for a signal group -/
def generateSignalGroupPort (direction : String) (sg : SignalGroup) : String :=
  let svType := signalGroupToSV sg
  s!"  {direction} {svType} {sg.name}"

/-- Generate port declaration(s) for a single wire.
    Returns a list of port strings because output signal groups expand to multiple ports. -/
def generateWirePorts (ctx : Context) (_c : Circuit) (w : Wire) (direction : String) : List String :=
  -- Skip clock and reset (will be added explicitly)
  if ctx.clockWires.contains w || ctx.resetWires.contains w then
    []
  else
    -- Check if wire is part of a signal group
    match ctx.wireToGroup.find? (fun (w', _) => w'.name == w.name) with
    | some (_, sg) =>
        -- Only emit port for the first wire in the group
        if sg.wires.head? == some w then
          if direction == "output" && outputNeedsIndividualPorts ctx.wireToGroup ctx.wireToIndex _c sg then
            -- Output signal groups with individual bit assignments: emit one port per bit
            sg.wires.enum.map (fun (_, wire) => s!"  {direction} logic {wire.name}")
          else
            -- Input signal groups and bus-wide output groups: keep vectorized
            [generateSignalGroupPort direction sg]
        else
          []
    | none =>
        -- Standalone wire - emit as single-bit logic
        [s!"  {direction} logic {w.name}"]

/-- Generate all port declarations -/
def generatePorts (ctx : Context) (c : Circuit) : String :=
  let inputPorts := c.inputs.flatMap (generateWirePorts ctx c · "input")
  let outputPorts := c.outputs.flatMap (generateWirePorts ctx c · "output")

  -- Add explicit clock and reset ports that were filtered from regular inputs
  -- Only add ports that: (1) exist in the circuit's inputs, and (2) were filtered
  let hasClock := c.inputs.any (fun w => ctx.clockWires.contains w)
  let hasReset := c.inputs.any (fun w => ctx.resetWires.contains w)
  let clockResetPorts :=
    (if hasClock then ["  input logic clock"] else []) ++
    (if hasReset then ["  input logic reset"] else [])

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
      some s!"  logic {sanitizeSVName w.name};"

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
  | GateType.DFF | GateType.DFF_SET => ""

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
  | GateType.DFF | GateType.DFF_SET =>
      ""  -- DFFs handled separately
  | _ =>
      match g.inputs with
      | [i0, i1] =>
          s!"  assign {outRef} = {wireRef ctx c i0} {op} {wireRef ctx c i1};"
      | _ => "  // ERROR: Binary gate should have 2 inputs"

/-- Resolve a single contiguous slice of wires belonging to the same SignalGroup, all zero/one,
    or a repetition of an identical wire. -/
def resolveContiguousSlice (c : Circuit) (wireGroupMap : Std.HashMap String (SignalGroup × Nat))
    (wireToGroup : List (Wire × SignalGroup)) (wireToIndex : List (Wire × Nat))
    (slice : List Wire) : Option String :=
  let width := slice.length
  if width == 0 then none
  else if slice.all (fun w => w.name == "zero") then
    some s!"{width}'d0"
  else if slice.all (fun w => w.name == "one") then
    if width == 1 then some "1'b1"
    else some ("{" ++ toString width ++ "{1'b1}}")
  else if slice.all (fun w => w.name == slice.head!.name) then
    let w := slice.head!
    match wireGroupMap[w.name]? with
    | some (sg, idx) =>
        let singleRef := if sg.width == 1 then sg.name else s!"{sg.name}[{idx}]"
        if width == 1 then some singleRef
        else some ("{" ++ toString width ++ "{" ++ singleRef ++ "}}")
    | none =>
        let singleRef := sanitizeSVName w.name
        if width == 1 then some singleRef
        else some ("{" ++ toString width ++ "{" ++ singleRef ++ "}}")
  else
    let wireInfos := slice.map (fun w => wireGroupMap[w.name]?)
    if wireInfos.all Option.isSome then
      let infos := wireInfos.filterMap id
      match infos with
      | (firstSg, _) :: _ =>
          if infos.all (fun (sg, _) => sg.name == firstSg.name) then
            let isOutput := c.outputs.any (fun ow => firstSg.wires.any (fun sw => sw.name == ow.name))
            if isOutput && outputNeedsIndividualPorts wireToGroup wireToIndex c firstSg then
              none
            else
              let indices := infos.map (·.2)
              match indices with
              | startIdx :: _ =>
                  let isContiguous := indices.enum.all (fun (pos, idx) => idx == startIdx + pos)
                  if isContiguous then
                    if startIdx == 0 && width == firstSg.width then
                      some firstSg.name
                    else if width == 1 then
                      some s!"{firstSg.name}[{startIdx}]"
                    else
                      some s!"{firstSg.name}[{startIdx + width - 1}:{startIdx}]"
                  else
                    none
              | [] => none
          else none
      | [] => none
    else if width == 1 then
      let w := slice.head!
      if w.name != "zero" && w.name != "one" then
        some (sanitizeSVName w.name)
      else none
    else none

/-- State machine kind for partitioning slices -/
inductive RunKind where
  | Zero
  | One
  | Contig (sgName : String) (lastIdx : Nat)
  | Rep (wireName : String)
  | Undecided (sgName : String) (idx : Nat)
  | Single (wireName : String)
  deriving Repr, DecidableEq

/-- Partition wires into maximal contiguous or repeated slices -/
def partitionIntoSlices (wireGroupMap : Std.HashMap String (SignalGroup × Nat))
    (wires : List Wire) : List (List Wire) :=
  match wires with
  | [] => []
  | firstWire :: rest =>
      let initKind :=
        if firstWire.name == "zero" then RunKind.Zero
        else if firstWire.name == "one" then RunKind.One
        else match wireGroupMap[firstWire.name]? with
        | some (sg, idx) => RunKind.Undecided sg.name idx
        | none => RunKind.Single firstWire.name

      let (runs, currentRun, _) := rest.foldl (fun (acc : List (List Wire) × List Wire × RunKind) w =>
        let (accRuns, curRun, kind) := acc
        let wIsZero := w.name == "zero"
        let wIsOne := w.name == "one"
        let wBusOpt := wireGroupMap[w.name]?

        match kind with
        | RunKind.Zero =>
            if wIsZero then (accRuns, curRun ++ [w], RunKind.Zero)
            else (accRuns ++ [curRun], [w],
                  if wIsOne then RunKind.One
                  else match wBusOpt with
                  | some (sg, idx) => RunKind.Undecided sg.name idx
                  | none => RunKind.Single w.name)
        | RunKind.One =>
            if wIsOne then (accRuns, curRun ++ [w], RunKind.One)
            else (accRuns ++ [curRun], [w],
                  if wIsZero then RunKind.Zero
                  else match wBusOpt with
                  | some (sg, idx) => RunKind.Undecided sg.name idx
                  | none => RunKind.Single w.name)
        | RunKind.Undecided sg0 idx0 =>
            match wBusOpt with
            | some (sg1, idx1) =>
                if sg1.name == sg0 && idx1 == idx0 + 1 then
                  (accRuns, curRun ++ [w], RunKind.Contig sg0 idx1)
                else if sg1.name == sg0 && idx1 == idx0 then
                  (accRuns, curRun ++ [w], RunKind.Rep w.name)
                else
                  (accRuns ++ [curRun], [w], RunKind.Undecided sg1.name idx1)
            | none =>
                if wIsZero then (accRuns ++ [curRun], [w], RunKind.Zero)
                else if wIsOne then (accRuns ++ [curRun], [w], RunKind.One)
                else (accRuns ++ [curRun], [w], RunKind.Single w.name)
        | RunKind.Contig sg0 lastIdx =>
            match wBusOpt with
            | some (sg1, idx1) =>
                if sg1.name == sg0 && idx1 == lastIdx + 1 then
                  (accRuns, curRun ++ [w], RunKind.Contig sg0 idx1)
                else
                  (accRuns ++ [curRun], [w], RunKind.Undecided sg1.name idx1)
            | none =>
                if wIsZero then (accRuns ++ [curRun], [w], RunKind.Zero)
                else if wIsOne then (accRuns ++ [curRun], [w], RunKind.One)
                else (accRuns ++ [curRun], [w], RunKind.Single w.name)
        | RunKind.Rep wireName0 =>
            if w.name == wireName0 then
              (accRuns, curRun ++ [w], RunKind.Rep wireName0)
            else
              (accRuns ++ [curRun], [w],
               if wIsZero then RunKind.Zero
               else if wIsOne then RunKind.One
               else match wBusOpt with
               | some (sg, idx) => RunKind.Undecided sg.name idx
               | none => RunKind.Single w.name)
        | RunKind.Single wireName0 =>
            if w.name == wireName0 then
              (accRuns, curRun ++ [w], RunKind.Rep wireName0)
            else
              (accRuns ++ [curRun], [w],
               if wIsZero then RunKind.Zero
               else if wIsOne then RunKind.One
               else match wBusOpt with
               | some (sg, idx) => RunKind.Undecided sg.name idx
               | none => RunKind.Single w.name)
      ) ([], [firstWire], initKind)
      runs ++ [currentRun]

/-- Resolve a list of wires to a bus reference string, if all wires belong to the same
    SignalGroup in contiguous order, or are all zero, or a concatenation of such.
    Uses wireGroupMap for O(1) wire->(group, index) lookups. -/
def resolveBusRef (c : Circuit) (wireGroupMap : Std.HashMap String (SignalGroup × Nat))
    (wireToGroup : List (Wire × SignalGroup)) (wireToIndex : List (Wire × Nat))
    (wires : List Wire) : Option String :=
  let width := wires.length
  if width == 0 then none
  else
    let slices := partitionIntoSlices wireGroupMap wires
    let resolvedSlices := slices.map (resolveContiguousSlice c wireGroupMap wireToGroup wireToIndex)
    if resolvedSlices.all Option.isSome then
      let sliceStrs := resolvedSlices.filterMap id
      match sliceStrs with
      | [single] => some single
      | _ =>
          -- Verilog concatenation is {MSB, ..., LSB}; wires[0] is LSB, so reverse
          some ("{" ++ String.intercalate ", " sliceStrs.reverse ++ "}")
    else
      none

/-- Generate all combinational logic assignments with O(N) bus collapsing -/
def generateCombLogic (ctx : Context) (c : Circuit) : String := Id.run do
  let combGates := c.gates.filter (fun g => !g.gateType.isDFF)
  if combGates.isEmpty then ""
  else
    -- Step 1: Build O(1) lookup tables
    let mut wireToIndexMap : Std.HashMap String Nat := {}
    for (w, idx) in ctx.wireToIndex do
      wireToIndexMap := wireToIndexMap.insert w.name idx

    let mut wireGroupMap : Std.HashMap String (SignalGroup × Nat) := {}
    for (w, sg) in ctx.wireToGroup do
      if let some idx := wireToIndexMap[w.name]? then
        wireGroupMap := wireGroupMap.insert w.name (sg, idx)

    let mut gateByOutput : Std.HashMap String (Nat × Gate) := {}
    for (idx, g) in combGates.enum do
      gateByOutput := gateByOutput.insert g.output.name (idx, g)

    -- Step 2: Find all unique multi-bit signal groups in O(N)
    let mut allSgs : List SignalGroup := []
    let mut seenSgNames : Std.HashSet String := {}
    for (_, sg) in ctx.wireToGroup do
      if sg.width > 1 && !seenSgNames.contains sg.name then
        seenSgNames := seenSgNames.insert sg.name
        allSgs := allSgs ++ [sg]

    -- Step 3: Check each signal group once for bus collapsing
    let mut collapseAtIdx : Std.HashMap Nat String := {}
    let mut consumedIndices : Std.HashSet Nat := {}

    for sg in allSgs do
      let isOutput := c.outputs.any (fun ow => sg.wires.any (fun sw => sw.name == ow.name))
      if !(isOutput && outputNeedsIndividualPorts ctx.wireToGroup ctx.wireToIndex c sg) then
        let gatesOpt := sg.wires.map (fun w => gateByOutput[w.name]?)
        if gatesOpt.all Option.isSome then
          let entries := gatesOpt.filterMap id
          if entries.length == sg.width then
            -- Pair each gate with its bit position within the bus
            let indexedEntries : List (Nat × Gate × Nat) :=
              entries.enum.map (fun (bitIdx, (gateIdx, gate)) => (gateIdx, gate, bitIdx))

            -- Partition into contiguous runs of compatible gates
            let runs : List (List (Nat × Gate × Nat)) := match indexedEntries with
              | [] => []
              | firstE :: restE =>
                  let isCompat (e1 e2 : Nat × Gate × Nat) : Bool :=
                    let (_, g1, _) := e1
                    let (_, g2, _) := e2
                    if g1.gateType != g2.gateType then false
                    else match g1.gateType with
                    | GateType.MUX =>
                        match g1.inputs[2]?, g2.inputs[2]? with
                        | some s1, some s2 => s1.name == s2.name
                        | _, _ => false
                    | _ => true

                  let (allRuns, curRun, _) := restE.foldl (fun (acc : List (List (Nat × Gate × Nat)) × List (Nat × Gate × Nat) × (Nat × Gate × Nat)) e =>
                    let (accRuns, cur, lastE) := acc
                    if isCompat lastE e then (accRuns, cur ++ [e], e)
                    else (accRuns ++ [cur], [e], e)
                  ) ([], [firstE], firstE)
                  allRuns ++ [curRun]

            for slice in runs do
              let len := slice.length
              if len >= 2 then
                match slice with
                | (headGateIdx, firstGate, startBit) :: _ =>
                    let sliceGates := slice.map (·.2.1)
                    let sliceGateIndices := slice.map (·.1)
                    let lhs := if startBit == 0 && len == sg.width then sg.name
                               else s!"{sg.name}[{startBit + len - 1}:{startBit}]"

                    let collapsed? : Option String := match firstGate.gateType with
                      | GateType.MUX =>
                          if sliceGates.all (fun g => g.inputs.length == 3) then
                            match firstGate.inputs[2]? with
                            | some sel0 =>
                                let in0Wires := sliceGates.filterMap (fun g => g.inputs[0]?)
                                let in1Wires := sliceGates.filterMap (fun g => g.inputs[1]?)
                                if in0Wires.length == len && in1Wires.length == len then
                                  match resolveBusRef c wireGroupMap ctx.wireToGroup ctx.wireToIndex in0Wires,
                                        resolveBusRef c wireGroupMap ctx.wireToGroup ctx.wireToIndex in1Wires with
                                  | some in0Ref, some in1Ref =>
                                      let selRef := wireRef ctx c sel0
                                      some s!"  assign {lhs} = {selRef} ? {in1Ref} : {in0Ref};"
                                  | _, _ => none
                                else none
                            | none => none
                          else none
                      | GateType.BUF =>
                          if sliceGates.all (fun g => g.inputs.length == 1) then
                            let inWires := sliceGates.filterMap (fun g => g.inputs[0]?)
                            if inWires.length == len then
                              match resolveBusRef c wireGroupMap ctx.wireToGroup ctx.wireToIndex inWires with
                              | some inRef => some s!"  assign {lhs} = {inRef};"
                              | none => none
                            else none
                          else none
                      | GateType.NOT =>
                          if sliceGates.all (fun g => g.inputs.length == 1) then
                            let inWires := sliceGates.filterMap (fun g => g.inputs[0]?)
                            if inWires.length == len then
                              match resolveBusRef c wireGroupMap ctx.wireToGroup ctx.wireToIndex inWires with
                              | some inRef => some s!"  assign {lhs} = ~{inRef};"
                              | none => none
                            else none
                          else none
                      | GateType.AND | GateType.OR | GateType.XOR =>
                          if sliceGates.all (fun g => g.inputs.length == 2) then
                            let in0Wires := sliceGates.filterMap (fun g => g.inputs[0]?)
                            let in1Wires := sliceGates.filterMap (fun g => g.inputs[1]?)
                            if in0Wires.length == len && in1Wires.length == len then
                              match resolveBusRef c wireGroupMap ctx.wireToGroup ctx.wireToIndex in0Wires,
                                    resolveBusRef c wireGroupMap ctx.wireToGroup ctx.wireToIndex in1Wires with
                              | some in0Ref, some in1Ref =>
                                  let op := gateTypeToSVOperator firstGate.gateType
                                  some s!"  assign {lhs} = {in0Ref} {op} {in1Ref};"
                              | _, _ => none
                            else none
                          else none
                      | _ => none

                    if let some assignStr := collapsed? then
                      let minIdx := sliceGateIndices.foldl min headGateIdx
                      collapseAtIdx := collapseAtIdx.insert minIdx assignStr
                      for idx in sliceGateIndices do
                        consumedIndices := consumedIndices.insert idx
                | [] => ()

    -- Step 4: Single linear pass to emit assignments
    let mut assignments : List String := []
    for (idx, g) in combGates.enum do
      if let some assignStr := collapseAtIdx[idx]? then
        assignments := assignments ++ [assignStr]
      else if consumedIndices.contains idx then
        continue
      else
        let a := generateCombAssignment ctx c g
        if !a.isEmpty then
          assignments := assignments ++ [a]

    joinLines assignments

/-! ## Register Generation -/

/-- Find all DFF/DFF_SET gates in circuit -/
def findDFFs (c : Circuit) : List Gate :=
  c.gates.filter (fun g => g.gateType.isDFF)

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

/-- Compute the reset value for a signal group by checking which wires are DFF_SET.
    Returns an SV literal like "6'b100000" or "1'b0". -/
private def computeGroupResetVal (c : Circuit) (sg : SignalGroup) : String :=
  -- Check each wire in the group: is it driven by DFF_SET?
  let bits := sg.wires.map (fun w =>
    c.gates.any (fun g => g.gateType == GateType.DFF_SET && g.output.name == w.name))
  let hasAnySet := bits.any id
  if !hasAnySet then
    -- All zeros
    if sg.width > 1 then s!"{sg.width}'d0" else "1'b0"
  else if bits.all id then
    -- All ones
    if sg.width > 1 then s!"{sg.width}'d{2^sg.width - 1}" else "1'b1"
  else
    -- Mixed: emit binary literal (LSB first in wires list = bit 0)
    let bitStr := bits.reverse.map (fun b => if b then "1" else "0") |> String.join
    s!"{sg.width}'b{bitStr}"

/-- Generate register declaration and assignment for a DFF/DFF_SET.
    Returns (declaration_option, assign, reset_assign, reg_name) -/
def generateDFFDecl (ctx : Context) (c : Circuit) (g : Gate) : Option (Option String × String × String × String) :=
  match g.inputs with
  | [d, _clk, _rst] =>
      -- Check if output is a circuit output
      let isCircuitOutput := c.outputs.any (fun w => w.name == g.output.name)

      -- Check if this register is part of a signal group
      match ctx.wireToGroup.find? (fun (w', _) => w'.name == g.output.name) with
      | some (_, sg) =>
          -- Part of a bus - emit per-bit assignment for each DFF
          let idx := sg.wires.enum.findSome? (fun (p : Nat × Wire) => if p.2.name == g.output.name then some p.1 else none)
          match idx with
          | some i =>
            let svType := signalGroupToSV sg
            let regName := if isCircuitOutput then sg.name else s!"{sg.name}_reg"
            let isScalar := sg.width == 1
            let dRef := match ctx.wireToGroup.find? (fun (w', _) => w'.name == d.name) with
              | some (_, inputGroup) =>
                if inputGroup.width == 1 then inputGroup.name
                else
                  let dIdx := inputGroup.wires.enum.findSome? (fun (p : Nat × Wire) => if p.2.name == d.name then some p.1 else none)
                  match dIdx with
                  | some j => s!"{inputGroup.name}[{j}]"
                  | none => inputGroup.name
              | none => d.name
            -- Only emit declaration and reset for the first wire in the group
            if sg.wires.head? == some g.output then
              let decl := if isCircuitOutput then none else some s!"  {svType} {regName};"
              let resetVal := computeGroupResetVal c sg
              let assignStr := if isScalar then s!"      {regName} <= {dRef};" else s!"      {regName}[{i}] <= {dRef};"
              some (decl, assignStr, s!"      {regName} <= {resetVal};", regName)
            else
              -- Non-first wire: just the per-bit assignment, no decl/reset
              let assignStr := if isScalar then s!"      {regName} <= {dRef};" else s!"      {regName}[{i}] <= {dRef};"
              some (none, assignStr, "", regName)
          | none => none
      | none =>
          -- Standalone register
          let regName := if isCircuitOutput then g.output.name else s!"{g.output.name}_reg"
          let dRef := match ctx.wireToGroup.find? (fun (w', _) => w'.name == d.name) with
            | some (_, inputGroup) =>
              -- Single-bit DFF input from a bus: need bit index
              let idx := inputGroup.wires.enum.findSome? (fun (p : Nat × Wire) => if p.2.name == d.name then some p.1 else none)
              match idx with
              | some i => s!"{inputGroup.name}[{i}]"
              | none => inputGroup.name
            | none => d.name
          let decl := if isCircuitOutput then none else some s!"  logic {regName};"
          let resetVal := if g.gateType == GateType.DFF_SET then "1'b1" else "1'b0"
          some (decl, s!"      {regName} <= {dRef};", s!"      {regName} <= {resetVal};", regName)
  | _ =>
      none

/-- Generate always_ff block for register group with O(N) bus collapsing -/
def generateAlwaysFFBlock (ctx : Context) (c : Circuit) (clk : Wire) (rst : Wire) (dffs : List Gate) : String := Id.run do
  if dffs.isEmpty then ""
  else
    -- Step 1: Build lookup tables
    let mut wireGroupMap : Std.HashMap String (SignalGroup × Nat) := {}
    for (w, sg) in ctx.wireToGroup do
      if let some (_, idx) := ctx.wireToIndex.find? (fun (w', _) => w'.name == w.name) then
        wireGroupMap := wireGroupMap.insert w.name (sg, idx)

    let mut dffByOutput : Std.HashMap String (Nat × Gate) := {}
    for (idx, g) in dffs.enum do
      dffByOutput := dffByOutput.insert g.output.name (idx, g)

    let allSgs := ctx.wireToGroup.map (·.2) |>.foldl (fun acc sg =>
      if sg.width > 1 && !acc.any (fun s => s.name == sg.name) then acc ++ [sg] else acc
    ) []

    -- Step 2: Check multi-bit groups for collapsing
    let mut collapseAtIdx : Std.HashMap Nat (Option String × String × String × String) := {}
    let mut consumedIndices : Std.HashSet Nat := {}

    for sg in allSgs do
      let dffsOpt := sg.wires.map (fun w => dffByOutput[w.name]?)
      if dffsOpt.all Option.isSome then
        let entries := dffsOpt.filterMap id
        if entries.length == sg.width then
          let indices := entries.map (·.1)
          let sgDFFs := entries.map (·.2)
          let dWires := sgDFFs.filterMap (fun g => g.inputs.head?)
          if dWires.length == sg.width then
            if let some inRef := resolveBusRef c wireGroupMap ctx.wireToGroup ctx.wireToIndex dWires then
              let isCircuitOutput := c.outputs.any (fun w => sg.wires.any (fun sw => sw.name == w.name))
              let regName := if isCircuitOutput then sg.name else s!"{sg.name}_reg"
              let svType := signalGroupToSV sg
              let decl := if isCircuitOutput then none else some s!"  {svType} {regName};"
              let resetVal := computeGroupResetVal c sg
              let assignStr := s!"      {regName} <= {inRef};"
              let resetAssignStr := s!"      {regName} <= {resetVal};"
              match indices with
              | firstIdx :: _ =>
                  let minIdx := indices.foldl min firstIdx
                  collapseAtIdx := collapseAtIdx.insert minIdx (decl, assignStr, resetAssignStr, regName)
                  for idx in indices do
                    consumedIndices := consumedIndices.insert idx
              | [] => ()

    -- Step 3: Single linear pass to collect decls, assigns, resets, regNames
    let mut decls : List String := []
    let mut assigns : List String := []
    let mut resetAssigns : List String := []
    let mut regNames : List String := []

    for (idx, g) in dffs.enum do
      if let some (declOpt, assignStr, resetStr, regName) := collapseAtIdx[idx]? then
        if let some d := declOpt then decls := decls ++ [d]
        assigns := assigns ++ [assignStr]
        resetAssigns := resetAssigns ++ [resetStr]
        regNames := regNames ++ [regName]
      else if consumedIndices.contains idx then
        continue
      else
        if let some (declOpt, assignStr, resetStr, regName) := generateDFFDecl ctx c g then
          if let some d := declOpt then decls := decls ++ [d]
          assigns := assigns ++ [assignStr]
          if !resetStr.isEmpty then resetAssigns := resetAssigns ++ [resetStr]
          regNames := regNames ++ [regName]

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
        "      // Reset registers (DFF→0, DFF_SET→1)",
        joinLines resetAssigns,
        "    end else begin",
        joinLines assigns,
        "    end",
        "  end"
      ]

      -- Generate feedback assignments: connect _reg back to combinational bus
      -- For non-circuit-output DFF groups, the register name differs from the bus name
      let feedbackAssigns := regNames.filterMap (fun regName =>
        -- If regName ends with "_reg", generate assign busName = regName
        -- Skip if regName itself is a circuit output (the output port IS the register)
        if regName.endsWith "_reg" then
          let busName := regName.dropEnd 4  -- Remove "_reg" suffix
          let regIsCircuitOutput := c.outputs.any (fun w =>
            extractBaseName w.name == regName || w.name == regName)
          if regIsCircuitOutput then none
          else some s!"  assign {busName} = {regName};"
        else
          none) |>.foldl (fun acc s => if acc.contains s then acc else acc ++ [s]) []
      let feedbackStr := joinLines feedbackAssigns

      let base := if declsStr.isEmpty then
        alwaysBlock
      else
        declsStr ++ "\n\n" ++ alwaysBlock

      if feedbackStr.isEmpty then
        base
      else
        base ++ "\n\n" ++ feedbackStr

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

/-- Parse a port name that may contain indexing in various formats.
    Bracket:    "alloc_physRd[0]" → some ("alloc_physRd", 0)
    Underscore: "data_3"          → some ("data", 3)
    Bare:       "in0"             → some ("in", 0)
    Non-indexed:"enq_valid"       → none -/
def parsePortIndex (portName : String) : Option (String × Nat) :=
  -- Try bracket indexing first: portName[N]
  match portName.splitOn "[" with
  | [base, idxPart] =>
      let idxStr := String.ofList (idxPart.toList.takeWhile (· != ']'))
      match idxStr.toNat? with
      | some idx => some (base, idx)
      | none => none
  | _ =>
      -- Try underscore or bare suffix: extract trailing digits
      let chars := portName.toList
      let digitSuffix := chars.reverse.takeWhile Char.isDigit |>.reverse
      if digitSuffix.isEmpty then
        none
      else
        let idxStr := String.ofList digitSuffix
        let baseStr := String.ofList (chars.take (chars.length - digitSuffix.length))
        match idxStr.toNat? with
        | some idx =>
            -- Strip trailing underscore from base if present (underscore indexing)
            let base := if baseStr.endsWith "_" then
              String.ofList (baseStr.toList.dropLast)
            else
              baseStr
            -- Don't parse if base is empty
            if base.isEmpty then none
            else some (base, idx)
        | none => none

/-- Get the set of output signal group names that use individual ports for a sub-module. -/
def getSubModuleIndividualOutputGroups (allCircuits : List Circuit) (moduleName : String)
    : List String :=
  match allCircuits.find? (fun sc => sc.name == moduleName) with
  | none => []
  | some subMod =>
      let subCtx := mkContext subMod
      let allSgs := subCtx.wireToGroup.map (·.2)
      let uniqueSgNames := dedupStrings (allSgs.map (·.name))
      let uniqueSgs := uniqueSgNames.filterMap (fun n => allSgs.find? (fun sg => sg.name == n))
      uniqueSgs.filter (fun sg =>
          let isOutputGroup := sg.wires.any (fun w => subMod.outputs.any (fun ow => ow.name == w.name))
          isOutputGroup && outputNeedsIndividualPorts subCtx.wireToGroup subCtx.wireToIndex subMod sg
        )
        |>.map (·.name)

/-- Build a mapping of port base names to their grouped bus names for a sub-module.
    Uses the sub-module's signal groups + auto-detected groups to determine
    which individual port names (e.g., "in_0", "data_3") belong to buses (e.g., "in", "data"). -/
def buildSubModulePortGroups (allCircuits : List Circuit) (moduleName : String)
    : List (String × String × Nat) :=
  -- Returns: list of (individualPortName, busName, bitIndex)
  match allCircuits.find? (fun sc => sc.name == moduleName) with
  | none => []
  | some subMod =>
      let subCtx := mkContext subMod
      -- For each input and output wire in the sub-module, check if it's in a signal group
      -- Include ALL signal groups (even individual-port outputs) for grouping
      (subMod.inputs ++ subMod.outputs).filterMap (fun w =>
        match subCtx.wireToGroup.find? (fun (w', _) => w'.name == w.name) with
        | some (_, sg) =>
            match subCtx.wireToIndex.find? (fun (w', _) => w'.name == w.name) with
            | some (_, idx) => some (w.name, sg.name, idx)
            | none => none
        | none => none
      )

/-- Group port map entries using the sub-module's actual port structure.
    Matches portMap entry names against sub-module wire names and groups
    them according to the sub-module's signal groups. -/
def groupPortMapEntries (allCircuits : List Circuit) (inst : CircuitInstance)
    : List (Sum (String × Wire) (String × List (Nat × Wire))) :=
  let subModFound := allCircuits.any (fun sc => sc.name == inst.moduleName)
  let portGroups := buildSubModulePortGroups allCircuits inst.moduleName
  -- If sub-module not in allCircuits, infer grouping from port name patterns
  -- If sub-module IS in allCircuits but has no groups, respect that (don't infer)
  let portGroups := if portGroups.isEmpty && !subModFound then
    inst.portMap.filterMap (fun (pname, _) =>
      match parsePortIndex pname with
      | some (base, idx) => some (pname, base, idx)
      | none => none)
  else portGroups
  -- Pre-compute: count how many times each port name appears in portMap
  -- (for detecting bare group names like "sum" repeated 32 times)
  let portNameCounts := inst.portMap.foldl (fun acc (pname, _) =>
    match acc.find? (fun (n, _) => n == pname) with
    | some _ => acc.map (fun (n, c) => if n == pname then (n, c + 1) else (n, c))
    | none => acc ++ [(pname, 1)]
  ) ([] : List (String × Nat))
  -- Track running index per bare group name
  let initAcc : List (String × Wire × Option (String × Nat)) × List (String × Nat) := ([], [])
  let (parsed, _) := inst.portMap.foldl (fun acc (pname, w) =>
    let results := acc.1
    let bareIdxMap := acc.2
    -- Try direct match: portMap name == sub-module wire name
    let directMatch := portGroups.find? (fun (entry : String × String × Nat) =>
      entry.1 == pname)
    match directMatch with
    | some (_, busName, idx) =>
        (results ++ [(pname, w, some (busName, idx))], bareIdxMap)
    | none =>
        -- Try parsePortIndex for bracket/underscore/bare patterns
        match parsePortIndex pname with
        | some (base, idx) =>
            -- Verify this base name matches a bus in the sub-module
            if portGroups.any (fun (entry : String × String × Nat) => entry.2.1 == base) then
              (results ++ [(pname, w, some (base, idx))], bareIdxMap)
            else
              (results ++ [(pname, w, (none : Option (String × Nat)))], bareIdxMap)
        | none =>
            -- Check if this bare name is a sub-module signal group name with multiple entries
            -- (e.g., "sum" appearing 32 times → group "sum" with indices 0..31)
            let isGroupName := portGroups.any (fun (entry : String × String × Nat) => entry.2.1 == pname)
            let count := (portNameCounts.find? (fun (n, _) => n == pname)).map (·.2) |>.getD 0
            if isGroupName && count > 1 then
              let curIdx := (bareIdxMap.find? (fun (n, _) => n == pname)).map (·.2) |>.getD 0
              let newMap := match bareIdxMap.find? (fun (n, _) => n == pname) with
                | some _ => bareIdxMap.map (fun (n, i) => if n == pname then (n, i + 1) else (n, i))
                | none => bareIdxMap ++ [(pname, 1)]
              (results ++ [(pname, w, some (pname, curIdx))], newMap)
            else
              (results ++ [(pname, w, (none : Option (String × Nat)))], bareIdxMap)
  ) initAcc
  -- Collect groups (handling interleaved portMaps)
  let groupAcc := parsed.foldl
    (fun (groups : List (String × List (Nat × Wire))) (_pname, _w, parsed?) =>
      match parsed? with
      | some (base, idx) =>
          match groups.find? (fun (b, _) => b == base) with
          | some _ =>
              groups.map (fun (b, es) =>
                if b == base then (b, es ++ [(idx, _w)]) else (b, es))
          | none =>
              groups ++ [(base, [(idx, _w)])]
      | none => groups
    ) []
  -- Emit groups at first occurrence, scalars inline
  parsed.foldl (fun (acc : List (Sum (String × Wire) (String × List (Nat × Wire))) × List String)
    (pname, w, parsed?) =>
      let (result, emittedBases) := acc
      match parsed? with
      | some (base, _) =>
          if emittedBases.contains base then
            (result, emittedBases)
          else
            match groupAcc.find? (fun (b, _) => b == base) with
            | some (_, entries) =>
                (result ++ [Sum.inr (base, entries)], emittedBases ++ [base])
            | none => (result, emittedBases)
      | none =>
          (result ++ [Sum.inl (pname, w)], emittedBases)
  ) ([], []) |>.1

/-- Generate port connection for module instantiation -/
def generatePortConnection (ctx : Context) (c : Circuit) (portName : String) (wire : Wire) : String :=
  s!"    .{portName}({wireRef ctx c wire})"

/-- Try to parse a wire reference of the form "busName[idx]" into (busName, idx). -/
def parseIndexedWireRef (ref : String) : Option (String × Nat) :=
  match ref.splitOn "[" with
  | [busName, rest] =>
      match rest.splitOn "]" with
      | [idxStr, ""] => idxStr.toNat?.map (fun idx => (busName, idx))
      | _ => none
  | _ => none

/-- Try to extract common bus name and contiguous index range from wire references.
    If all refs are busName[start], busName[start+1], ..., busName[start+N-1],
    returns some (busName, start, start + N - 1). Otherwise returns none. -/
def extractCommonBusSlice (wireRefs : List String) : Option (String × Nat × Nat) :=
  match wireRefs.head? with
  | none => none
  | some firstRef =>
      match parseIndexedWireRef firstRef with
      | some (busName, startIdx) =>
          let allMatch := wireRefs.enum.all fun (pos, ref) =>
            parseIndexedWireRef ref == some (busName, startIdx + pos)
          if allMatch then
            some (busName, startIdx, startIdx + wireRefs.length - 1)
          else none
      | none => none

/-- Generate a bus port connection.
    Entries are sorted by index. If all wires form a contiguous bus or slice,
    connects directly. Otherwise uses concatenation \{MSB, ..., LSB\} syntax.
    When entries cover only a subrange of the parent bus, emits a range slice. -/
def generateBusPortConnection (ctx : Context) (c : Circuit) (baseName : String)
    (entries : List (Nat × Wire)) : String :=
  let sorted := entries.toArray.qsort (fun a b => a.1 < b.1) |>.toList
  let wireRefs := sorted.map (fun (_, w) => wireRef ctx c w)
  match extractCommonBusSlice wireRefs with
  | some (busName, lo, hi) =>
      let nEntries := sorted.length
      let parentWidth := match ctx.wireToGroup.find? (fun (_, sg) => sg.name == busName) with
        | some (_, sg) => sg.width
        | none => nEntries
      if lo == 0 && nEntries == parentWidth then
        -- Full bus connection: .portName(busName)
        s!"    .{baseName}({busName})"
      else if hi == lo then
        -- Single bit slice: .portName(busName[lo])
        s!"    .{baseName}({busName}[{lo}])"
      else
        -- Subrange: .portName(busName[hi:lo])
        s!"    .{baseName}({busName}[{hi}:{lo}])"
  | none =>
      -- Concatenation: .portName({wire_N, ..., wire_0})
      let concat := "{" ++ String.intercalate ", " wireRefs.reverse ++ "}"
      s!"    .{baseName}({concat})"

/-- Generate individual port connections for a bus group where the sub-module
    uses individual ports (e.g., out_0, out_1, ...). -/
def generateIndividualBusPortConnections (ctx : Context) (c : Circuit)
    (subMod : Option Circuit) (baseName : String) (entries : List (Nat × Wire)) : List String :=
  let sorted := entries.toArray.qsort (fun a b => a.1 < b.1) |>.toList
  sorted.map (fun (idx, w) =>
    let portName := match subMod with
      | some sm =>
          let candidateBare := s!"{baseName}{idx}"
          let candidateWithUnderscore := s!"{baseName}_{idx}"
          if (sm.inputs ++ sm.outputs).any (fun pw => pw.name == candidateBare) then
            candidateBare
          else
            candidateWithUnderscore
      | none => s!"{baseName}_{idx}"
    s!"    .{portName}({wireRef ctx c w})")

/-- Generate module instantiation -/
def generateInstance (ctx : Context) (c : Circuit) (allCircuits : List Circuit)
    (inst : CircuitInstance) : String :=
  let grouped := groupPortMapEntries allCircuits inst
  let subMod := allCircuits.find? (fun sc => sc.name == inst.moduleName)
  -- Get output signal groups with individual ports for this sub-module
  let individualOutputGroups := getSubModuleIndividualOutputGroups allCircuits inst.moduleName
  let portConnections := grouped.flatMap (fun entry =>
    match entry with
    | Sum.inl (pname, w) => [generatePortConnection ctx c pname w]
    | Sum.inr (baseName, entries) =>
        -- Check if this bus group corresponds to an individual-port output
        if individualOutputGroups.contains baseName then
          generateIndividualBusPortConnections ctx c subMod baseName entries
        else
          [generateBusPortConnection ctx c baseName entries]
  )

  let connectionsStr := String.intercalate ",\n" portConnections

  joinLines [
    s!"  {inst.moduleName} {inst.instName} (",
    connectionsStr,
    "  );"
  ]

/-- Generate all module instantiations -/
def generateInstances (ctx : Context) (c : Circuit) (allCircuits : List Circuit) : String :=
  let instances := c.instances.map (generateInstance ctx c allCircuits)
  joinLines instances

/-! ## RAM Primitive Generation -/

/-- Generate SystemVerilog for a single RAMPrimitive.
    Emits a reg array with clocked write and combinational (async) read. -/
def generateRAM (ctx : Context) (c : Circuit) (ram : RAMPrimitive) : String :=
  let addrBits := ram.readPorts.head?.map (·.addr.length) |>.getD 1
  let depthMinusOne := ram.depth - 1
  -- RAM array declaration
  let arrayDecl := s!"  reg [{ram.width - 1}:0] {ram.name} [0:{depthMinusOne}];"
  -- Write ports
  let clkRef := wireRef ctx c ram.clock
  let writePorts := ram.writePorts.enum.map (fun (_, wp) =>
    let enRef := wireRef ctx c wp.en
    -- Build address concatenation (MSB first)
    let addrRefs := wp.addr.reverse.map (wireRef ctx c ·)
    let addrExpr := if addrRefs.length == 1 then addrRefs.head!
                    else "{" ++ String.intercalate ", " addrRefs ++ "}"
    -- Build data concatenation (MSB first)
    let dataRefs := wp.data.reverse.map (wireRef ctx c ·)
    let dataExpr := if dataRefs.length == 1 then dataRefs.head!
                    else "{" ++ String.intercalate ", " dataRefs ++ "}"
    joinLines [
      s!"  always @(posedge {clkRef})",
      s!"    if ({enRef}) {ram.name}[{addrExpr}] <= {dataExpr};"
    ])
  -- Read ports (async)
  let readPorts := ram.readPorts.enum.map (fun (_, rp) =>
    -- Build address concatenation (MSB first)
    let addrRefs := rp.addr.reverse.map (wireRef ctx c ·)
    let addrExpr := if addrRefs.length == 1 then addrRefs.head!
                    else "{" ++ String.intercalate ", " addrRefs ++ "}"
    -- Assign individual output bits from the read data
    let readDataWire := s!"{ram.name}[{addrExpr}]"
    let assigns := rp.data.enum.map (fun (idx, w) =>
      s!"  assign {wireRef ctx c w} = {readDataWire}[{idx}];")
    joinLines assigns)
  let _ := addrBits  -- suppress unused warning
  joinLines ([arrayDecl] ++ writePorts ++ readPorts)

/-- Generate all RAM primitives -/
def generateRAMs (ctx : Context) (c : Circuit) : String :=
  if c.rams.isEmpty then ""
  else
    let ramStrs := c.rams.map (generateRAM ctx c)
    joinLines ramStrs

/-! ## Module Generation -/

/-- Generate complete SystemVerilog module for a circuit -/
def generateModule (c : Circuit) (allCircuits : List Circuit := []) : String :=
  let ctx := mkContext c

  let keepHierarchyAttr := if c.keepHierarchy then
    "(* keep_hierarchy = \"yes\" *)\n"
  else
    ""

  let header := joinLines [
    "// Auto-generated by Shoumei Codegen V2",
    s!"// Source: {c.name}",
    "",
    s!"{keepHierarchyAttr}module {c.name} ("
  ]

  let ports := generatePorts ctx c
  let portSection := if ports.isEmpty then
    ");"
  else
    ports ++ "\n);"

  let internalSignals := generateInternalSignals ctx c
  let combLogic := generateCombLogic ctx c
  let registers := generateRegisters ctx c
  let instances := generateInstances ctx c allCircuits
  let rams := generateRAMs ctx c
  let assertions := SVA.emitSVA c ctx.clockWires ctx.resetWires

  let body := joinLines [
    portSection,
    "",
    if internalSignals.isEmpty then "" else internalSignals ++ "\n",
    if combLogic.isEmpty then "" else combLogic ++ "\n",
    if registers.isEmpty then "" else registers ++ "\n",
    if rams.isEmpty then "" else rams ++ "\n",
    if instances.isEmpty then "" else instances,
    if assertions.isEmpty then "" else "\n" ++ assertions
  ]

  let footer := "endmodule\n"

  joinLines [header, body, footer]

/-! ## Public API -/

/-- Generate SystemVerilog code for a circuit -/
def toSystemVerilog (c : Circuit) (allCircuits : List Circuit := []) : String :=
  generateModule c allCircuits

end Shoumei.Codegen.SystemVerilog
