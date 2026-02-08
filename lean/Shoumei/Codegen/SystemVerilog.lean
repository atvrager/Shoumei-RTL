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

/-- Check if an output signal group needs individual port declarations
    (matching Chisel Vec behavior) vs vectorized (matching Chisel UInt behavior).
    Returns true if the signal group needs individual ports. -/
def outputNeedsIndividualPorts (wireToGroup : List (Wire × SignalGroup))
    (wireToIndex : List (Wire × Nat)) (c : Circuit) (sg : SignalGroup) : Bool :=
  if sg.width <= 1 then
    false  -- Single-bit outputs don't need individual ports
  else
    let combGates := c.gates.filter (fun g => !g.gateType.isDFF)
    let outputGates := combGates.filter (fun g =>
      sg.wires.any (fun w => w.name == g.output.name)
    )
    if outputGates.isEmpty then
      false  -- No gates write to this group (e.g., driven by instances)
    else
      match outputGates.head? with
      | none => false
      | some firstGate =>
          let allSameType := outputGates.all (fun g => g.gateType == firstGate.gateType)
          if !(allSameType && outputGates.length == sg.width) then
            true  -- Mixed types or incomplete coverage → individual
          else
            -- Check if gates form a bus-wide operation pattern
            match firstGate.gateType with
            | GateType.BUF =>
                match firstGate.inputs with
                | [in0] =>
                    let in0GroupName := wireToGroup.find? (fun (w', _) => w'.name == in0.name) |>.map (·.2.name)
                    match in0GroupName with
                    | some firstBusName =>
                        let allInSameBus := outputGates.all (fun g =>
                          match g.inputs with
                          | [inp] =>
                              let inpGroupName := wireToGroup.find? (fun (w', _) => w'.name == inp.name) |>.map (·.2.name)
                              inpGroupName == some firstBusName
                          | _ => false
                        )
                        !allInSameBus
                    | none => true
                | _ => true
            | GateType.AND | GateType.OR | GateType.XOR =>
                match firstGate.inputs with
                | [in0, in1] =>
                    let in0GroupName := wireToGroup.find? (fun (w', _) => w'.name == in0.name) |>.map (·.2.name)
                    let in1GroupName := wireToGroup.find? (fun (w', _) => w'.name == in1.name) |>.map (·.2.name)
                    if in0GroupName.isSome || in1GroupName.isSome then
                      let allUniform := outputGates.all (fun g =>
                        match g.inputs with
                        | [gi0, gi1] =>
                            let gi0GroupName := wireToGroup.find? (fun (w', _) => w'.name == gi0.name) |>.map (·.2.name)
                            let gi1GroupName := wireToGroup.find? (fun (w', _) => w'.name == gi1.name) |>.map (·.2.name)
                            gi0GroupName == in0GroupName && gi1GroupName == in1GroupName
                        | _ => false
                      )
                      !allUniform
                    else
                      true
                | _ => true
            | GateType.MUX =>
                match firstGate.inputs with
                | [in0, in1, sel] =>
                    let in0Bus := wireToGroup.any (fun (w', _) => w'.name == in0.name)
                    let in1Bus := wireToGroup.any (fun (w', _) => w'.name == in1.name)
                    if in0Bus && in1Bus then
                      let in0Group := wireToGroup.find? (fun (w', _) => w'.name == in0.name) |>.map (·.2.name)
                      let in1Group := wireToGroup.find? (fun (w', _) => w'.name == in1.name) |>.map (·.2.name)
                      let selGroup := wireToGroup.find? (fun (w', _) => w'.name == sel.name) |>.map (·.2.name)
                      let allGatesUniform := outputGates.all (fun g =>
                        match g.inputs with
                        | [g_in0, g_in1, g_sel] =>
                            let g0 := wireToGroup.find? (fun (w', _) => w'.name == g_in0.name) |>.map (·.2.name)
                            let g1 := wireToGroup.find? (fun (w', _) => w'.name == g_in1.name) |>.map (·.2.name)
                            let gs := wireToGroup.find? (fun (w', _) => w'.name == g_sel.name) |>.map (·.2.name)
                            g0 == in0Group && g1 == in1Group && gs == selGroup
                        | _ => false
                      )
                      if !allGatesUniform then
                        true
                      else
                        let selInBus := wireToGroup.any (fun (w', _) => w'.name == sel.name)
                        let selIdx := wireToIndex.find? (fun (w', _) => w'.name == sel.name) |>.map (·.2)
                        match selInBus, selIdx with
                        | false, _ => false
                        | true, some _ => false
                        | _, _ => true
                    else
                      true
                | _ => true
            | GateType.NOT =>
                -- NOT gates: check if all inputs come from the same bus
                match firstGate.inputs with
                | [in0] =>
                    let in0GroupName := wireToGroup.find? (fun (w', _) => w'.name == in0.name) |>.map (·.2.name)
                    match in0GroupName with
                    | some firstBusName =>
                        let allInSameBus := outputGates.all (fun g =>
                          match g.inputs with
                          | [inp] =>
                              let inpGroupName := wireToGroup.find? (fun (w', _) => w'.name == inp.name) |>.map (·.2.name)
                              inpGroupName == some firstBusName
                          | _ => false
                        )
                        !allInSameBus
                    | none => true
                | _ => true
            | _ => true  -- DFF and other types → individual

/-- Build context from circuit -/
def mkContext (c : Circuit) : Context :=
  let clockWires := findClockWires c
  let resetWires := findResetWires c
  -- A circuit is sequential if it has DFF gates OR clock/reset wires
  -- (hierarchical modules may have no DFFs but pass clock/reset to instances)
  let isSequential := c.gates.any (fun g => g.gateType.isDFF) ||
                      !clockWires.isEmpty || !resetWires.isEmpty

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
            -- Output signal groups with individual bit assignments: emit individual ports to match Chisel/CIRCT
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

/-- Generate all combinational logic assignments -/
def generateCombLogic (ctx : Context) (c : Circuit) : String :=
  let combGates := c.gates.filter (fun g => !g.gateType.isDFF)
  let assignments := combGates.map (generateCombAssignment ctx c)
  joinLines (assignments.filter (· != ""))

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
          -- Part of a bus - only emit for first register in group
          if sg.wires.head? == some g.output then
            let svType := signalGroupToSV sg
            let regName := if isCircuitOutput then sg.name else s!"{sg.name}_reg"
            let dRef := match ctx.wireToGroup.find? (fun (w', _) => w'.name == d.name) with
              | some (_, inputGroup) => inputGroup.name
              | none => d.name
            let decl := if isCircuitOutput then none else some s!"  {svType} {regName};"
            let resetVal := computeGroupResetVal c sg
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
          let resetVal := if g.gateType == GateType.DFF_SET then "1'b1" else "1'b0"
          some (decl, s!"      {regName} <= {dRef};", s!"      {regName} <= {resetVal};", regName)
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
      "      // Reset registers (DFF→0, DFF_SET→1)",
      joinLines resetAssigns,
      "    end else begin",
      joinLines assigns,
      "    end",
      "  end"
    ]

    -- Generate feedback assignments: connect _reg back to combinational bus
    -- For non-circuit-output DFF groups, the register name differs from the bus name
    let feedbackAssigns := results.filterMap (fun (_, _, _, regName) =>
      -- If regName ends with "_reg", generate assign busName = regName
      -- Skip if regName itself is a circuit output (the output port IS the register)
      if regName.endsWith "_reg" then
        let busName := regName.dropEnd 4  -- Remove "_reg" suffix
        let regIsCircuitOutput := c.outputs.any (fun w =>
          extractBaseName w.name == regName || w.name == regName)
        if regIsCircuitOutput then none
        else some s!"  assign {busName} = {regName};"
      else
        none)
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
      let uniqueSgNames := (allSgs.map (·.name)).eraseDups
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
  let portGroups := buildSubModulePortGroups allCircuits inst.moduleName
  -- If sub-module not in allCircuits, infer grouping from port name patterns
  let portGroups := if portGroups.isEmpty then
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
    directly. Otherwise uses concatenation \{MSB, ..., LSB\} syntax.
    When entries cover only a subrange of the parent bus, emits a range slice. -/
def generateBusPortConnection (ctx : Context) (c : Circuit) (baseName : String)
    (entries : List (Nat × Wire)) : String :=
  let sorted := entries.toArray.qsort (fun a b => a.1 < b.1) |>.toList
  let wireRefs := sorted.map (fun (_, w) => wireRef ctx c w)
  match extractCommonBusName wireRefs sorted with
  | some busName =>
      -- Check if the entries cover only a subrange of the parent bus
      let nEntries := sorted.length
      -- Find the parent signal group width for this bus
      let parentWidth := match ctx.wireToGroup.find? (fun (_, sg) => sg.name == busName) with
        | some (_, sg) => sg.width
        | none => nEntries
      if nEntries == parentWidth then
        -- Full bus connection: .portName(busName)
        s!"    .{baseName}({busName})"
      else
        -- Subrange: .portName(busName[hi:lo])
        let lo := match sorted.head? with | some (i, _) => i | none => 0
        let hi := match sorted.getLast? with | some (i, _) => i | none => 0
        s!"    .{baseName}({busName}[{hi}:{lo}])"
  | none =>
      -- Concatenation: .portName({wire_N, ..., wire_0})
      let concat := "{" ++ String.intercalate ", " wireRefs.reverse ++ "}"
      s!"    .{baseName}({concat})"

/-- Generate individual port connections for a bus group where the sub-module
    uses individual ports (e.g., out_0, out_1, ...). -/
def generateIndividualBusPortConnections (ctx : Context) (c : Circuit)
    (baseName : String) (entries : List (Nat × Wire)) : List String :=
  let sorted := entries.toArray.qsort (fun a b => a.1 < b.1) |>.toList
  sorted.map (fun (idx, w) => s!"    .{baseName}_{idx}({wireRef ctx c w})")

/-- Generate module instantiation -/
def generateInstance (ctx : Context) (c : Circuit) (allCircuits : List Circuit)
    (inst : CircuitInstance) : String :=
  let grouped := groupPortMapEntries allCircuits inst
  -- Get output signal groups with individual ports for this sub-module
  let individualOutputGroups := getSubModuleIndividualOutputGroups allCircuits inst.moduleName
  let portConnections := grouped.flatMap (fun entry =>
    match entry with
    | Sum.inl (pname, w) => [generatePortConnection ctx c pname w]
    | Sum.inr (baseName, entries) =>
        -- Check if this bus group corresponds to an individual-port output
        if individualOutputGroups.contains baseName then
          generateIndividualBusPortConnections ctx c baseName entries
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
def toSystemVerilog (c : Circuit) (allCircuits : List Circuit := []) : String :=
  generateModule c allCircuits

end Shoumei.Codegen.SystemVerilog
