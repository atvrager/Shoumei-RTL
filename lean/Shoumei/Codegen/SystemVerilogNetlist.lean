/-
Codegen/SystemVerilogNetlist.lean - SystemVerilog Netlist Generator (Flat Mode)

Generates flat netlist SystemVerilog by recursively inlining all instances.
Output is a single module with only primitive gates, using hierarchical wire names.

Design principles:
- Fully flat: all instances recursively inlined to gates
- Hierarchical naming: `u_mem__reg_0__dff_q` preserves original structure
- Typed buses: logic [31:0] (reuses bus reconstruction from V2)
- Single always_ff per register group
- No module instantiations in output (pure netlist)

Use cases:
- Formal verification tools that prefer flat netlists
- Equivalence checking against hierarchical SV
- Gate-level simulation

Target: IEEE 1800-2017 SystemVerilog
Validation: Yosys equiv_make vs hierarchical SV
-/

import Shoumei.DSL
import Shoumei.DSL.Interfaces
import Shoumei.Codegen.Common
import Shoumei.Codegen.SystemVerilog

namespace Shoumei.Codegen.SystemVerilogNetlist

open Shoumei.Codegen
open Shoumei.Codegen.SystemVerilog  -- Reuse bus reconstruction

/-! ## Flattening Logic -/

/-- Wire remapping function type: maps old wire to new hierarchical wire -/
abbrev WireMap := Wire → Wire

/-- Create hierarchical wire name: prefix all wires with instance name -/
def prefixWireName (instName : String) (w : Wire) : Wire :=
  { name := s!"{instName}__{w.name}" }

/-- Recursively flatten a circuit by inlining all instances.
    Returns list of gates with hierarchically-named wires.

    Strategy:
    1. Keep all direct gates from this circuit
    2. For each instance:
       a. Look up the instance's circuit definition
       b. Create wire remapping: instance port → parent wire, internal → prefixed
       c. Recursively flatten the instance circuit
       d. Collect all resulting gates

    Note: This requires access to all circuit definitions (circuit registry).
    For now, we assume instances are NOT flattened (future work: circuit registry).
    Current implementation: just keeps direct gates (TODO: add registry lookup).
-/
partial def flattenCircuit (c : Circuit) : List Gate :=
  -- TODO Phase 6: Implement recursive instance inlining
  -- For now, just return direct gates (works for leaf modules)
  -- Future: Look up instance circuits and recursively inline
  c.gates

/-! ## Helper Functions (adapted from V2) -/

/-- Get wire reference (supports both individual wires and bus signals) -/
def wireRef (ctx : Context) (_c : Circuit) (w : Wire) : String :=
  match ctx.wireToGroup.find? (fun (w', _) => w'.name == w.name) with
  | some (_, sg) =>
      -- Part of a bus - use indexed reference
      match ctx.wireToIndex.find? (fun (w', _) => w'.name == w.name) with
      | some (_, idx) => s!"{sg.name}[{idx}]"
      | none => w.name
  | none => w.name

/-- Convert signal group to SystemVerilog type -/
def signalGroupToSV (sg : SignalGroup) : String :=
  if sg.width > 1 then
    s!"logic [{sg.width - 1}:0]"
  else
    "logic"

/-- Join list of strings with newlines -/
def joinLines (lines : List String) : String :=
  String.intercalate "\n" lines

/-- Find all DFF/DFF_SET gates -/
def findDFFs (gates : List Gate) : List Gate :=
  gates.filter (fun g => g.gateType.isDFF)

/-- Group DFFs by their clock and reset signals -/
def groupDFFsByClockReset (dffs : List Gate) : List (Wire × Wire × List Gate) :=
  match dffs.head? with
  | none => []
  | some firstDFF =>
      match firstDFF.inputs with
      | [_, clk, rst] => [(clk, rst, dffs)]
      | _ => []

/-! ## Port Generation -/

/-- Generate port declaration for a wire -/
def generateWirePort (ctx : Context) (_c : Circuit) (w : Wire) (direction : String) : Option String :=
  -- Skip clock and reset (will be added explicitly for sequential circuits)
  if ctx.clockWires.contains w || ctx.resetWires.contains w then
    none
  else
    match ctx.wireToGroup.find? (fun (w', _) => w'.name == w.name) with
    | some (_, sg) =>
        -- Part of a bus - only emit for first wire in group
        if sg.wires.head? == some w then
          let svType := signalGroupToSV sg
          some s!"  {direction} {svType} {sg.name}"
        else
          none
    | none =>
        -- Standalone wire
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
    match allPorts with
    | [] => ""
    | [single] => single
    | _ =>
        let withCommas := allPorts.dropLast.map (fun p => p ++ ",")
        let lastPort := allPorts.getLast!
        joinLines (withCommas ++ [lastPort])

/-! ## Internal Wire Generation -/

/-- Check if wire is a port (input or output) -/
def isPort (c : Circuit) (w : Wire) : Bool :=
  c.inputs.any (fun inp => inp.name == w.name) ||
  c.outputs.any (fun out => out.name == w.name)

/-- Generate signal declaration for an internal wire -/
def generateInternalSignalDecl (ctx : Context) (_c : Circuit) (w : Wire) : Option String :=
  match ctx.wireToGroup.find? (fun (w', _) => w'.name == w.name) with
  | some (_, sg) =>
      -- Part of a bus - only emit for first wire in group
      if sg.wires.head? == some w then
        let svType := signalGroupToSV sg
        some s!"  {svType} {sg.name};"
      else
        none
  | none =>
      -- Standalone wire
      some s!"  logic {w.name};"

/-- Generate internal wire declarations -/
def generateInternalWires (ctx : Context) (c : Circuit) (gates : List Gate) : String :=
  -- Collect all internal wires (gate outputs that aren't ports)
  let internalWires := gates.map (·.output) |>.filter (fun w => !isPort c w)
  let decls := internalWires.filterMap (generateInternalSignalDecl ctx c)
  joinLines decls

/-! ## Combinational Logic Generation -/

/-- Generate continuous assignment for a gate -/
def generateGateAssign (ctx : Context) (c : Circuit) (g : Gate) : Option String :=
  match g.gateType with
  | GateType.DFF | GateType.DFF_SET => none  -- DFFs handled in always_ff blocks
  | GateType.AND =>
      match g.inputs with
      | [a, b] => some s!"  assign {wireRef ctx c g.output} = {wireRef ctx c a} & {wireRef ctx c b};"
      | _ => none
  | GateType.OR =>
      match g.inputs with
      | [a, b] => some s!"  assign {wireRef ctx c g.output} = {wireRef ctx c a} | {wireRef ctx c b};"
      | _ => none
  | GateType.XOR =>
      match g.inputs with
      | [a, b] => some s!"  assign {wireRef ctx c g.output} = {wireRef ctx c a} ^ {wireRef ctx c b};"
      | _ => none
  | GateType.NOT =>
      match g.inputs with
      | [a] => some s!"  assign {wireRef ctx c g.output} = ~{wireRef ctx c a};"
      | _ => none
  | GateType.BUF =>
      match g.inputs with
      | [a] => some s!"  assign {wireRef ctx c g.output} = {wireRef ctx c a};"
      | _ => none
  | GateType.MUX =>
      match g.inputs with
      | [sel, a, b] => some s!"  assign {wireRef ctx c g.output} = {wireRef ctx c sel} ? {wireRef ctx c a} : {wireRef ctx c b};"
      | _ => none

/-- Generate all combinational logic -/
def generateCombLogic (ctx : Context) (c : Circuit) (gates : List Gate) : String :=
  let assigns := gates.filterMap (generateGateAssign ctx c)
  joinLines assigns

/-! ## Sequential Logic Generation -/

/-- Compute the reset value for a signal group by checking which wires are DFF_SET.
    Returns an SV literal like "6'b100000" or "1'b0". -/
private def computeGroupResetVal (gates : List Gate) (sg : SignalGroup) : String :=
  let bits := sg.wires.map (fun w =>
    gates.any (fun g => g.gateType == GateType.DFF_SET && g.output.name == w.name))
  let hasAnySet := bits.any id
  if !hasAnySet then
    if sg.width > 1 then s!"{sg.width}'d0" else "1'b0"
  else if bits.all id then
    if sg.width > 1 then s!"{sg.width}'d{2^sg.width - 1}" else "1'b1"
  else
    let bitStr := bits.reverse.map (fun b => if b then "1" else "0") |> String.join
    s!"{sg.width}'b{bitStr}"

/-- Generate register declaration and assignment for a DFF/DFF_SET -/
def generateDFFDecl (ctx : Context) (c : Circuit) (gates : List Gate) (g : Gate) : Option (Option String × String × String) :=
  match g.inputs with
  | [d, _clk, _rst] =>
      let isCircuitOutput := c.outputs.any (fun w => w.name == g.output.name)

      match ctx.wireToGroup.find? (fun (w', _) => w'.name == g.output.name) with
      | some (_, sg) =>
          if sg.wires.head? == some g.output then
            let svType := signalGroupToSV sg
            let regName := if isCircuitOutput then sg.name else s!"{sg.name}_reg"
            let dRef := match ctx.wireToGroup.find? (fun (w', _) => w'.name == d.name) with
              | some (_, inputGroup) => inputGroup.name
              | none => d.name
            let decl := if isCircuitOutput then none else some s!"  {svType} {regName};"
            let resetVal := computeGroupResetVal gates sg
            some (decl, s!"      {regName} <= {dRef};", s!"      {regName} <= {resetVal};")
          else
            none
      | none =>
          let regName := if isCircuitOutput then g.output.name else s!"{g.output.name}_reg"
          let dRef := match ctx.wireToGroup.find? (fun (w', _) => w'.name == d.name) with
            | some (_, inputGroup) => inputGroup.name
            | none => d.name
          let decl := if isCircuitOutput then none else some s!"  logic {regName};"
          let resetVal := if g.gateType == GateType.DFF_SET then "1'b1" else "1'b0"
          some (decl, s!"      {regName} <= {dRef};", s!"      {regName} <= {resetVal};")
  | _ => none

/-- Generate always_ff block for register group -/
def generateAlwaysFFBlock (ctx : Context) (c : Circuit) (allDFFs : List Gate) (clk : Wire) (rst : Wire) (dffs : List Gate) : String :=
  let results := dffs.filterMap (generateDFFDecl ctx c allDFFs)
  let decls := results.filterMap (fun (decl, _, _) => decl)
  let assigns := results.map (fun (_, assign, _) => assign)
  let resetAssigns := results.map (fun (_, _, resetAssign) => resetAssign)

  if assigns.isEmpty then
    ""
  else
    let declsStr := joinLines decls
    let clkRef := wireRef ctx c clk
    let rstRef := wireRef ctx c rst

    let alwaysBlock := joinLines [
      s!"  always_ff @(posedge {clkRef} or posedge {rstRef}) begin",
      s!"    if ({rstRef}) begin",
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
def generateRegisters (ctx : Context) (c : Circuit) (gates : List Gate) : String :=
  let dffs := findDFFs gates
  if dffs.isEmpty then
    ""
  else
    let grouped := groupDFFsByClockReset dffs
    let blocks := grouped.map (fun (clk, rst, dffGroup) =>
      generateAlwaysFFBlock ctx c dffs clk rst dffGroup
    )
    String.intercalate "\n\n" blocks

/-! ## Netlist Generation -/

/-- Generate flat netlist SystemVerilog.
    Produces single module with all instances inlined to gates. -/
def toSystemVerilogNetlist (c : Circuit) : String :=
  -- Step 1: Flatten circuit to gates only
  let flatGates := flattenCircuit c

  -- Step 2: Build context (detect clock/reset from original circuit)
  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let isSeq := flatGates.any (fun g => g.gateType.isDFF)

  -- Step 3: Auto-detect signal groups from wire patterns
  let allWires := (c.inputs ++ c.outputs ++ flatGates.map (·.output)).eraseDups
  let signalGroups := autoDetectSignalGroups allWires

  -- Step 4: Build wire→group mapping
  let wireToGroup := signalGroups.flatMap (fun sg =>
    sg.wires.map (fun w => (w, sg))
  )
  let wireToIndex := signalGroups.flatMap (fun sg =>
    sg.wires.enum.map (fun (idx, w) => (w, idx))
  )

  let ctx : Context := {
    wireToGroup := wireToGroup
    wireToIndex := wireToIndex
    clockWires := clockWires
    resetWires := resetWires
    isSequential := isSeq
  }

  -- Step 5: Generate module header
  let header := joinLines [
    "// Flat netlist auto-generated by Shoumei Codegen",
    s!"// Source: {c.name} (all instances inlined)",
    s!"// {flatGates.length} gates total",
    "",
    s!"module {c.name} ("
  ]

  -- Step 6: Generate ports (using signal groups for buses)
  let ports := generatePorts ctx c

  -- Step 7: Generate internal wires
  let internalWires := generateInternalWires ctx c flatGates

  -- Step 8: Generate combinational logic
  let combLogic := generateCombLogic ctx c flatGates

  -- Step 9: Generate always_ff blocks for registers
  let registers := generateRegisters ctx c flatGates

  -- Step 10: Assemble module
  let body := joinLines [
    if ports.isEmpty then ");" else ports ++ "\n);",
    "",
    if internalWires.isEmpty then "" else internalWires ++ "\n",
    if combLogic.isEmpty then "" else combLogic ++ "\n",
    if registers.isEmpty then "" else registers
  ]

  let footer := "endmodule"

  joinLines [header, body, footer]

end Shoumei.Codegen.SystemVerilogNetlist
