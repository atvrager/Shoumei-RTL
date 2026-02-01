/-
Codegen/SystemVerilog.lean - SystemVerilog Code Generator

Generates synthesizable Verilog from DSL circuits.

Design:
- Verilog-95 format for ABC compatibility
- Combinational circuits only (no always blocks yet)
- Sequential circuits (registers/always blocks) - NOT YET IMPLEMENTED

Target: Verilog-95 (for ABC), extensible to SystemVerilog
-/

import Shoumei.DSL
import Shoumei.Codegen.Common

namespace Shoumei.Codegen.SystemVerilog

open Shoumei.Codegen

-- Generate SystemVerilog operator for a combinational gate type
def gateTypeToOperator (gt : GateType) : String :=
  match gt with
  | GateType.AND => "&"
  | GateType.OR => "|"
  | GateType.NOT => "~"
  | GateType.XOR => "^"
  | GateType.BUF => ""   -- Buffer is direct assignment (no operator)
  | GateType.MUX => "?"  -- Ternary operator (special handling required)
  | GateType.DFF => ""  -- DFF doesn't use operators, uses always block

-- Helper: Get wire reference (handles flattened I/O with underscore indexing)
def wireRef (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (w : Wire) : String :=
  match inputToIndex.find? (fun p => p.fst.name == w.name) with
  | some (_wire, idx) => s!"inputs_{idx}"
  | none =>
      match outputToIndex.find? (fun p => p.fst.name == w.name) with
      | some (_wire, idx) => s!"outputs_{idx}"
      | none => w.name

-- Generate a single combinational gate assignment
-- Note: DFFs are handled separately in generateAlwaysBlocks
def generateCombGate (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (g : Gate) : String :=
  let op := gateTypeToOperator g.gateType
  let outRef := wireRef inputToIndex outputToIndex g.output
  match g.gateType with
  | GateType.NOT =>
      -- Unary operator: ~input
      match g.inputs with
      | [i0] => s!"  assign {outRef} = {op}{wireRef inputToIndex outputToIndex i0};"
      | _ => s!"  // ERROR: NOT gate should have 1 input"
  | GateType.BUF =>
      -- Buffer: direct assignment
      match g.inputs with
      | [i0] => s!"  assign {outRef} = {wireRef inputToIndex outputToIndex i0};"
      | _ => s!"  // ERROR: BUF gate should have 1 input"
  | GateType.MUX =>
      -- Ternary operator: sel ? in1 : in0
      -- inputs: [in0, in1, sel]
      match g.inputs with
      | [in0, in1, sel] =>
          let in0Ref := wireRef inputToIndex outputToIndex in0
          let in1Ref := wireRef inputToIndex outputToIndex in1
          let selRef := wireRef inputToIndex outputToIndex sel
          s!"  assign {outRef} = {selRef} ? {in1Ref} : {in0Ref};"
      | _ => s!"  // ERROR: MUX gate should have 3 inputs: [in0, in1, sel]"
  | GateType.DFF =>
      ""  -- DFFs handled in always blocks, not assign statements
  | _ =>
      -- Binary operators: input1 op input2
      match g.inputs with
      | [i0, i1] =>
          let i0Ref := wireRef inputToIndex outputToIndex i0
          let i1Ref := wireRef inputToIndex outputToIndex i1
          s!"  assign {outRef} = {i0Ref} {op} {i1Ref};"
      | _ => s!"  // ERROR: Binary gate should have 2 inputs"

-- Generate always block for a D Flip-Flop
-- DFF inputs: [d, clk, reset], output: q
def generateDFF (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (g : Gate) : String :=
  match g.inputs with
  | [d, clk, reset] =>
      let dRef := wireRef inputToIndex outputToIndex d
      let clkRef := wireRef inputToIndex outputToIndex clk
      let resetRef := wireRef inputToIndex outputToIndex reset
      let qRef := wireRef inputToIndex outputToIndex g.output
      joinLines [
        s!"  always @(posedge {clkRef}) begin",
        s!"    if ({resetRef})",
        s!"      {qRef} <= 1'b0;",
        s!"    else",
        s!"      {qRef} <= {dRef};",
        s!"  end"
      ]
  | _ => s!"  // ERROR: DFF should have 3 inputs: [d, clk, reset]"

-- Helper: find all internal wires (gate outputs that are not circuit outputs)
def findInternalWires (c : Circuit) : List Wire :=
  let gateOutputs := c.gates.map (fun g => g.output)
  gateOutputs.filter (fun w => !c.outputs.contains w)

-- Helper: find all DFF output wires (need to be declared as reg, not wire)
def findDFFOutputs (c : Circuit) : List Wire :=
  c.gates.filter (fun g => g.gateType == GateType.DFF) |>.map (fun g => g.output)

-- Generate all internal wire declarations
-- DFF outputs are declared as 'reg', other internal wires as 'wire'
def generateWireDeclarations (c : Circuit) : String :=
  let internalWires := findInternalWires c
  let dffOutputs := findDFFOutputs c
  if internalWires.isEmpty then
    ""
  else
    let decls := internalWires.map (fun w =>
      if dffOutputs.contains w then
        s!"  reg {w.name};"  -- DFF outputs must be 'reg'
      else
        s!"  wire {w.name};"
    )
    joinLines decls

-- Generate all combinational gate assignments (DFFs handled separately)
def generateCombAssignments (c : Circuit) (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) : String :=
  let combGates := c.gates.filter (fun g => g.gateType.isCombinational)
  let assignments := combGates.map (generateCombGate inputToIndex outputToIndex)
  joinLines assignments

-- Generate all always blocks for sequential elements (DFFs)
def generateAlwaysBlocks (c : Circuit) (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) : String :=
  let dffGates := c.gates.filter (fun g => g.gateType == GateType.DFF)
  let blocks := dffGates.map (generateDFF inputToIndex outputToIndex)
  joinLines blocks


-- Main code generator: Circuit → SystemVerilog module
-- Supports both combinational and sequential circuits
-- Uses bundled I/O (input/output vectors) for large circuits (>500 I/O ports)
def toSystemVerilog (c : Circuit) : String :=
  let moduleName := c.name
  let dffOutputs := findDFFOutputs c

  -- Check if we should use bundled I/O (for large circuits)
  let (inputToIndex, outputToIndex, useBundledIO, filteredInputs) :=
    let dffGates := c.gates.filter (fun g => g.gateType == GateType.DFF)
    let clockWires := dffGates.filterMap (fun g => match g.inputs with | [_d, clk, _res] => some clk | _ => none)
    let resetWires := dffGates.filterMap (fun g => match g.inputs with | [_d, _clk, res] => some res | _ => none)
    let implicitWires := clockWires ++ resetWires
    let filtered := c.inputs.filter (fun w => !implicitWires.contains w)
    let totalPorts := filtered.length + c.outputs.length
    let useBundle := totalPorts > 50
    if useBundle then
      (filtered.enum.map (fun ⟨idx, wire⟩ => (wire, idx)),
       c.outputs.enum.map (fun ⟨idx, wire⟩ => (wire, idx)),
       true, filtered)
    else
      ([], [], false, c.inputs)

  -- Generate port list and declarations
  let (portList, inputSection, outputSection) :=
    if useBundledIO then
      -- Flattened I/O with underscore indexing (matches CIRCT firtool output)
      -- Generate individual ports for bundle + implicit ports
      let inputPortNames := filteredInputs.enum.map (fun ⟨idx, _⟩ => s!"inputs_{idx}")
      let outputPortNames := c.outputs.enum.map (fun ⟨idx, _⟩ => s!"outputs_{idx}")
      
      -- Find implicit ports to keep them separate
      let implicitInputs := c.inputs.filter (fun w => !filteredInputs.contains w)
      let implicitPortNames := implicitInputs.map (fun w => w.name)
      
      let allPortNames := inputPortNames ++ implicitPortNames ++ outputPortNames
      let portListStr := String.intercalate ", " allPortNames
 
      -- Generate individual declarations
      let inputDecls := filteredInputs.enum.map (fun ⟨idx, _⟩ => s!"  input inputs_{idx};")
      let implicitDecls := implicitInputs.map (fun w => s!"  input {w.name};")
      let inputSectionStr := joinLines (inputDecls ++ implicitDecls)
 
      -- Generate individual output declarations
      let outputDecls := c.outputs.enum.map (fun ⟨idx, wire⟩ =>
        if dffOutputs.contains wire then
          s!"  output reg outputs_{idx};"
        else
          s!"  output outputs_{idx};"
      )
      let outputSectionStr := joinLines outputDecls
 
      (portListStr, inputSectionStr, outputSectionStr)
    else
      -- Individual I/O: traditional Verilog-95 style
      let allPorts := c.inputs ++ c.outputs
      let portNames := allPorts.map (fun w => w.name)
      let portListStr := String.intercalate ", " portNames

      let inputDecls := c.inputs.map (fun w => s!"  input {w.name};")
      let inputSectionStr := joinLines inputDecls

      let outputDecls := c.outputs.map (fun w =>
        if dffOutputs.contains w then
          s!"  output reg {w.name};"
        else
          s!"  output {w.name};"
      )
      let outputSectionStr := joinLines outputDecls

      (portListStr, inputSectionStr, outputSectionStr)

  -- Get wire declarations, combinational assignments, and always blocks
  let wireDecls := generateWireDeclarations c
  let combAssigns := generateCombAssignments c inputToIndex outputToIndex
  let alwaysBlocks := generateAlwaysBlocks c inputToIndex outputToIndex

  -- Build module
  joinLines [
    s!"module {moduleName}({portList});",
    inputSection,
    outputSection,
    "",
    wireDecls,
    "",
    combAssigns,
    "",
    alwaysBlocks,
    "",
    "endmodule"
  ]

-- TODO: Prove correctness theorem
-- theorem toSystemVerilog_correct (c : Circuit) :
--   ⟦ toSystemVerilog c ⟧ = evalCircuit c := by
--   sorry

end Shoumei.Codegen.SystemVerilog
