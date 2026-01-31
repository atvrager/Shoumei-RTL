/-
Codegen/SystemVerilog.lean - SystemVerilog Code Generator

Generates synthesizable Verilog from DSL circuits.

Design:
- Verilog-95 format for ABC compatibility
- Combinational circuits only (no always blocks yet)
- Sequential circuits (registers/always blocks) - NOT YET IMPLEMENTED

Target: Verilog-95 (for ABC), extensible to SystemVerilog
-/

import ProvenRTL.DSL
import ProvenRTL.Codegen.Common

namespace ProvenRTL.Codegen.SystemVerilog

open ProvenRTL.Codegen

-- Generate SystemVerilog operator for a combinational gate type
def gateTypeToOperator (gt : GateType) : String :=
  match gt with
  | GateType.AND => "&"
  | GateType.OR => "|"
  | GateType.NOT => "~"
  | GateType.XOR => "^"
  | GateType.DFF => ""  -- DFF doesn't use operators, uses always block

-- Generate a single combinational gate assignment
-- Note: DFFs are handled separately in generateAlwaysBlocks
def generateCombGate (g : Gate) : String :=
  let op := gateTypeToOperator g.gateType
  match g.gateType with
  | GateType.NOT =>
      -- Unary operator: ~input
      match g.inputs with
      | [i0] => s!"  assign {g.output.name} = {op}{i0.name};"
      | _ => s!"  // ERROR: NOT gate should have 1 input"
  | GateType.DFF =>
      ""  -- DFFs handled in always blocks, not assign statements
  | _ =>
      -- Binary operators: input1 op input2
      match g.inputs with
      | [i0, i1] => s!"  assign {g.output.name} = {i0.name} {op} {i1.name};"
      | _ => s!"  // ERROR: Binary gate should have 2 inputs"

-- Generate always block for a D Flip-Flop
-- DFF inputs: [d, clk, reset], output: q
def generateDFF (g : Gate) : String :=
  match g.inputs with
  | [d, clk, reset] =>
      joinLines [
        s!"  always @(posedge {clk.name}) begin",
        s!"    if ({reset.name})",
        s!"      {g.output.name} <= 1'b0;",
        s!"    else",
        s!"      {g.output.name} <= {d.name};",
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
def generateCombAssignments (c : Circuit) : String :=
  let combGates := c.gates.filter (fun g => g.gateType.isCombinational)
  let assignments := combGates.map generateCombGate
  joinLines assignments

-- Generate all always blocks for sequential elements (DFFs)
def generateAlwaysBlocks (c : Circuit) : String :=
  let dffGates := c.gates.filter (fun g => g.gateType == GateType.DFF)
  let blocks := dffGates.map generateDFF
  joinLines blocks


-- Main code generator: Circuit → SystemVerilog module
-- Supports both combinational and sequential circuits
def toSystemVerilog (c : Circuit) : String :=
  let moduleName := c.name
  let dffOutputs := findDFFOutputs c

  -- Use Verilog-95 style for ABC compatibility:
  -- module name(port1, port2, ...);
  --   input port1;
  --   output port2;  (or 'output reg' for DFF outputs)
  --   ...
  -- endmodule

  -- Port list (just names, no direction)
  let allPorts := c.inputs ++ c.outputs
  let portNames := allPorts.map (fun w => w.name)
  let portList := String.intercalate ", " portNames

  -- Input declarations
  let inputDecls := c.inputs.map (fun w => s!"  input {w.name};")
  let inputSection := joinLines inputDecls

  -- Output declarations (use 'output reg' for DFF outputs)
  let outputDecls := c.outputs.map (fun w =>
    if dffOutputs.contains w then
      s!"  output reg {w.name};"
    else
      s!"  output {w.name};"
  )
  let outputSection := joinLines outputDecls

  -- Get wire declarations, combinational assignments, and always blocks
  let wireDecls := generateWireDeclarations c
  let combAssigns := generateCombAssignments c
  let alwaysBlocks := generateAlwaysBlocks c

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

end ProvenRTL.Codegen.SystemVerilog
