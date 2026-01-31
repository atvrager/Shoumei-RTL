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

-- Generate SystemVerilog operator for a gate type
def gateTypeToOperator (gt : GateType) : String :=
  match gt with
  | GateType.AND => "&"
  | GateType.OR => "|"
  | GateType.NOT => "~"
  | GateType.XOR => "^"

-- Generate a single gate assignment
def generateGate (g : Gate) : String :=
  let op := gateTypeToOperator g.gateType
  match g.gateType with
  | GateType.NOT =>
      -- Unary operator: ~input
      match g.inputs with
      | [i0] => s!"  assign {g.output.name} = {op}{i0.name};"
      | _ => s!"  // ERROR: NOT gate should have 1 input"
  | _ =>
      -- Binary operators: input1 op input2
      match g.inputs with
      | [i0, i1] => s!"  assign {g.output.name} = {i0.name} {op} {i1.name};"
      | _ => s!"  // ERROR: Binary gate should have 2 inputs"

-- Helper: find all internal wires (gate outputs that are not circuit outputs)
def findInternalWires (c : Circuit) : List Wire :=
  let gateOutputs := c.gates.map (fun g => g.output)
  gateOutputs.filter (fun w => !c.outputs.contains w)

-- Generate all internal wire declarations
def generateWireDeclarations (c : Circuit) : String :=
  let internalWires := findInternalWires c
  if internalWires.isEmpty then
    ""
  else
    let decls := internalWires.map (fun w => s!"  wire {w.name};")
    joinLines decls

-- Generate all gate assignments
def generateAssignments (c : Circuit) : String :=
  let assignments := c.gates.map generateGate
  joinLines assignments

-- Check if circuit has sequential elements
def hasSequentialElements (_ : Circuit) : Bool :=
  -- TODO: When adding registers/sequential elements to GateType, check for them here
  -- For now, all gates are combinational
  false

-- Validation: Ensure circuit is combinational
def validateCombinational (c : Circuit) : Except String Unit :=
  if hasSequentialElements c then
    Except.error s!"Circuit '{c.name}' has sequential elements but SystemVerilog generator only supports combinational circuits. Please extend the generator to add always blocks for sequential logic."
  else
    Except.ok ()

-- Main code generator: Circuit → SystemVerilog module
def toSystemVerilog (c : Circuit) : String :=
  let moduleName := c.name

  -- Validate that circuit is combinational
  match validateCombinational c with
  | Except.error msg => s!"// ERROR: {msg}\n// Generator needs updating for sequential circuits!"
  | Except.ok _ =>
      -- Use Verilog-95 style for ABC compatibility:
      -- module name(port1, port2, ...);
      --   input port1;
      --   output port2;
      --   ...
      -- endmodule

      -- Port list (just names, no direction)
      let allPorts := c.inputs ++ c.outputs
      let portNames := allPorts.map (fun w => w.name)
      let portList := String.intercalate ", " portNames

      -- Input declarations
      let inputDecls := c.inputs.map (fun w => s!"  input {w.name};")
      let inputSection := joinLines inputDecls

      -- Output declarations
      let outputDecls := c.outputs.map (fun w => s!"  output {w.name};")
      let outputSection := joinLines outputDecls

      -- Get wire declarations and assignments
      let wireDecls := generateWireDeclarations c
      let assigns := generateAssignments c

      -- Build module
      joinLines [
        s!"module {moduleName}({portList});",
        inputSection,
        outputSection,
        "",
        wireDecls,
        "",
        assigns,
        "",
        "endmodule"
      ]

-- TODO: Prove correctness theorem
-- theorem toSystemVerilog_correct (c : Circuit) :
--   ⟦ toSystemVerilog c ⟧ = evalCircuit c := by
--   sorry

end ProvenRTL.Codegen.SystemVerilog
