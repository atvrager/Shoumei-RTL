/-
Codegen/SystemVerilog.lean - SystemVerilog Code Generator

Generates synthesizable SystemVerilog from DSL circuits.
Currently stubbed with hardcoded output - to be implemented fully.

Target: IEEE 1800-2017 SystemVerilog, synthesizable subset
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

-- Main code generator: Circuit → SystemVerilog module
def toSystemVerilog (c : Circuit) : String :=
  let moduleName := c.name

  -- Format inputs: one per line
  let inputLines := c.inputs.map (fun w => s!"  input {w.name}")
  let inputsSection := String.intercalate ",\n" inputLines

  -- Format outputs: one per line
  let outputLines := c.outputs.map (fun w => s!"  output {w.name}")
  let outputsSection := String.intercalate ",\n" outputLines

  -- Get wire declarations and assignments
  let wireDecls := generateWireDeclarations c
  let assigns := generateAssignments c

  -- Build module
  let header := s!"module {moduleName}(\n{inputsSection},\n{outputsSection}\n);"
  let body := if wireDecls.isEmpty then assigns else wireDecls ++ "\n\n" ++ assigns

  joinLines [
    header,
    "",
    body,
    "",
    "endmodule"
  ]

-- TODO: Prove correctness theorem
-- theorem toSystemVerilog_correct (c : Circuit) :
--   ⟦ toSystemVerilog c ⟧ = evalCircuit c := by
--   sorry

end ProvenRTL.Codegen.SystemVerilog
