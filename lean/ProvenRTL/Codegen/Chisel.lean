/-
Codegen/Chisel.lean - Chisel Code Generator

Generates Chisel (Scala) code from DSL circuits.
Currently stubbed with hardcoded output - to be implemented fully.

Target: Chisel 6.x (Scala 3)
Output will be compiled to SystemVerilog via FIRRTL/CIRCT
-/

import ProvenRTL.DSL
import ProvenRTL.Codegen.Common

namespace ProvenRTL.Codegen.Chisel

open ProvenRTL.Codegen

-- Generate Chisel operator for a gate type
def gateTypeToOperator (gt : GateType) : String :=
  match gt with
  | GateType.AND => "&"
  | GateType.OR => "|"
  | GateType.NOT => "~"
  | GateType.XOR => "^"

-- Helper: check if a wire is a circuit input
def isCircuitInput (c : Circuit) (w : Wire) : Bool :=
  c.inputs.contains w

-- Helper: check if a wire is a circuit output
def isCircuitOutput (c : Circuit) (w : Wire) : Bool :=
  c.outputs.contains w

-- Helper: generate wire reference (io.name for inputs/outputs, name for internal wires)
def wireRef (c : Circuit) (w : Wire) : String :=
  if isCircuitInput c w || isCircuitOutput c w then
    s!"io.{w.name}"
  else
    w.name

-- Generate a single gate assignment
def generateGate (c : Circuit) (g : Gate) : String :=
  let op := gateTypeToOperator g.gateType
  let outRef := wireRef c g.output
  match g.gateType with
  | GateType.NOT =>
      match g.inputs with
      | [i0] => s!"  {outRef} := {op}{wireRef c i0}"
      | _ => s!"  // ERROR: NOT gate should have 1 input"
  | _ =>
      match g.inputs with
      | [i0, i1] => s!"  {outRef} := {wireRef c i0} {op} {wireRef c i1}"
      | _ => s!"  // ERROR: Binary gate should have 2 inputs"

-- Helper: find all internal wires (same as SystemVerilog)
def findInternalWires (c : Circuit) : List Wire :=
  let gateOutputs := c.gates.map (fun g => g.output)
  gateOutputs.filter (fun w => !c.outputs.contains w)

-- Generate IO bundle declaration
def generateIOBundle (c : Circuit) : String :=
  let inputDecls := c.inputs.map (fun w => s!"    val {w.name} = Input(Bool())")
  let outputDecls := c.outputs.map (fun w => s!"    val {w.name} = Output(Bool())")
  let allDecls := inputDecls ++ outputDecls

  joinLines ([
    "  val io = IO(new Bundle {"
  ] ++ allDecls ++ [
    "  })"
  ])

-- Generate gate logic (wire declarations + assignments)
def generateLogic (c : Circuit) : String :=
  -- Internal wire declarations
  let internalWires := findInternalWires c
  let wireDecls := internalWires.map (fun w => s!"  val {w.name} = Wire(Bool())")

  -- Gate assignments
  let assignments := c.gates.map (generateGate c)

  -- Combine with blank line separator if we have both
  if wireDecls.isEmpty then
    joinLines assignments
  else if assignments.isEmpty then
    joinLines wireDecls
  else
    joinLines wireDecls ++ "\n\n" ++ joinLines assignments

-- Main code generator: Circuit → Chisel module
def toChisel (c : Circuit) : String :=
  let moduleName := c.name

  joinLines [
    "package generated",
    "",
    "import chisel3._",
    "import chisel3.util._",
    "",
    "class " ++ moduleName ++ " extends Module {",
    generateIOBundle c,
    "",
    generateLogic c,
    "}"
  ]

-- TODO: Prove correctness theorem
-- theorem toChisel_correct (c : Circuit) :
--   ⟦ toChisel c ⟧ = evalCircuit c := by
--   sorry

end ProvenRTL.Codegen.Chisel
