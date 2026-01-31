/-
Codegen/Chisel.lean - Chisel Code Generator

Generates Chisel (Scala) code from DSL circuits.

Design:
- Combinational circuits: RawModule (no clock/reset, direct port declarations)
- Sequential circuits: Module (with clock/reset) - NOT YET IMPLEMENTED
- Port names match LEAN output exactly for LEC

Target: Chisel 7.x (Scala 2.13)
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

-- Helper: generate wire reference
-- For RawModule without IO bundle, all wires use direct names
def wireRef (_ : Circuit) (w : Wire) : String :=
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

-- Generate IO port declarations
-- For RawModule, we use direct port declarations instead of IO bundle
-- This makes port names match exactly with LEAN output (no io_ prefix)
def generateIOBundle (c : Circuit) : String :=
  let inputDecls := c.inputs.map (fun w => s!"  val {w.name} = IO(Input(Bool()))")
  let outputDecls := c.outputs.map (fun w => s!"  val {w.name} = IO(Output(Bool()))")
  let allDecls := inputDecls ++ outputDecls

  joinLines allDecls

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

-- Check if circuit has sequential elements
-- Currently, we only support combinational gates
-- When sequential elements are added to the DSL, this will need updating
def hasSequentialElements (_ : Circuit) : Bool :=
  -- TODO: When adding registers/sequential elements to GateType, check for them here
  -- For now, all gates are combinational
  false

-- Validation: Ensure circuit is combinational
-- This fails compilation if someone adds sequential elements without updating the generator
def validateCombinational (c : Circuit) : Except String Unit :=
  if hasSequentialElements c then
    Except.error s!"Circuit '{c.name}' has sequential elements but Chisel generator only supports combinational circuits. Please extend the generator to use Module for sequential circuits."
  else
    Except.ok ()

-- Main code generator: Circuit → Chisel module
def toChisel (c : Circuit) : String :=
  let moduleName := c.name

  -- Validate that circuit is combinational
  -- If this fails, it means sequential elements were added to DSL
  -- and the generator needs to be extended
  match validateCombinational c with
  | Except.error msg => s!"// ERROR: {msg}\n// Generator needs updating for sequential circuits!"
  | Except.ok _ =>
      -- Use RawModule for combinational circuits (no clock/reset)
      -- When adding sequential support, use Module for circuits with registers
      joinLines [
        "package generated",
        "",
        "import chisel3._",
        "import chisel3.util._",
        "",
        "class " ++ moduleName ++ " extends RawModule {",
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
