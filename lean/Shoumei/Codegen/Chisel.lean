/-
Codegen/Chisel.lean - Chisel Code Generator

Generates Chisel (Scala) code from DSL circuits.

Design:
- Combinational circuits: RawModule (no clock/reset, direct port declarations)
- Sequential circuits: Module (with implicit clock/reset, registers)
- Port names match LEAN output exactly for LEC

Target: Chisel 7.x (Scala 2.13)
Output will be compiled to SystemVerilog via FIRRTL/CIRCT
-/

import Shoumei.DSL
import Shoumei.Codegen.Common

namespace Shoumei.Codegen.Chisel

open Shoumei.Codegen

-- Generate Chisel operator for a combinational gate type
def gateTypeToOperator (gt : GateType) : String :=
  match gt with
  | GateType.AND => "&"
  | GateType.OR => "|"
  | GateType.NOT => "~"
  | GateType.XOR => "^"
  | GateType.DFF => ""  -- DFF doesn't use operators, uses RegInit

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

-- Generate a single combinational gate assignment
-- DFFs are handled separately
def generateCombGate (c : Circuit) (g : Gate) : String :=
  let op := gateTypeToOperator g.gateType
  let outRef := wireRef c g.output
  match g.gateType with
  | GateType.NOT =>
      match g.inputs with
      | [i0] => s!"  {outRef} := {op}{wireRef c i0}"
      | _ => s!"  // ERROR: NOT gate should have 1 input"
  | GateType.DFF =>
      ""  -- DFFs handled separately in generateDFFLogic
  | _ =>
      match g.inputs with
      | [i0, i1] => s!"  {outRef} := {wireRef c i0} {op} {wireRef c i1}"
      | _ => s!"  // ERROR: Binary gate should have 2 inputs"

-- Helper: find all clock wires (wires used as clock inputs to DFFs)
-- For Module, these should not be in the IO bundle (clock is implicit)
def findClockWires (c : Circuit) : List Wire :=
  c.gates.filterMap (fun g =>
    if g.gateType == GateType.DFF then
      match g.inputs with
      | [_d, clk, _reset] => some clk
      | _ => none
    else
      none
  )

-- Helper: find all reset wires (wires used as reset inputs to DFFs)
-- For Module, these should not be in the IO bundle (reset is implicit)
def findResetWires (c : Circuit) : List Wire :=
  c.gates.filterMap (fun g =>
    if g.gateType == GateType.DFF then
      match g.inputs with
      | [_d, _clk, reset] => some reset
      | _ => none
    else
      none
  )

-- Generate D Flip-Flop logic in Chisel
-- DFF inputs: [d, clk, reset], output: q
-- Note: In Module, clock and reset are implicit
-- If reset wire is in circuit inputs, use it; otherwise use implicit reset.asBool
-- If output is a circuit output, use _reg suffix for the register
def generateDFF (c : Circuit) (g : Gate) : String :=
  match g.inputs with
  | [d, _clk, reset] =>
      let isOutput := isCircuitOutput c g.output
      let regName := if isOutput then g.output.name ++ "_reg" else g.output.name
      let outRef := wireRef c g.output
      let dRef := wireRef c d
      -- Check if reset is an explicit input (not filtered out)
      -- If it's filtered (used as DFF reset), use implicit reset.asBool
      let allResetWires := findResetWires c
      let resetRef := if allResetWires.contains reset then "reset.asBool" else wireRef c reset
      let updateLogic := joinLines [
        "  when(" ++ resetRef ++ ") {",
        "    " ++ regName ++ " := false.B",
        "  }.otherwise {",
        "    " ++ regName ++ " := " ++ dRef,
        "  }"
      ]
      -- If DFF output is a circuit output, add connection
      if isOutput then
        updateLogic ++ "\n  " ++ outRef ++ " := " ++ regName
      else
        updateLogic
  | _ => "  // ERROR: DFF should have 3 inputs: [d, clk, reset]"

-- Helper: find all internal wires (same as SystemVerilog)
def findInternalWires (c : Circuit) : List Wire :=
  let gateOutputs := c.gates.map (fun g => g.output)
  gateOutputs.filter (fun w => !c.outputs.contains w)

-- Helper: find all DFF output wires
def findDFFOutputs (c : Circuit) : List Wire :=
  c.gates.filter (fun g => g.gateType == GateType.DFF) |>.map (fun g => g.output)

-- Generate IO port declarations
-- For RawModule: all ports declared directly
-- For Module: filter out clock and reset wires (both are implicit in Module)
def generateIOBundle (c : Circuit) (isSequential : Bool) : String :=
  let clockWires := if isSequential then findClockWires c else []
  let resetWires := if isSequential then findResetWires c else []
  let implicitWires := clockWires ++ resetWires
  -- Filter out clock and reset wires from inputs for sequential circuits
  let filteredInputs := c.inputs.filter (fun w => !implicitWires.contains w)
  let inputDecls := filteredInputs.map (fun w => s!"  val {w.name} = IO(Input(Bool()))")
  let outputDecls := c.outputs.map (fun w => s!"  val {w.name} = IO(Output(Bool()))")
  let allDecls := inputDecls ++ outputDecls

  joinLines allDecls

-- Generate combinational logic (wire declarations + assignments for comb gates)
def generateCombLogic (c : Circuit) : String :=
  let internalWires := findInternalWires c
  let dffOutputs := findDFFOutputs c
  -- Only declare wires for non-DFF outputs (DFFs use RegInit)
  let wireDecls := internalWires.filter (fun w => !dffOutputs.contains w) |>.map (fun w => s!"  val {w.name} = Wire(Bool())")

  -- Combinational gate assignments
  let combGates := c.gates.filter (fun g => g.gateType.isCombinational)
  let assignments := combGates.map (generateCombGate c)

  -- Combine with blank line separator if we have both
  if wireDecls.isEmpty then
    joinLines assignments
  else if assignments.isEmpty then
    joinLines wireDecls
  else
    joinLines wireDecls ++ "\n\n" ++ joinLines assignments

-- Generate sequential logic (register declarations + DFF logic)
def generateSeqLogic (c : Circuit) : String :=
  let dffGates := c.gates.filter (fun g => g.gateType == GateType.DFF)
  if dffGates.isEmpty then
    ""
  else
    -- Register declarations (use _reg suffix if output is a circuit output)
    let regDecls := dffGates.map (fun g =>
      let isOutput := isCircuitOutput c g.output
      let regName := if isOutput then g.output.name ++ "_reg" else g.output.name
      s!"  val {regName} = RegInit(false.B)")
    -- DFF update logic
    let dffLogic := dffGates.map (generateDFF c)
    joinLines regDecls ++ "\n\n" ++ joinLines dffLogic

-- Main code generator: Circuit → Chisel module
-- Uses RawModule for purely combinational circuits
-- Uses Module for sequential circuits (with implicit clock/reset)
def toChisel (c : Circuit) : String :=
  let moduleName := c.name
  let isSequential := c.hasSequentialElements

  if isSequential then
    -- Use Module for sequential circuits (implicit clock/reset)
    let combLogic := generateCombLogic c
    let seqLogic := generateSeqLogic c
    let logic := if combLogic.isEmpty then
                   seqLogic
                 else if seqLogic.isEmpty then
                   combLogic
                 else
                   combLogic ++ "\n\n" ++ seqLogic

    joinLines [
      "package generated",
      "",
      "import chisel3._",
      "import chisel3.util._",
      "",
      "class " ++ moduleName ++ " extends Module {",
      generateIOBundle c true,  -- true = sequential, filter out clock
      "",
      logic,
      "}"
    ]
  else
    -- Use RawModule for combinational circuits (no clock/reset)
    joinLines [
      "package generated",
      "",
      "import chisel3._",
      "import chisel3.util._",
      "",
      "class " ++ moduleName ++ " extends RawModule {",
      generateIOBundle c false,  -- false = combinational, keep all ports
      "",
      generateCombLogic c,
      "}"
    ]

-- TODO: Prove correctness theorem
-- theorem toChisel_correct (c : Circuit) :
--   ⟦ toChisel c ⟧ = evalCircuit c := by
--   sorry

end Shoumei.Codegen.Chisel
