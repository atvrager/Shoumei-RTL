/-
Codegen/SystemC.lean - SystemC Code Generator

Generates SystemC simulation models from DSL circuits.

Design:
- Generates both .h (header) and .cpp (implementation) files
- SC_MODULE for all circuits
- SC_METHOD for combinational logic with sensitivity lists
- SC_CTHREAD for sequential logic (DFFs) with clock edges
- Supports both small and large circuits (bundled I/O with sc_vector)

Target: SystemC 2.3.3+ (ISO/IEC 1666-2011)
-/

import Shoumei.DSL
import Shoumei.Codegen.Common

namespace Shoumei.Codegen.SystemC

open Shoumei.Codegen

-- Generate SystemC operator for a combinational gate type
def gateTypeToOperator (gt : GateType) : String :=
  match gt with
  | GateType.AND => "&"
  | GateType.OR => "|"
  | GateType.NOT => "~"
  | GateType.XOR => "^"
  | GateType.BUF => ""   -- Buffer is direct assignment (no operator)
  | GateType.MUX => "?"  -- Ternary operator (special handling required)
  | GateType.DFF => ""   -- DFF doesn't use operators, uses SC_CTHREAD

-- Helper: Get wire reference for SystemC (handles both individual and bundled I/O)
def wireRef (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (w : Wire) : String :=
  match inputToIndex.find? (fun p => p.fst.name == w.name) with
  | some (_wire, idx) => s!"inputs[{idx}]"
  | none =>
      match outputToIndex.find? (fun p => p.fst.name == w.name) with
      | some (_wire, idx) => s!"outputs[{idx}]"
      | none => w.name

-- Helper: find all internal wires (gate outputs that are not circuit outputs)
def findInternalWires (c : Circuit) : List Wire :=
  let gateOutputs := c.gates.map (fun g => g.output)
  gateOutputs.filter (fun w => !c.outputs.contains w)

-- Helper: find all DFF output wires (need special handling)
def findDFFOutputs (c : Circuit) : List Wire :=
  c.gates.filter (fun g => g.gateType == GateType.DFF)
    |>.map (fun g => g.output)

-- Helper: find all clock wires (from DFF inputs)
def findClockWires (c : Circuit) : List Wire :=
  c.gates.filterMap (fun g =>
    if g.gateType == GateType.DFF then
      match g.inputs with
      | [_d, clk, _reset] => some clk
      | _ => none
    else
      none)
  |>.eraseDups

-- Helper: find all reset wires (from DFF inputs)
def findResetWires (c : Circuit) : List Wire :=
  c.gates.filterMap (fun g =>
    if g.gateType == GateType.DFF then
      match g.inputs with
      | [_d, _clk, reset] => some reset
      | _ => none
    else
      none)
  |>.eraseDups

-- Generate port declarations for header file
def generatePortDeclarations (c : Circuit) (useBundledIO : Bool) : String :=
  if useBundledIO then
    let inputCount := c.inputs.length
    let outputCount := c.outputs.length
    joinLines [
      s!"  sc_vector<sc_in<bool>> inputs;    // {inputCount} input ports",
      s!"  sc_vector<sc_out<bool>> outputs;  // {outputCount} output ports"
    ]
  else
    -- Individual port declarations (include all inputs/outputs)
    let inputDecls := c.inputs.map (fun w => s!"  sc_in<bool> {w.name};")
    let outputDecls := c.outputs.map (fun w => s!"  sc_out<bool> {w.name};")
    joinLines (inputDecls ++ outputDecls)

-- Generate internal signal declarations
def generateSignalDeclarations (c : Circuit) : String :=
  let internalWires := findInternalWires c
  if internalWires.isEmpty then
    ""
  else
    let decls := internalWires.map (fun w => s!"  sc_signal<bool> {w.name};")
    joinLines decls

-- Generate sensitivity list for SC_METHOD (all non-clock/reset inputs for data)
def generateSensitivityList (c : Circuit) (useBundledIO : Bool) : String :=
  if useBundledIO then
    -- For bundled I/O, sensitivity on entire vector
    "    sensitive << inputs;"
  else
    -- Individual inputs (exclude clock/reset from combinational sensitivity)
    let isSeq := c.hasSequentialElements
    let clocks := findClockWires c
    let resets := findResetWires c

    let dataInputs := if isSeq then
      c.inputs.filter (fun w => !clocks.contains w && !resets.contains w)
    else
      c.inputs

    if dataInputs.isEmpty then
      "    // No data inputs for sensitivity list"
    else
      let inputNames := dataInputs.map (fun w => w.name)
      let senseList := String.intercalate " << " inputNames
      s!"    sensitive << {senseList};"

-- Generate constructor (SC_CTOR) with process registration
def generateConstructor (c : Circuit) (useBundledIO : Bool) : String :=
  let moduleName := c.name
  let isSeq := c.hasSequentialElements

  -- Port initialization (only for bundled I/O)
  let portInit := if useBundledIO then
    [s!"    : inputs(\"inputs\", {c.inputs.length}), outputs(\"outputs\", {c.outputs.length})"]
  else
    []

  -- Process registration
  let clocks := findClockWires c
  let clockName := if !clocks.isEmpty then clocks.head!.name else "clock"

  let processReg := if isSeq then
    [
      "    SC_METHOD(comb_logic);",
      generateSensitivityList c useBundledIO,
      s!"    SC_CTHREAD(seq_logic, {clockName}.pos());",
      "    reset_signal_is(reset, true);"
    ]
  else
    [
      "    SC_METHOD(comb_logic);",
      generateSensitivityList c useBundledIO
    ]

  let ctorStart := if !portInit.isEmpty then
    [s!"  SC_CTOR({moduleName})"] ++ portInit ++ ["  {"]
  else
    [s!"  SC_CTOR({moduleName}) " ++ "{"]

  joinLines (ctorStart ++ processReg ++ ["  }"])

-- Generate a single combinational gate assignment (for .cpp file)
def generateCombGateSystemC (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (g : Gate) : String :=
  let op := gateTypeToOperator g.gateType
  let outRef := wireRef inputToIndex outputToIndex g.output

  match g.gateType with
  | GateType.NOT =>
      match g.inputs with
      | [i0] =>
          let i0Ref := wireRef inputToIndex outputToIndex i0
          s!"  {outRef}.write(~{i0Ref}.read());"
      | _ => "  // ERROR: NOT gate should have 1 input"
  | GateType.BUF =>
      match g.inputs with
      | [i0] =>
          let i0Ref := wireRef inputToIndex outputToIndex i0
          s!"  {outRef}.write({i0Ref}.read());"
      | _ => "  // ERROR: BUF gate should have 1 input"
  | GateType.MUX =>
      -- Ternary operator: sel ? in1 : in0
      -- inputs: [in0, in1, sel]
      match g.inputs with
      | [in0, in1, sel] =>
          let in0Ref := wireRef inputToIndex outputToIndex in0
          let in1Ref := wireRef inputToIndex outputToIndex in1
          let selRef := wireRef inputToIndex outputToIndex sel
          s!"  {outRef}.write({selRef}.read() ? {in1Ref}.read() : {in0Ref}.read());"
      | _ => "  // ERROR: MUX gate should have 3 inputs: [in0, in1, sel]"
  | GateType.DFF =>
      ""  -- DFFs handled in seq_logic, not comb_logic
  | _ =>
      -- Binary operators: input1 op input2
      match g.inputs with
      | [i0, i1] =>
          let i0Ref := wireRef inputToIndex outputToIndex i0
          let i1Ref := wireRef inputToIndex outputToIndex i1
          s!"  {outRef}.write({i0Ref}.read() {op} {i1Ref}.read());"
      | _ => "  // ERROR: Binary gate should have 2 inputs"

-- Generate DFF logic for SC_CTHREAD
def generateDFFSystemC (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (g : Gate) : String :=
  match g.inputs with
  | [d, _clk, reset] =>
      let dRef := wireRef inputToIndex outputToIndex d
      let resetRef := wireRef inputToIndex outputToIndex reset
      let qRef := wireRef inputToIndex outputToIndex g.output
      joinLines [
        s!"    if ({resetRef}.read()) " ++ "{",
        s!"      {qRef}.write(false);",
        "    } else {",
        s!"      {qRef}.write({dRef}.read());",
        "    }"
      ]
  | _ => "    // ERROR: DFF should have 3 inputs: [d, clk, reset]"

-- Generate comb_logic method body
def generateCombMethod (c : Circuit) (useBundledIO : Bool) : String :=
  let inputToIndex := if useBundledIO then c.inputs.enum.map (fun ⟨idx, w⟩ => (w, idx)) else []
  let outputToIndex := if useBundledIO then c.outputs.enum.map (fun ⟨idx, w⟩ => (w, idx)) else []

  let combGates := c.gates.filter (fun g => g.gateType.isCombinational)
  let assignments := combGates.map (fun g => generateCombGateSystemC inputToIndex outputToIndex g)

  joinLines [
    s!"void {c.name}::comb_logic() " ++ "{",
    joinLines assignments,
    "}"
  ]

-- Generate seq_logic method body (for sequential circuits)
def generateSeqMethod (c : Circuit) (useBundledIO : Bool) : String :=
  let inputToIndex := if useBundledIO then c.inputs.enum.map (fun ⟨idx, w⟩ => (w, idx)) else []
  let outputToIndex := if useBundledIO then c.outputs.enum.map (fun ⟨idx, w⟩ => (w, idx)) else []

  let dffGates := c.gates.filter (fun g => g.gateType == GateType.DFF)
  let dffLogic := dffGates.map (fun g => generateDFFSystemC inputToIndex outputToIndex g)

  joinLines [
    s!"void {c.name}::seq_logic() " ++ "{",
    "  while (true) {",
    "    wait();  // Wait for clock edge",
    joinLines dffLogic,
    "  }",
    "}"
  ]

-- Main function: Generate SystemC header file (.h)
def toSystemCHeader (c : Circuit) : String :=
  let moduleName := c.name
  let guardName := moduleName.toUpper ++ "_H"
  let isSeq := c.hasSequentialElements
  let useBundledIO := (c.inputs.length + c.outputs.length) > 500

  -- Port declarations
  let portDecls := generatePortDeclarations c useBundledIO

  -- Signal declarations
  let signalDecls := generateSignalDeclarations c

  -- Process method declarations
  let processDecls := if isSeq then
    joinLines [
      "  void comb_logic();",
      "  void seq_logic();"
    ]
  else
    "  void comb_logic();"

  -- Constructor
  let ctor := generateConstructor c useBundledIO

  joinLines [
    s!"#ifndef {guardName}",
    s!"#define {guardName}",
    "",
    "#include <systemc.h>",
    "",
    s!"SC_MODULE({moduleName}) " ++ "{",
    "  // Ports",
    portDecls,
    "",
    "  // Internal signals",
    signalDecls,
    "",
    "  // Process methods",
    processDecls,
    "",
    "  // Constructor",
    ctor,
    "};",
    "",
    s!"#endif // {guardName}"
  ]

-- Main function: Generate SystemC implementation file (.cpp)
def toSystemCImpl (c : Circuit) : String :=
  let moduleName := c.name
  let isSeq := c.hasSequentialElements
  let useBundledIO := (c.inputs.length + c.outputs.length) > 500

  let combMethod := generateCombMethod c useBundledIO
  let seqMethod := if isSeq then generateSeqMethod c useBundledIO else ""

  let parts := [
    s!"#include \"{moduleName}.h\"",
    "",
    combMethod
  ]

  let partsWithSeq := if isSeq then
    parts ++ ["", seqMethod]
  else
    parts

  joinLines partsWithSeq

end Shoumei.Codegen.SystemC
