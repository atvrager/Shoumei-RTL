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
  | GateType.BUF => ""     -- Buffer is direct assignment (no operator)
  | GateType.MUX => "Mux"  -- Special function call (not infix)
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
  | GateType.BUF =>
      -- Buffer: direct assignment
      match g.inputs with
      | [i0] => s!"  {outRef} := {wireRef c i0}"
      | _ => s!"  // ERROR: BUF gate should have 1 input"
  | GateType.MUX =>
      -- Mux(sel, in1, in0) - note: Chisel Mux has sel first, then true value, then false value
      match g.inputs with
      | [in0, in1, sel] => s!"  {outRef} := Mux({wireRef c sel}, {wireRef c in1}, {wireRef c in0})"
      | _ => s!"  // ERROR: MUX gate should have 3 inputs: [in0, in1, sel]"
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
-- For large circuits (>500 I/O ports), use Vec bundles to avoid JVM constructor limits
-- For RawModule: all ports declared directly
-- For Module: filter out clock and reset wires (both are implicit in Module)
def generateIOBundle (c : Circuit) (isSequential : Bool) : String :=
  let clockWires := if isSequential then findClockWires c else []
  let resetWires := if isSequential then findResetWires c else []
  let implicitWires := clockWires ++ resetWires
  -- Filter out clock and reset wires from inputs for sequential circuits
  let filteredInputs := c.inputs.filter (fun w => !implicitWires.contains w)

  let totalIOPorts := filteredInputs.length + c.outputs.length

  if totalIOPorts > 500 then
    -- Use Vec bundles for large I/O
    let inputDecl := s!"  val inputs = IO(Input(Vec({filteredInputs.length}, Bool())))"
    let outputDecl := s!"  val outputs = IO(Output(Vec({c.outputs.length}, Bool())))"
    inputDecl ++ "\n" ++ outputDecl
  else
    -- Individual port declarations for small/medium circuits
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

-- Generate register declarations only (no update logic)
def generateRegDecls (c : Circuit) : String :=
  let dffGates := c.gates.filter (fun g => g.gateType == GateType.DFF)
  if dffGates.isEmpty then
    ""
  else
    -- Register declarations (use _reg suffix if output is a circuit output)
    let regDecls := dffGates.map (fun g =>
      let isOutput := isCircuitOutput c g.output
      let regName := if isOutput then g.output.name ++ "_reg" else g.output.name
      s!"  val {regName} = RegInit(false.B)")
    joinLines regDecls

-- Generate register update logic only (no declarations)
def generateRegUpdates (c : Circuit) : String :=
  let dffGates := c.gates.filter (fun g => g.gateType == GateType.DFF)
  if dffGates.isEmpty then
    ""
  else
    let dffLogic := dffGates.map (generateDFF c)
    joinLines dffLogic

-- Helper: chunk a list into sublists of size n
partial def chunkList {α : Type} (xs : List α) (n : Nat) : List (List α) :=
  if n == 0 || xs.isEmpty then []
  else
    let chunk := xs.take n
    let rest := xs.drop n
    chunk :: chunkList rest n

-- Helper: Create wire array declaration for large circuits (avoids individual val declarations)
def generateWireArrayDecl (numWires : Nat) : String :=
  s!"  val _wires = Wire(Vec({numWires}, Bool()))"

-- Helper: Get wire reference (handles wire arrays and I/O bundles)
def wireRefIndexed (_c : Circuit) (wireToIndex : List (Wire × Nat)) (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (w : Wire) : String :=
  -- Check if it's an internal wire (in wire array)
  match wireToIndex.find? (fun p => p.fst.name == w.name) with
  | some (_wire, idx) => s!"_wires({idx})"
  | none =>
      -- Check if it's an input port
      match inputToIndex.find? (fun p => p.fst.name == w.name) with
      | some (_wire, idx) => s!"inputs({idx})"
      | none =>
          -- Check if it's an output port
          match outputToIndex.find? (fun p => p.fst.name == w.name) with
          | some (_wire, idx) => s!"outputs({idx})"
          | none => w.name  -- Direct name (for small circuits without bundling)

-- Generate combinational gate with indexed wires
def generateCombGateIndexed (c : Circuit) (wireToIndex : List (Wire × Nat)) (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (g : Gate) : String :=
  let outRef := wireRefIndexed c wireToIndex inputToIndex outputToIndex g.output
  match g.gateType with
  | GateType.AND =>
      if h : g.inputs.length >= 2 then
        let in0Ref := wireRefIndexed c wireToIndex inputToIndex outputToIndex (g.inputs.get ⟨0, by omega⟩)
        let in1Ref := wireRefIndexed c wireToIndex inputToIndex outputToIndex (g.inputs.get ⟨1, by omega⟩)
        s!"  {outRef} := {in0Ref} & {in1Ref}"
      else
        s!"  // ERROR: AND gate should have 2 inputs"
  | GateType.OR =>
      if h : g.inputs.length >= 2 then
        let in0Ref := wireRefIndexed c wireToIndex inputToIndex outputToIndex (g.inputs.get ⟨0, by omega⟩)
        let in1Ref := wireRefIndexed c wireToIndex inputToIndex outputToIndex (g.inputs.get ⟨1, by omega⟩)
        s!"  {outRef} := {in0Ref} | {in1Ref}"
      else
        s!"  // ERROR: OR gate should have 2 inputs"
  | GateType.NOT =>
      if h : g.inputs.length >= 1 then
        let inRef := wireRefIndexed c wireToIndex inputToIndex outputToIndex (g.inputs.get ⟨0, by omega⟩)
        s!"  {outRef} := ~{inRef}"
      else
        s!"  // ERROR: NOT gate should have 1 input"
  | GateType.BUF =>
      if h : g.inputs.length >= 1 then
        let inRef := wireRefIndexed c wireToIndex inputToIndex outputToIndex (g.inputs.get ⟨0, by omega⟩)
        s!"  {outRef} := {inRef}"
      else
        s!"  // ERROR: BUF gate should have 1 input"
  | GateType.XOR =>
      if h : g.inputs.length >= 2 then
        let in0Ref := wireRefIndexed c wireToIndex inputToIndex outputToIndex (g.inputs.get ⟨0, by omega⟩)
        let in1Ref := wireRefIndexed c wireToIndex inputToIndex outputToIndex (g.inputs.get ⟨1, by omega⟩)
        s!"  {outRef} := {in0Ref} ^ {in1Ref}"
      else
        s!"  // ERROR: XOR gate should have 2 inputs"
  | GateType.MUX =>
      if h : g.inputs.length >= 3 then
        let in0Ref := wireRefIndexed c wireToIndex inputToIndex outputToIndex (g.inputs.get ⟨0, by omega⟩)
        let in1Ref := wireRefIndexed c wireToIndex inputToIndex outputToIndex (g.inputs.get ⟨1, by omega⟩)
        let selRef := wireRefIndexed c wireToIndex inputToIndex outputToIndex (g.inputs.get ⟨2, by omega⟩)
        s!"  {outRef} := Mux({selRef}, {in1Ref}, {in0Ref})"
      else
        s!"  // ERROR: MUX gate should have 3 inputs: [in0, in1, sel]"
  | GateType.DFF => ""  -- DFFs handled in always blocks

-- Generate combinational logic with chunking for large circuits
-- Uses wire arrays (Vec) for circuits with >1000 internal wires to avoid JVM constructor limits
def generateCombLogicChunked (c : Circuit) (chunkSize : Nat := 200) : (String × String) :=
  let internalWires := findInternalWires c
  let dffOutputs := findDFFOutputs c
  let wiresToDeclare := internalWires.filter (fun w => !dffOutputs.contains w)

  let combGates := c.gates.filter (fun g => g.gateType.isCombinational)

  -- Use wire arrays for circuits with many wires (>1000)
  let useWireArray := wiresToDeclare.length > 1000

  if useWireArray then
    -- Very large circuit: use wire array AND I/O bundles to avoid individual val declarations
    let wireToIndex := wiresToDeclare.enum.map (fun ⟨idx, wire⟩ => (wire, idx))
    let wireArrayDecl := generateWireArrayDecl wiresToDeclare.length

    -- Also create index mappings for I/O ports (for bundled I/O)
    let totalIOPorts := c.inputs.length + c.outputs.length
    let (inputToIndex, outputToIndex) := if totalIOPorts > 500 then
      (c.inputs.enum.map (fun ⟨idx, wire⟩ => (wire, idx)),
       c.outputs.enum.map (fun ⟨idx, wire⟩ => (wire, idx)))
    else
      ([], [])  -- No bundling for small circuits

    let gateChunks := chunkList combGates chunkSize

    -- Generate helper methods for gate assignments using indexed wires
    let gateHelperMethods := gateChunks.enum.map (fun ⟨idx, chunk⟩ =>
      let assignments := chunk.map (generateCombGateIndexed c wireToIndex inputToIndex outputToIndex)
      joinLines [
        s!"  private def initLogic{idx}(): Unit = " ++ "{",
        joinLines (assignments.map (fun a => "  " ++ a)),
        "  }"
      ]
    )

    -- Generate calls to helper methods
    let gateHelperCalls := List.range gateChunks.length |>.map (fun i => s!"  initLogic{i}()")

    -- Main logic: wire array declaration + helper calls
    let mainLogic := wireArrayDecl ++ "\n\n" ++ joinLines gateHelperCalls

    -- Helper methods
    let allHelpers := joinLines gateHelperMethods

    (mainLogic, allHelpers)
  else if combGates.length <= chunkSize then
    -- Small circuit: inline everything
    let wireDecls := wiresToDeclare.map (fun w => s!"  val {w.name} = Wire(Bool())")
    let assignments := combGates.map (generateCombGate c)
    let logic := if wireDecls.isEmpty then joinLines assignments
                 else if assignments.isEmpty then joinLines wireDecls
                 else joinLines wireDecls ++ "\n\n" ++ joinLines assignments
    (logic, "")
  else
    -- Medium circuit: chunk gate assignments but use individual wire declarations
    let wireDecls := wiresToDeclare.map (fun w => s!"  val {w.name} = Wire(Bool())")
    let gateChunks := chunkList combGates chunkSize

    -- Generate helper methods for gate assignments only
    let gateHelperMethods := gateChunks.enum.map (fun ⟨idx, chunk⟩ =>
      let assignments := chunk.map (generateCombGate c)
      joinLines [
        s!"  private def initLogic{idx}(): Unit = " ++ "{",
        joinLines (assignments.map (fun a => "  " ++ a)),
        "  }"
      ]
    )

    -- Generate calls to helper methods
    let gateHelperCalls := List.range gateChunks.length |>.map (fun i => s!"  initLogic{i}()")

    -- Main logic: wire declarations + helper calls for gates
    let mainLogic := joinLines wireDecls ++ "\n\n" ++ joinLines gateHelperCalls

    -- Helper methods for gate assignments
    let allHelpers := joinLines gateHelperMethods

    (mainLogic, allHelpers)

-- Main code generator: Circuit → Chisel module
-- Uses RawModule for purely combinational circuits
-- Uses Module for sequential circuits (with implicit clock/reset)
def toChisel (c : Circuit) : String :=
  let moduleName := c.name
  let isSequential := c.hasSequentialElements

  if isSequential then
    -- Use Module for sequential circuits (implicit clock/reset)
    -- IMPORTANT: Order matters in Chisel!
    -- 1. Register declarations (val reg = RegInit(...))
    -- 2. Wire declarations + combinational logic
    -- 3. Register updates (when/otherwise blocks)
    let regDecls := generateRegDecls c
    let combLogic := generateCombLogic c
    let regUpdates := generateRegUpdates c

    let parts := [regDecls, combLogic, regUpdates].filter (fun s => !s.isEmpty)
    let logic := String.intercalate "\n\n" parts

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
    let (mainLogic, helperMethods) := generateCombLogicChunked c 25  -- Very aggressive chunking for JVM limits
    let classBody := if helperMethods.isEmpty then
      -- Small circuit: no helper methods needed
      joinLines [
        generateIOBundle c false,
        "",
        mainLogic
      ]
    else
      -- Large circuit: include helper methods
      joinLines [
        generateIOBundle c false,
        "",
        mainLogic,
        "",
        helperMethods
      ]

    joinLines [
      "package generated",
      "",
      "import chisel3._",
      "import chisel3.util._",
      "",
      "class " ++ moduleName ++ " extends RawModule {",
      classBody,
      "}"
    ]

-- TODO: Prove correctness theorem
-- theorem toChisel_correct (c : Circuit) :
--   ⟦ toChisel c ⟧ = evalCircuit c := by
--   sorry

end Shoumei.Codegen.Chisel
