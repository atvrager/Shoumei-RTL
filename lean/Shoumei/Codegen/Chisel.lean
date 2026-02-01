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

-- Context for wire mapping in large circuits
structure ChiselContext where
  wireToIndex : List (Wire × Nat)
  inputToIndex : List (Wire × Nat)
  outputToIndex : List (Wire × Nat)
  regToIndex : List (Wire × Nat)
  useWireArray : Bool
  useIOBundle : Bool
  useRegArray : Bool

-- Helper: generate wire reference using context
def wireRef (ctx : ChiselContext) (w : Wire) : String :=
  -- Check if it's a register (using reg array)
  let isRegArray := match ctx.regToIndex.find? (fun p => p.fst.name == w.name) with
    | some (_reg, idx) => if ctx.useRegArray then some idx else none
    | none => none
  
  match isRegArray with
  | some idx => s!"_regs({idx})"
  | none =>
    -- Check if it's an IO port (if using bundle)
    if ctx.useIOBundle then
      match ctx.inputToIndex.find? (fun p => p.fst.name == w.name) with
      | some (_wire, idx) => s!"inputs({idx})"
      | none =>
          match ctx.outputToIndex.find? (fun p => p.fst.name == w.name) with
          | some (_wire, idx) => s!"outputs({idx})"
          | none =>
              -- If not IO, check if it's a wire in the wire array
              if ctx.useWireArray then
                match ctx.wireToIndex.find? (fun p => p.fst.name == w.name) with
                | some (_wire, idx) => s!"_wires({idx})"
                | none => w.name
              else
                w.name
    else
      -- Not using IO bundle, check wire array
      if ctx.useWireArray then
        match ctx.wireToIndex.find? (fun p => p.fst.name == w.name) with
        | some (_wire, idx) => s!"_wires({idx})"
        | none => w.name
      else
        w.name

-- Generate a single combinational gate assignment
def generateCombGate (ctx : ChiselContext) (g : Gate) : String :=
  let op := gateTypeToOperator g.gateType
  let outRef := wireRef ctx g.output
  match g.gateType with
  | GateType.NOT =>
      match g.inputs with
      | [i0] => s!"  {outRef} := {op}{wireRef ctx i0}"
      | _ => s!"  // ERROR: NOT gate should have 1 input"
  | GateType.BUF =>
      match g.inputs with
      | [i0] => s!"  {outRef} := {wireRef ctx i0}"
      | _ => s!"  // ERROR: BUF gate should have 1 input"
  | GateType.MUX =>
      match g.inputs with
      | [in0, in1, sel] => s!"  {outRef} := Mux({wireRef ctx sel}, {wireRef ctx in1}, {wireRef ctx in0})"
      | _ => s!"  // ERROR: MUX gate should have 3 inputs: [in0, in1, sel]"
  | GateType.DFF => ""
  | _ =>
      match g.inputs with
      | [i0, i1] => s!"  {outRef} := {wireRef ctx i0} {op} {wireRef ctx i1}"
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
def generateDFF (ctx : ChiselContext) (c : Circuit) (g : Gate) : String :=
  match g.inputs with
  | [d, _clk, reset] =>
      let isOutput := c.outputs.contains g.output
      let regRef := wireRef ctx g.output
      let dRef := wireRef ctx d
      let allResetWires := findResetWires c
      let resetRef := if allResetWires.contains reset then "reset.asBool" else wireRef ctx reset
      
      -- Use Mux instead of when/otherwise to keep method size small
      let updateLogic := s!"  {regRef} := Mux({resetRef}, false.B, {dRef})"
      
      -- For registers in array, we don't need _reg suffix or extra connection
      -- unless it's a circuit output and NOT in the reg array (which shouldn't happen now)
      if isOutput && !ctx.useRegArray then
        let regName := g.output.name ++ "_reg"
        let outRefTarget := wireRef ctx g.output
        joinLines [
          s!"  {regName} := Mux({resetRef}, false.B, {dRef})",
          s!"  {outRefTarget} := {regName}"
        ]
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
def generateIOBundle (c : Circuit) (isSequential : Bool) (ctx : ChiselContext) : String :=
  let clockWires := if isSequential then findClockWires c else []
  let resetWires := if isSequential then findResetWires c else []
  let implicitWires := clockWires ++ resetWires
  let filteredInputs := c.inputs.filter (fun w => !implicitWires.contains w)

  if ctx.useIOBundle then
    let inputDecl := s!"  val inputs = IO(Input(Vec({filteredInputs.length}, Bool())))"
    let outputDecl := s!"  val outputs = IO(Output(Vec({c.outputs.length}, Bool())))"
    inputDecl ++ "\n" ++ outputDecl
  else
    let inputDecls := filteredInputs.map (fun w => s!"  val {w.name} = IO(Input(Bool()))")
    let outputDecls := c.outputs.map (fun w => s!"  val {w.name} = IO(Output(Bool()))")
    joinLines (inputDecls ++ outputDecls)

-- Generate combinational logic (wire declarations + assignments for comb gates)
def generateCombLogic (ctx : ChiselContext) (c : Circuit) : String :=
  let internalWires := findInternalWires c
  let dffOutputs := findDFFOutputs c
  -- Only declare wires for non-DFF outputs (DFFs use RegInit)
  let wireDecls := internalWires.filter (fun w => !dffOutputs.contains w) |>.map (fun w => s!"  val {w.name} = Wire(Bool())")

  -- Combinational gate assignments
  let combGates := c.gates.filter (fun g => g.gateType.isCombinational)
  let assignments := combGates.map (generateCombGate ctx)

  -- Combine with blank line separator if we have both
  if wireDecls.isEmpty then
    joinLines assignments
  else if assignments.isEmpty then
    joinLines wireDecls
  else
    joinLines wireDecls ++ "\n\n" ++ joinLines assignments

-- Generate register declarations only (no update logic)
def generateRegDecls (c : Circuit) (ctx : ChiselContext) : String :=
  let dffGates := c.gates.filter (fun g => g.gateType == GateType.DFF)
  if dffGates.isEmpty then ""
  else if ctx.useRegArray then
    s!"  val _regs = Reg(Vec({dffGates.length}, Bool()))"
  else
    -- Register declarations (use _reg suffix if output is a circuit output)
    let regDecls := dffGates.map (fun g =>
      let isOutput := c.outputs.contains g.output
      let regName := if isOutput then g.output.name ++ "_reg" else g.output.name
      s!"  val {regName} = RegInit(false.B)")
    joinLines regDecls

-- Generate register update logic only (no declarations)
def generateRegUpdates (ctx : ChiselContext) (c : Circuit) : String :=
  let dffGates := c.gates.filter (fun g => g.gateType == GateType.DFF)
  if dffGates.isEmpty then ""
  else joinLines (dffGates.map (generateDFF ctx c))

-- Helper: chunk a list into sublists of size n
partial def chunkList {α : Type} (xs : List α) (n : Nat) : List (List α) :=
  if n == 0 || xs.isEmpty then []
  else
    let chunk := xs.take n
    let rest := xs.drop n
    chunk :: chunkList rest n

-- Generate register update logic with chunking for large circuits
def generateRegUpdatesChunked (ctx : ChiselContext) (c : Circuit) (chunkSize : Nat := 50) : (String × String) :=
  let dffGates := c.gates.filter (fun g => g.gateType == GateType.DFF)
  if dffGates.isEmpty then ("", "")
  else if dffGates.length <= chunkSize then (generateRegUpdates ctx c, "")
  else
    let chunks := chunkList dffGates chunkSize
    let helperMethods := chunks.enum.map (fun ⟨idx, chunk⟩ =>
      let logic := chunk.map (generateDFF ctx c)
      joinLines [
        s!"  private def updateRegs{idx}(): Unit = " ++ "{",
        joinLines logic,
        "  }"
      ]
    )
    let helperCalls := List.range chunks.length |>.map (fun i => s!"  updateRegs{i}()")
    (joinLines helperCalls, joinLines helperMethods)





-- Generate combinational logic with chunking for large circuits
def generateCombLogicChunked (ctx : ChiselContext) (c : Circuit) (chunkSize : Nat := 200) : (String × String) :=
  let combGates := c.gates.filter (fun g => g.gateType.isCombinational)

  if ctx.useWireArray then
    let wireArrayDecl := s!"  val _wires = Wire(Vec({ctx.wireToIndex.length}, Bool()))"
    let gateChunks := chunkList combGates chunkSize
    let helperMethods := gateChunks.enum.map (fun ⟨idx, chunk⟩ =>
      let assignments := chunk.map (generateCombGate ctx)
      joinLines [
        s!"  private def initLogic{idx}(): Unit = " ++ "{",
        joinLines (assignments.map (fun a => "  " ++ a)),
        "  }"
      ]
    )
    let helperCalls := List.range gateChunks.length |>.map (fun i => s!"  initLogic{i}()")
    (wireArrayDecl ++ "\n\n" ++ joinLines helperCalls, joinLines helperMethods)
  else if combGates.length <= chunkSize then
    let internalWires := findInternalWires c
    let dffOutputs := findDFFOutputs c
    let wiresToDeclare := internalWires.filter (fun w => !dffOutputs.contains w)
    let wireDecls := wiresToDeclare.map (fun w => s!"  val {w.name} = Wire(Bool())")
    let assignments := combGates.map (generateCombGate ctx)
    (joinLines (wireDecls ++ [""] ++ assignments), "")
  else
    let internalWires := findInternalWires c
    let dffOutputs := findDFFOutputs c
    let wiresToDeclare := internalWires.filter (fun w => !dffOutputs.contains w)
    let wireDecls := wiresToDeclare.map (fun w => s!"  val {w.name} = Wire(Bool())")
    let gateChunks := chunkList combGates chunkSize
    let helperMethods := gateChunks.enum.map (fun ⟨idx, chunk⟩ =>
      let assignments := chunk.map (generateCombGate ctx)
      joinLines [
        s!"  private def initLogic{idx}(): Unit = " ++ "{",
        joinLines (assignments.map (fun a => "  " ++ a)),
        "  }"
      ]
    )
    let helperCalls := List.range gateChunks.length |>.map (fun i => s!"  initLogic{i}()")
    (joinLines (wireDecls ++ [""] ++ helperCalls), joinLines helperMethods)

-- Main code generator: Circuit → Chisel module
def toChisel (c : Circuit) : String :=
  let moduleName := c.name
  let isSequential := c.hasSequentialElements

  -- Setup context for large circuits
  let internalWires := findInternalWires c
  let dffOutputs := findDFFOutputs c
  let wiresToDeclare := internalWires.filter (fun w => !dffOutputs.contains w)
  let clockWires := if isSequential then findClockWires c else []
  let resetWires := if isSequential then findResetWires c else []
  let implicitWires := clockWires ++ resetWires
  let filteredInputs := c.inputs.filter (fun w => !implicitWires.contains w)
  let totalIOPorts := filteredInputs.length + c.outputs.length

  let dffGates := c.gates.filter (fun g => g.gateType == GateType.DFF)

  let ctx : ChiselContext := {
    wireToIndex := wiresToDeclare.enum.map (fun ⟨idx, wire⟩ => (wire, idx)),
    inputToIndex := filteredInputs.enum.map (fun ⟨idx, wire⟩ => (wire, idx)),
    outputToIndex := c.outputs.enum.map (fun ⟨idx, wire⟩ => (wire, idx)),
    regToIndex := dffGates.enum.map (fun ⟨idx, g⟩ => (g.output, idx)),
    useWireArray := wiresToDeclare.length > 200,
    useIOBundle := totalIOPorts > 50,
    useRegArray := dffGates.length > 50
  }

  if isSequential then
    let regDecls := generateRegDecls c ctx
    let (combMain, combHelpers) := generateCombLogicChunked ctx c 500
    let (updateMain, updateHelpers) := generateRegUpdatesChunked ctx c 500

    let parts := [regDecls, combMain, updateMain].filter (fun s => !s.isEmpty)
    let logic := String.intercalate "\n\n" parts
    let helpers := [combHelpers, updateHelpers].filter (fun s => !s.isEmpty)
    let helpersString := String.intercalate "\n\n" helpers

    joinLines [
      "package generated",
      "",
      "import chisel3._",
      "import chisel3.util._",
      "",
      "class " ++ moduleName ++ " extends Module {",
      generateIOBundle c true ctx,
      "",
      logic,
      (if helpersString.isEmpty then "" else "\n" ++ helpersString),
      "}"
    ]
  else
    let (mainLogic, helperMethods) := generateCombLogicChunked ctx c 500
    let classBody := joinLines [
      generateIOBundle c false ctx,
      "",
      mainLogic,
      if helperMethods.isEmpty then "" else "\n" ++ helperMethods
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
