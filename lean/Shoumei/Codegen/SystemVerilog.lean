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
        s!"  always @(posedge {clkRef} or posedge {resetRef}) begin",
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


-- Generate submodule instantiation
-- Helper: extract numeric suffix from wire name (e.g., "opcode3" → "3")
def extractNumericSuffix (name : String) : String :=
  let chars := name.toList.reverse
  let digits := chars.takeWhile Char.isDigit
  String.ofList digits.reverse

-- Helper: check if string ends with a digit
def endsWithDigit (s : String) : Bool :=
  match s.toList.reverse.head? with
  | some c => c.isDigit
  | none => false

-- Helper: parse bracket notation like "inputs[123]" → ("inputs", 123)
def parseBracketNotation (s : String) : Option (String × Nat) :=
  if !s.contains '[' then none
  else
    let parts := s.splitOn "["
    match parts with
    | [base, rest] =>
        let numStr : String := (rest.takeWhile (· != ']')).toString
        match numStr.toNat? with
        | some n => some (base, n)
        | none => none
    | _ => none

-- Helper: infer structured port name from module name and flat index
-- E.g., Mux64x32 with inputs[0] → in0_b0, inputs[32] → in1_b0, inputs[2048] → sel0
def inferStructuredPortName (moduleName : String) (baseName : String) (flatIndex : Nat) : Option String :=
  -- Parse module name like "Mux64x32" → (64 entries, 32 bits each)
  if moduleName.startsWith "Mux" then
    let rest := (moduleName.drop 3).toString  -- Remove "Mux"
    let parts := rest.splitOn "x"
    match parts with
    | [numEntriesStr, widthStr] =>
        match (numEntriesStr : String).toNat?, (widthStr : String).toNat? with
        | some numEntries, some width =>
            if baseName == "inputs" then
              let totalDataInputs := numEntries * width
              if flatIndex < totalDataInputs then
                -- Data input: in{entry}_b{bit}
                let entryIdx := flatIndex / width
                let bitIdx := flatIndex % width
                some s!"in{entryIdx}_b{bitIdx}"
              else
                -- Select input: sel{n}
                let selIdx := flatIndex - totalDataInputs
                some s!"sel{selIdx}"
            else if baseName == "outputs" then
              some s!"out{flatIndex}"
            else
              none
        | _, _ => none
    | _ => none
  else
    none

-- Helper: construct port reference from port base name and wire name
-- Simple rule: brackets → underscores, done. No complex translation needed.
-- E.g., portBase="inputs[123]" → "inputs_123"
--       portBase="op", wireName="opcode3" → "op3"
def constructPortRef (portBase : String) (wireName : String) : String :=
  -- If it has brackets, convert to SystemVerilog style (bundled IO)
  if portBase.contains '[' then
    portBase.replace "[" "_" |>.replace "]" ""
  -- If it already ends with a digit, it's complete
  else if endsWithDigit portBase then
    portBase
  else
    -- Construct from base + wire index ONLY if wire name suggests indexing
    -- E.g., portBase="a", wireName="a0" → "a0" (correct)
    --       portBase="eq", wireName="e0_cdb_match_src1" → "eq" (don't append "1")
    let suffix := extractNumericSuffix wireName
    if suffix.isEmpty then
      portBase
    else
      -- Only append suffix if wireName starts with or contains portBase
      -- This handles cases like: portBase="a", wireName="a0" or "entry0_a0"
      if wireName.startsWith portBase || wireName.contains ("_" ++ portBase) then
        portBase ++ suffix
      else
        portBase

def generateInstance (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (inst : CircuitInstance) : String :=
  let portConnections := inst.portMap.map (fun (portBaseName, wire) =>
    let wRef := wireRef inputToIndex outputToIndex wire
    let portRef := constructPortRef portBaseName wire.name
    s!".{portRef}({wRef})"
  )
  let portsStr := String.intercalate ",\n    " portConnections
  s!"  {inst.moduleName} {inst.instName} (\n    {portsStr}\n  );"

-- Generate all submodule instances
def generateInstances (c : Circuit) (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) : String :=
  let instances := c.instances.map (generateInstance inputToIndex outputToIndex)
  joinLines instances

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
    let useBundle := totalPorts > 200  -- Use bundled IO for very large modules to avoid excessive ports
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
  let instanceBlocks := generateInstances c inputToIndex outputToIndex

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
    instanceBlocks,
    "",
    "endmodule"
  ]

-- TODO: Prove correctness theorem
-- theorem toSystemVerilog_correct (c : Circuit) :
--   ⟦ toSystemVerilog c ⟧ = evalCircuit c := by
--   sorry

end Shoumei.Codegen.SystemVerilog
