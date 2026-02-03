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

/-! ## Helper Functions for Wire Name Parsing -/

-- Helper: Verilog/SystemVerilog reserved keywords (must not be used as identifiers)
def verilogKeywords : List String :=
  ["and", "or", "xor", "not", "nand", "nor", "xnor", "buf", "bufif0", "bufif1",
   "module", "endmodule", "input", "output", "inout", "wire", "reg", "assign",
   "always", "if", "else", "case", "casez", "casex", "default", "for", "while",
   "repeat", "begin", "end", "posedge", "negedge", "initial", "parameter",
   "localparam", "generate", "genvar", "task", "function", "return"]

-- Helper: check if a name is a Verilog keyword
def isVerilogKeyword (name : String) : Bool :=
  verilogKeywords.contains name

-- Helper: check if string ends with a digit
def endsWithDigit (s : String) : Bool :=
  match s.toList.reverse.head? with
  | some c => c.isDigit
  | none => false

-- Helper: extract numeric suffix from wire name (e.g., "opcode3" → "3")
def extractNumericSuffix (name : String) : String :=
  let chars := name.toList.reverse
  let digits := chars.takeWhile Char.isDigit
  String.ofList digits.reverse

-- Helper: extract basename and index from wire name ending in digits
-- E.g., "write_data_0" → ("write_data", 0), "opcode5" → ("opcode", 5), "e01" → none (not a bus)
-- Heuristic: only treat as bus if basename ends with underscore OR is substantial (3+ chars)
-- This avoids treating "e01" as "e[1]" (should stay as standalone wire "e01")
-- Also avoids Verilog keywords like "and", "or", "xor"
def splitWireName (w : Wire) : Option (String × Nat) :=
  let name := w.name
  if !endsWithDigit name then none
  else
    let suffix : String := extractNumericSuffix name
    match suffix.toNat? with
    | some idx =>
        let basenameWithSep := (name.dropEnd suffix.length).toString
        -- Strip trailing underscore if present (write_data_0 → write_data, not write_data_)
        let basename := if basenameWithSep.endsWith "_" then
          (basenameWithSep.dropEnd 1).toString
        else
          basenameWithSep

        -- Reject if basename is a Verilog keyword
        if isVerilogKeyword basename then
          none
        -- Only treat as bus if:
        -- 1. Original basename ended with underscore (clear separator: "data_5" → "data[5]")
        -- 2. Basename is substantial (3+ chars) AND suffix is short (1-2 digits)
        --    This handles "opcode5" → "opcode[5]" but NOT "e01" → "e[1]"
        else if basenameWithSep.endsWith "_" then
          some (basename, idx)
        else if basename.length >= 3 && suffix.length <= 2 then
          some (basename, idx)
        else
          none
    | none => none

/-! ## Main Code Generation Functions -/

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

-- Helper: Get wire reference (handles flattened I/O with underscore indexing and bus indexing)
-- Takes circuit for checking if wire is an input/output (to avoid bus grouping on ports)
def wireRef (c : Circuit) (busWires : List Wire) (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (w : Wire) : String :=
  match inputToIndex.find? (fun p => p.fst.name == w.name) with
  | some (_wire, idx) => s!"inputs_{idx}"
  | none =>
      match outputToIndex.find? (fun p => p.fst.name == w.name) with
      | some (_wire, idx) => s!"outputs_{idx}"
      | none =>
          -- Don't apply bus grouping to input/output wires (they're individual ports)
          if c.inputs.contains w || c.outputs.contains w then
            w.name
          else
            -- Check if this wire is part of a declared bus
            if busWires.contains w then
              match splitWireName w with
              | some (basename, idx) => s!"{basename}[{idx}]"
              | none => w.name
            else
              w.name

-- Generate a single combinational gate assignment
-- Note: DFFs are handled separately in generateAlwaysBlocks
def generateCombGate (c : Circuit) (busWires : List Wire) (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (g : Gate) : String :=
  let op := gateTypeToOperator g.gateType
  let outRef := wireRef c busWires inputToIndex outputToIndex g.output
  match g.gateType with
  | GateType.NOT =>
      -- Unary operator: ~input
      match g.inputs with
      | [i0] => s!"  assign {outRef} = {op}{wireRef c busWires inputToIndex outputToIndex i0};"
      | _ => s!"  // ERROR: NOT gate should have 1 input"
  | GateType.BUF =>
      -- Buffer: direct assignment
      match g.inputs with
      | [i0] => s!"  assign {outRef} = {wireRef c busWires inputToIndex outputToIndex i0};"
      | _ => s!"  // ERROR: BUF gate should have 1 input"
  | GateType.MUX =>
      -- Ternary operator: sel ? in1 : in0
      -- inputs: [in0, in1, sel]
      match g.inputs with
      | [in0, in1, sel] =>
          let in0Ref := wireRef c busWires inputToIndex outputToIndex in0
          let in1Ref := wireRef c busWires inputToIndex outputToIndex in1
          let selRef := wireRef c busWires inputToIndex outputToIndex sel
          s!"  assign {outRef} = {selRef} ? {in1Ref} : {in0Ref};"
      | _ => s!"  // ERROR: MUX gate should have 3 inputs: [in0, in1, sel]"
  | GateType.DFF =>
      ""  -- DFFs handled in always blocks, not assign statements
  | _ =>
      -- Binary operators: input1 op input2
      match g.inputs with
      | [i0, i1] =>
          let i0Ref := wireRef c busWires inputToIndex outputToIndex i0
          let i1Ref := wireRef c busWires inputToIndex outputToIndex i1
          s!"  assign {outRef} = {i0Ref} {op} {i1Ref};"
      | _ => s!"  // ERROR: Binary gate should have 2 inputs"

-- Generate always block for a D Flip-Flop
-- DFF inputs: [d, clk, reset], output: q
def generateDFF (c : Circuit) (busWires : List Wire) (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (g : Gate) : String :=
  match g.inputs with
  | [d, clk, reset] =>
      let dRef := wireRef c busWires inputToIndex outputToIndex d
      let clkRef := wireRef c busWires inputToIndex outputToIndex clk
      let resetRef := wireRef c busWires inputToIndex outputToIndex reset
      let qRef := wireRef c busWires inputToIndex outputToIndex g.output
      joinLines [
        s!"  always @(posedge {clkRef} or posedge {resetRef}) begin",
        s!"    if ({resetRef})",
        s!"      {qRef} <= 1'b0;",
        s!"    else",
        s!"      {qRef} <= {dRef};",
        s!"  end"
      ]
  | _ => s!"  // ERROR: DFF should have 3 inputs: [d, clk, reset]"

-- Helper: find all internal wires (gate outputs + instance wires that are not circuit I/O)
def findInternalWires (c : Circuit) : List Wire :=
  let gateOutputs := c.gates.map (fun g => g.output)
  let instanceWires := c.instances.flatMap (fun inst => inst.portMap.map (·.snd))
  let allWires := gateOutputs ++ instanceWires
  -- Filter out circuit inputs and outputs, and remove duplicates
  let internalWires := allWires.filter (fun w => !c.outputs.contains w && !c.inputs.contains w)
  internalWires.eraseDups

-- Helper: find all DFF output wires (need to be declared as reg, not wire)
def findDFFOutputs (c : Circuit) : List Wire :=
  c.gates.filter (fun g => g.gateType == GateType.DFF) |>.map (fun g => g.output)

-- Helper: group wires into buses by basename
-- Returns: list of (basename, list of (index, wire)) for buses, and list of standalone wires
structure WireGroups where
  buses : List (String × List (Nat × Wire))
  standalone : List Wire

def groupWiresByBasename (wires : List Wire) : WireGroups :=
  -- First, split wires into those with numeric suffixes and standalone
  let (indexed, standalone) := wires.foldl (fun (acc1, acc2) w =>
    match splitWireName w with
    | some (base, idx) => ((base, idx, w) :: acc1, acc2)
    | none => (acc1, w :: acc2)
  ) ([], [])

  -- Group by basename
  let grouped := indexed.foldl (fun acc (base, idx, w) =>
    match acc.find? (fun p => p.fst == base) with
    | some (_, existingList) =>
        acc.erase (base, existingList) |>.cons (base, (idx, w) :: existingList)
    | none =>
        (base, [(idx, w)]) :: acc
  ) []

  -- Only treat as bus if there are 2+ wires with same basename (heuristic)
  let (realBuses, moreStandalone) := grouped.foldl (fun (buses, standalone) (base, wires) =>
    if wires.length >= 2 then
      ((base, wires) :: buses, standalone)
    else
      (buses, standalone ++ wires.map (·.snd))
  ) ([], standalone)

  { buses := realBuses, standalone := moreStandalone }

-- Helper: generate bus declaration (wire or reg)
def generateBusDecl (basename : String) (indices : List (Nat × Wire)) (isReg : Bool) : String :=
  let sorted := indices.toArray.qsort (fun a b => a.fst < b.fst) |>.toList
  let maxIdx := sorted.reverse.head!.fst
  let wireType := if isReg then "reg" else "wire"
  s!"  {wireType} [{maxIdx}:0] {basename};"

-- Helper: get list of wires that are part of declared buses (for wireRef)
def getBusWires (c : Circuit) : List Wire :=
  let internalWires := findInternalWires c
  let groups := groupWiresByBasename internalWires
  groups.buses.flatMap (fun (_, wires) => wires.map (·.snd))

-- Generate all internal wire declarations with bus grouping
-- DFF outputs are declared as 'reg', other internal wires as 'wire'
def generateWireDeclarations (c : Circuit) : String :=
  let internalWires := findInternalWires c
  let dffOutputs := findDFFOutputs c
  if internalWires.isEmpty then
    ""
  else
    let groups := groupWiresByBasename internalWires

    -- Generate bus declarations
    let busDecls := groups.buses.map (fun (basename, wires) =>
      -- Check if any wire in the bus is a DFF output
      let isReg := wires.any (fun (_, w) => dffOutputs.contains w)
      generateBusDecl basename wires isReg
    )

    -- Generate standalone wire declarations
    let standaloneDecls := groups.standalone.map (fun w =>
      if dffOutputs.contains w then
        s!"  reg {w.name};"
      else
        s!"  wire {w.name};"
    )

    joinLines (busDecls ++ standaloneDecls)

-- Generate all combinational gate assignments (DFFs handled separately)
def generateCombAssignments (c : Circuit) (busWires : List Wire) (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) : String :=
  let combGates := c.gates.filter (fun g => g.gateType.isCombinational)
  let assignments := combGates.map (generateCombGate c busWires inputToIndex outputToIndex)
  joinLines assignments

-- Generate all always blocks for sequential elements (DFFs)
def generateAlwaysBlocks (c : Circuit) (busWires : List Wire) (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) : String :=
  let dffGates := c.gates.filter (fun g => g.gateType == GateType.DFF)
  let blocks := dffGates.map (generateDFF c busWires inputToIndex outputToIndex)
  joinLines blocks


-- Generate submodule instantiation
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
-- Rules match Chisel codegen for consistency:
-- 1. "inputs[123]" or similar bundled IO → keep underscores for array-like naming
-- 2. Named ports like "alloc_physRd[0]" → strip brackets to "alloc_physRd0" (no underscore)
-- E.g., portBase="inputs[123]" → "inputs_123" (bundled IO uses underscores)
--       portBase="alloc_physRd[0]" → "alloc_physRd0" (named ports concatenate directly)
--       portBase="op", wireName="opcode3" → "op3"
def constructPortRef (portBase : String) (wireName : String) : String :=
  -- If it has brackets, handle based on context
  if portBase.contains '[' then
    -- For all indexed ports, convert brackets to underscores to match makeIndexedWires naming
    -- E.g., "head_archRd[4]" → "head_archRd_4", "inputs[0]" → "inputs_0"
    portBase.replace "[" "_" |>.replace "]" ""
  -- If it already ends with a digit, it's complete
  else if endsWithDigit portBase then
    portBase
  else
    -- Construct from base + wire index ONLY if wire name suggests indexing
    -- E.g., portBase="tag_out", wireName="tag_out_0" → "tag_out_0"
    --       portBase="eq", wireName="e0_cdb_match_src1" → "eq" (don't append "1")
    let suffix := extractNumericSuffix wireName
    if suffix.isEmpty then
      portBase
    else
      -- Only append suffix if wireName starts with or contains portBase
      -- This handles cases like: portBase="a", wireName="a_0" or "entry0_a_0"
      if wireName.startsWith portBase || wireName.contains ("_" ++ portBase) then
        portBase ++ "_" ++ suffix  -- Add underscore separator to match makeIndexedWires
      else
        portBase

-- Check if a module name corresponds to a module with bundled IO (>200 ports)
-- This is a heuristic based on known module sizes
private def moduleUsesBundledIO (moduleName : String) : Bool :=
  -- Modules known to use bundled IO (>200 total ports)
  moduleName == "StoreBuffer8" || moduleName == "MemoryExecUnit" ||
  moduleName == "LSU" || moduleName == "ROB16" ||
  moduleName == "ReservationStation4" || moduleName == "MulDivRS4" ||
  moduleName == "PhysRegFile_64x32" || moduleName == "RAT_32x6" ||
  moduleName == "FreeList_64"

-- Map port names with underscores to bundled IO Vec indices for SystemVerilog
-- SystemVerilog uses flat naming: inputs_0, inputs_1, outputs_0, etc.
private def mapPortNameToSVBundle (moduleName portName : String) : Option String :=
  -- For StoreBuffer8: map port names to inputs_N/outputs_N
  if moduleName == "StoreBuffer8" then
    -- StoreBuffer8 inputs order (excluding clock which is explicit):
    -- 0: reset, 1: zero, 2: one, 3: enq_en, 4-35: enq_address, 36-67: enq_data,
    -- 68-69: enq_size, 70: commit_en, 71-73: commit_idx, 74: deq_ready,
    -- 75-106: fwd_address, 107: flush_en
    if portName == "reset" then some "inputs_0"
    else if portName == "zero" then some "inputs_1"
    else if portName == "one" then some "inputs_2"
    else if portName == "enq_en" then some "inputs_3"
    else if portName == "commit_en" then some "inputs_70"
    else if portName == "deq_ready" then some "inputs_74"
    else if portName == "flush_en" then some "inputs_107"
    else if portName.startsWith "enq_address_" then
      portName.drop 12 |>.toNat? |>.map (fun i => s!"inputs_{4 + i}")
    else if portName.startsWith "enq_data_" then
      portName.drop 9 |>.toNat? |>.map (fun i => s!"inputs_{36 + i}")
    else if portName.startsWith "enq_size_" then
      portName.drop 9 |>.toNat? |>.map (fun i => s!"inputs_{68 + i}")
    else if portName.startsWith "commit_idx_" then
      portName.drop 11 |>.toNat? |>.map (fun i => s!"inputs_{71 + i}")
    else if portName.startsWith "fwd_address_" then
      portName.drop 12 |>.toNat? |>.map (fun i => s!"inputs_{75 + i}")
    -- Outputs: 0: full, 1: empty, 2-4: enq_idx, 5: deq_valid, 6-71: deq_bits, 72: fwd_hit, 73-104: fwd_data
    else if portName == "full" then some "outputs_0"
    else if portName == "empty" then some "outputs_1"
    else if portName == "deq_valid" then some "outputs_5"
    else if portName == "fwd_hit" then some "outputs_72"
    else if portName.startsWith "enq_idx_" then
      portName.drop 8 |>.toNat? |>.map (fun i => s!"outputs_{2 + i}")
    else if portName.startsWith "deq_bits_" then
      portName.drop 9 |>.toNat? |>.map (fun i => s!"outputs_{6 + i}")
    else if portName.startsWith "fwd_data_" then
      portName.drop 9 |>.toNat? |>.map (fun i => s!"outputs_{73 + i}")
    else none
  else none

def generateInstance (c : Circuit) (busWires : List Wire) (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (inst : CircuitInstance) : String :=
  let childUsesBundledIO := moduleUsesBundledIO inst.moduleName
  let portConnections := inst.portMap.map (fun (portBaseName, wire) =>
    let wRef := wireRef c busWires inputToIndex outputToIndex wire
    -- If child uses bundled IO, map port names to flat bundle indices
    let portRef :=
      if childUsesBundledIO then
        match mapPortNameToSVBundle inst.moduleName portBaseName with
        | some bundleRef => bundleRef
        | none => constructPortRef portBaseName wire.name
      else constructPortRef portBaseName wire.name
    s!".{portRef}({wRef})"
  )
  let portsStr := String.intercalate ",\n    " portConnections
  s!"  {inst.moduleName} {inst.instName} (\n    {portsStr}\n  );"

-- Generate all submodule instances
def generateInstances (c : Circuit) (busWires : List Wire) (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) : String :=
  let instances := c.instances.map (generateInstance c busWires inputToIndex outputToIndex)
  joinLines instances

-- Main code generator: Circuit → SystemVerilog module
-- Supports both combinational and sequential circuits
-- Uses bundled I/O (input/output vectors) for large circuits (>500 I/O ports)
def toSystemVerilog (c : Circuit) : String :=
  let moduleName := c.name
  let dffOutputs := findDFFOutputs c

  -- Check if we should use bundled I/O (for large circuits)
  let (inputToIndex, outputToIndex, useBundledIO, filteredInputs) :=
    -- Find clock/reset from both DFF gates AND instance connections
    let clockWires := findClockWires c
    let resetWires := findResetWires c
    let implicitWires := (clockWires ++ resetWires).eraseDups
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
  let busWires := getBusWires c
  let wireDecls := generateWireDeclarations c
  let combAssigns := generateCombAssignments c busWires inputToIndex outputToIndex
  let alwaysBlocks := generateAlwaysBlocks c busWires inputToIndex outputToIndex
  let instanceBlocks := generateInstances c busWires inputToIndex outputToIndex

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
