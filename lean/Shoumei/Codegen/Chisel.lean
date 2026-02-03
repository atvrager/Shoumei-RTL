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
  let instanceWires := c.instances.map (fun inst => inst.portMap.map (fun (_, w) => w)) |>.flatten
  let allCandidates := (gateOutputs ++ instanceWires).eraseDups
  allCandidates.filter (fun w => !c.inputs.contains w && !c.outputs.contains w)

-- Helper: find all DFF output wires
def findDFFOutputs (c : Circuit) : List Wire :=
  c.gates.filter (fun g => g.gateType == GateType.DFF) |>.map (fun g => g.output)

-- Generate IO port declarations
-- Generate IO port declarations
def generateIOBundle (c : Circuit) (_ : Bool) (ctx : ChiselContext) : String :=
  -- Only treat clock/reset as implicit if they're actually used by DFFs in this circuit
  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let implicitWires := (clockWires ++ resetWires).eraseDups
  let filteredInputs := c.inputs.filter (fun w => !implicitWires.contains w)

  let implicitDecls := implicitWires.map (fun w =>
    if clockWires.contains w then s!"  val {w.name} = IO(Input(Clock()))"
    else s!"  val {w.name} = IO(Input(AsyncReset()))"
  )
  
  if ctx.useIOBundle then
    let inputDecl := s!"  val inputs = IO(Input(Vec({filteredInputs.length}, Bool())))"
    let outputDecl := s!"  val outputs = IO(Output(Vec({c.outputs.length}, Bool())))"
    let dontTouchDecl := s!"  dontTouch(outputs)"
    let decList := implicitDecls ++ [inputDecl, outputDecl, dontTouchDecl]
    joinLines decList
  else
    let inputDecls := filteredInputs.map (fun w => s!"  val {w.name} = IO(Input(Bool()))")
    let outputDecls := c.outputs.map (fun w => s!"  val {w.name} = IO(Output(Bool()))")
    let dontTouchDecls := c.outputs.map (fun w => s!"  dontTouch({w.name})")
    joinLines (implicitDecls ++ inputDecls ++ outputDecls ++ dontTouchDecls)

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
    s!"  val _regs = withClockAndReset(clock, reset) " ++ "{ Reg(Vec(" ++ toString dffGates.length ++ ", Bool())) }"
  else
    -- Register declarations (use _reg suffix if output is a circuit output)
    let regDecls := dffGates.map (fun g =>
      let isOutput := c.outputs.contains g.output
      let regName := if isOutput then g.output.name ++ "_reg" else g.output.name
      s!"  val {regName} = withClockAndReset(clock, reset) " ++ "{ RegInit(false.B) }")
    joinLines regDecls

-- Generate register update logic only (no declarations)
def generateRegUpdates (ctx : ChiselContext) (c : Circuit) : String :=
  let dffGates := c.gates.filter (fun g => g.gateType == GateType.DFF)
  if dffGates.isEmpty then ""
  else joinLines (dffGates.map (generateDFF ctx c))

-- Generate register output connections (for reg arrays where outputs are circuit outputs)
def generateRegOutputConnections (ctx : ChiselContext) (c : Circuit) : String :=
  if !ctx.useRegArray then ""
  else
    let dffGates := c.gates.filter (fun g => g.gateType == GateType.DFF)
    let outputConnections := dffGates.filterMap (fun g =>
      if c.outputs.contains g.output then
        match ctx.regToIndex.find? (fun p => p.fst.name == g.output.name) with
        | some (_wire, idx) => some s!"  {g.output.name} := _regs({idx})"
        | none => none
      else
        none
    )
    if outputConnections.isEmpty then ""
    else joinLines outputConnections

-- Helper: chunk a list into sublists of size n
partial def chunkList {α : Type} (xs : List α) (n : Nat) : List (List α) :=
  if n == 0 || xs.isEmpty then []
  else
    let chunk := xs.take n
    let rest := xs.drop n
    chunk :: chunkList rest n

-- Generate register update logic with chunking for large circuits
def generateRegUpdatesChunked (ctx : ChiselContext) (c : Circuit) (chunkSize : Nat := 5) : (String × String) :=
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
-- Rules:
-- 1. "inputs[123]" or "outputs[123]" → "inputs(123)" or "outputs(123)" (bundled IO array indexing)
-- 2. "alloc_physRd[0]" → "alloc_physRd0" (named ports with bracket notation)
-- 3. "a0" → "a_0" (convert old naming to new convention with underscores)
-- 4. "result19" → "result_19" (convert old naming to new convention)
def constructPortRef (portBase : String) (wireName : String) : String :=
  -- If it has brackets, handle based on whether it's bundled IO or named ports
  if portBase.contains '[' then
    -- Bundled IO uses inputs[N] or outputs[N] - convert to array indexing
    if portBase.startsWith "inputs[" || portBase.startsWith "outputs[" then
      portBase.replace "[" "(" |>.replace "]" ")"
    -- Named ports like alloc_physRd[0] - convert to alloc_physRd_0 (add underscore)
    else
      portBase.replace "[" "_" |>.replace "]" ""
  -- Special case: MuxTree bit notation pattern "xxx_bN" should stay as-is
  -- E.g., "in1_b16" should NOT become "in1_b_16"
  -- Check if it matches the pattern: contains "_b" and the part after "_b" is all digits
  else if portBase.contains "_b" && endsWithDigit portBase then
    let parts := portBase.splitOn "_b"
    -- If split produces exactly 2 parts and the second part is all digits, it's a _bN pattern
    if parts.length == 2 then
      let suffix := parts.getLast!
      if suffix.all Char.isDigit && !suffix.isEmpty then
        portBase  -- It's a valid _bN pattern, keep as-is
      else
        -- Not a valid _bN pattern, fall through to normal digit handling
        let suffix := extractNumericSuffix portBase
        let base := (portBase.dropEnd suffix.length).toString
        if suffix.isEmpty then portBase
        else if base.endsWith "_" then portBase
        else s!"{base}_{suffix}"
    else
      -- Not a _bN pattern, fall through to normal digit handling
      let suffix := extractNumericSuffix portBase
      let base := (portBase.dropEnd suffix.length).toString
      if suffix.isEmpty then portBase
      else if base.endsWith "_" then portBase
      else s!"{base}_{suffix}"
  -- If portBase ends with digits, split into base + index and add underscore if needed
  -- E.g., "a0" → "a_0", "result19" → "result_19", "const_0" → "const_0" (already has underscore)
  else if endsWithDigit portBase then
    let suffix := extractNumericSuffix portBase
    let base := (portBase.dropEnd suffix.length).toString
    if suffix.isEmpty then portBase
    else if base.endsWith "_" then portBase  -- Already has underscore, keep as-is
    else s!"{base}_{suffix}"
  else
    -- Construct from base + wire index ONLY if wire name suggests indexing
    -- E.g., portBase="a", wireName="a_0" → "a_0" (preserve underscores)
    --       portBase="eq", wireName="e0_cdb_match_src1" → "eq" (don't append "1")
    let suffix := extractNumericSuffix wireName
    if suffix.isEmpty then
      portBase
    else
      -- Only append suffix if wireName starts with or contains portBase
      -- This handles cases like: portBase="a", wireName="a_0" or "entry0_a_0"
      if wireName.startsWith portBase || wireName.contains ("_" ++ portBase) then
        portBase ++ "_" ++ suffix
      else
        portBase

/-! ## Bulk Vec Connection Helpers -/

-- Helper: get the _wires array index for a wire, if it resolves to _wires(idx)
def getWireArrayIdx (ctx : ChiselContext) (w : Wire) : Option Nat :=
  if !ctx.useWireArray then none
  else
    -- Must not be a register
    match ctx.regToIndex.find? (fun p => p.fst.name == w.name) with
    | some _ => none
    | none =>
      -- Must not be an IO port (when using IO bundle)
      if ctx.useIOBundle then
        match ctx.inputToIndex.find? (fun p => p.fst.name == w.name) with
        | some _ => none
        | none =>
          match ctx.outputToIndex.find? (fun p => p.fst.name == w.name) with
          | some _ => none
          | none =>
            ctx.wireToIndex.find? (fun p => p.fst.name == w.name) |>.map Prod.snd
      else
        ctx.wireToIndex.find? (fun p => p.fst.name == w.name) |>.map Prod.snd

-- Group port map entries by bracket base name.
-- Returns (groups, standalone_entries) where groups are (baseName, sorted list of (portIndex, wire))
def groupPortMapEntries (entries : List (String × Wire))
    : (List (String × List (Nat × Wire)) × List (String × Wire)) :=
  let result := entries.foldl (fun acc entry =>
    let grps := acc.fst
    let stand := acc.snd
    let portName := entry.fst
    let wire := entry.snd
    match parseBracketNotation portName with
    | some (base, idx) =>
      match grps.find? (fun p => p.fst == base) with
      | some _ =>
        let grps' := grps.map (fun p => if p.fst == base then (p.fst, (idx, wire) :: p.snd) else p)
        (grps', stand)
      | none =>
        ((base, [(idx, wire)]) :: grps, stand)
    | none =>
      (grps, (portName, wire) :: stand)
  ) (([] : List (String × List (Nat × Wire))), ([] : List (String × Wire)))
  -- Sort each group by port index
  let sortedGroups := result.fst.map (fun p =>
    (p.fst, p.snd.toArray.qsort (fun a b => a.fst < b.fst) |>.toList))
  (sortedGroups, result.snd.reverse)

-- Check if a sorted group of (portIndex, wire) pairs has contiguous _wires indices.
-- Returns some(wireArrayStart) if wire[i] → _wires(start + i) for all i.
def checkContiguousWires (ctx : ChiselContext) (group : List (Nat × Wire)) : Option Nat :=
  match group with
  | [] => none
  | (_, firstWire) :: rest =>
    match getWireArrayIdx ctx firstWire with
    | some firstIdx =>
      let allContiguous := rest.enum.all (fun pair =>
        let i := pair.fst
        let w := pair.snd.snd
        match getWireArrayIdx ctx w with
        | some idx => idx == firstIdx + (i + 1)
        | none => false)
      if allContiguous then some firstIdx else none
    | none => none

/-! ## Instance Connection Generation -/

-- Split a sorted group of (portIndex, wire) entries into contiguous sub-ranges.
-- Returns a list of connection strings: foreach loops for contiguous runs, individual lines otherwise.
private def generateGroupConnections (ctx : ChiselContext) (instName baseName : String)
    (entries : List (Nat × Wire)) : List String :=
  let rec go (es : List (Nat × Wire)) (fuel : Nat) : List String :=
    match fuel, es with
    | 0, _ => []  -- fuel exhausted
    | _, [] => []
    | fuel' + 1, (portIdx, wire) :: rest =>
      match getWireArrayIdx ctx wire with
      | some wireIdx =>
        -- Try to extend a contiguous run
        let rec extend (rs : List (Nat × Wire)) (n : Nat) : Nat × List (Nat × Wire) :=
          match rs with
          | (nextPort, nextWire) :: rest2 =>
            if nextPort == portIdx + n then
              match getWireArrayIdx ctx nextWire with
              | some nextWireIdx =>
                if nextWireIdx == wireIdx + n then
                  extend rest2 (n + 1)
                else (n, rs)
              | none => (n, rs)
            else (n, rs)
          | [] => (n, [])
        let (count, remaining) := extend rest 1
        if count >= 4 then
          -- Emit foreach loop for contiguous range of 4+ entries
          let line := "  (0 until " ++ toString count ++ ").foreach " ++ "{ i => " ++
            instName ++ "." ++ baseName ++ "(" ++ toString portIdx ++ " + i) <> _wires(" ++
            toString wireIdx ++ " + i) }"
          line :: go remaining fuel'
        else
          -- Too short for a loop, emit individually
          let short := (portIdx, wire) :: rest.take (count - 1)
          let indiv := short.map (fun (idx, w) =>
            s!"  {instName}.{baseName}({idx}) <> {wireRef ctx w}")
          indiv ++ go (rest.drop (count - 1)) fuel'
      | none =>
        -- Wire not in _wires array, emit individually
        let line := s!"  {instName}.{baseName}({portIdx}) <> {wireRef ctx wire}"
        line :: go rest fuel'
  go entries (entries.length + 1)

-- Check if a module name corresponds to a module with bundled IO (>200 ports)
-- This is a heuristic based on known module sizes
private def moduleUsesBundledIO (moduleName : String) : Bool :=
  -- Modules known to use bundled IO (>200 total ports, or large internal complexity)
  moduleName == "StoreBuffer8" || moduleName == "MemoryExecUnit" ||
  moduleName == "LSU" ||
  moduleName == "ReservationStation4" || moduleName == "MulDivRS4" ||
  moduleName == "PhysRegFile_64x32" || moduleName == "RAT_32x6" ||
  moduleName == "FreeList_64" || moduleName == "PipelinedMultiplier"

-- Map port names with underscores to bundled IO Vec indices
-- This handles both "inputs" and "outputs" Vecs
private def mapPortNameToVecRef (moduleName portName : String) : Option String :=
  -- For StoreBuffer8: map port names to inputs/outputs Vec indices
  if moduleName == "StoreBuffer8" then
    -- StoreBuffer8 inputs order (excluding clock which is explicit):
    -- 0: reset, 1: zero, 2: one, 3: enq_en, 4-35: enq_address, 36-67: enq_data,
    -- 68-69: enq_size, 70: commit_en, 71-73: commit_idx, 74: deq_ready,
    -- 75-106: fwd_address, 107: flush_en
    if portName == "reset" then some "inputs(0)"
    else if portName == "zero" then some "inputs(1)"
    else if portName == "one" then some "inputs(2)"
    else if portName == "enq_en" then some "inputs(3)"
    else if portName == "commit_en" then some "inputs(70)"
    else if portName == "deq_ready" then some "inputs(74)"
    else if portName == "flush_en" then some "inputs(107)"
    else if portName.startsWith "enq_address_" then
      portName.drop 12 |>.toNat? |>.map (fun i => s!"inputs({4 + i})")
    else if portName.startsWith "enq_data_" then
      portName.drop 9 |>.toNat? |>.map (fun i => s!"inputs({36 + i})")
    else if portName.startsWith "enq_size_" then
      portName.drop 9 |>.toNat? |>.map (fun i => s!"inputs({68 + i})")
    else if portName.startsWith "commit_idx_" then
      portName.drop 11 |>.toNat? |>.map (fun i => s!"inputs({71 + i})")
    else if portName.startsWith "fwd_address_" then
      portName.drop 12 |>.toNat? |>.map (fun i => s!"inputs({75 + i})")
    -- Outputs: 0: full, 1: empty, 2-4: enq_idx, 5: deq_valid, 6-71: deq_bits, 72: fwd_hit, 73-104: fwd_data
    else if portName == "full" then some "outputs(0)"
    else if portName == "empty" then some "outputs(1)"
    else if portName == "deq_valid" then some "outputs(5)"
    else if portName == "fwd_hit" then some "outputs(72)"
    else if portName.startsWith "enq_idx_" then
      portName.drop 8 |>.toNat? |>.map (fun i => s!"outputs({2 + i})")
    else if portName.startsWith "deq_bits_" then
      portName.drop 9 |>.toNat? |>.map (fun i => s!"outputs({6 + i})")
    else if portName.startsWith "fwd_data_" then
      portName.drop 9 |>.toNat? |>.map (fun i => s!"outputs({73 + i})")
    else none
  -- Generic handler for bundled I/O port names (inputs_N, outputs_N)
  else if portName.startsWith "inputs_" then
    portName.drop 7 |>.toNat? |>.map (fun i => s!"inputs({i})")
  else if portName.startsWith "outputs_" then
    portName.drop 8 |>.toNat? |>.map (fun i => s!"outputs({i})")
  else none

-- Generate submodule instantiation with bulk Vec connections for bracketed port groups
def generateInstanceChunked (ctx : ChiselContext) (c : Circuit) (inst : CircuitInstance) (chunkSize : Nat := 5) : (String × String) :=
  let instDecl := s!"  val {inst.instName} = Module(new {inst.moduleName})"
  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let childUsesBundledIO := moduleUsesBundledIO inst.moduleName

  -- Only group port map entries for bundled IO modules (which use Vec ports)
  -- For named-port modules (like ROB16), treat all entries as standalone
  let (groups, standaloneEntries) :=
    if childUsesBundledIO then
      groupPortMapEntries inst.portMap
    else
      ([], inst.portMap)  -- No grouping for named ports

  -- Generate connection lines for bracketed groups (foreach loops + individual)
  -- Only used for bundled IO modules
  let groupConns := groups.map (fun p =>
    generateGroupConnections ctx inst.instName p.fst p.snd) |>.flatten

  -- Generate connection lines for standalone entries (clock, reset, etc.)
  let standConns := standaloneEntries.map (fun entry =>
    let portName := entry.fst
    let wire := entry.snd
    let wRef := wireRef ctx wire
    -- If child uses bundled IO, map port names to Vec indices
    let portRef :=
      if childUsesBundledIO then
        match mapPortNameToVecRef inst.moduleName portName with
        | some vecRef => vecRef
        | none => constructPortRef portName wire.name
      else constructPortRef portName wire.name
    -- Don't apply .asClock/.asAsyncReset conversions to Vec references
    -- But DO apply .asBool to reset when connecting to a Bool Vec element
    let isVecRef := portRef.startsWith "inputs" || portRef.startsWith "outputs"
    let wRefConverted :=
      if isVecRef then
        -- If connecting reset to a Vec Bool element, need .asBool conversion
        if portName == "reset" || wire.name == "reset" then
          s!"{wRef}.asBool"
        else wRef
      else if (portName == "clock" || portRef == "clock") && !clockWires.contains wire then
        s!"{wRef}.asClock"
      else if (portName == "reset" || portRef == "reset") && !resetWires.contains wire then
        s!"{wRef}.asAsyncReset"
      else wRef
    s!"  {inst.instName}.{portRef} <> {wRefConverted}"
  )

  -- Generate non-bracketed connections (for instances without bracket notation)
  let nonBracketConns := if groups.isEmpty then
    inst.portMap.map (fun entry =>
      let portBaseName := entry.fst
      let wire := entry.snd
      let wRef := wireRef ctx wire
      -- If child uses bundled IO, map port names to Vec indices
      let portRef :=
        if childUsesBundledIO then
          match mapPortNameToVecRef inst.moduleName portBaseName with
          | some vecRef => vecRef
          | none => constructPortRef portBaseName wire.name
        else constructPortRef portBaseName wire.name
      -- Handle Vec references specially
      let isVecRef := portRef.startsWith "inputs" || portRef.startsWith "outputs"
      let wRefConverted :=
        if isVecRef then
          -- If connecting reset to a Vec Bool element, need .asBool conversion
          if portBaseName == "reset" || wire.name == "reset" then
            s!"{wRef}.asBool"
          else wRef
        else if (portBaseName == "clock" || portRef == "clock") && !clockWires.contains wire then
          s!"{wRef}.asClock"
        else if (portBaseName == "reset" || portRef == "reset") && !resetWires.contains wire then
          s!"{wRef}.asAsyncReset"
        else wRef
      s!"  {inst.instName}.{portRef} <> {wRefConverted}")
  else []

  let allConns := groupConns ++ standConns ++ nonBracketConns

  -- Always apply chunking if connection count exceeds threshold
  if allConns.length <= chunkSize then
    (joinLines ([instDecl] ++ allConns), "")
  else
    let chunks := chunkList allConns chunkSize
    let helperMethods := chunks.enum.map (fun ⟨idx, chunk⟩ =>
      joinLines [
        s!"  private def connect_{inst.instName}_{idx}(): Unit = " ++ "{",
        joinLines chunk,
        "  }"
      ]
    )
    let helperCalls := List.range chunks.length |>.map (fun i => s!"  connect_{inst.instName}_{i}()")
    (joinLines ([instDecl] ++ helperCalls), joinLines helperMethods)

-- Generate all submodule instances with chunking
def generateInstancesChunked (ctx : ChiselContext) (c : Circuit) : (String × String) :=
  let results := c.instances.map (fun inst => generateInstanceChunked ctx c inst 5)
  let calls := results.map Prod.fst
  let metods := results.map Prod.snd
  (joinLines calls, joinLines metods)

-- Generate wire declarations only
def generateWireDecls (ctx : ChiselContext) (c : Circuit) : String :=
  let internalWires := findInternalWires c
  let dffOutputs := findDFFOutputs c
  let wiresToDeclare := internalWires.filter (fun w => !dffOutputs.contains w)
  if ctx.useWireArray then
    s!"  val _wires = Wire(Vec({ctx.wireToIndex.length}, Bool()))"
  else
    joinLines (wiresToDeclare.map (fun w => s!"  val {w.name} = Wire(Bool())"))


-- Generate combinational assignments only (two-tier chunking for very large circuits)
def generateCombAssignmentsChunked (ctx : ChiselContext) (c : Circuit) (chunkSize : Nat := 5) : (String × String) :=
  let combGates := c.gates.filter (fun g => g.gateType.isCombinational)

  if ctx.useWireArray then
    let gateChunks := chunkList combGates chunkSize
    let helperMethods := gateChunks.enum.map (fun ⟨idx, chunk⟩ =>
      let assignments := chunk.map (generateCombGate ctx)
      joinLines [
        s!"  private def initLogic{idx}(): Unit = " ++ "{",
        joinLines (assignments.map (fun a => "  " ++ a)),
        "  }"
      ]
    )
    -- Multi-tier: if we have >10 chunk methods, group them into super-chunks
    if gateChunks.length > 10 then
      let chunkCallsList := List.range gateChunks.length |>.map (fun i => s!"initLogic{i}()")
      let superChunks := chunkList chunkCallsList 10
      let superHelpers := superChunks.enum.map (fun ⟨idx, calls⟩ =>
        joinLines [
          s!"  private def initLogicGroup{idx}(): Unit = " ++ "{",
          joinLines (calls.map (fun c => s!"    {c}")),
          "  }"
        ]
      )
      -- Third tier: if we have >10 super-chunk methods, group those too
      if superChunks.length > 10 then
        let superCalls := List.range superChunks.length |>.map (fun i => s!"initLogicGroup{i}()")
        let ultraChunks := chunkList superCalls 10
        let ultraHelpers := ultraChunks.enum.map (fun ⟨idx, calls⟩ =>
          joinLines [
            s!"  private def initLogicUltra{idx}(): Unit = " ++ "{",
            joinLines (calls.map (fun c => s!"    {c}")),
            "  }"
          ]
        )
        let ultraCalls := List.range ultraChunks.length |>.map (fun i => s!"  initLogicUltra{i}()")
        (joinLines ultraCalls, joinLines helperMethods ++ "\n\n" ++ joinLines superHelpers ++ "\n\n" ++ joinLines ultraHelpers)
      else
        let superCalls := List.range superChunks.length |>.map (fun i => s!"  initLogicGroup{i}()")
        (joinLines superCalls, joinLines helperMethods ++ "\n\n" ++ joinLines superHelpers)
    else
      let helperCalls := List.range gateChunks.length |>.map (fun i => s!"  initLogic{i}()")
      (joinLines helperCalls, joinLines helperMethods)
  else if combGates.length <= chunkSize then
    let assignments := combGates.map (generateCombGate ctx)
    (joinLines assignments, "")
  else
    let gateChunks := chunkList combGates chunkSize
    let helperMethods := gateChunks.enum.map (fun ⟨idx, chunk⟩ =>
      let assignments := chunk.map (generateCombGate ctx)
      joinLines [
        s!"  private def initLogic{idx}(): Unit = " ++ "{",
        joinLines (assignments.map (fun a => "  " ++ a)),
        "  }"
      ]
    )
    -- Multi-tier: if we have >10 chunk methods, group them
    if gateChunks.length > 10 then
      let chunkCallsList := List.range gateChunks.length |>.map (fun i => s!"initLogic{i}()")
      let superChunks := chunkList chunkCallsList 10
      let superHelpers := superChunks.enum.map (fun ⟨idx, calls⟩ =>
        joinLines [
          s!"  private def initLogicGroup{idx}(): Unit = " ++ "{",
          joinLines (calls.map (fun c => s!"    {c}")),
          "  }"
        ]
      )
      -- Third tier: if we have >10 super-chunk methods, group those too
      if superChunks.length > 10 then
        let superCalls := List.range superChunks.length |>.map (fun i => s!"initLogicGroup{i}()")
        let ultraChunks := chunkList superCalls 10
        let ultraHelpers := ultraChunks.enum.map (fun ⟨idx, calls⟩ =>
          joinLines [
            s!"  private def initLogicUltra{idx}(): Unit = " ++ "{",
            joinLines (calls.map (fun c => s!"    {c}")),
            "  }"
          ]
        )
        let ultraCalls := List.range ultraChunks.length |>.map (fun i => s!"  initLogicUltra{i}()")
        (joinLines ultraCalls, joinLines helperMethods ++ "\n\n" ++ joinLines superHelpers ++ "\n\n" ++ joinLines ultraHelpers)
      else
        let superCalls := List.range superChunks.length |>.map (fun i => s!"  initLogicGroup{i}()")
        (joinLines superCalls, joinLines helperMethods ++ "\n\n" ++ joinLines superHelpers)
    else
      let helperCalls := List.range gateChunks.length |>.map (fun i => s!"  initLogic{i}()")
      (joinLines helperCalls, joinLines helperMethods)

-- Main code generator: Circuit → Chisel module
def toChisel (c : Circuit) : String :=
  let moduleName := c.name
  let isSequential := c.hasSequentialElements

  -- Use BlackBox for modules with >2000 gates (JVM class size limits)
  -- BlackBox references the Lean-generated SystemVerilog directly
  if c.gates.length > 2000 then
    let ioDecl := generateIOBundle c false {
      wireToIndex := [], inputToIndex := [], outputToIndex := [],
      regToIndex := [], useWireArray := false,
      useIOBundle := c.inputs.length + c.outputs.length > 200,
      useRegArray := false
    }
    joinLines [
      s!"// BlackBox wrapper for {moduleName} ({c.gates.length} gates)",
      s!"// References Lean-generated SV: output/sv-from-lean/{moduleName}.sv",
      "",
      "package generated",
      "",
      "import chisel3._",
      "import chisel3.util._",
      "",
      "class " ++ moduleName ++ " extends ExtModule {",
      ioDecl,
      "}"
    ]
  else
    -- Setup context for large circuits
  let internalWires := findInternalWires c
  let dffOutputs := findDFFOutputs c
  let wiresToDeclare := internalWires.filter (fun w => !dffOutputs.contains w)
  -- Find clock/reset from both DFF gates AND instance connections
  -- Don't check isSequential - circuits can have sequential instances without DFFs
  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let implicitWires := (clockWires ++ resetWires).eraseDups
  let filteredInputs := c.inputs.filter (fun w => !implicitWires.contains w)
  let totalIOPorts := filteredInputs.length + c.outputs.length

  let dffGates := c.gates.filter (fun g => g.gateType == GateType.DFF)

  -- Check if this is a "simple register" (only DFFs, no comb logic, no instances)
  -- For these, we must match LEAN SV structure exactly (no reg arrays)
  let isSimpleRegister := c.gates.all (fun g => g.gateType == GateType.DFF) &&
                          c.instances.isEmpty

  let ctx : ChiselContext := {
    wireToIndex := wiresToDeclare.enum.map (fun ⟨idx, wire⟩ => (wire, idx)),
    inputToIndex := filteredInputs.enum.map (fun ⟨idx, wire⟩ => (wire, idx)),
    outputToIndex := c.outputs.enum.map (fun ⟨idx, wire⟩ => (wire, idx)),
    regToIndex := dffGates.enum.map (fun ⟨idx, g⟩ => (g.output, idx)),
    useWireArray := wiresToDeclare.length > 200,
    useIOBundle := totalIOPorts > 200,  -- Use bundled IO for very large modules to avoid JVM method size limits
    useRegArray := dffGates.length > 50 && !isSimpleRegister  -- Never use reg arrays for simple registers
  }

  if isSequential then
    let regDecls := generateRegDecls c ctx
    let wireDecls := generateWireDecls ctx c
    let (instances, instanceHelpers) := generateInstancesChunked ctx c
    let (combMain, combHelpers) := generateCombAssignmentsChunked ctx c 5
    let (updateMain, updateHelpers) := generateRegUpdatesChunked ctx c 5
    let regOutputs := generateRegOutputConnections ctx c

    let parts := [regDecls, wireDecls, instances, combMain, updateMain, regOutputs].filter (fun s => !s.isEmpty)
    let logic := String.intercalate "\n\n" parts
    let helpers := [instanceHelpers, combHelpers, updateHelpers].filter (fun s => !s.isEmpty)
    let helpersString := String.intercalate "\n\n" helpers

    joinLines [
      "package generated",
      "",
      "import chisel3._",
      "import chisel3.util._",
      "",
      "class " ++ moduleName ++ " extends RawModule {",
      generateIOBundle c true ctx,
      "",
      logic,
      (if helpersString.isEmpty then "" else "\n" ++ helpersString),
      "}"
    ]
  else
    let wireDecls := generateWireDecls ctx c
    let (instances, instanceHelpers) := generateInstancesChunked ctx c
    let (mainLogic, helperMethods) := generateCombAssignmentsChunked ctx c 5
    let allHelpers := [instanceHelpers, helperMethods].filter (fun s => !s.isEmpty) |> String.intercalate "\n"
    
    let classBody := joinLines [
      generateIOBundle c false ctx,
      "",
      wireDecls,
      "",
      instances,
      "",
      mainLogic,
      if allHelpers.isEmpty then "" else "\n" ++ allHelpers
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
