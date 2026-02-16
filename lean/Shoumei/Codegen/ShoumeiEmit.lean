/-
Codegen/ShoumeiEmit.lean - Shoumei Text Format Pretty Printer

Emits Circuit values as human-readable `.shoumei` text files.
See docs/shoumei-text-format.md for the format specification.
-/

import Shoumei.DSL
import Shoumei.Codegen.Common
import Std.Data.HashSet
import Std.Data.HashMap

namespace Shoumei.Codegen.ShoumeiEmit

open Shoumei.Codegen

instance : Inhabited Gate where
  default := { gateType := .BUF, inputs := [], output := ⟨""⟩ }


/-! ## Wire-to-Bus Context -/

/-- Context for emission: maps wires to their parent bus and bit index. -/
structure EmitCtx where
  wireToGroup : List (Wire × SignalGroup)
  wireToIndex : List (Wire × Nat)
  -- Fast lookup maps (wire name → signal group / index)
  groupMap : Std.HashMap String SignalGroup := {}
  indexMap : Std.HashMap String Nat := {}

/-- Parse wire name into (baseName, index), e.g. "a_3" → ("a", 3) -/
def parseWireName (w : Wire) : Option (String × Nat) :=
  let name := w.name
  match name.splitOn "_" with
  | [] => none
  | parts =>
    match parts.reverse with
    | [] => none
    | lastPart :: restReversed =>
      match lastPart.toNat? with
      | some idx =>
        let baseName := String.intercalate "_" restReversed.reverse
        some (baseName, idx)
      | none => none

/-- Port name separator style: underscore (d_0), bare digits (a31), or bracket (in0[0]). -/
inductive PortSep where | underscore | bare | bracket
  deriving BEq

/-- Parse a port name into (prefix, index, separator style).
    Tries bracket ("in0[0]" → ("in0", 0, bracket)),
    then underscore ("d_0" → ("d_", 0, underscore)),
    then trailing digits ("a31" → ("a", 31, bare)). -/
def parsePortName (portName : String) : Option (String × Nat × PortSep) :=
  -- Try bracket pattern: name[idx]
  if portName.endsWith "]" then
    match portName.splitOn "[" with
    | [base, idxBracket] =>
      let idxStr := idxBracket.dropEnd 1
      match idxStr.toNat? with
      | some idx => some (base, idx, .bracket)
      | none => none
    | _ => none
  else
    -- Try underscore split: "d_0" → ("d_", 0)
    let parts := portName.splitOn "_"
    match parts.reverse with
    | lastPart :: restRev =>
      if restRev.isEmpty then trySuffix portName
      else
        match lastPart.toNat? with
        | some idx =>
          let pfx := String.intercalate "_" restRev.reverse ++ "_"
          some (pfx, idx, .underscore)
        | none => trySuffix portName
    | _ => trySuffix portName
where
  trySuffix (s : String) : Option (String × Nat × PortSep) :=
    let chars := s.toList
    let revDigits := chars.reverse.takeWhile Char.isDigit
    if revDigits.isEmpty then none
    else
      let numDigits := revDigits.length
      let pfx := String.ofList (chars.take (chars.length - numDigits))
      let sfx := String.ofList revDigits.reverse
      match sfx.toNat? with
      | some idx => if pfx.isEmpty then none else some (pfx, idx, .bare)
      | none => none

/-- Group wires by base name for bus reconstruction -/
def groupWiresByBaseName (wires : List Wire) : List (String × List (Nat × Wire)) :=
  let parsed := wires.filterMap (fun w =>
    match parseWireName w with
    | some (base, idx) => some (base, idx, w)
    | none => none
  )
  parsed.foldl (fun acc (base, idx, w) =>
    match acc.find? (fun p => p.1 == base) with
    | some (_, existing) =>
      acc.filter (fun p => p.1 != base) ++ [(base, existing ++ [(idx, w)])]
    | none =>
      acc ++ [(base, [(idx, w)])]
  ) []

/-- Check if indexed wires form a valid bus (contiguous 0..N-1) -/
def isValidBus (indexedWires : List (Nat × Wire)) : Bool :=
  if indexedWires.isEmpty then false
  else
    let indices := indexedWires.map (·.1)
    let sorted := indices.toArray.qsort (· < ·) |>.toList
    sorted == List.range sorted.length

/-- Auto-detect signal groups from wire naming patterns -/
def autoDetectSignalGroups (wires : List Wire) : List SignalGroup :=
  let grouped := groupWiresByBaseName wires
  grouped.filterMap (fun (baseName, indexedWires) =>
    if isValidBus indexedWires then
      let sortedWires := indexedWires.toArray.qsort (fun a b => a.1 < b.1)
                         |>.toList.map (·.2)
      let width := sortedWires.length
      some { name := baseName, width := width, wires := sortedWires }
    else
      none
  )

/-- Find all internal wires (not inputs or outputs) -/
def findInternalWires (c : Circuit) : List Wire :=
  let gateOutputs := c.gates.map (fun g => g.output)
  let instanceWires := c.instances.flatMap (fun inst => inst.portMap.map (fun p => p.2))
  (gateOutputs ++ instanceWires).eraseDups.filter (fun w =>
    !c.inputs.contains w && !c.outputs.contains w
  )

/-- Build emission context from a circuit -/
def mkCtx (c : Circuit) : EmitCtx :=
  let internalWires := findInternalWires c
  let autoGroups := autoDetectSignalGroups internalWires
  let allGroups := c.signalGroups ++ autoGroups
  -- Deduplicate: keep first occurrence of each group name
  let deduped := allGroups.foldl (fun acc sg =>
    if acc.any (fun s => s.name == sg.name) then acc else acc ++ [sg]
  ) []
  let wireToGroup := deduped.flatMap (fun sg =>
    sg.wires.map (fun w => (w, sg))
  )
  let wireToIndex := deduped.flatMap (fun sg =>
    sg.wires.enum.map (fun (idx, w) => (w, idx))
  )
  let groupMap := wireToGroup.foldl (fun (m : Std.HashMap String SignalGroup) (w, sg) =>
    m.insert w.name sg) {}
  let indexMap := wireToIndex.foldl (fun (m : Std.HashMap String Nat) (w, idx) =>
    m.insert w.name idx) {}
  { wireToGroup, wireToIndex, groupMap, indexMap }

/-! ## Wire Reference Formatting -/

/-- Format a wire reference: bus wires become `name[idx]`, scalars stay as-is -/
def wireRef (w : Wire) (ctx : EmitCtx) : String :=
  match ctx.groupMap[w.name]? with
  | some sg =>
    if sg.width > 1 then
      match ctx.indexMap[w.name]? with
      | some idx => s!"{sg.name}[{idx}]"
      | none => w.name
    else
      sg.name
  | none => w.name

/-- Get gate type name -/
def gateTypeName (gt : GateType) : String :=
  match gt with
  | .AND => "AND"
  | .OR => "OR"
  | .NOT => "NOT"
  | .XOR => "XOR"
  | .BUF => "BUF"
  | .MUX => "MUX"
  | .DFF => "DFF"
  | .DFF_SET => "DFF_SET"

/-! ## Header Emission -/

/-- Emit a port list (inputs or outputs) with bus compression.
    Returns comma-separated port names, with buses emitted once as `name[width]`. -/
def emitPortList (wires : List Wire) (ctx : EmitCtx) : String :=
  -- Track which group names we've already emitted
  let (_, parts) := wires.foldl (fun (emittedGroups, acc) w =>
    match ctx.groupMap[w.name]? with
    | some sg =>
      if sg.width > 1 then
        if emittedGroups.contains sg.name then
          (emittedGroups, acc)  -- skip, already emitted this bus
        else
          (emittedGroups ++ [sg.name], acc ++ [s!"{sg.name}[{sg.width}]"])
      else
        -- Width-1 signal group, emit as scalar
        (emittedGroups, acc ++ [sg.name])
    | none =>
      (emittedGroups, acc ++ [w.name])
  ) (([] : List String), ([] : List String))
  ", ".intercalate parts

/-- Emit the module header line -/
def emitHeader (c : Circuit) (ctx : EmitCtx) : String :=
  let inputs := emitPortList c.inputs ctx
  let outputs := emitPortList c.outputs ctx
  s!"module {c.name}({inputs} -> {outputs})"

/-! ## Annotations -/

def emitAnnotations (c : Circuit) : List String :=
  if c.keepHierarchy then ["  @keepHierarchy"] else []

/-! ## Internal Wire Declarations -/

/-- Emit internal bus declarations (wire name[width]) -/
def emitInternalWireDecls (c : Circuit) (ctx : EmitCtx) : List String :=
  -- Find signal groups that are purely internal (no wire is an input or output)
  let inputSet := c.inputs.map (·.name)
  let outputSet := c.outputs.map (·.name)
  -- Collect unique group names for internal buses
  let (_, decls) := ctx.wireToGroup.foldl (fun (seen, acc) (_w, sg) =>
    if sg.width > 1 && !seen.contains sg.name then
      -- Check if any wire of this group is an input or output
      let isIO := sg.wires.any (fun sw =>
        inputSet.contains sw.name || outputSet.contains sw.name)
      if isIO then (seen ++ [sg.name], acc)
      else (seen ++ [sg.name], acc ++ [s!"  wire {sg.name}[{sg.width}]"])
    else (seen, acc)
  ) (([] : List String), ([] : List String))
  decls

/-! ## Loop Compression -/

/-- Signature for a gate: (GateType, outputBusOrScalar, [inputBusOrScalar]) -/
structure GateSig where
  gateType : GateType
  outputKey : String  -- bus name or wire name (for scalars)
  inputKeys : List String  -- bus name or wire name per input
  deriving BEq, Repr

/-- Classify a wire as (busName, bitIndex) or (wireName, none) -/
def classifyWire (w : Wire) (ctx : EmitCtx) : String × Option Nat :=
  match ctx.groupMap[w.name]? with
  | some sg =>
    if sg.width > 1 then
      match ctx.indexMap[w.name]? with
      | some idx => (sg.name, some idx)
      | none => (w.name, none)
    else (sg.name, none)
  | none => (w.name, none)

/-- Per-gate info for loop compression: output bus/index, and per-input (bus, index). -/
structure GateInfo where
  gateIdx  : Nat
  outBus   : String
  outIdx   : Option Nat
  inputs   : List (String × Option Nat)  -- (busOrScalar, bitIdx)
  deriving Inhabited

/-- Compute base signature (gate type + output bus + input bus/scalar names).
    This groups gates that MIGHT form a loop together, before checking index patterns. -/
def gateBaseKey (g : Gate) (ctx : EmitCtx) : String × GateInfo × Nat :=
  let (outKey, outIdx) := classifyWire g.output ctx
  let inputInfos := g.inputs.map (fun w => classifyWire w ctx)
  let inputBusNames := inputInfos.map (fun (k, _) => k)
  let gt := gateTypeName g.gateType
  let baseKey := s!"{gt}:{outKey}:{",".intercalate inputBusNames}"
  let info : GateInfo := { gateIdx := 0, outBus := outKey, outIdx := outIdx, inputs := inputInfos }
  (baseKey, info, outIdx.getD 0)


/-- A compressed loop or a single gate statement -/
inductive EmitItem where
  | single (gateIdx : Nat)
  | loop (gateIndices : List Nat) (startIdx : Nat) (count : Nat) (sig : GateSig)

/-- Format a single gate as a statement -/
def formatGate (g : Gate) (ctx : EmitCtx) : String :=
  let out := wireRef g.output ctx
  let inputs := ", ".intercalate (g.inputs.map (fun w => wireRef w ctx))
  let gt := gateTypeName g.gateType
  s!"  {out} = {gt}({inputs})"


/-- For a contiguous run of gates (sorted by output bit index), determine for each input
    position whether it co-varies with the output index or is fixed.
    Returns a GateSig with proper ~busName / busName#idx / scalar encoding. -/
def buildLoopSig (gateType : GateType) (outBus : String)
    (gateInfos : Array GateInfo) : GateSig :=
  if gateInfos.size == 0 then
    { gateType, outputKey := outBus, inputKeys := [] }
  else
    let first := gateInfos[0]!
    let numInputs := first.inputs.length
    let inputKeys := List.range numInputs |>.map (fun inputPos =>
      let (busName, _) := match first.inputs[inputPos]? with
        | some x => x
        | none => ("?", none)
      -- Check if this input co-varies across the run:
      -- It co-varies if each gate's input index == that gate's output index
      let coVaries := gateInfos.all (fun info =>
        match info.inputs[inputPos]?, info.outIdx with
        | some (_, some iIdx), some oIdx => iIdx == oIdx
        | _, _ => false
      )
      if coVaries then s!"~{busName}"
      else
        -- Check if it's fixed (same index for all gates)
        let isFixed := gateInfos.all (fun info =>
          match info.inputs[inputPos]?, first.inputs[inputPos]? with
          | some (_, some i1), some (_, some i2) => i1 == i2
          | some (_, none), some (_, none) => true  -- both scalar
          | _, _ => false
        )
        if isFixed then
          match first.inputs[inputPos]? with
          | some (_, some idx) => s!"{busName}#{idx}"
          | _ => busName  -- scalar
        else busName  -- shouldn't happen in practice
    )
    { gateType, outputKey := outBus, inputKeys }

/-- Perform loop compression on the gate list.
    Returns emit items in original gate order. -/
def compressGates (gates : List Gate) (ctx : EmitCtx) : List EmitItem := Id.run do
  let n : Nat := gates.length
  let gatesArr := gates.toArray

  -- Step 1: Compute base key + gate info for each gate
  let precomputed := gates.enum.map (fun (i, g) =>
    let (baseKey, info, _) := gateBaseKey g ctx
    (baseKey, { info with gateIdx := i }, info.outIdx)
  ) |>.toArray

  -- Step 2: Collect entries with bus output indices, sort by base key
  let entries : Array (String × Nat × Nat × GateInfo) := (Array.range n).filterMap (fun i =>
    match precomputed[i]? with
    | some (key, info, some outIdx) => some (key, i, outIdx, info)
    | _ => none
  )
  let sortedEntries := entries.qsort (fun a b => a.1 < b.1)

  -- Step 3: Group by base key, find contiguous output index runs, verify co-variance
  let mut loops : Array (Nat × GateSig × Nat × Nat × Array Nat) := #[]
  let mut groupStart := 0
  while groupStart < sortedEntries.size do
    let key := sortedEntries[groupStart]!.1
    let mut groupEnd := groupStart
    while groupEnd < sortedEntries.size && sortedEntries[groupEnd]!.1 == key do
      groupEnd := groupEnd + 1
    -- Sort by output bit index (third element of tuple)
    let groupEntries := sortedEntries.extract groupStart groupEnd
      |>.qsort (fun (_, _, a, _) (_, _, b, _) => a < b)
    -- Find contiguous runs of output bit indices
    let getOutIdx := fun (e : String × Nat × Nat × GateInfo) => e.2.2.1
    let mut runStart := 0
    while runStart < groupEntries.size do
      let mut runEnd := runStart + 1
      while runEnd < groupEntries.size &&
            getOutIdx groupEntries[runEnd]! == getOutIdx groupEntries[runEnd - 1]! + 1 do
        runEnd := runEnd + 1
      let runLen := runEnd - runStart
      if runLen >= 2 then
        let runSlice := groupEntries.extract runStart runEnd
        let runInfos := runSlice.map (fun (_, _, _, info) => info)
        let (_, firstGateIdx, startBit, firstInfo) := groupEntries[runStart]!
        -- Determine co-variance from the actual run data
        let gt := gatesArr[firstGateIdx]!.gateType
        let sig := buildLoopSig gt firstInfo.outBus runInfos
        let gateIndices := runSlice.map (fun (_, gi, _, _) => gi)
        loops := loops.push (firstGateIdx, sig, startBit, runLen, gateIndices)
      runStart := runEnd
    groupStart := groupEnd

  -- Step 4: Build HashSet for consumed indices and HashMap for loop starts
  let mut consumedSet : Std.HashSet Nat := {}
  let mut loopStartMap : Std.HashMap Nat (GateSig × Nat × Nat) := {}
  for (firstIdx, sig, startBit, count, indices) in loops do
    for idx in indices do
      consumedSet := consumedSet.insert idx
    loopStartMap := loopStartMap.insert firstIdx (sig, startBit, count)

  -- Step 5: Emit items in original gate order — O(n) with O(1) lookups
  let result := gates.enum.filterMap (fun (i, _) =>
    match loopStartMap[i]? with
    | some (sig, startBit, count) => some (EmitItem.loop [] startBit count sig)
    | none =>
      if consumedSet.contains i then none
      else some (EmitItem.single i)
  )
  result

/-! ## Loop Format with Bus/Scalar Distinction -/

/-- Format a loop, resolving which inputs are bus-indexed vs scalar.
    Uses the first gate in the run to determine bus membership. -/
def formatLoopFromGates (sig : GateSig) (startIdx : Nat) (count : Nat)
    (_firstGate : Gate) (_ctx : EmitCtx) : String :=
  let outRef := s!"{sig.outputKey}[i]"
  -- Decode input keys:
  -- "~busName" → co-varying bus input → "busName[i]"
  -- "busName#idx" → fixed bus input → "busName[idx]"
  -- anything else → scalar wire name
  let inputRefs := sig.inputKeys.map (fun key =>
    if key.startsWith "~" then
      let busName := key.drop 1
      s!"{busName}[i]"
    else if key.any (· == '#') then
      match key.splitOn "#" with
      | [busName, idxStr] => s!"{busName}[{idxStr}]"
      | _ => key
    else key  -- scalar
  )
  let inputs := ", ".intercalate inputRefs
  let gt := gateTypeName sig.gateType
  let endIdx := startIdx + count
  s!"  {outRef} = {gt}({inputs})  for i in {startIdx}..{endIdx}"

/-! ## Gate Emission -/

def emitGates (c : Circuit) (ctx : EmitCtx) : List String :=
  let gatesArr := c.gates.toArray
  let items := compressGates c.gates ctx
  items.filterMap (fun item =>
    match item with
    | .single gateIdx =>
      match gatesArr[gateIdx]? with
      | some g => some (formatGate g ctx)
      | none => none
    | .loop _ startIdx count sig =>
      -- The loop's first gate is at the startIdx bit position
      -- Find it from the consumed gates using the loopStartMap key
      -- The EmitItem.loop is emitted at the first gate's position, so we can
      -- find it by looking for any gate with the right output bus and bit index
      let firstGate := gatesArr.find? (fun g =>
        let (outBus, outIdx) := classifyWire g.output ctx
        outBus == sig.outputKey && outIdx == some startIdx
      )
      match firstGate with
      | some g => some (formatLoopFromGates sig startIdx count g ctx)
      | none =>
        -- Fallback: format without first gate context
        let outRef := s!"{sig.outputKey}[i]"
        let inputRefs := sig.inputKeys.map (fun key =>
          if key.startsWith "~" then s!"{key.drop 1}[i]"
          else if key.any (· == '#') then
            match key.splitOn "#" with
            | [busName, idxStr] => s!"{busName}[{idxStr}]"
            | _ => key
          else key
        )
        let inputs := ", ".intercalate inputRefs
        let gt := gateTypeName sig.gateType
        some s!"  {outRef} = {gt}({inputs})  for i in {startIdx}..{startIdx + count}"
  )

/-! ## Instance Emission -/

/-- Compress a port map list into bus-compressed strings where possible.
    Contiguous port groups (e.g. d_0..d_63) mapping to matching bus wires
    are collapsed to `d_[64] = d`. -/
def compressPortMap (ports : List (String × Wire)) (ctx : EmitCtx) : List String :=
  -- Step 1: Parse port names and group by (prefix, sep)
  let withParsed := ports.map fun (pn, w) => (pn, w, parsePortName pn)
  -- Group key: (prefix, sep) — use string encoding for grouping
  let groupKey := fun (pfx : String) (sep : PortSep) =>
    match sep with | .bracket => pfx ++ "[" | _ => pfx
  let groups : List (String × PortSep × List (Nat × String × Wire)) :=
    withParsed.foldl (fun acc (_pn, w, parsed) =>
      match parsed with
      | some (pfx, idx, sep) =>
        let key := groupKey pfx sep
        match acc.find? (fun (k, _, _) => k == key) with
        | some (_, _, entries) =>
          acc.filter (fun (k, _, _) => k != key) ++ [(key, sep, entries ++ [(idx, _pn, w)])]
        | none => acc ++ [(key, sep, [(idx, _pn, w)])]
      | none => acc
    ) []
  -- Step 2: Determine which groups can be bus-compressed
  let busCompressed : List (String × PortSep × String × Nat × String) :=
    groups.filterMap fun (key, sep, entries) =>
      if entries.length < 2 then none
      else
        let sorted := entries.toArray.qsort (fun a b => a.1 < b.1) |>.toList
        let indices := sorted.map (·.1)
        if indices != List.range sorted.length then none
        else
          let busInfo := sorted.filterMap fun (idx, _, w) =>
            match ctx.groupMap[w.name]?, ctx.indexMap[w.name]? with
            | some sg, some wIdx => if sg.width > 1 && wIdx == idx then some sg.name else none
            | _, _ => none
          if busInfo.length != sorted.length then none
          else
            let busNames := busInfo.eraseDups
            -- Recover the base prefix from the first entry
            match busNames with
            | [busName] =>
              let basePfx := match sorted.head? with
                | some (_, pn, _) =>
                  match parsePortName pn with
                  | some (p, _, _) => p
                  | none => key
                | none => key
              some (key, sep, basePfx, sorted.length, busName)
            | _ => none
  let compressedSet := busCompressed.map (·.1)
  -- Step 3: Emit, skipping already-emitted bus members
  let (_, result) := withParsed.foldl (fun (state : List String × List String) entry =>
    let (emitted, acc) := state
    let (pn, w, parsed) := entry
    match parsed with
    | some (pfx, _, sep) =>
      let key := groupKey pfx sep
      if compressedSet.contains key then
        if emitted.contains key then (emitted, acc)
        else
          match busCompressed.find? (fun (k, _, _, _, _) => k == key) with
          | some (_, portSep, basePfx, width, busName) =>
            let compressed := match portSep with
              | .bracket => s!"{basePfx}[[{width}]] = {busName}"
              | _ => s!"{basePfx}[{width}] = {busName}"
            (emitted ++ [key], acc ++ [compressed])
          | none => (emitted, acc ++ [s!"{pn} = {wireRef w ctx}"])
      else (emitted, acc ++ [s!"{pn} = {wireRef w ctx}"])
    | none => (emitted, acc ++ [s!"{pn} = {wireRef w ctx}"])
  ) ([], [])
  result

/-- Emit instance statements with bus-compressed port maps. -/
def emitInstances (c : Circuit) (ctx : EmitCtx) (_allCircuits : List Circuit) : List String :=
  -- Precompute: wires driven by the parent (circuit inputs + gate outputs)
  let drivenByParent : Std.HashSet String :=
    let s := c.inputs.foldl (fun s w => s.insert w.name) {}
    c.gates.foldl (fun s g => s.insert g.output.name) s

  c.instances.map (fun inst =>
    let outputPorts := inst.portMap.filter (fun (_, w) =>
      !drivenByParent.contains w.name)
    let inputPorts := inst.portMap.filter (fun (_, w) =>
      drivenByParent.contains w.name)

    let inputStrs := compressPortMap inputPorts ctx
    let outputStrs := compressPortMap outputPorts ctx

    let portBody := if !inputStrs.isEmpty && !outputStrs.isEmpty then
      let inPart := ",\n    ".intercalate inputStrs
      let outPart := ",\n    ".intercalate outputStrs
      s!"    {inPart}\n    -> {outPart}"
    else
      let allPorts := inputStrs ++ outputStrs
      let part := ",\n    ".intercalate allPorts
      s!"    {part}"

    s!"  inst {inst.moduleName} {inst.instName}(\n{portBody}\n  )"
  )

/-! ## Top-Level Emission -/

/-- Emit a circuit as a `.shoumei` text string -/
def emitCircuit (c : Circuit) (allCircuits : List Circuit := []) : String :=
  let ctx := mkCtx c
  let header := emitHeader c ctx
  let annotations := emitAnnotations c
  let wireDecls := emitInternalWireDecls c ctx
  let gates := emitGates c ctx
  let instances := emitInstances c ctx allCircuits

  let bodyParts := wireDecls ++
    (if !wireDecls.isEmpty && (!gates.isEmpty || !instances.isEmpty) then [""] else []) ++
    gates ++
    (if !gates.isEmpty && !instances.isEmpty then [""] else []) ++
    instances

  let body := "\n".intercalate bodyParts

  if annotations.isEmpty then
    s!"{header} \{\n{body}\n}"
  else
    let anns := "\n".intercalate annotations
    s!"{header}\n{anns}\n\{\n{body}\n}"

end Shoumei.Codegen.ShoumeiEmit
