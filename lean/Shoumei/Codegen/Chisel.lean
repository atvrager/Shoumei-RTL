/-
Codegen/Chisel.lean - Chisel Code Generator (Hierarchical Mode)

Generates proper Chisel with Bundles, UInt, Decoupled interfaces from
annotated circuits. Uses signalGroups and interface bundles to produce
readable, typed Chisel output.

Design principles:
- Single-assign style (no when blocks)
- Typed signals (UInt, Bool, Bundles) from annotations
- ShoumeiReg wrapper for consistent register handling
- Bus reconstruction for vectorized operations
- Decoupled helper for ready/valid interfaces

Target: Chisel 7.x (Scala 2.13)
Output compiled to SystemVerilog via FIRRTL/CIRCT
-/

import Shoumei.DSL
import Shoumei.DSL.Interfaces
import Shoumei.Codegen.Common

namespace Shoumei.Codegen.Chisel

open Shoumei.Codegen

/-! ## Context and State -/

/-- Code generation context for Chisel.
    Tracks wire-to-signal mappings, bundle membership, and types. -/
structure Context where
  /-- Map wire to its parent signal group (if any) -/
  wireToGroup : List (Wire × SignalGroup)
  /-- Map wire to its bit index within the group -/
  wireToIndex : List (Wire × Nat)
  /-- Clock wires (implicit in Module) -/
  clockWires : List Wire
  /-- Reset wires (implicit in Module) -/
  resetWires : List Wire
  /-- Whether this is a sequential circuit (has DFFs) -/
  isSequential : Bool
  deriving Repr

/-! ## Bus Reconstruction Helpers -/

/-- Parse a wire name to extract base name and optional index.
    Examples: "data_31" → some ("data", 31), "valid" → none -/
def parseWireName (w : Wire) : Option (String × Nat) :=
  let name := w.name
  -- Find the last underscore
  match name.splitOn "_" with
  | [] => none
  | parts =>
      match parts.reverse with
      | [] => none
      | lastPart :: restReversed =>
          -- Check if last part is a number
          match lastPart.toNat? with
          | some idx =>
              let baseName := String.intercalate "_" restReversed.reverse
              some (baseName, idx)
          | none => none

/-- Group wires by base name (for bus reconstruction) -/
def groupWiresByBaseName (wires : List Wire) : List (String × List (Nat × Wire)) :=
  let parsed := wires.filterMap (fun w =>
    match parseWireName w with
    | some (base, idx) => some (base, idx, w)
    | none => none
  )
  -- Group by base name
  let grouped := parsed.foldl (fun acc (base, idx, w) =>
    match acc.find? (fun p => p.1 == base) with
    | some (_, existing) =>
        acc.filter (fun p => p.1 != base) ++ [(base, existing ++ [(idx, w)])]
    | none =>
        acc ++ [(base, [(idx, w)])]
  ) []
  grouped

/-- Check if a list of (index, wire) pairs forms a valid bus.
    Valid means: indices are contiguous from 0 to N-1 -/
def isValidBus (indexedWires : List (Nat × Wire)) : Bool :=
  if indexedWires.isEmpty then false
  else
    let indices := indexedWires.map (·.1)
    let sorted := indices.toArray.qsort (· < ·) |>.toList
    -- Check if sorted indices are [0, 1, 2, ..., n-1]
    sorted == List.range sorted.length

/-- Auto-detect signal groups from wire naming patterns -/
def autoDetectSignalGroups (wires : List Wire) : List SignalGroup :=
  let grouped := groupWiresByBaseName wires
  grouped.filterMap (fun (baseName, indexedWires) =>
    if isValidBus indexedWires then
      -- Sort wires by index to ensure correct order
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

/-- Build context from circuit -/
def mkContext (c : Circuit) : Context :=
  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let isSequential := c.gates.any (fun g => g.gateType == GateType.DFF)

  -- Auto-detect signal groups from internal wires
  let internalWires := findInternalWires c
  let autoDetectedGroups := autoDetectSignalGroups internalWires

  -- Combine explicit annotations with auto-detected groups
  -- Explicit annotations take precedence (come first)
  let allGroups := c.signalGroups ++ autoDetectedGroups

  -- Build wire-to-group mapping from all signal groups
  let wireToGroup := allGroups.flatMap (fun sg =>
    sg.wires.map (fun w => (w, sg))
  )

  -- Build wire-to-index mapping (bit index within bus)
  let wireToIndex := allGroups.flatMap (fun sg =>
    sg.wires.enum.map (fun (idx, w) => (w, idx))
  )

  { wireToGroup, wireToIndex, clockWires, resetWires, isSequential }

/-! ## Signal Type Helpers -/

/-- Convert SignalType to Chisel type string -/
def signalTypeToChisel (st : SignalType) : String :=
  match st with
  | .Bool => "Bool()"
  | .UInt w => s!"UInt({w}.W)"
  | .SInt w => s!"SInt({w}.W)"

/-- Get Chisel type for a signal group -/
def signalGroupToChisel (sg : SignalGroup) : String :=
  signalTypeToChisel sg.stype

/-! ## Wire Reference Generation -/

/-- Try to extract indexed signal name and index from a wire name like "next_0" -> ("next", 0) -/
def parseIndexedName (name : String) : Option (String × Nat) :=
  match name.splitOn "_" with
  | [base, idxStr] =>
      match idxStr.toNat? with
      | some idx => some (base, idx)
      | none => none
  | _ => none

/-- Deduplicate signal groups by name -/
private def dedupSignalGroups (sgs : List SignalGroup) : List SignalGroup :=
  sgs.foldl (fun acc sg =>
    if acc.any (fun s => s.name == sg.name) then acc
    else acc ++ [sg]
  ) []

/-- Check if a base name corresponds to a Vec declaration by looking for indexed pattern in signal groups -/
def isVecBase (ctx : Context) (baseName : String) : Bool :=
  -- Check if there are multiple signal groups with names matching baseName_0, baseName_1, etc.
  let signalGroups := dedupSignalGroups (ctx.wireToGroup.map (·.2))
  let matchingGroups := signalGroups.filter (fun sg =>
    match parseIndexedName sg.name with
    | some (base, _) => base == baseName
    | none => false
  )
  matchingGroups.length >= 2

/-- Generate reference to a wire in generated Chisel code.

    For wires in signal groups: use group name
    For bundle fields: use io.bundle_name.field_name
    For standalone wires: use wire name directly -/
def wireRef (ctx : Context) (_c : Circuit) (w : Wire) : String :=
  -- Check if this is clock or reset (should be implicit)
  if ctx.clockWires.contains w then
    "clock"
  else if ctx.resetWires.contains w then
    "reset.asBool"
  else
    -- Check if wire belongs to a signal group
    match ctx.wireToGroup.find? (fun (w', _) => w'.name == w.name) with
    | some (_, sg) =>
        -- Check if signal group matches indexed pattern AND a Vec exists for it
        match parseIndexedName sg.name with
        | some (baseName, vecIdx) =>
            if isVecBase ctx baseName then
              -- This signal group is part of a Vec - use Vec indexing
              -- For multi-bit signals within the Vec element, also include bit index
              if sg.width > 1 then
                match ctx.wireToIndex.find? (fun ⟨w', _⟩ => w'.name == w.name) with
                | some (_, bitIdx) => s!"{baseName}({vecIdx})({bitIdx})"
                | none => s!"{baseName}({vecIdx})"  -- Whole bus element
              else
                s!"{baseName}({vecIdx})"
            else
              -- Not part of a Vec, use normal signal group reference
              if sg.width > 1 then
                match ctx.wireToIndex.find? (fun ⟨w', _⟩ => w'.name == w.name) with
                | some (_, idx) => s!"{sg.name}({idx})"
                | none => sg.name
              else
                sg.name
        | none =>
            -- Not an indexed pattern - use normal signal group reference
            if sg.width > 1 then
              match ctx.wireToIndex.find? (fun ⟨w', _⟩ => w'.name == w.name) with
              | some (_, idx) => s!"{sg.name}({idx})"
              | none => sg.name
            else
              sg.name
    | none =>
        -- Check if it's a bundle field
        -- For now, just use the wire name
        -- TODO: Implement bundle field resolution
        w.name

/-! ## Bundle Generation -/

/-- Generate Chisel Bundle class definition from InterfaceBundle -/
def generateBundleClass (bundle : InterfaceBundle) : String :=
  let fields := bundle.signals.map (fun (fname, stype) =>
    s!"  val {fname} = {signalTypeToChisel stype}"
  )
  joinLines (["class " ++ bundle.name ++ "_bundle extends Bundle {"] ++ fields ++ ["}"])

/-- Generate Interfaces.scala file with all bundle definitions -/
def generateInterfacesFile (bundles : List InterfaceBundle) : String :=
  let header := joinLines [
    "// Auto-generated by Shoumei Codegen V2",
    "// Shared Bundle definitions for typed interfaces",
    "",
    "package generated",
    "",
    "import chisel3._",
    "import chisel3.util._",
    ""
  ]

  let bundleDefs := bundles.map generateBundleClass
  let bundlesStr := String.intercalate "\n\n" bundleDefs

  header ++ bundlesStr ++ "\n"

/-! ## Module IO Generation -/

/-- Generate IO declaration for a single wire with inferred type -/
def generateWireIO (ctx : Context) (c : Circuit) (w : Wire) (isInput : Bool) : Option String :=
  -- Skip implicit clock/reset
  if ctx.clockWires.contains w || ctx.resetWires.contains w then
    none
  else
    -- Skip DFF outputs when they're circuit outputs (registers handle these)
    let isDFFOutput := c.gates.any (fun g => g.gateType == GateType.DFF && g.output.name == w.name)
    if !isInput && isDFFOutput then
      none
    else
      -- Check if wire is part of a signal group
      match ctx.wireToGroup.find? (fun (w', _) => w'.name == w.name) with
      | some (_, sg) =>
          -- Only emit IO for the first wire in the group (we'll create one typed signal)
          if sg.wires.head? == some w then
            let chiselType := signalGroupToChisel sg
            let dir := if isInput then "Input" else "Output"
            some s!"  val {sg.name} = IO({dir}({chiselType}))"
          else
            none  -- Skip other wires in the group
      | none =>
          -- Standalone wire - emit as Bool
          let dir := if isInput then "Input" else "Output"
          some s!"  val {w.name} = IO({dir}(Bool()))"

/-- Generate IO declarations for all ports -/
def generateIO (ctx : Context) (c : Circuit) : String :=
  let inputDecls := c.inputs.filterMap (generateWireIO ctx c · true)
  let outputDecls := c.outputs.filterMap (generateWireIO ctx c · false)

  -- For sequential circuits (Module), clock and reset are implicit
  -- For combinational circuits (RawModule), they must be explicit
  -- But since combinational circuits don't have DFFs, they won't have clock/reset anyway
  -- So we can skip the implicit declarations entirely

  joinLines (inputDecls ++ outputDecls)

/-! ## Internal Signal Generation -/

/-- Generate Wire declaration for internal signals -/
def generateInternalWireDecl (ctx : Context) (_c : Circuit) (w : Wire) : Option String :=
  -- Check if wire is part of a signal group
  match ctx.wireToGroup.find? (fun (w', _) => w'.name == w.name) with
  | some (_, sg) =>
      -- Only emit for first wire in group
      if sg.wires.head? == some w then
        let chiselType := signalGroupToChisel sg
        some s!"  val {sg.name} = Wire({chiselType})"
      else
        none
  | none =>
      -- Standalone wire
      some s!"  val {w.name} = Wire(Bool())"

/-- Detect indexed signal group patterns and group them into Vec declarations -/
def detectVecPatterns (ctx : Context) (internalWires : List Wire) : List (String × Nat × String) × List Wire :=
  -- Extract unique signal groups from wireToGroup
  let signalGroups := dedupSignalGroups (ctx.wireToGroup.map (·.2))

  -- Group signal groups by base name (before underscore + number)
  let grouped := List.foldl (fun acc sg =>
    match parseIndexedName sg.name with
    | some (base, idx) =>
        match acc.find? (fun ((b, _, _), _) => b == base) with
        | some ((_, width, chiselType), indices) =>
            acc.filter (fun ((b, _, _), _) => b != base) ++ [((base, width, chiselType), indices ++ [(idx, sg)])]
        | none =>
            let chiselType := signalGroupToChisel sg
            acc ++ [((base, sg.width, chiselType), [(idx, sg)])]
    | none => acc
  ) [] signalGroups

  -- Check which groups form complete indexed sequences
  let vecDecls := List.filterMap (fun ((base, _width, chiselType), indexed) =>
    if indexed.length >= 2 then
      let sorted := indexed.toArray.qsort (fun a b => a.1 < b.1) |>.toList
      let maxIdx := sorted.getLast? |>.map (·.1) |>.getD 0
      let firstIdx := sorted.head? |>.map (·.1) |>.getD 999
      if sorted.length == maxIdx + 1 && firstIdx == 0 then
        some (base, maxIdx + 1, chiselType)
      else none
    else none
  ) grouped

  -- Collect signal group names that are handled by Vec declarations
  let handledGroups := List.filter (fun ((_base, _, _), indexed) =>
    if indexed.length >= 2 then
      let sorted := indexed.toArray.qsort (fun a b => a.1 < b.1) |>.toList
      let maxIdx := sorted.getLast? |>.map (·.1) |>.getD 0
      let firstIdx := sorted.head? |>.map (·.1) |>.getD 999
      sorted.length == maxIdx + 1 && firstIdx == 0
    else false
  ) grouped |>.flatMap (·.2) |>.map (·.2.name)

  -- Filter internal wires to remove those handled by Vec declarations
  let remainingWires := List.filter (fun w =>
    match ctx.wireToGroup.find? (fun (w', _) => w'.name == w.name) with
    | some (_, sg) => !List.contains handledGroups sg.name
    | none => true
  ) internalWires

  (vecDecls, remainingWires)

/-- Generate all internal wire declarations -/
def generateInternalWires (ctx : Context) (c : Circuit) : String :=
  let internalWires := findInternalWires c
  let (vecDecls, remainingWires) := detectVecPatterns ctx internalWires

  -- Generate Vec declarations
  let vecDeclStrs := vecDecls.map (fun (base, count, chiselType) =>
    s!"  val {base} = Wire(Vec({count}, {chiselType}))")

  -- Generate regular wire declarations
  let wireDeclStrs := remainingWires.filterMap (generateInternalWireDecl ctx c)

  joinLines (vecDeclStrs ++ wireDeclStrs)

/-! ## Gate Emission (with Bus Reconstruction) -/

/-- Generate Chisel operator for a gate type -/
def gateTypeToOperator (gt : GateType) : String :=
  match gt with
  | GateType.AND => "&"
  | GateType.OR => "|"
  | GateType.NOT => "~"
  | GateType.XOR => "^"
  | GateType.BUF => ""
  | GateType.MUX => "Mux"
  | GateType.DFF => ""

/-- Generate assignment for a combinational gate -/
def generateCombGate (ctx : Context) (c : Circuit) (g : Gate) : String :=
  let op := gateTypeToOperator g.gateType
  let outRef := wireRef ctx c g.output

  match g.gateType with
  | GateType.NOT =>
      match g.inputs with
      | [i0] => s!"  {outRef} := {op}{wireRef ctx c i0}"
      | _ => "  // ERROR: NOT gate should have 1 input"
  | GateType.BUF =>
      match g.inputs with
      | [i0] => s!"  {outRef} := {wireRef ctx c i0}"
      | _ => "  // ERROR: BUF gate should have 1 input"
  | GateType.MUX =>
      match g.inputs with
      | [in0, in1, sel] =>
          s!"  {outRef} := Mux({wireRef ctx c sel}, {wireRef ctx c in1}, {wireRef ctx c in0})"
      | _ => "  // ERROR: MUX gate should have 3 inputs"
  | GateType.DFF =>
      ""  -- DFFs handled separately
  | _ =>
      match g.inputs with
      | [i0, i1] =>
          s!"  {outRef} := {wireRef ctx c i0} {op} {wireRef ctx c i1}"
      | _ => "  // ERROR: Binary gate should have 2 inputs"

/-- Check if a gate's output is part of a bus (signal group) -/
def isPartOfBus (ctx : Context) (w : Wire) : Option SignalGroup :=
  ctx.wireToGroup.find? (fun (w', _) => w'.name == w.name) |>.map (·.2)

/-- Try to match a gate to a bus-wide operation pattern.
    Returns some (output_bus, input_buses, operation) if the gate is part of a bus pattern. -/
def matchBusPattern (ctx : Context) (g : Gate) : Option (SignalGroup × List (Option SignalGroup) × GateType) :=
  match isPartOfBus ctx g.output with
  | some outBus =>
      let inputBuses := g.inputs.map (fun inp => isPartOfBus ctx inp)
      some (outBus, inputBuses, g.gateType)
  | none => none

/-- Group gates by bus-wide operations.
    Returns list of (output_bus, gates) where gates operate on that bus. -/
def groupGatesByBus (ctx : Context) (gates : List Gate) : List (SignalGroup × List Gate) :=
  gates.foldl (fun acc g =>
    match matchBusPattern ctx g with
    | some (outBus, _, _) =>
        match acc.find? (fun (bus, _) => bus.name == outBus.name) with
        | some (_, existing) =>
            acc.filter (fun (bus, _) => bus.name != outBus.name) ++ [(outBus, existing ++ [g])]
        | none =>
            acc ++ [(outBus, [g])]
    | none => acc
  ) []

/-- Check if a list of gates forms a complete bus-wide operation -/
def isCompleteBusOp (_ctx : Context) (bus : SignalGroup) (gates : List Gate) : Bool :=
  gates.length == bus.width

/-- Generate bus-wide operation for gates that operate on all bits of a bus -/
def generateBusWideOp (ctx : Context) (_c : Circuit) (bus : SignalGroup) (gates : List Gate) : Option String :=
  if !isCompleteBusOp ctx bus gates then none
  else
    -- Get the first gate as template (all should have same structure)
    match gates.head? with
    | none => none
    | some firstGate =>
        match firstGate.gateType with
        | GateType.MUX =>
            -- Check if all inputs are buses or scalars
            match firstGate.inputs with
            | [in0, in1, sel] =>
                let in0Bus := isPartOfBus ctx in0
                let in1Bus := isPartOfBus ctx in1
                let selBus := isPartOfBus ctx sel

                -- Get the bit index of select within its bus (if any)
                let selIdx := ctx.wireToIndex.find? (fun (w', _) => w'.name == sel.name) |>.map (·.2)

                -- Generate based on pattern
                match in0Bus, in1Bus, selBus, selIdx with
                | some b0, some b1, none, _ =>
                    -- Bus mux with standalone scalar select: out := Mux(sel, in1, in0)
                    some s!"  {bus.name} := Mux({sel.name}, {b1.name}, {b0.name})"
                | some b0, some b1, some selB, some idx =>
                    -- Bus mux with indexed select: out := Mux(selBus(idx), in1, in0)
                    some s!"  {bus.name} := Mux({selB.name}({idx}), {b1.name}, {b0.name})"
                | _, _, _, _ =>
                    -- Fall through to individual gates
                    none
            | _ => none
        | GateType.BUF =>
            -- Simple bus assignment: out := in
            match firstGate.inputs with
            | [in0] =>
                let in0Bus := isPartOfBus ctx in0
                match in0Bus with
                | some b0 =>
                    -- Bus-wide assignment: out := in
                    some s!"  {bus.name} := {b0.name}"
                | none => none
            | _ => none
        | GateType.AND | GateType.OR | GateType.XOR =>
            match firstGate.inputs with
            | [in0, in1] =>
                let in0Bus := isPartOfBus ctx in0
                let in1Bus := isPartOfBus ctx in1
                let op := gateTypeToOperator firstGate.gateType

                match in0Bus, in1Bus with
                | some b0, some b1 =>
                    -- Bus-wide binary op: out := in0 op in1
                    some s!"  {bus.name} := {b0.name} {op} {b1.name}"
                | some b0, none =>
                    -- Bus op scalar: generate for loop
                    let forLoop := joinLines [
                      s!"  for (i <- 0 until {bus.width}) " ++ "{",
                      s!"    {bus.name}(i) := {b0.name}(i) {op} {in1.name}",
                      "  }"
                    ]
                    some forLoop
                | none, some b1 =>
                    -- Scalar op bus: generate for loop
                    let forLoop := joinLines [
                      s!"  for (i <- 0 until {bus.width}) " ++ "{",
                      s!"    {bus.name}(i) := {in0.name} {op} {b1.name}(i)",
                      "  }"
                    ]
                    some forLoop
                | none, none => none
            | _ => none
        | _ => none

/-- Detect consecutive constant assignments and convert to for loops -/
def consolidateConstantAssignments (assignments : List String) : List String :=
  -- Parse constant assignments: signal(i) := const
  let constPattern := assignments.filterMap (fun assign =>
    let parts := assign.trimAscii.toString.splitOn " := "
    match parts with
    | [lhs, rhs] =>
        -- Check if lhs has form signal(index)
        if lhs.contains "(" && lhs.contains ")" then
          let lhsParts := lhs.splitOn "("
          match lhsParts with
          | [sigName, idxWithParen] =>
              let idxStr := idxWithParen.dropEnd 1 |>.toString
              match idxStr.toNat? with
              | some idx =>
                  some (sigName.trimAscii.toString, idx, rhs.trimAscii.toString)
              | none => none
          | _ => none
        else none
    | _ => none
  )

  -- Group by (signal, constant)
  let grouped := constPattern.foldl (fun acc (sig, idx, const) =>
    let key := (sig, const)
    match acc.find? (fun ((k, _)) => k == key) with
    | some (_, indices) =>
        acc.filter (fun ((k, _)) => k != key) ++ [(key, indices ++ [idx])]
    | none =>
        acc ++ [(key, [idx])]
  ) []

  -- Generate for loops for consecutive sequences
  let forLoops := grouped.flatMap (fun ((sig, const), indices) =>
    if indices.length >= 4 then  -- Only optimize if 4+ consecutive
      let sorted := indices.toArray.qsort (· < ·) |>.toList
      -- Find consecutive ranges
      let ranges := sorted.foldl (fun acc idx =>
        match acc.getLast? with
        | some (startIdx, lastIdx) =>
            if idx == lastIdx + 1 then
              -- Extend current range
              acc.dropLast ++ [(startIdx, idx)]
            else
              -- Start new range
              acc ++ [(idx, idx)]
        | none =>
            [(idx, idx)]
      ) []

      -- Generate for loops for ranges of 4+
      ranges.filterMap (fun (startIdx, endIdx) =>
        if endIdx - startIdx + 1 >= 4 then
          let forLoop := joinLines [
            s!"  for (i <- {startIdx} to {endIdx}) " ++ "{",
            s!"    {sig}(i) := {const}",
            "  }"
          ]
          some ((startIdx, endIdx), forLoop)
        else none
      )
    else []
  )

  -- Collect all indices handled by for loops
  let handledIndices := forLoops.flatMap (fun ((startIdx, endIdx), _) =>
    List.range (endIdx - startIdx + 1) |>.map (· + startIdx)
  )

  -- Filter out assignments handled by for loops
  let remaining := assignments.filter (fun assign =>
    let parts := assign.trimAscii.toString.splitOn " := "
    match parts with
    | [lhs, _] =>
        if lhs.contains "(" && lhs.contains ")" then
          let lhsParts := lhs.splitOn "("
          match lhsParts with
          | [_, idxWithParen] =>
              let idxStr := idxWithParen.dropEnd 1 |>.toString
              match idxStr.toNat? with
              | some idx => !handledIndices.contains idx
              | none => true
          | _ => true
        else true
    | _ => true
  )

  remaining ++ (forLoops.map (·.2))

/-- Detect patterns in bus assignments that can be converted to for loops -/
def consolidateIntoForLoops (assignments : List String) : List String :=
  -- Try to match Mux pattern: name_i := Mux(sel(i), arg, other_i)
  let muxPattern := assignments.filterMap (fun assign =>
    -- Parse: "  next_0 := Mux(we(0), wr_data, reg_0)"
    let parts := assign.trimAscii.toString.splitOn " := Mux("
    match parts with
    | [lhs, rhs] =>
        match parseIndexedName lhs.trimAscii.toString with
        | some (outBase, outIdx) =>
            -- Parse the Mux arguments
            -- Expected: "sel(i), arg, other_i)"
            let args := rhs.dropEnd 1 |>.toString.splitOn ", "
            match args with
            | [sel, arg, other] =>
                -- Check if sel has form "name(i)"
                if sel.contains "(" && sel.contains ")" then
                  let selParts := sel.splitOn "("
                  match selParts with
                  | [selBase, selIdxWithParen] =>
                      let selIdx := selIdxWithParen.dropEnd 1 |>.toString
                      match selIdx.toNat? with
                      | some sIdx =>
                          if sIdx == outIdx then
                            -- Check if other has same index
                            match parseIndexedName (other.trimAscii.toString) with
                            | some (otherBase, otherIdx) =>
                                if otherIdx == outIdx then
                                  some (outBase, selBase, arg.trimAscii.toString, otherBase, outIdx)
                                else none
                            | none => none
                          else none
                      | none => none
                  | _ => none
                else none
            | _ => none
        | none => none
    | _ => none
  )

  -- Group by pattern (outBase, selBase, arg, otherBase)
  let grouped := muxPattern.foldl (fun acc (outB, selB, arg, otherB, idx) =>
    let key := (outB, selB, arg, otherB)
    match acc.find? (fun ((k, _)) => k == key) with
    | some (_, indices) =>
        acc.filter (fun ((k, _)) => k != key) ++ [(key, indices ++ [idx])]
    | none =>
        acc ++ [(key, [idx])]
  ) []

  -- Check which patterns form complete sequences and generate for loops
  let forLoops := grouped.filterMap (fun ((outB, selB, arg, otherB), indices) =>
    if indices.length >= 2 then
      -- Check if indices form a complete sequence 0..n-1
      let sorted := indices.toArray.qsort (· < ·) |>.toList
      let maxIdx := sorted.getLast? |>.getD 0
      if sorted.length == maxIdx + 1 && sorted.head? == some 0 then
        let forLoop := joinLines [
          s!"  for (i <- 0 until {maxIdx + 1}) " ++ "{",
          s!"    {outB}(i) := Mux({selB}(i), {arg}, {otherB}(i))",
          "  }"
        ]
        some (sorted, forLoop)
      else none
    else none
  )

  -- Collect indices that are handled by for loops
  let handledIndices := forLoops.flatMap (·.1)

  -- Filter out assignments that are now in for loops
  let remaining := assignments.filter (fun assign =>
    let parts := assign.trimAscii.toString.splitOn " := "
    match parts with
    | [lhs, _] =>
        match parseIndexedName (lhs.trimAscii.toString) with
        | some (_, idx) =>
            !handledIndices.contains idx
        | none => true
    | _ => true
  )

  remaining ++ (forLoops.map (·.2))

/-- Generate all combinational gate logic with bus-wide optimization -/
def generateCombGates (ctx : Context) (c : Circuit) : String :=
  let combGates := c.gates.filter (fun g => g.gateType != GateType.DFF)

  -- Group gates by bus operations
  let busGroups := groupGatesByBus ctx combGates

  -- Generate bus-wide operations (returns Option String)
  let busOpsWithGates := busGroups.filterMap (fun (bus, gates) =>
    match generateBusWideOp ctx c bus gates with
    | some op => some (op, gates)  -- Return both the operation and the gates
    | none => none
  )

  let busOps := busOpsWithGates.map (·.1)

  -- Find gates that were actually handled by successful bus-wide ops
  let handledGates := busOpsWithGates.flatMap (·.2)

  -- Generate individual assignments for remaining gates
  let remainingGates := combGates.filter (fun g =>
    !handledGates.any (fun hg => hg.output.name == g.output.name)
  )
  let individualOps := remainingGates.map (generateCombGate ctx c) |>.filter (· != "")

  -- Consolidate indexed patterns into for loops
  let allOps := busOps ++ individualOps
  let afterConstOpt := consolidateConstantAssignments allOps
  let consolidated := consolidateIntoForLoops afterConstOpt

  joinLines consolidated

/-! ## Module Instance Generation -/

/-- Check if a wire is used as input anywhere in the circuit.
    This includes gate inputs and instance port connections.
    Used to determine if a port is an output from an instance (driven into parent circuit). -/
def isWireUsedAsInput (c : Circuit) (w : Wire) : Bool :=
  -- Check if wire is used as input to any gate
  let usedInGates := c.gates.any (fun g => g.inputs.any (fun inp => inp.name == w.name))

  -- Check if wire is connected to any other instance (appears in portMap)
  let usedInInstances := c.instances.any (fun inst =>
    inst.portMap.any (fun (_, wire) => wire.name == w.name)
  )

  usedInGates || usedInInstances

/-- Extract base port name from Lean SV port names with digit suffixes.
    In Lean SV, each bit of a bus gets a separate port: a0, a1, a2, ... or a_0, a_1, ...
    This strips the digit suffix (and optional underscore) to get the base name for grouping.
    Examples: "a0" -> "a", "a_0" -> "a", "sum_15" -> "sum", "valid" -> "valid" -/
def stripPortDigitSuffix (pname : String) : String :=
  let chars := pname.toList
  let reversed := chars.reverse
  -- Drop trailing digits
  let withoutDigits := reversed.dropWhile (·.isDigit)
  -- Also drop trailing underscore if present
  -- For "branch_target_0" -> "branch_target" (default convention)
  -- Note: Some modules use trailing _ in signal group names (e.g., rs1_addr_)
  -- Those should use different portMap naming (e.g., "rs1_addr0" without _ before digit)
  let withoutUnderscore := match withoutDigits with
    | '_' :: rest => rest
    | other => other
  -- If we dropped anything and there are still chars, that's the base name
  if withoutUnderscore.length < reversed.length && withoutUnderscore.length > 0 then
    String.ofList withoutUnderscore.reverse
  else
    -- No digits at end, return as-is
    pname

/-- Extract base port name from various port naming formats.
    Handles bundled format with brackets and non-bundled with digit suffixes.
    Examples: "inputs[0]" -> "inputs", "in_0" -> "in", "in0" -> "in", "valid" -> "valid" -/
def extractPortBaseName (portName : String) : String :=
  -- Check for bundled format first: "inputs[123]"
  if portName.contains '[' then
    match portName.splitOn "[" with
    | baseName :: _ => baseName
    | [] => portName
  else
    -- Non-bundled format: use existing digit suffix stripping
    stripPortDigitSuffix portName

/-- Group portMap entries by the signal group of the connected wires.
    Returns list of (signalGroupName, portBaseName, list of portMap entries).
    Only includes entries where the wire belongs to a signal group. -/
def groupPortMapBySignalGroup (ctx : Context) (portMap : List (String × Wire))
    : List (String × String × List (String × Wire)) :=
  -- For each portMap entry, find the wire's signal group
  let withGroups := portMap.filterMap (fun entry@(portName, wire) =>
    match ctx.wireToGroup.find? (fun (w, _) => w.name == wire.name) with
    | some (_, sg) =>
        let portBase := extractPortBaseName portName
        some (sg.name, portBase, entry)
    | none => none
  )

  -- Group entries by (signalGroupName, portBaseName) pair
  withGroups.foldl (fun acc (sgName, portBase, entry) =>
    let key := (sgName, portBase)
    match acc.find? (fun ((sg, pb), _) => sg == sgName && pb == portBase) with
    | some (_, entries) =>
        acc.filter (fun ((sg, pb), _) => !(sg == sgName && pb == portBase)) ++
        [(key, entries ++ [entry])]
    | none =>
        acc ++ [(key, [entry])]
  ) [] |>.map (fun ((sg, pb), entries) => (sg, pb, entries))

/-- Generate Chisel module instantiation and port connections -/
def generateInstance (ctx : Context) (c : Circuit) (inst : CircuitInstance) : List String :=
  -- 1. Create module instantiation statement
  let instantiation := s!"  val {inst.instName} = Module(new {inst.moduleName}())"

  -- 2. Filter out clock and reset wires (implicit in Chisel modules)
  let filteredPortMap := inst.portMap.filter (fun (pname, wire) =>
    let baseName := extractPortBaseName pname
    baseName != "clock" && baseName != "reset" &&
    !ctx.clockWires.contains wire && !ctx.resetWires.contains wire
  )

  -- 3. Partition into wires that belong to signal groups vs standalone wires
  let (groupedEntries, standaloneEntries) := filteredPortMap.partition (fun (_, wire) =>
    ctx.wireToGroup.any (fun (w, _) => w.name == wire.name)
  )

  -- 4. Group the bus entries by signal group
  let busGroups := groupPortMapBySignalGroup ctx groupedEntries

  -- 5. Generate bus connections (one connection per signal group)
  let busConnections := busGroups.map (fun (sgName, portBase, entries) =>
    -- Determine direction: check if wire is produced by any gate in parent
    -- If wire is NOT produced by gates, it must be produced by instance = output
    -- If wire IS produced by gates or is input, it drives instance = input
    let isProducedByGate := entries.any (fun (_, w) =>
      c.gates.any (fun g => g.output.name == w.name)
    )
    let isCircuitInput := entries.any (fun (_, w) =>
      c.inputs.any (fun inp => inp.name == w.name)
    )
    let isInstanceInput := isProducedByGate || isCircuitInput

    -- Generate connection statement
    if isInstanceInput then
      s!"  {inst.instName}.{portBase} := {sgName}"
    else
      s!"  {sgName} := {inst.instName}.{portBase}"
  )

  -- 6. Generate standalone wire connections (one per wire)
  -- For standalone wires, use the FULL port name (don't strip indices)
  let standaloneConnections := standaloneEntries.map (fun (portName, wire) =>
    let wireRefStr := wireRef ctx c wire

    -- Same direction logic: check if wire is produced by gate or is input
    let isProducedByGate := c.gates.any (fun g => g.output.name == wire.name)
    let isCircuitInput := c.inputs.any (fun inp => inp.name == wire.name)
    let isInstanceInput := isProducedByGate || isCircuitInput

    if isInstanceInput then
      s!"  {inst.instName}.{portName} := {wireRefStr}"
    else
      s!"  {wireRefStr} := {inst.instName}.{portName}"
  )

  -- 7. Return instantiation + all connections
  [instantiation] ++ busConnections ++ standaloneConnections

/-- Generate all module instantiations -/
def generateInstances (ctx : Context) (c : Circuit) : String :=
  let instances := c.instances.flatMap (generateInstance ctx c)
  joinLines instances

/-! ## Register Generation (ShoumeiReg) -/

/-- Find all DFF gates in circuit -/
def findDFFs (c : Circuit) : List Gate :=
  c.gates.filter (fun g => g.gateType == GateType.DFF)

/-- Generate register declaration using ShoumeiReg helper -/
def generateRegisterDecl (ctx : Context) (c : Circuit) (g : Gate) : String :=
  match g.inputs with
  | [_d, clk, _rst] =>
      -- Check if this register output is also a circuit output
      let isCircuitOutput := c.outputs.any (fun w => w.name == g.output.name)

      -- Check if this register is part of a signal group
      match ctx.wireToGroup.find? (fun (w', _) => w'.name == g.output.name) with
      | some (_, sg) =>
          -- Part of a bus - only emit for first register in group
          if sg.wires.head? == some g.output then
            let clockRef := wireRef ctx c clk
            let resetRef := if ctx.isSequential then
              -- Module has implicit reset (type Reset, need to cast to AsyncReset)
              "reset.asAsyncReset"
            else
              -- RawModule needs explicit reset (shouldn't happen for DFFs, but fallback)
              match ctx.resetWires.head? with
              | some rw => rw.name
              | none => "reset"
            -- If it's a circuit output, don't add _reg suffix
            let regName := if isCircuitOutput then sg.name else s!"{sg.name}_reg"
            s!"  val {regName} = ShoumeiReg({sg.width}, {clockRef}, {resetRef})"
          else
            ""
      | none =>
          -- Standalone register
          let clockRef := wireRef ctx c clk
          let resetRef := if ctx.isSequential then
            "reset.asAsyncReset"
          else
            match ctx.resetWires.head? with
            | some rw => rw.name
            | none => "reset"
          let regName := if isCircuitOutput then g.output.name else s!"{g.output.name}_reg"
          s!"  val {regName} = ShoumeiReg(1, {clockRef}, {resetRef})"
  | _ =>
      "  // ERROR: DFF should have 3 inputs [d, clk, reset]"

/-- Generate register update assignments (single-assign style) -/
def generateRegisterUpdate (ctx : Context) (c : Circuit) (g : Gate) : String :=
  match g.inputs with
  | [d, _clk, _rst] =>
      -- Check if this register output is also a circuit output
      let isCircuitOutput := c.outputs.any (fun w => w.name == g.output.name)

      -- Check if register output is part of a signal group
      match ctx.wireToGroup.find? (fun (w', _) => w'.name == g.output.name) with
      | some (_, outputGroup) =>
          -- Part of a bus - only emit for first register
          if outputGroup.wires.head? == some g.output then
            -- For bus registers (ShoumeiReg with width > 1), reference the entire D input signal group
            let dName := match ctx.wireToGroup.find? (fun ⟨w', _⟩ => w'.name == d.name) with
              | some (_, dGroup) =>
                  -- Check if D signal group matches indexed pattern (e.g., "next_0" -> "next(0)")
                  match parseIndexedName dGroup.name with
                  | some (baseName, vecIdx) => s!"{baseName}({vecIdx})"
                  | none => dGroup.name
              | none => wireRef ctx c d  -- Fallback to wireRef for non-grouped wires
            let regName := if isCircuitOutput then outputGroup.name else s!"{outputGroup.name}_reg"
            s!"  {regName} := {dName}"
          else
            ""
      | none =>
          -- Standalone register
          let dName := wireRef ctx c d
          let regName := if isCircuitOutput then g.output.name else s!"{g.output.name}_reg"
          s!"  {regName} := {dName}"
  | _ =>
      ""

/-- Generate all register logic -/
def generateRegisters (ctx : Context) (c : Circuit) : String :=
  let dffs := findDFFs c
  let decls := dffs.map (generateRegisterDecl ctx c)
  let updates := dffs.map (generateRegisterUpdate ctx c)

  let declsStr := joinLines (decls.filter (· != ""))
  let updatesStr := joinLines (updates.filter (· != ""))

  if declsStr.isEmpty then
    ""
  else
    declsStr ++ "\n\n" ++ updatesStr

/-! ## Module Generation -/

/-- Generate complete Chisel module for a circuit -/
def generateModule (c : Circuit) : String :=
  let ctx := mkContext c

  -- Module or RawModule based on sequential/combinational
  let moduleType := if ctx.isSequential then "Module" else "RawModule"

  let header := joinLines [
    s!"// Auto-generated by Shoumei Codegen V2",
    s!"// Source: {c.name}",
    "",
    "package generated",
    "",
    "import chisel3._",
    "import chisel3.util._",
    "import shoumei.ShoumeiReg",
    "",
    "class " ++ c.name ++ " extends " ++ moduleType ++ " {"
  ]

  let io := generateIO ctx c
  let internalWires := generateInternalWires ctx c
  let combGates := generateCombGates ctx c
  let instances := generateInstances ctx c
  let registers := generateRegisters ctx c

  let body := joinLines [
    io,
    "",
    internalWires,
    "",
    combGates,
    "",
    instances,
    "",
    registers
  ]

  let footer := "}"

  joinLines [header, body, footer]

/-! ## Public API -/

/-- Generate Chisel code for a circuit -/
def toChisel (c : Circuit) : String :=
  generateModule c

end Shoumei.Codegen.Chisel
