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
  -- A circuit is sequential if it has DFFs or clock/reset wires
  -- (not just having instances -- combinational hierarchical modules like ALU32, Mux64x32 don't need clock)
  let isSequential := c.gates.any (fun g => g.gateType.isDFF) ||
                      !clockWires.isEmpty || !resetWires.isEmpty

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

/-- Extract base name from a wire name by stripping digit suffix.
    Examples: "addr_0" -> "addr", "sel_1" -> "sel", "data" -> "data" -/
def extractBaseName (wireName : String) : String :=
  let parts := wireName.splitOn "_"
  if parts.length >= 2 then
    let lastPart := parts.getLast!
    if lastPart.all (·.isDigit) then
      String.intercalate "_" (parts.dropLast)
    else
      wireName
  else
    wireName

/-- Check if binary gates (AND/OR/XOR) have uniform inputs.
    Returns false (needs UInt) if all gates have inputs from same two signal groups.
    Returns true (needs Vec) otherwise. -/
def hasUniformBinaryInputs (gates : List Gate) : Bool :=
  let inputPairs := gates.filterMap (fun g =>
    match g.inputs with
    | [in0, in1] => some (extractBaseName in0.name, extractBaseName in1.name)
    | _ => none
  )
  if inputPairs.length != gates.length then
    false  -- Some gates don't have 2 inputs, not uniform
  else
    let (input0Bases, input1Bases) := inputPairs.unzip
    let unique0 := input0Bases.eraseDups
    let unique1 := input1Bases.eraseDups
    -- If both inputs uniform (same source for all gates), bus-wide operation
    unique0.length == 1 && unique1.length == 1

/-- Check if a wire belongs to a signal group (bus) using context.
    This mirrors the `isPartOfBus` function used by `generateBusWideOp`. -/
def isPartOfBusCtx (ctx : Context) (w : Wire) : Bool :=
  ctx.wireToGroup.any (fun (w', _) => w'.name == w.name)

/-- Check if gates match a pattern that generateBusWideOp will ACTUALLY handle.
    Returns false (use UInt) if generateBusWideOp will succeed.
    Returns true (use Vec) if generateBusWideOp will fail (need individual assignments).

    This must match generateBusWideOp's logic exactly to avoid declaring UInt
    for signals that will be assigned bit-by-bit. -/
def willGenerateIndividualAssignments (ctx : Context) (_c : Circuit) (gates : List Gate) : Bool :=
  match gates.head? with
  | none => false  -- No gates, doesn't need Vec
  | some firstGate =>
      let allSameType := gates.all (fun g => g.gateType == firstGate.gateType)
      if !allSameType then
        true  -- Mixed gate types, needs Vec
      else
        match firstGate.gateType with
        | GateType.BUF =>
            -- BUF: generateBusWideOp succeeds only if input is part of the SAME signal group
            match firstGate.inputs with
            | [in0] =>
                let in0GroupName := ctx.wireToGroup.find? (fun (w', _) => w'.name == in0.name) |>.map (·.2.name)
                match in0GroupName with
                | some firstBusName =>
                    -- First gate input is in a bus. Check ALL inputs are in the SAME bus.
                    let allInSameBus := gates.all (fun g =>
                      match g.inputs with
                      | [inp] =>
                          let inpGroupName := ctx.wireToGroup.find? (fun (w', _) => w'.name == inp.name) |>.map (·.2.name)
                          inpGroupName == some firstBusName
                      | _ => false
                    )
                    !allInSameBus  -- All in same bus → bus-wide (UInt), otherwise → Vec
                | none =>
                    true  -- Input not in bus → generateBusWideOp returns none → Vec
            | _ => true
        | GateType.AND | GateType.OR | GateType.XOR =>
            -- Binary ops: generateBusWideOp needs at least one input bus
            -- Must check bus IDENTITY (same bus name), not just membership
            match firstGate.inputs with
            | [in0, in1] =>
                let in0GroupName := ctx.wireToGroup.find? (fun (w', _) => w'.name == in0.name) |>.map (·.2.name)
                let in1GroupName := ctx.wireToGroup.find? (fun (w', _) => w'.name == in1.name) |>.map (·.2.name)
                if in0GroupName.isSome || in1GroupName.isSome then
                  -- At least one input is a bus → check uniformity (same bus identity)
                  let allUniform := gates.all (fun g =>
                    match g.inputs with
                    | [gi0, gi1] =>
                        let gi0GroupName := ctx.wireToGroup.find? (fun (w', _) => w'.name == gi0.name) |>.map (·.2.name)
                        let gi1GroupName := ctx.wireToGroup.find? (fun (w', _) => w'.name == gi1.name) |>.map (·.2.name)
                        gi0GroupName == in0GroupName && gi1GroupName == in1GroupName
                    | _ => false
                  )
                  !allUniform  -- Uniform (same buses) → bus-wide/Cat (UInt), non-uniform → Vec
                else
                  true  -- Neither input is a bus → Vec
            | _ => true
        | GateType.MUX =>
            -- MUX: generateBusWideOp needs bus inputs with uniform pattern
            match firstGate.inputs with
            | [in0, in1, sel] =>
                let in0Bus := isPartOfBusCtx ctx in0
                let in1Bus := isPartOfBusCtx ctx in1
                -- generateBusWideOp for MUX requires BOTH in0 and in1 to be buses
                if in0Bus && in1Bus then
                  -- Check all gates have same bus pattern (allGatesUniform in generateBusWideOp)
                  let in0Group := ctx.wireToGroup.find? (fun (w', _) => w'.name == in0.name) |>.map (·.2.name)
                  let in1Group := ctx.wireToGroup.find? (fun (w', _) => w'.name == in1.name) |>.map (·.2.name)
                  let selGroup := ctx.wireToGroup.find? (fun (w', _) => w'.name == sel.name) |>.map (·.2.name)
                  let allGatesUniform := gates.all (fun g =>
                    match g.inputs with
                    | [g_in0, g_in1, g_sel] =>
                        let g0 := ctx.wireToGroup.find? (fun (w', _) => w'.name == g_in0.name) |>.map (·.2.name)
                        let g1 := ctx.wireToGroup.find? (fun (w', _) => w'.name == g_in1.name) |>.map (·.2.name)
                        let gs := ctx.wireToGroup.find? (fun (w', _) => w'.name == g_sel.name) |>.map (·.2.name)
                        g0 == in0Group && g1 == in1Group && gs == selGroup
                    | _ => false
                  )
                  if !allGatesUniform then
                    true  -- Non-uniform → Vec
                  else
                    -- Check the specific pattern generateBusWideOp handles
                    let selInBus := isPartOfBusCtx ctx sel
                    let selIdx := ctx.wireToIndex.find? (fun (w', _) => w'.name == sel.name) |>.map (·.2)
                    match selInBus, selIdx with
                    | false, _ => false  -- Scalar select with bus inputs → handled (UInt)
                    | true, some _ => false  -- Indexed select with bus inputs → handled (UInt)
                    | _, _ => true  -- Other patterns → not handled → Vec
                else
                  true  -- Both inputs not buses → generateBusWideOp returns none → Vec
            | _ => true
        | _ =>
            -- Other gates (NOT, DFF, etc.) don't match bus-wide patterns
            true  -- Needs Vec

/-- Check if an output signal group has individual bit assignments from gates.
    Returns true only if the output has gates doing individual bit computations,
    not just complete BUF copies from another signal group or bus-wide operations. -/
def outputHasIndividualBitAssignmentsHelper (ctx : Context) (c : Circuit) (sg : SignalGroup) : Bool :=
  if sg.width <= 1 then
    false  -- Single-bit outputs don't need Vec
  else
    let combGates := c.gates.filter (fun g => !g.gateType.isDFF)

    -- Get all gates that write to this signal group
    let outputGates := combGates.filter (fun g =>
      sg.wires.any (fun w => w.name == g.output.name)
    )

    if outputGates.isEmpty then
      false  -- No gates, doesn't need Vec
    else
      -- Check if this matches a bus-wide operation pattern in generateBusWideOp
      match outputGates.head? with
      | none => false  -- Should not happen since we checked isEmpty
      | some firstGate =>
          let allSameGateType := outputGates.all (fun g => g.gateType == firstGate.gateType)

          if !(allSameGateType && outputGates.length == sg.width) then
            true  -- Mixed types or incomplete coverage - needs Vec
          else
            -- All bits have same gate type and all bits covered
            -- Check if this will generate individual assignments or bus-wide operation
            willGenerateIndividualAssignments ctx c outputGates

/-- Check if a signal group should be declared as Vec(width, Bool()) instead of UInt(width.W).
    Uses context to check actual signal group membership of gate inputs,
    matching the logic of generateBusWideOp exactly. -/
def needsVecDeclarationHelper (ctx : Context) (sg : SignalGroup) (c : Circuit) : Bool :=
  if sg.width <= 1 then
    false  -- Single-bit signals don't need Vec
  else
    let combGates := c.gates.filter (fun g => !g.gateType.isDFF)

    -- Get all combinational gates that write to this signal group
    let outputGates := combGates.filter (fun g =>
      sg.wires.any (fun w => w.name == g.output.name)
    )

    if outputGates.isEmpty then
      false  -- No gates write to this signal group
    else
      -- Check if this matches a bus-wide operation pattern in generateBusWideOp
      match outputGates.head? with
      | none => false  -- Should not happen since we checked isEmpty
      | some firstGate =>
          let allSameGateType := outputGates.all (fun g => g.gateType == firstGate.gateType)

          if !(allSameGateType && outputGates.length == sg.width) then
            true  -- Mixed types or incomplete coverage - needs Vec
          else
            -- All bits have same gate type and all bits covered
            -- Check if this will generate individual assignments or bus-wide operation
            willGenerateIndividualAssignments ctx c outputGates

/-! ## Wire and Port Reference Helpers -/

/-- Check if a wire is used in non-DFF gates (i.e., in combinational logic) -/
def isWireUsedInCombLogic (c : Circuit) (wireName : String) : Bool :=
  c.gates.any (fun g =>
    g.gateType != GateType.DFF && g.inputs.any (fun inp => inp.name == wireName)
  )

/-- Get the IO port name for a wire, renaming if needed to avoid conflicts -/
def getIOPortName (_ctx : Context) (_c : Circuit) (w : Wire) : String :=
  -- For sequential modules, clock and reset are implicit in Chisel (Module class).
  -- When they're used in combinational logic, use the implicit signals directly
  -- rather than creating separate ports (which would cause port mismatches with Lean SV).
  w.name

/-- Generate reference to a wire in generated Chisel code.

    For wires in signal groups: use group name
    For bundle fields: use io.bundle_name.field_name
    For standalone wires: use wire name directly

    When reading from Vec signal groups (for instance port connections), automatically adds .asUInt -/
def wireRef (ctx : Context) (c : Circuit) (w : Wire) : String :=
  -- Check if this is clock or reset
  if ctx.clockWires.contains w then
    -- Always use Chisel's implicit clock (no separate port needed)
    "clock.asBool"
  else if ctx.resetWires.contains w then
    -- Always use Chisel's implicit reset (no separate port needed)
    "reset.asBool"
  else if ctx.isSequential && w.name == "clock" then
    "clock.asBool"
  else if ctx.isSequential && w.name == "reset" then
    "reset.asBool"
  else
    -- Check if wire belongs to a signal group
    match ctx.wireToGroup.find? (fun (w', _) => w'.name == w.name) with
    | some (_, sg) =>
        -- Check if this signal group is a DFF output (register)
        let isDFFOutput := sg.wires.any (fun sw =>
          c.gates.any (fun g => g.gateType == GateType.DFF && g.output.name == sw.name)
        )

        -- Check if signal group matches indexed pattern AND a Vec exists for it
        match parseIndexedName sg.name with
        | some (baseName, vecIdx) =>
            if isVecBase ctx baseName then
              -- This signal group is part of a Vec - use Vec indexing
              -- For multi-bit signals within the Vec element, also include bit index
              if sg.width > 1 then
                match ctx.wireToIndex.find? (fun ⟨w', _⟩ => w'.name == w.name) with
                | some (_, bitIdx) => s!"{baseName}({vecIdx})({bitIdx})"
                | none =>
                    -- Whole bus element - add .asUInt if it's a Vec
                    let baseRef := s!"{baseName}({vecIdx})"
                    if needsVecDeclarationHelper ctx sg c then s!"{baseRef}.asUInt" else baseRef
              else
                s!"{baseName}({vecIdx})"
            else
              -- Not part of a Vec, use normal signal group reference
              let sgRef := if isDFFOutput then s!"{sg.name}_reg" else sg.name
              if sg.width > 1 then
                match ctx.wireToIndex.find? (fun ⟨w', _⟩ => w'.name == w.name) with
                | some (_, idx) => s!"{sgRef}({idx})"
                | none =>
                    -- Add .asUInt if this is an output with Vec declaration
                    let isOutput := c.outputs.any (fun ow => sg.wires.any (fun sw => sw.name == ow.name))
                    if isOutput && outputHasIndividualBitAssignmentsHelper ctx c sg then
                      s!"{sgRef}.asUInt"
                    else
                      sgRef
              else
                sgRef
        | none =>
            -- Not an indexed pattern - use normal signal group reference
            let sgRef := if isDFFOutput then s!"{sg.name}_reg" else sg.name
            if sg.width > 1 then
              match ctx.wireToIndex.find? (fun ⟨w', _⟩ => w'.name == w.name) with
              | some (_, idx) => s!"{sgRef}({idx})"
              | none =>
                    -- Add .asUInt if this is an output with Vec declaration
                    let isOutput := c.outputs.any (fun ow => sg.wires.any (fun sw => sw.name == ow.name))
                    if isOutput && outputHasIndividualBitAssignmentsHelper ctx c sg then
                      s!"{sgRef}.asUInt"
                    else
                      sgRef
            else
              sgRef
    | none =>
        -- Check if this wire is a DFF output (register)
        -- If so, use _reg suffix since all registers now use that suffix
        let isDFFOutput := c.gates.any (fun g =>
          g.gateType == GateType.DFF && g.output.name == w.name
        )
        if isDFFOutput then
          s!"{w.name}_reg"
        else
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
  -- For Module (sequential circuits), skip wires named "clock" or "reset"
  -- They're available as implicit signals via Module's clock/reset
  else if ctx.isSequential && (w.name == "clock" || w.name == "reset") then
    none  -- Use clock.asBool / reset.asBool in wireRef instead of a separate port
  else
    -- Skip DFF outputs ONLY if they're NOT circuit outputs (internal register state)
    -- DFF outputs that ARE circuit outputs need to be exposed as IO ports
    let isDFFOutput := c.gates.any (fun g => g.gateType == GateType.DFF && g.output.name == w.name)
    let isCircuitOutput := c.outputs.any (fun out => out.name == w.name)
    if !isInput && isDFFOutput && !isCircuitOutput then
      none  -- Internal register, skip
    else
      -- Check if wire is part of a signal group
      match ctx.wireToGroup.find? (fun (w', _) => w'.name == w.name) with
      | some (_, sg) =>
          -- Only emit IO for the first wire in the group (we'll create one typed signal)
          if sg.wires.head? == some w then
            -- For outputs with individual bit assignments, use Vec type
            let chiselType := if !isInput && outputHasIndividualBitAssignmentsHelper ctx c sg && sg.width > 1 then
                               s!"Vec({sg.width}, Bool())"
                             else
                               signalGroupToChisel sg
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
def generateInternalWireDecl (ctx : Context) (c : Circuit) (w : Wire) : Option String :=
  -- Check if wire is part of a signal group
  match ctx.wireToGroup.find? (fun (w', _) => w'.name == w.name) with
  | some (_, sg) =>
      -- Only emit for first wire in group
      if sg.wires.head? == some w then
        -- Determine if we need Vec for individual bit assignments
        let useVec := needsVecDeclarationHelper ctx sg c
        let chiselType := if useVec then
                           s!"Vec({sg.width}, Bool())"
                         else
                           signalGroupToChisel sg
        some s!"  val {sg.name} = Wire({chiselType})"
      else
        none
  | none =>
      -- Skip standalone DFF outputs (handled by register declarations via _reg suffix)
      let isDFFOutput := c.gates.any (fun g => g.gateType == GateType.DFF && g.output.name == w.name)
      if isDFFOutput then
        none  -- Register declaration (ShoumeiReg) handles this wire
      else
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
  | GateType.DFF | GateType.DFF_SET => ""

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
  | GateType.DFF | GateType.DFF_SET =>
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

/-- Get reference to an entire signal group (for bus connections).
    Handles Vec indexing if the signal group is part of a Vec pattern.
    Example: "next_0" -> "next(0)", "wr_data" -> "wr_data" -/
def signalGroupRef (ctx : Context) (sgName : String) : String :=
  match parseIndexedName sgName with
  | some (baseName, vecIdx) =>
      if isVecBase ctx baseName then
        s!"{baseName}({vecIdx})"  -- Part of Vec - use Vec indexing
      else
        sgName  -- Not part of Vec - use signal group name directly
  | none => sgName  -- No index pattern - use as-is

/-- Get reference to a signal group for bus operations, adding .asUInt if it's declared as Vec. -/
def signalGroupRefForBusOp (ctx : Context) (c : Circuit) (sg : SignalGroup) : String :=
  let baseRef := signalGroupRef ctx sg.name
  -- Check if this signal group is declared as Vec (needs .asUInt for bus ops)
  if needsVecDeclarationHelper ctx sg c then
    s!"{baseRef}.asUInt"
  else
    baseRef

/-- Generate bus-wide operation for gates that operate on all bits of a bus -/
def generateBusWideOp (ctx : Context) (_c : Circuit) (bus : SignalGroup) (gates : List Gate) : Option String :=
  if !isCompleteBusOp ctx bus gates then none
  else
    -- Get the first gate as template (all should have same structure)
    match gates.head? with
    | none => none
    | some firstGate =>
        -- All gates must have the same type for a bus-wide operation
        let allSameType := gates.all (fun g => g.gateType == firstGate.gateType)
        if !allSameType then none
        else
        -- All gates must have the same input-bus membership pattern
        -- (e.g., if firstGate has inputs from [none, some(count_not)],
        --  ALL gates must have the same pattern, not [some(other), some(count_not)])
        let allUniformInputs := gates.all (fun g =>
          g.inputs.length == firstGate.inputs.length &&
          (g.inputs.zip firstGate.inputs).all (fun (gi, fi) =>
            match isPartOfBus ctx gi, isPartOfBus ctx fi with
            | some sg1, some sg2 => sg1.name == sg2.name
            | none, none => true
            | _, _ => false
          )
        )
        if !allUniformInputs then none
        else
        match firstGate.gateType with
        | GateType.MUX =>
            -- Check if all inputs are buses or scalars
            match firstGate.inputs with
            | [in0, in1, sel] =>
                let in0Bus := isPartOfBus ctx in0
                let in1Bus := isPartOfBus ctx in1
                let selBus := isPartOfBus ctx sel

                -- Check if ALL gates have inputs from the SAME buses (uniform inputs)
                -- This is critical for bus-wide MUX operations
                let allGatesUniform := gates.all (fun g =>
                  match g.inputs with
                  | [g_in0, g_in1, g_sel] =>
                      let g_in0Bus := isPartOfBus ctx g_in0
                      let g_in1Bus := isPartOfBus ctx g_in1
                      let g_selBus := isPartOfBus ctx g_sel
                      -- Check if this gate's inputs are from the same buses as firstGate
                      (match g_in0Bus, in0Bus with
                       | some gb0, some b0 => gb0.name == b0.name
                       | none, none => true
                       | _, _ => false) &&
                      (match g_in1Bus, in1Bus with
                       | some gb1, some b1 => gb1.name == b1.name
                       | none, none => true
                       | _, _ => false) &&
                      (match g_selBus, selBus with
                       | some gbs, some bs => gbs.name == bs.name
                       | none, none => true
                       | _, _ => false)
                  | _ => false
                )

                if !allGatesUniform then
                  none  -- Gates have inputs from different buses, use individual assignments
                else
                  -- Get the bit index of select within its bus (if any)
                  let selIdx := ctx.wireToIndex.find? (fun (w', _) => w'.name == sel.name) |>.map (·.2)

                  -- Generate based on pattern
                  match in0Bus, in1Bus, selBus, selIdx with
                  | some b0, some b1, none, _ =>
                      -- Bus mux with standalone scalar select: out := Mux(sel, in1, in0)
                      let outRef := signalGroupRef ctx bus.name
                      let in1Ref := signalGroupRefForBusOp ctx _c b1
                      let in0Ref := signalGroupRefForBusOp ctx _c b0
                      some s!"  {outRef} := Mux({sel.name}, {in1Ref}, {in0Ref})"
                  | some b0, some b1, some selB, some idx =>
                      -- Bus mux with indexed select: out := Mux(selBus(idx), in1, in0)
                      let outRef := signalGroupRef ctx bus.name
                      let in1Ref := signalGroupRefForBusOp ctx _c b1
                      let in0Ref := signalGroupRefForBusOp ctx _c b0
                      some s!"  {outRef} := Mux({selB.name}({idx}), {in1Ref}, {in0Ref})"
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
                    let outRef := signalGroupRef ctx bus.name
                    let inRef := signalGroupRefForBusOp ctx _c b0
                    some s!"  {outRef} := {inRef}"
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
                    let outRef := signalGroupRef ctx bus.name
                    let in0Ref := signalGroupRefForBusOp ctx _c b0
                    let in1Ref := signalGroupRefForBusOp ctx _c b1
                    some s!"  {outRef} := {in0Ref} {op} {in1Ref}"
                | some b0, none =>
                    -- Bus op scalar: use Cat to build result
                    -- Check if the scalar input is the same across all gates
                    let scalarIsUniform := gates.all (fun g =>
                      match g.inputs with
                      | [_, scalar] => scalar.name == in1.name
                      | _ => false
                    )
                    if scalarIsUniform then
                      let outRef := signalGroupRef ctx bus.name
                      let in0Ref := if needsVecDeclarationHelper ctx b0 _c then
                                     signalGroupRef ctx b0.name
                                   else
                                     signalGroupRefForBusOp ctx _c b0
                      let in0Access := if needsVecDeclarationHelper ctx b0 _c then
                                        s!"{in0Ref}(i)"
                                      else
                                        in0Ref
                      let forLoop := joinLines [
                        s!"  {outRef} := Cat(",
                        s!"    (0 until {bus.width}).reverse.map(i => {in0Access} {op} {in1.name})",
                        "  )"
                      ]
                      some forLoop
                    else
                      -- Scalar varies per bit: build Cat with per-gate expressions
                      let sortedGates := gates.toArray.qsort (fun g1 g2 =>
                        match ctx.wireToIndex.find? (fun ⟨w', _⟩ => w'.name == g1.output.name),
                              ctx.wireToIndex.find? (fun ⟨w', _⟩ => w'.name == g2.output.name) with
                        | some (_, i1), some (_, i2) => i1 < i2
                        | _, _ => g1.output.name < g2.output.name
                      ) |>.toList
                      let outRef := signalGroupRef ctx bus.name
                      let perBitExprs := sortedGates.reverse.map (fun g =>
                        match g.inputs with
                        | [busIn, scalarIn] =>
                            let busRef := wireRef ctx _c busIn
                            s!"{busRef} {op} {scalarIn.name}"
                        | _ => "false.B"
                      )
                      let catBody := String.intercalate ", " perBitExprs
                      some s!"  {outRef} := Cat({catBody})"
                | none, some b1 =>
                    -- Scalar op bus: use Cat to build result
                    -- Check if the scalar input is the same across all gates
                    let scalarIsUniform := gates.all (fun g =>
                      match g.inputs with
                      | [scalar, _] => scalar.name == in0.name
                      | _ => false
                    )
                    if scalarIsUniform then
                      let outRef := signalGroupRef ctx bus.name
                      let in1Ref := if needsVecDeclarationHelper ctx b1 _c then
                                     signalGroupRef ctx b1.name
                                   else
                                     signalGroupRefForBusOp ctx _c b1
                      let in1Access := if needsVecDeclarationHelper ctx b1 _c then
                                        s!"{in1Ref}(i)"
                                      else
                                        in1Ref
                      let forLoop := joinLines [
                        s!"  {outRef} := Cat(",
                        s!"    (0 until {bus.width}).reverse.map(i => {in0.name} {op} {in1Access})",
                        "  )"
                      ]
                      some forLoop
                    else
                      -- Scalar varies per bit: build Cat with per-gate expressions
                      let sortedGates := gates.toArray.qsort (fun g1 g2 =>
                        match ctx.wireToIndex.find? (fun ⟨w', _⟩ => w'.name == g1.output.name),
                              ctx.wireToIndex.find? (fun ⟨w', _⟩ => w'.name == g2.output.name) with
                        | some (_, i1), some (_, i2) => i1 < i2
                        | _, _ => g1.output.name < g2.output.name
                      ) |>.toList
                      let outRef := signalGroupRef ctx bus.name
                      let perBitExprs := sortedGates.reverse.map (fun g =>
                        match g.inputs with
                        | [scalarIn, busIn] =>
                            let busRef := wireRef ctx _c busIn
                            s!"{scalarIn.name} {op} {busRef}"
                        | _ => "false.B"
                      )
                      let catBody := String.intercalate ", " perBitExprs
                      some s!"  {outRef} := Cat({catBody})"
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

  -- Collect all (signal, index) pairs handled by for loops
  let handledEntries : List (String × Nat) := forLoops.flatMap (fun ((startIdx, endIdx), forStr) =>
    -- Extract signal name from the for loop body
    -- For loop format: "  for (i <- start to end) {\n    sig(i) := const\n  }"
    let sigName := match forStr.splitOn "(i)" with
      | sigPart :: _ =>
          -- Extract just the signal name from "  for ... {\n    sigName"
          match sigPart.splitOn "\n" with
          | _ :: bodyPart :: _ => bodyPart.trimAscii.toString
          | _ => ""
      | _ => ""
    List.range (endIdx - startIdx + 1) |>.map (fun offset => (sigName, offset + startIdx))
  )

  -- Filter out assignments handled by for loops (checking both signal name AND index)
  let remaining := assignments.filter (fun assign =>
    let parts := assign.trimAscii.toString.splitOn " := "
    match parts with
    | [lhs, _] =>
        if lhs.contains "(" && lhs.contains ")" then
          let lhsParts := lhs.splitOn "("
          match lhsParts with
          | [sigNameRaw, idxWithParen] =>
              let sigName := sigNameRaw.trimAscii.toString
              let idxStr := idxWithParen.dropEnd 1 |>.toString
              match idxStr.toNat? with
              | some idx => !handledEntries.contains (sigName, idx)
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

/-- Generate all combinational gate logic with bus-wide optimization.
    excludedWires: wire names already driven by instance outputs (skip to avoid double-assignment) -/
def generateCombGates (ctx : Context) (c : Circuit) (excludedWires : List String := []) : String :=
  let combGates := c.gates.filter (fun g => !g.gateType.isDFF)

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
  -- Also exclude gates whose outputs are already driven by instance connections
  let remainingGates := combGates.filter (fun g =>
    !handledGates.any (fun hg => hg.output.name == g.output.name) &&
    !excludedWires.contains g.output.name
  )
  let individualOps := remainingGates.map (generateCombGate ctx c) |>.filter (· != "")

  -- Consolidate constant assignments (but skip for loop consolidation to avoid bit extraction LHS)
  let allOps := busOps ++ individualOps
  let afterConstOpt := consolidateConstantAssignments allOps
  -- Disabled: consolidateIntoForLoops creates bit extraction assignments which don't work in Chisel
  -- let consolidated := consolidateIntoForLoops afterConstOpt

  joinLines afterConstOpt

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

/-- Determine if a port is an INPUT on the sub-module by looking up its Circuit definition.
    Converts portMap port name to match sub-module wire names, then checks inputs/outputs.
    Returns: some true = input, some false = output, none = sub-module not found. -/
def isSubModuleInput (allCircuits : List Circuit) (moduleName : String) (portBase : String) : Option Bool :=
  match allCircuits.find? (fun sc => sc.name == moduleName) with
  | none => none  -- Sub-module not in allCircuits
  | some subMod =>
      -- Normalize: strip trailing underscores to handle "agu_address_" vs "agu_address" mismatches
      -- (mkWires "agu_address_" 32 creates "agu_address__0" → extractBaseName → "agu_address_")
      let normalize (s : String) : String :=
        let chars := s.toList.reverse.dropWhile (· == '_') |>.reverse
        if chars.isEmpty then s else String.ofList chars
      let normalizedPortBase := normalize portBase
      -- Check if portBase matches any input wire's base name
      let isInput := subMod.inputs.any (fun w => normalize (extractBaseName w.name) == normalizedPortBase)
      -- Check if portBase matches any output wire's base name
      let isOutput := subMod.outputs.any (fun w => normalize (extractBaseName w.name) == normalizedPortBase)
      if isInput && !isOutput then some true
      else if isOutput && !isInput then some false
      else if isInput && isOutput then some true  -- Ambiguous, assume input (safer)
      else none  -- Not found in either list

/-- Determine port direction for an instance connection.
    Priority: 1. Sub-module definition, 2. Wire source analysis, 3. Port name heuristic, 4. Default. -/
def determinePortDirection (_ctx : Context) (c : Circuit) (allCircuits : List Circuit)
    (inst : CircuitInstance) (portBase : String) (wire : Wire) : Bool :=
  -- 1. Check sub-module definition (most reliable)
  match isSubModuleInput allCircuits inst.moduleName portBase with
  | some isInput => isInput
  | none =>
      -- 2. Check if wire is produced by a gate or is a circuit input → instance INPUT
      let isProducedByGate := c.gates.any (fun g => g.output.name == wire.name)
      let isCircuitInput := c.inputs.any (fun inp => inp.name == wire.name)
      if isProducedByGate || isCircuitInput then true
      else
        -- 3. Check if wire is a circuit output → instance OUTPUT
        let isCircuitOutput := c.outputs.any (fun out => out.name == wire.name)
        if isCircuitOutput then false
        else
          -- 3b. For sub-modules not in allCircuits: check if wire is ONLY consumed
          -- (used as gate input or by other instances) and NOT produced by any gate.
          -- If so, this instance must be producing it (instance OUTPUT).
          let subModKnown := allCircuits.any (fun sc => sc.name == inst.moduleName)
          if !subModKnown then
            let isConsumedByGate := c.gates.any (fun g =>
              g.inputs.any (fun inp => inp.name == wire.name))
            let isConsumedByOtherInstance := c.instances.any (fun otherInst =>
              otherInst.instName != inst.instName &&
              otherInst.portMap.any (fun (_, w) => w.name == wire.name))
            if isConsumedByGate || isConsumedByOtherInstance then false
            else true  -- Unknown sub-module, wire not consumed elsewhere → assume input
          else
          -- 4. Port name heuristics (expanded)
          let containsAddr := (portBase.splitOn "addr").length > 1
          let portNameSuggestsInput :=
            portBase.startsWith "in" || portBase == "d" || portBase.startsWith "d_" ||
            portBase.startsWith "a" || portBase.startsWith "b" ||
            portBase.startsWith "sel" || containsAddr ||
            portBase.startsWith "write" || portBase.startsWith "en" ||
            portBase.startsWith "enq_data" || portBase.startsWith "enq_valid" ||
            portBase.startsWith "deq_ready" ||
            portBase.startsWith "wr_" || portBase.startsWith "rd_tag"
          let portNameSuggestsOutput :=
            portBase.startsWith "out" || portBase == "q" || portBase.startsWith "q_" ||
            portBase.startsWith "result" ||
            portBase.startsWith "deq_data" || portBase.startsWith "deq_valid" ||
            portBase.startsWith "enq_ready" || portBase.startsWith "rd_data" ||
            portBase.startsWith "read_data"
          if portNameSuggestsInput && !portNameSuggestsOutput then true
          else if portNameSuggestsOutput && !portNameSuggestsInput then false
          else true  -- Default: assume input (write to instance port - safer than reading)

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

/-- Extract numeric index from a bracket-notation port name.
    Example: "in0[31]" → some 31, "out[5]" → some 5, "valid" → none -/
def extractBracketIndex (portName : String) : Option Nat :=
  match portName.splitOn "[" with
  | [_, rest] =>
      let idxStr := String.ofList (rest.toList.takeWhile (· != ']'))
      idxStr.toNat?
  | _ => none

/-- Convert bracket notation in port names to Chisel parenthesis notation.
    Example: "alloc_oldPhysRd[0]" -> "alloc_oldPhysRd(0)" -/
def convertPortNameToChisel (portName : String) : String :=
  portName.replace "[" "(" |>.replace "]" ")"

/-- Generate Chisel module instantiation and port connections -/
def generateInstance (ctx : Context) (c : Circuit) (allCircuits : List Circuit) (inst : CircuitInstance) : List String :=
  -- 1. Create module instantiation statement
  let instantiation := s!"  val {inst.instName} = Module(new {inst.moduleName}())"

  -- 2. Filter out clock and reset wires (implicit in Chisel modules)
  --    But keep entries where the sub-module has renamed "reset"→"reset_in" or "clock"→"clock_in"
  let (clockResetEntries, nonClockResetEntries) := inst.portMap.partition (fun (_, wire) =>
    ctx.clockWires.contains wire || ctx.resetWires.contains wire
  )
  -- Also filter entries with clock/reset port names even if wire isn't detected as clock/reset
  let filteredPortMap := nonClockResetEntries.filter (fun (pname, _) =>
    let baseName := extractPortBaseName pname
    baseName != "clock" && baseName != "reset"
  )

  -- 2b. Check if filtered clock/reset entries need explicit connections
  --     For sequential sub-modules (Chisel Module), clock/reset are implicit - no explicit connection needed.
  --     For RawModule sub-modules that use clock/reset in comb logic, generate explicit port connections.
  let renamedClockResetConnections := clockResetEntries.filterMap (fun (pname, _wire) =>
    let baseName := extractPortBaseName pname
    if baseName == "reset" || baseName == "clock" then
      match allCircuits.find? (fun sc => sc.name == inst.moduleName) with
      | none => none
      | some subMod =>
          -- Check if sub-module is sequential (will be generated as Chisel Module with implicit clock/reset)
          let subClockWires := findClockWires subMod
          let subResetWires := findResetWires subMod
          let subIsSequential := subMod.gates.any (fun g => g.gateType.isDFF) ||
                                 !subClockWires.isEmpty || !subResetWires.isEmpty
          if subIsSequential then
            -- Sequential sub-module: Chisel propagates clock/reset implicitly, no explicit connection needed
            none
          else if isWireUsedInCombLogic subMod baseName then
            -- Non-sequential sub-module uses clock/reset in combinational logic → needs explicit port
            let wireRefStr := if baseName == "reset" then "reset.asBool" else "clock.asBool"
            some s!"  {inst.instName}.{baseName} := {wireRefStr}"
          else
            none  -- Implicit propagation handles it
    else
      none
  )

  -- 3. Partition into wires that belong to signal groups vs standalone wires
  let (groupedEntries, standaloneEntries) := filteredPortMap.partition (fun (_, wire) =>
    ctx.wireToGroup.any (fun (w, _) => w.name == wire.name)
  )

  -- 4. Group the bus entries by signal group
  let busGroups := groupPortMapBySignalGroup ctx groupedEntries

  -- 5. Generate bus connections (one connection per signal group)
  let busConnections := busGroups.map (fun (sgName, portBase, entries) =>
    -- Use determinePortDirection for reliable direction detection
    let firstWire := entries.head?.map (·.2) |>.getD (Wire.mk "")
    let isInstanceInput := determinePortDirection ctx c allCircuits inst portBase firstWire

    -- Get proper reference for entire signal group (handles Vec indexing)
    let sgRef := signalGroupRef ctx sgName

    -- Generate connection statement
    if isInstanceInput then
      -- Add .asUInt if source signal group is Vec (instance port expects UInt)
      let sourceSg := ctx.wireToGroup.find? (fun (_, sg) => sg.name == sgName)
      let sourceIsVec := match sourceSg with
        | some (_, sg) => needsVecDeclarationHelper ctx sg c
        | none => false
      let srcRef := if sourceIsVec then s!"{sgRef}.asUInt" else sgRef
      s!"  {inst.instName}.{portBase} := {srcRef}"
    else
      -- For instance outputs, add .asUInt if receiving signal is not Vec
      let receivingSg := ctx.wireToGroup.find? (fun (_, sg) => sg.name == sgName)
      let needsAsUInt := match receivingSg with
        | some (_, sg) => !needsVecDeclarationHelper ctx sg c
        | none => false
      let instRef := if needsAsUInt then
                      s!"{inst.instName}.{portBase}.asUInt"
                    else
                      s!"{inst.instName}.{portBase}"
      s!"  {sgRef} := {instRef}"
  )

  -- 6. Group standalone entries by port base name (for bundled ports like alloc_oldPhysRd[0..5])
  --    Only group entries that use bracket notation (not underscore/digit suffixes)
  let standaloneGrouped : List (String × List (String × Wire)) :=
    standaloneEntries.foldl (fun acc (portName, wire) =>
      -- Only group if port name contains brackets (bundled notation)
      if portName.contains '[' then
        let baseName := extractPortBaseName portName
        match acc.find? (fun (base, _) => base == baseName) with
        | some (_, entries) =>
            acc.filter (fun (base, _) => base != baseName) ++ [(baseName, entries ++ [(portName, wire)])]
        | none =>
            acc ++ [(baseName, [(portName, wire)])]
      else
        -- Not bundled - treat as separate entry with full name as base
        acc ++ [(portName, [(portName, wire)])]
    ) []

  -- 7. Generate standalone wire connections (uses determinePortDirection)
  let standaloneConnections := standaloneGrouped.flatMap (fun (baseName, entries) =>
    if entries.length > 1 then
      -- Multiple entries with same base - generate Cat expression
      -- Sort by numeric index (not lexicographic) to handle indices >= 10 correctly
      let sortedEntries := entries.toArray.qsort (fun (p1, _) (p2, _) =>
        match extractBracketIndex p1, extractBracketIndex p2 with
        | some i1, some i2 => i1 < i2
        | some _, none => true
        | none, some _ => false
        | none, none => p1 < p2
      ) |>.toList
      let wireRefs := sortedEntries.map (fun (_, w) => wireRef ctx c w)
      let catExpr := "Cat(" ++ String.intercalate ", " wireRefs.reverse ++ ")"  -- Cat is MSB-first

      -- Determine direction using unified helper
      let (_, firstWire) := sortedEntries.head!
      let isInstanceInput := determinePortDirection ctx c allCircuits inst baseName firstWire

      if isInstanceInput then
        [s!"  {inst.instName}.{baseName} := {catExpr}"]
      else
        -- Output from instance - need to extract bits
        sortedEntries.map (fun (portName, wire) =>
          let wireRefStr := wireRef ctx c wire
          let chiselPortName := convertPortNameToChisel portName
          s!"  {wireRefStr} := {inst.instName}.{chiselPortName}"
        )
    else
      -- Single entry - use direct connection with unified direction detection
      entries.map (fun (portName, wire) =>
        let wireRefStr := wireRef ctx c wire
        let chiselPortName := convertPortNameToChisel portName
        let portBaseForDir := extractPortBaseName portName
        let isInstanceInput := determinePortDirection ctx c allCircuits inst portBaseForDir wire

        if isInstanceInput then
          s!"  {inst.instName}.{chiselPortName} := {wireRefStr}"
        else
          s!"  {wireRefStr} := {inst.instName}.{chiselPortName}"
      )
  )

  -- 8. Generate DontCare for standalone sub-module input ports missing from portMap
  --    Only handles truly standalone single-wire ports (e.g., "one", "zero")
  --    Skips wires that are part of any signal group (those become bus ports in Chisel)
  let dontCareConnections := match allCircuits.find? (fun sc => sc.name == inst.moduleName) with
    | none => []
    | some subMod =>
        -- Build sub-module's signal group wire set (explicit annotations + auto-detected)
        let subModInternalWires := findInternalWires subMod
        let subModAutoGroups := autoDetectSignalGroups subModInternalWires
        let allSubModGroups := subMod.signalGroups ++ subModAutoGroups
        let allGroupedWireNames := allSubModGroups.flatMap (fun sg => sg.wires.map (·.name))
        -- Also check auto-grouped input/output wires (signal groups from IO wires)
        let ioGroupedWireNames := (subMod.inputs ++ subMod.outputs).filter (fun w =>
          extractBaseName w.name != w.name  -- Has _N suffix → part of a bus
        ) |>.map (·.name)
        let allGroupedNames := (allGroupedWireNames ++ ioGroupedWireNames).eraseDups
        -- Find truly standalone input wires: not in any signal group, not clock/reset, input-only
        let standaloneInputs := subMod.inputs.filter (fun w =>
          !allGroupedNames.contains w.name &&
          w.name != "clock" && w.name != "reset" &&
          !subMod.outputs.any (fun ow => ow.name == w.name)
        )
        -- Check if these ports appear in the portMap
        standaloneInputs.filter (fun w =>
          !inst.portMap.any (fun (pname, _) => pname == w.name) &&
          !inst.portMap.any (fun (pname, _) => extractPortBaseName pname == w.name)
        ) |>.map (fun w =>
          s!"  {inst.instName}.{w.name} := DontCare"
        )

  -- 9. Return instantiation + all connections
  [instantiation] ++ busConnections ++ standaloneConnections ++ renamedClockResetConnections ++ dontCareConnections

/-- Generate all module instantiations -/
def generateInstances (ctx : Context) (c : Circuit) (allCircuits : List Circuit) : String :=
  let instances := c.instances.flatMap (generateInstance ctx c allCircuits)
  joinLines instances

/-! ## Register Generation (ShoumeiReg) -/

/-- Find all DFF gates in circuit -/
def findDFFs (c : Circuit) : List Gate :=
  c.gates.filter (fun g => g.gateType.isDFF)

/-- Compute the init value for a signal group by checking which wires are DFF_SET.
    Returns the integer init value (0 if all DFF, nonzero if some DFF_SET). -/
private def computeGroupInitVal (c : Circuit) (sg : SignalGroup) : Nat :=
  sg.wires.enum.foldl (fun acc ⟨i, w⟩ =>
    if c.gates.any (fun g => g.gateType == GateType.DFF_SET && g.output.name == w.name)
    then acc + 2^i else acc) 0

/-- Generate register declaration using ShoumeiReg/ShoumeiRegInit helper -/
def generateRegisterDecl (ctx : Context) (c : Circuit) (g : Gate) : String :=
  match g.inputs with
  | [_d, _clk, _rst] =>
      match ctx.wireToGroup.find? (fun (w', _) => w'.name == g.output.name) with
      | some (_, sg) =>
          if sg.wires.head? == some g.output then
            let clockRef := "clock"
            let resetRef := if ctx.isSequential then
              "reset.asAsyncReset"
            else
              match ctx.resetWires.head? with
              | some rw => rw.name
              | none => "reset"
            let regName := s!"{sg.name}_reg"
            let initVal := computeGroupInitVal c sg
            if initVal == 0 then
              s!"  val {regName} = ShoumeiReg({sg.width}, {clockRef}, {resetRef})"
            else
              s!"  val {regName} = ShoumeiRegInit({sg.width}, BigInt({initVal}), {clockRef}, {resetRef})"
          else
            ""
      | none =>
          let clockRef := "clock"
          let resetRef := if ctx.isSequential then
            "reset.asAsyncReset"
          else
            match ctx.resetWires.head? with
            | some rw => rw.name
            | none => "reset"
          let regName := s!"{g.output.name}_reg"
          if g.gateType == GateType.DFF_SET then
            s!"  val {regName} = ShoumeiRegInit.bool({clockRef}, {resetRef})"
          else
            s!"  val {regName} = ShoumeiReg(1, {clockRef}, {resetRef})"
  | _ =>
      "  // ERROR: DFF should have 3 inputs [d, clk, reset]"

/-- Generate register update assignments (single-assign style) -/
def generateRegisterUpdate (ctx : Context) (c : Circuit) (g : Gate) : String :=
  match g.inputs with
  | [d, _clk, _rst] =>
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
            -- Always use _reg suffix
            let regName := s!"{outputGroup.name}_reg"
            -- Add .asUInt if D input signal group is Vec (register is UInt)
            let dIsVec := match ctx.wireToGroup.find? (fun ⟨w', _⟩ => w'.name == d.name) with
              | some (_, dGroup) => needsVecDeclarationHelper ctx dGroup c
              | none => false
            let dRef := if dIsVec then s!"{dName}.asUInt" else dName
            s!"  {regName} := {dRef}"
          else
            ""
      | none =>
          -- Standalone register
          let dName := wireRef ctx c d
          -- Always use _reg suffix
          let regName := s!"{g.output.name}_reg"
          s!"  {regName} := {dName}"
  | _ =>
      ""

/-- Generate wiring from internal registers to output IO ports AND internal Vec wires.
    When a DFF output belongs to a signal group that forms a Vec pattern,
    we need: vec(i) := reg_i_reg, not just circuit output wiring.
    excludedWires: wire names already driven by instance outputs (skip to avoid double-assignment) -/
def generateRegisterOutputWiring (ctx : Context) (c : Circuit) (g : Gate) (excludedWires : List String := []) : String :=
  let isCircuitOutput := c.outputs.any (fun w => w.name == g.output.name)
  -- Also check if this DFF output belongs to an internal signal group
  -- (needs wiring so the Wire Vec gets populated from the registers)
  let isInternalGrouped := !isCircuitOutput && ctx.wireToGroup.any (fun (w', _) => w'.name == g.output.name)
  -- Skip if this wire is already driven by an instance connection
  let isExcluded := excludedWires.contains g.output.name

  if (!isCircuitOutput && !isInternalGrouped) || isExcluded then
    ""  -- Standalone internal register or instance-driven wire - no separate wiring needed
  else
    match ctx.wireToGroup.find? (fun (w', _) => w'.name == g.output.name) with
    | some (_, outputGroup) =>
        -- Part of a bus - only emit for first register in group
        if outputGroup.wires.head? == some g.output then
          -- Check if this group is part of a Vec pattern (e.g., reg_0, reg_1, ...)
          let sgRef := match parseIndexedName outputGroup.name with
            | some (baseName, vecIdx) =>
                if isVecBase ctx baseName then
                  s!"{baseName}({vecIdx})"  -- Vec element
                else
                  outputGroup.name
            | none => outputGroup.name
          s!"  {sgRef} := {outputGroup.name}_reg"
        else
          ""
    | none =>
        if isCircuitOutput then
          -- Standalone register that is a circuit output
          s!"  {g.output.name} := {g.output.name}_reg"
        else
          ""

/-- Generate all register logic.
    excludedWires: wire names already driven by instance outputs (skip output wiring) -/
def generateRegisters (ctx : Context) (c : Circuit) (excludedWires : List String := []) : String :=
  let dffs := findDFFs c
  let decls := dffs.map (generateRegisterDecl ctx c)
  let updates := dffs.map (generateRegisterUpdate ctx c)
  let wirings := dffs.map (fun g => generateRegisterOutputWiring ctx c g excludedWires)

  let declsStr := joinLines (decls.filter (· != ""))
  let updatesStr := joinLines (updates.filter (· != ""))
  let wiringsStr := joinLines (wirings.filter (· != ""))

  if declsStr.isEmpty then
    ""
  else
    let result := declsStr ++ "\n\n" ++ updatesStr
    if wiringsStr.isEmpty then
      result
    else
      result ++ "\n\n" ++ wiringsStr

/-! ## Module Generation -/

/-- Generate complete Chisel module for a circuit -/
def generateModule (c : Circuit) (allCircuits : List Circuit := []) : String :=
  let ctx := mkContext c

  -- Module or RawModule based on sequential/combinational
  let moduleType := if ctx.isSequential then "Module" else "RawModule"

  -- Collect imports for submodule instances in other packages (e.g. decoder modules)
  let decoderImports := c.instances.filterMap (fun inst =>
    if inst.moduleName.endsWith "Decoder" then
      some s!"import shoumei.riscv.{inst.moduleName.toLower}.{inst.moduleName}"
    else none)
  let decoderImports := decoderImports.eraseDups

  let header := joinLines ([
    s!"// Auto-generated by Shoumei Codegen V2",
    s!"// Source: {c.name}",
    "",
    "package generated",
    "",
    "import chisel3._",
    "import chisel3.util._",
    "import shoumei.ShoumeiReg",
    "import shoumei.ShoumeiRegInit"
  ] ++ decoderImports ++ [
    "",
    "class " ++ c.name ++ " extends " ++ moduleType ++ " {"
  ])

  let io := generateIO ctx c

  -- Generate dontTouch for all output ports to prevent CIRCT DCE from removing them
  let outputDontTouch := c.outputs.filterMap (fun w =>
    if ctx.clockWires.contains w || ctx.resetWires.contains w then none
    else
      match ctx.wireToGroup.find? (fun (w', _) => w'.name == w.name) with
      | some (_, sg) =>
          if sg.wires.head? == some w then
            some s!"  dontTouch({sg.name})"
          else none
      | none => some s!"  dontTouch({w.name})"
  )
  let dontTouchStr := joinLines outputDontTouch

  let internalWires := generateInternalWires ctx c

  -- Generate DontCare for undriven internal wires
  -- A wire is undriven if it's not a gate/DFF output and not an instance output port
  let gateOutputNames := c.gates.map (fun g => g.output.name)
  -- Normalize helper for sub-module port matching
  let normalize (s : String) : String :=
    let chars := s.toList.reverse.dropWhile (· == '_') |>.reverse
    if chars.isEmpty then s else String.ofList chars
  let instanceOutputNames := c.instances.flatMap (fun inst =>
    match allCircuits.find? (fun sc => sc.name == inst.moduleName) with
    | none => []  -- Can't determine sub-module ports, skip
    | some subMod =>
        -- Only include wires connected to OUTPUT ports of the sub-module
        inst.portMap.filter (fun (pname, _) =>
          let portBase := normalize (extractPortBaseName pname)
          subMod.outputs.any (fun w => normalize (extractBaseName w.name) == portBase)
        ) |>.map (fun (_, wire) => wire.name)
  )
  let drivenWireNames := (gateOutputNames ++ instanceOutputNames ++ c.inputs.map (·.name)).eraseDups
  let undrivenWires := (findInternalWires c).filter (fun w => !drivenWireNames.contains w.name)
  -- Generate DontCare for undriven signal groups (one per group)
  let undrivenDontCares := undrivenWires.filterMap (fun w =>
    match ctx.wireToGroup.find? (fun (w', _) => w'.name == w.name) with
    | some (_, sg) =>
        if sg.wires.head? == some w then
          some s!"  {sg.name} := DontCare"
        else
          none  -- Only emit once per signal group
    | none =>
        -- Standalone undriven wire
        some s!"  {w.name} := DontCare"
  )
  let undrivenStr := if undrivenDontCares.isEmpty then ""
                     else joinLines undrivenDontCares

  -- Pass instanceOutputNames to avoid double-assignment of instance-driven wires
  let registers := generateRegisters ctx c instanceOutputNames
  let combGates := generateCombGates ctx c instanceOutputNames
  let instances := generateInstances ctx c allCircuits

  let body := joinLines [
    io,
    dontTouchStr,
    "",
    internalWires,
    undrivenStr,
    "",
    registers,
    "",
    combGates,
    "",
    instances
  ]

  let footer := "}"

  joinLines [header, body, footer]

/-! ## Public API -/

/-- Generate Chisel code for a circuit.
    Pass allCircuits to enable sub-module port direction lookup for hierarchical modules. -/
def toChisel (c : Circuit) (allCircuits : List Circuit := []) : String :=
  generateModule c allCircuits

end Shoumei.Codegen.Chisel
