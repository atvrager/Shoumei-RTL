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
import Std.Data.HashMap
import Std.Data.HashSet

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
  /-- Fast lookup: wire name -> SignalGroup -/
  groupMap : Std.HashMap String SignalGroup := {}
  /-- Fast lookup: wire name -> bit index -/
  indexMap : Std.HashMap String Nat := {}
  /-- Fast lookup: wire names that are DFF outputs -/
  dffOutputSet : Std.HashSet String := {}
  /-- Fast lookup: wire names that are DFF_SET outputs -/
  dffSetOutputSet : Std.HashSet String := {}
  /-- Fast lookup: base names that are Vec bases (>= 2 indexed signal groups) -/
  vecBases : Std.HashSet String := {}
  /-- Precomputed internal wires -/
  internalWires : List Wire := []
  /-- Fast lookup: circuit output wire names -/
  outputWireSet : Std.HashSet String := {}
  /-- Fast lookup: signal group name -> SignalGroup -/
  sgNameMap : Std.HashMap String SignalGroup := {}
  /-- Fast lookup: gate output wire names -/
  gateOutputSet : Std.HashSet String := {}
  /-- Fast lookup: circuit input wire names -/
  inputWireSet : Std.HashSet String := {}
  /-- Signal groups that must be declared as Vec -/
  vecDeclarationGroups : Std.HashSet String := {}
  /-- Signal groups whose outputs have individual bit assignments -/
  outputIndividualBitGroups : Std.HashSet String := {}

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
  let (map, order) := wires.foldl (fun (map, order) w =>
    match parseWireName w with
    | some (base, idx) =>
        match map[base]? with
        | some arr => (map.insert base (arr.push (idx, w)), order)
        | none => (map.insert base #[(idx, w)], order.push base)
    | none => (map, order)
  ) (({} : Std.HashMap String (Array (Nat × Wire))), (#[] : Array String))
  order.toList.map (fun base => (base, map[base]!.toList))

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
  let ioSet : Std.HashSet String :=
    (c.inputs ++ c.outputs).foldl (fun s w => s.insert w.name) {}
  let allCandidates := c.gates.map (·.output) ++
    c.instances.flatMap (fun inst => inst.portMap.map (·.2)) ++
    c.rams.flatMap (fun ram =>
      let wpWires := ram.writePorts.flatMap (fun wp => [wp.en] ++ wp.addr ++ wp.data)
      let rpWires := ram.readPorts.flatMap (fun rp => rp.addr ++ rp.data)
      wpWires ++ rpWires)
  let (res, _) := allCandidates.foldl (fun (acc, seen) w =>
    if ioSet.contains w.name || seen.contains w.name then (acc, seen)
    else (acc.push w, seen.insert w.name)
  ) ((#[] : Array Wire), ({} : Std.HashSet String))
  res.toList


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
private def dedupSignalGroups (sgs : List SignalGroup) : List SignalGroup := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut result : Array SignalGroup := #[]
  for sg in sgs do
    if !seen.contains sg.name then
      seen := seen.insert sg.name
      result := result.push sg
  return result.toList

/-- Check if a base name corresponds to a Vec declaration by looking for indexed pattern in signal groups -/
def isVecBase (ctx : Context) (baseName : String) : Bool :=
  ctx.vecBases.contains baseName

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
  ctx.groupMap.contains w.name

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
                let in0GroupName := ctx.groupMap[in0.name]?.map (·.name)
                match in0GroupName with
                | some firstBusName =>
                    -- First gate input is in a bus. Check ALL inputs are in the SAME bus.
                    let allInSameBus := gates.all (fun g =>
                      match g.inputs with
                      | [inp] =>
                          let inpGroupName := ctx.groupMap[inp.name]?.map (·.name)
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
                let in0GroupName := ctx.groupMap[in0.name]?.map (·.name)
                let in1GroupName := ctx.groupMap[in1.name]?.map (·.name)
                if in0GroupName.isSome || in1GroupName.isSome then
                  -- At least one input is a bus → check uniformity (same bus identity)
                  let allUniform := gates.all (fun g =>
                    match g.inputs with
                    | [gi0, gi1] =>
                        let gi0GroupName := ctx.groupMap[gi0.name]?.map (·.name)
                        let gi1GroupName := ctx.groupMap[gi1.name]?.map (·.name)
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
                let in0Bus := ctx.groupMap.contains in0.name
                let in1Bus := ctx.groupMap.contains in1.name
                -- generateBusWideOp for MUX requires BOTH in0 and in1 to be buses
                if in0Bus && in1Bus then
                  -- Check all gates have same bus pattern (allGatesUniform in generateBusWideOp)
                  let in0Group := ctx.groupMap[in0.name]?.map (·.name)
                  let in1Group := ctx.groupMap[in1.name]?.map (·.name)
                  let selGroup := ctx.groupMap[sel.name]?.map (·.name)
                  let allGatesUniform := gates.all (fun g =>
                    match g.inputs with
                    | [g_in0, g_in1, g_sel] =>
                        let g0 := ctx.groupMap[g_in0.name]?.map (·.name)
                        let g1 := ctx.groupMap[g_in1.name]?.map (·.name)
                        let gs := ctx.groupMap[g_sel.name]?.map (·.name)
                        g0 == in0Group && g1 == in1Group && gs == selGroup
                    | _ => false
                  )
                  if !allGatesUniform then
                    true  -- Non-uniform → Vec
                  else
                    -- Check the specific pattern generateBusWideOp handles
                    let selInBus := ctx.groupMap.contains sel.name
                    let selIdx := ctx.indexMap[sel.name]?
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
    Evaluation version used during mkContext. -/
def evalOutputHasIndividualBitAssignments (ctx : Context) (c : Circuit) (sg : SignalGroup) : Bool :=
  if sg.width <= 1 then
    false  -- Single-bit outputs don't need Vec
  else
    let combGates := c.gates.filter (fun g => !g.gateType.isDFF)
    let sgWireNames : Std.HashSet String := sg.wires.foldl (fun s w => s.insert w.name) {}
    -- Get all gates that write to this signal group
    let outputGates := combGates.filter (fun g => sgWireNames.contains g.output.name)

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

/-- Build signal group dependency map in a single pass over combinational gates -/
def buildGroupDepMap (ctx : Context) (c : Circuit) : Std.HashMap String (List String) := Id.run do
  let mut depMap : Std.HashMap String (Std.HashSet String) := {}
  for g in c.gates do
    if !g.gateType.isDFF then
      if let some outSg := ctx.groupMap[g.output.name]? then
        for inp in g.inputs do
          if let some inSg := ctx.groupMap[inp.name]? then
            if inSg.name != outSg.name then
              let set := depMap[outSg.name]?.getD {}
              depMap := depMap.insert outSg.name (set.insert inSg.name)
  let mut res : Std.HashMap String (List String) := {}
  for (name, set) in depMap.toList do
    res := res.insert name set.toList
  return res

/-- Check if a signal group participates in a combinational cycle using precomputed depMap -/
def hasCombCycleWithDepMap (depMap : Std.HashMap String (List String)) (maxFuel : Nat) (sgName : String) : Bool :=
  let target := sgName
  let startDeps := depMap[target]?.getD []
  let rec go (visited : Std.HashSet String) (frontier : List String) : Nat → Bool
    | 0 => false
    | fuel + 1 =>
      match frontier with
      | [] => false
      | node :: rest =>
        if node == target then true
        else if visited.contains node then go visited rest fuel
        else
          let neighbors := depMap[node]?.getD []
          go (visited.insert node) (rest ++ neighbors) fuel
  go {} startDeps maxFuel

/-- Check if a signal group participates in a combinational cycle through signal group dependencies. -/
def hasCombCycleThroughGroup (ctx : Context) (c : Circuit) (sg : SignalGroup) : Bool :=
  let depMap := buildGroupDepMap ctx c
  hasCombCycleWithDepMap depMap (ctx.groupMap.size + 1) sg.name

/-- Check if a signal group should be declared as Vec(width, Bool()) instead of UInt(width.W).
    Evaluation version used during mkContext. -/
def evalNeedsVecDeclaration (ctx : Context) (depMap : Std.HashMap String (List String))
    (sg : SignalGroup) (c : Circuit) : Bool :=
  if sg.width <= 1 then
    false  -- Single-bit signals don't need Vec
  else
    let combGates := c.gates.filter (fun g => !g.gateType.isDFF)
    let sgWireNames : Std.HashSet String := sg.wires.foldl (fun s w => s.insert w.name) {}
    -- Get all combinational gates that write to this signal group
    let outputGates := combGates.filter (fun g => sgWireNames.contains g.output.name)

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
            let needsIndividual := willGenerateIndividualAssignments ctx c outputGates
            if needsIndividual then true
            else
              hasCombCycleWithDepMap depMap (ctx.groupMap.size + 1) sg.name

/-- Build context from circuit with precomputed lookup maps and analysis results. -/
def mkContext (c : Circuit) : Context := Id.run do
  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let isSequential := c.gates.any (fun g => g.gateType.isDFF) ||
                      !clockWires.isEmpty || !resetWires.isEmpty

  let internalWires := findInternalWires c
  let autoDetectedGroups := autoDetectSignalGroups internalWires
  let allGroups := c.signalGroups ++ autoDetectedGroups

  let wireToGroup := allGroups.flatMap (fun sg =>
    sg.wires.map (fun w => (w, sg))
  )
  let wireToIndex := allGroups.flatMap (fun sg =>
    sg.wires.enum.map (fun (idx, w) => (w, idx))
  )

  let groupMap := wireToGroup.foldl (fun (m : Std.HashMap String SignalGroup) (w, sg) =>
    m.insert w.name sg) {}
  let indexMap := wireToIndex.foldl (fun (m : Std.HashMap String Nat) (w, idx) =>
    m.insert w.name idx) {}

  let mut dffOutputSet : Std.HashSet String := {}
  let mut dffSetOutputSet : Std.HashSet String := {}
  let mut gateOutputSet : Std.HashSet String := {}
  for g in c.gates do
    gateOutputSet := gateOutputSet.insert g.output.name
    if g.gateType.isDFF then
      dffOutputSet := dffOutputSet.insert g.output.name
    if g.gateType == GateType.DFF_SET then
      dffSetOutputSet := dffSetOutputSet.insert g.output.name

  let mut outputWireSet : Std.HashSet String := {}
  for w in c.outputs do
    outputWireSet := outputWireSet.insert w.name

  let mut inputWireSet : Std.HashSet String := {}
  for w in c.inputs do
    inputWireSet := inputWireSet.insert w.name

  let mut sgNameMap : Std.HashMap String SignalGroup := {}
  for sg in allGroups do
    sgNameMap := sgNameMap.insert sg.name sg

  -- Precompute vecBases: base names with >= 2 distinct indexed signal groups
  let mut baseGroupCounts : Std.HashMap String (Std.HashSet String) := {}
  for sg in allGroups do
    if let some (base, _) := parseIndexedName sg.name then
      let set := baseGroupCounts[base]?.getD {}
      baseGroupCounts := baseGroupCounts.insert base (set.insert sg.name)
  let mut vecBases : Std.HashSet String := {}
  for (base, sgs) in baseGroupCounts.toList do
    if sgs.size >= 2 then
      vecBases := vecBases.insert base

  let baseCtx : Context := {
    wireToGroup, wireToIndex, clockWires, resetWires, isSequential,
    groupMap, indexMap, dffOutputSet, dffSetOutputSet, vecBases, internalWires,
    outputWireSet, sgNameMap, gateOutputSet, inputWireSet,
    vecDeclarationGroups := {}, outputIndividualBitGroups := {}
  }

  let depMap := buildGroupDepMap baseCtx c
  let mut vecDeclarationGroups : Std.HashSet String := {}
  let mut outputIndividualBitGroups : Std.HashSet String := {}
  for sg in allGroups do
    if evalOutputHasIndividualBitAssignments baseCtx c sg then
      outputIndividualBitGroups := outputIndividualBitGroups.insert sg.name
    if evalNeedsVecDeclaration baseCtx depMap sg c then
      vecDeclarationGroups := vecDeclarationGroups.insert sg.name

  return { baseCtx with vecDeclarationGroups, outputIndividualBitGroups }

/-- Fast O(1) check if a signal group should be declared as Vec(width, Bool()). -/
def needsVecDeclarationHelper (ctx : Context) (sg : SignalGroup) (_c : Circuit) : Bool :=
  ctx.vecDeclarationGroups.contains sg.name

/-- Fast O(1) check if an output signal group has individual bit assignments. -/
def outputHasIndividualBitAssignmentsHelper (ctx : Context) (_c : Circuit) (sg : SignalGroup) : Bool :=
  ctx.outputIndividualBitGroups.contains sg.name

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
    match ctx.groupMap[w.name]? with
    | some sg =>
        -- Check if this signal group is a DFF output (register)
        let isDFFOutput := sg.wires.any (fun sw => ctx.dffOutputSet.contains sw.name)

        -- Check if signal group matches indexed pattern AND a Vec exists for it
        match parseIndexedName sg.name with
        | some (baseName, vecIdx) =>
            if isVecBase ctx baseName then
              -- This signal group is part of a Vec - use Vec indexing
              -- For multi-bit signals within the Vec element, also include bit index
              if sg.width > 1 then
                match ctx.indexMap[w.name]? with
                | some bitIdx => s!"{baseName}({vecIdx})({bitIdx})"
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
                match ctx.indexMap[w.name]? with
                | some idx => s!"{sgRef}({idx})"
                | none =>
                    -- Add .asUInt if this is an output with Vec declaration
                    let isOutput := sg.wires.any (fun sw => ctx.outputWireSet.contains sw.name)
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
              match ctx.indexMap[w.name]? with
              | some idx => s!"{sgRef}({idx})"
              | none =>
                    -- Add .asUInt if this is an output with Vec declaration
                    let isOutput := sg.wires.any (fun sw => ctx.outputWireSet.contains sw.name)
                    if isOutput && outputHasIndividualBitAssignmentsHelper ctx c sg then
                      s!"{sgRef}.asUInt"
                    else
                      sgRef
            else
              sgRef
    | none =>
        -- Check if this wire is a DFF output (register)
        -- If so, use _reg suffix since all registers now use that suffix
        if ctx.dffOutputSet.contains w.name then
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
    let isDFFOutput := ctx.dffOutputSet.contains w.name
    let isCircuitOutput := ctx.outputWireSet.contains w.name
    if !isInput && isDFFOutput && !isCircuitOutput then
      none  -- Internal register, skip
    else
      -- Check if wire is part of a signal group
      match ctx.groupMap[w.name]? with
      | some sg =>
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
  match ctx.groupMap[w.name]? with
  | some sg =>
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
      let isDFFOutput := ctx.dffOutputSet.contains w.name
      if isDFFOutput then
        none  -- Register declaration (ShoumeiReg) handles this wire
      else
        -- Standalone wire
        some s!"  val {w.name} = Wire(Bool())"

/-- Detect indexed signal group patterns and group them into Vec declarations -/
def detectVecPatterns (ctx : Context) (c : Circuit) (internalWires : List Wire) : List (String × Nat × String) × List Wire := Id.run do
  -- Extract unique signal groups from wireToGroup
  let signalGroups := dedupSignalGroups (ctx.wireToGroup.map (·.2))

  -- Group signal groups by base name
  let mut map : Std.HashMap String ((Nat × String) × Array (Nat × SignalGroup)) := {}
  let mut order : Array String := #[]
  for sg in signalGroups do
    if let some (base, idx) := parseIndexedName sg.name then
      if let some ((width, chiselType), indices) := map[base]? then
        map := map.insert base ((width, chiselType), indices.push (idx, sg))
      else
        let needsVec := needsVecDeclarationHelper ctx sg c
        let chiselType := if needsVec && sg.width > 1 then s!"Vec({sg.width}, Bool())"
                          else signalGroupToChisel sg
        order := order.push base
        map := map.insert base ((sg.width, chiselType), #[(idx, sg)])

  let mut vecDecls : List (String × Nat × String) := []
  let mut handledGroups : Std.HashSet String := {}

  for base in order do
    if let some ((_width, chiselType), indexedArr) := map[base]? then
      if indexedArr.size >= 2 then
        let sorted := indexedArr.qsort (fun a b => a.1 < b.1)
        let maxIdx := sorted.back?.map (·.1) |>.getD 0
        let firstIdx := sorted[0]?.map (·.1) |>.getD 999
        if sorted.size == maxIdx + 1 && firstIdx == 0 then
          vecDecls := (base, maxIdx + 1, chiselType) :: vecDecls
          for (_, sg) in sorted do
            handledGroups := handledGroups.insert sg.name

  vecDecls := vecDecls.reverse

  -- Filter internal wires to remove those handled by Vec declarations
  let remainingWires := internalWires.filter (fun w =>
    match ctx.groupMap[w.name]? with
    | some sg => !handledGroups.contains sg.name
    | none => true
  )

  return (vecDecls, remainingWires)

/-- Generate all internal wire declarations -/
def generateInternalWires (ctx : Context) (c : Circuit) : String :=
  let internalWires := findInternalWires c
  let (vecDecls, remainingWires) := detectVecPatterns ctx c internalWires

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
          let selRef := wireRef ctx c sel
          -- Mux select must be Bool; 1-bit ShoumeiReg is UInt(1.W), needs .asBool
          let selBool := if selRef.endsWith "_reg" then s!"{selRef}.asBool" else selRef
          s!"  {outRef} := Mux({selBool}, {wireRef ctx c in1}, {wireRef ctx c in0})"
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
  ctx.groupMap[w.name]?

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
def groupGatesByBus (ctx : Context) (gates : List Gate) : List (SignalGroup × List Gate) := Id.run do
  let mut map : Std.HashMap String (SignalGroup × Array Gate) := {}
  let mut order : Array String := #[]
  for g in gates do
    if let some (outBus, _, _) := matchBusPattern ctx g then
      if let some (bus, arr) := map[outBus.name]? then
        map := map.insert outBus.name (bus, arr.push g)
      else
        order := order.push outBus.name
        map := map.insert outBus.name (outBus, #[g])
  let mut res : List (SignalGroup × List Gate) := []
  for name in order.toList.reverse do
    if let some (bus, arr) := map[name]? then
      res := (bus, arr.toList) :: res
  return res

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
  -- If this output bus needs Vec (e.g., due to combinational cycles), don't generate
  -- a bulk op; fall through to per-bit assignments to let FIRRTL track bit-level deps
  if needsVecDeclarationHelper ctx bus _c then none
  else if !isCompleteBusOp ctx bus gates then none
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
                  let selIdx := ctx.indexMap[sel.name]?

                  -- Generate based on pattern
                  match in0Bus, in1Bus, selBus, selIdx with
                  | some b0, some b1, none, _ =>
                      -- Bus mux with standalone scalar select: out := Mux(sel, in1, in0)
                      let outRef := signalGroupRef ctx bus.name
                      let in1Ref := signalGroupRefForBusOp ctx _c b1
                      let in0Ref := signalGroupRefForBusOp ctx _c b0
                      let selRef := wireRef ctx _c sel
                      let selBool := if selRef.endsWith "_reg" then s!"{selRef}.asBool" else selRef
                      some s!"  {outRef} := Mux({selBool}, {in1Ref}, {in0Ref})"
                  | some b0, some b1, some selB, some idx =>
                      -- Bus mux with indexed select: out := Mux(selBus(idx), in1, in0)
                      let outRef := signalGroupRef ctx bus.name
                      let in1Ref := signalGroupRefForBusOp ctx _c b1
                      let in0Ref := signalGroupRefForBusOp ctx _c b0
                      let selBusRef := signalGroupRef ctx selB.name
                      some s!"  {outRef} := Mux({selBusRef}({idx}), {in1Ref}, {in0Ref})"
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
                      let in1Ref := wireRef ctx _c in1
                      let forLoop := joinLines [
                        s!"  {outRef} := Cat(",
                        s!"    (0 until {bus.width}).reverse.map(i => {in0Access} {op} {in1Ref})",
                        "  )"
                      ]
                      some forLoop
                    else
                      -- Scalar varies per bit: build Cat with per-gate expressions
                      let sortedGates := gates.toArray.qsort (fun g1 g2 =>
                        match ctx.indexMap[g1.output.name]?,
                              ctx.indexMap[g2.output.name]? with
                        | some i1, some i2 => i1 < i2
                        | _, _ => g1.output.name < g2.output.name
                      ) |>.toList
                      let outRef := signalGroupRef ctx bus.name
                      let perBitExprs := sortedGates.reverse.map (fun g =>
                        match g.inputs with
                        | [busIn, scalarIn] =>
                            let busRef := wireRef ctx _c busIn
                            let scalarRef := wireRef ctx _c scalarIn
                            s!"{busRef} {op} {scalarRef}"
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
                      let in0Ref := wireRef ctx _c in0
                      let forLoop := joinLines [
                        s!"  {outRef} := Cat(",
                        s!"    (0 until {bus.width}).reverse.map(i => {in0Ref} {op} {in1Access})",
                        "  )"
                      ]
                      some forLoop
                    else
                      -- Scalar varies per bit: build Cat with per-gate expressions
                      let sortedGates := gates.toArray.qsort (fun g1 g2 =>
                        match ctx.indexMap[g1.output.name]?,
                              ctx.indexMap[g2.output.name]? with
                        | some i1, some i2 => i1 < i2
                        | _, _ => g1.output.name < g2.output.name
                      ) |>.toList
                      let outRef := signalGroupRef ctx bus.name
                      let perBitExprs := sortedGates.reverse.map (fun g =>
                        match g.inputs with
                        | [scalarIn, busIn] =>
                            let busRef := wireRef ctx _c busIn
                            let scalarRef := wireRef ctx _c scalarIn
                            s!"{scalarRef} {op} {busRef}"
                        | _ => "false.B"
                      )
                      let catBody := String.intercalate ", " perBitExprs
                      some s!"  {outRef} := Cat({catBody})"
                | none, none => none
            | _ => none
        | _ => none

/-- Detect consecutive constant assignments and convert to for loops -/
def consolidateConstantAssignments (assignments : List String) : List String := Id.run do
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
  let mut groupMap : Std.HashMap String (Array Nat) := {}
  let mut groupKeys : Array (String × String) := #[]
  for (sig, idx, const) in constPattern do
    let keyStr := s!"{sig}\x00{const}"
    if let some arr := groupMap[keyStr]? then
      groupMap := groupMap.insert keyStr (arr.push idx)
    else
      groupKeys := groupKeys.push (sig, const)
      groupMap := groupMap.insert keyStr #[idx]

  -- Generate for loops for consecutive sequences
  let mut forLoops : List ((Nat × Nat) × String) := []
  let mut handledEntries : Std.HashSet String := {}

  for (sig, const) in groupKeys do
    let keyStr := s!"{sig}\x00{const}"
    if let some indices := groupMap[keyStr]? then
      if indices.size >= 4 then
        let sorted := indices.qsort (· < ·)
        -- Find consecutive ranges
        let mut ranges : List (Nat × Nat) := []
        for idx in sorted do
          match ranges with
          | (startIdx, lastIdx) :: rest =>
              if idx == lastIdx + 1 then
                ranges := (startIdx, idx) :: rest
              else
                ranges := (idx, idx) :: ranges
          | [] =>
              ranges := [(idx, idx)]
        ranges := ranges.reverse

        for (startIdx, endIdx) in ranges do
          if endIdx - startIdx + 1 >= 4 then
            let forLoop := joinLines [
              s!"  for (i <- {startIdx} to {endIdx}) " ++ "{",
              s!"    {sig}(i) := {const}",
              "  }"
            ]
            forLoops := ((startIdx, endIdx), forLoop) :: forLoops
            for offset in [0:(endIdx - startIdx + 1)] do
              handledEntries := handledEntries.insert s!"{sig}({offset + startIdx})"

  forLoops := forLoops.reverse

  -- Filter out assignments handled by for loops (checking both signal name AND index)
  let remaining := assignments.filter (fun assign =>
    let parts := assign.trimAscii.toString.splitOn " := "
    match parts with
    | [lhs, _] =>
        if lhs.contains "(" && lhs.contains ")" then
          let trimmedLhs := lhs.trimAscii.toString
          !handledEntries.contains trimmedLhs
        else true
    | _ => true
  )

  return remaining ++ (forLoops.map (·.2))

/-- Detect patterns in bus assignments that can be converted to for loops -/
def consolidateIntoForLoops (assignments : List String) : List String :=
  assignments

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
  let handledGateOutputs : Std.HashSet String := busOpsWithGates.foldl (fun s (_, gates) =>
    gates.foldl (fun s2 g => s2.insert g.output.name) s) {}
  let excludedWiresSet : Std.HashSet String := excludedWires.foldl (fun s w => s.insert w) {}

  -- Generate individual assignments for remaining gates
  -- Also exclude gates whose outputs are already driven by instance connections
  let remainingGates := combGates.filter (fun g =>
    !handledGateOutputs.contains g.output.name &&
    !excludedWiresSet.contains g.output.name
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
def determinePortDirection (ctx : Context) (c : Circuit) (allCircuits : List Circuit)
    (inst : CircuitInstance) (portBase : String) (wire : Wire) : Bool :=
  -- 1. Check sub-module definition (most reliable)
  match isSubModuleInput allCircuits inst.moduleName portBase with
  | some isInput => isInput
  | none =>
      -- 2. Check if wire is produced by a gate or is a circuit input → instance INPUT
      let isProducedByGate := ctx.gateOutputSet.contains wire.name
      let isCircuitInput := ctx.inputWireSet.contains wire.name
      if isProducedByGate || isCircuitInput then true
      else
        -- 3. Check if wire is a circuit output → instance OUTPUT
        let isCircuitOutput := ctx.outputWireSet.contains wire.name
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
            else
              -- Wire not consumed: if also not driven by anything, it must be
              -- an output from the instance (nothing else can drive it)
              let isDriven := isProducedByGate || isCircuitInput
              if !isDriven then false  -- Instance output (unconnected)
              else true  -- Driven by something → assume input
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
    : List (String × String × List (String × Wire)) := Id.run do
  let mut map : Std.HashMap String (Array (String × Wire)) := {}
  let mut order : Array (String × String) := #[]
  for entry@(portName, wire) in portMap do
    if let some sg := ctx.groupMap[wire.name]? then
      let portBase := extractPortBaseName portName
      let keyStr := s!"{sg.name}\x00{portBase}"
      if let some arr := map[keyStr]? then
        map := map.insert keyStr (arr.push entry)
      else
        order := order.push (sg.name, portBase)
        map := map.insert keyStr #[entry]
  let mut res : List (String × String × List (String × Wire)) := []
  for (sgName, portBase) in order.toList.reverse do
    let keyStr := s!"{sgName}\x00{portBase}"
    if let some arr := map[keyStr]? then
      res := (sgName, portBase, arr.toList) :: res
  return res

/-- Extract numeric index from a bracket-notation port name.
    Example: "in0[31]" → some 31, "out[5]" → some 5, "valid" → none -/
def extractBracketIndex (portName : String) : Option Nat :=
  match portName.splitOn "[" with
  | [_, rest] =>
      let idxStr := String.ofList (rest.toList.takeWhile (· != ']'))
      idxStr.toNat?
  | _ => none

/-- Extract numeric index from underscore-suffix port name.
    Example: "q_0" → some 0, "grant_3" → some 3, "valid" → none -/
def extractUnderscoreIndex (portName : String) : Option Nat :=
  let parts := portName.splitOn "_"
  if parts.length >= 2 then
    let lastPart := parts.getLast!
    if lastPart.all (·.isDigit) && !lastPart.isEmpty then
      lastPart.toNat?
    else
      none
  else
    none

/-- Extract numeric index from either bracket or underscore notation.
    Example: "q[0]" → some 0, "q_0" → some 0, "valid" → none -/
def extractPortIndex (portName : String) : Option Nat :=
  extractBracketIndex portName |>.orElse (fun _ => extractUnderscoreIndex portName)

/-- Get the width of a sub-module's bus port, or 0 if not found -/
def subModuleBusPortWidth (allCircuits : List Circuit) (moduleName : String) (baseName : String) : Nat :=
  match allCircuits.find? (fun sc => sc.name == moduleName) with
  | none => 0
  | some subMod =>
      let allGroups := subMod.signalGroups ++ autoDetectSignalGroups (findInternalWires subMod)
      match allGroups.find? (fun sg => sg.name == baseName) with
      | some sg => sg.width
      | none => 0

/-- Check if a sub-module has a bus port with the given base name. -/
def subModuleHasBusPort (allCircuits : List Circuit) (moduleName : String) (baseName : String) : Bool :=
  match allCircuits.find? (fun sc => sc.name == moduleName) with
  | none => true  -- Unknown module: assume bus port exists (conservative)
  | some subMod =>
      -- Check explicit signal groups (same as mkContext)
      let hasExplicitGroup := subMod.signalGroups.any (fun sg => sg.name == baseName)
      -- Check auto-detected signal groups from internal wires (same as mkContext)
      let internalWires := findInternalWires subMod
      let autoGroups := autoDetectSignalGroups internalWires
      let hasAutoGroup := autoGroups.any (fun sg => sg.name == baseName)
      hasExplicitGroup || hasAutoGroup

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
    ctx.groupMap.contains wire.name
  )

  -- 4. Group the bus entries by signal group
  let busGroups := groupPortMapBySignalGroup ctx groupedEntries

  -- 5. Generate bus connections (one connection per signal group)
  --    When the sub-module has a matching bus port, use a single bus connection.
  --    When the sub-module has individual ports (no bus), use Cat/bit-extract for the mismatch.
  let busConnections := busGroups.flatMap (fun (sgName, portBase, entries) =>
    -- Use determinePortDirection for reliable direction detection
    let firstWire := entries.head?.map (·.2) |>.getD (Wire.mk "")
    let isInstanceInput := determinePortDirection ctx c allCircuits inst portBase firstWire

    -- Get proper reference for entire signal group (handles Vec indexing)
    let sgRef := signalGroupRef ctx sgName

    if subModuleHasBusPort allCircuits inst.moduleName portBase then
      -- Sub-module has a bus port: single bus connection
      -- Check for width mismatches between parent signal group and sub-module port
      let parentSgWidth := match ctx.sgNameMap[sgName]? with
        | some sg => sg.width
        | none => entries.length
      let subPortWidth := subModuleBusPortWidth allCircuits inst.moduleName portBase
      let isPartial := entries.length < parentSgWidth
      if isInstanceInput then
        let sourceSg := ctx.sgNameMap[sgName]?
        let sourceIsVec := match sourceSg with
          | some sg => needsVecDeclarationHelper ctx sg c
          | none => false
        let srcRef := if sourceIsVec then s!"{sgRef}.asUInt" else sgRef
        -- For partial connections, slice the parent signal group to match entries
        -- Compute actual bit range from wire indices (not always starting at 0)
        let slicedRef := if isPartial then
                           let wireIndices := entries.filterMap (fun (_, wire) => ctx.indexMap[wire.name]?)
                           let minIdx := wireIndices.foldl (fun acc i => if i < acc then i else acc)
                             (wireIndices.head?.getD 0)
                           let maxIdx := wireIndices.foldl (fun acc i => if i > acc then i else acc)
                             (wireIndices.head?.getD 0)
                           s!"{srcRef}({maxIdx}, {minIdx})"
                         else srcRef
        -- If sub-module port is wider than what we're providing, pad with zeros
        let paddedRef := if subPortWidth > 0 && entries.length < subPortWidth then
                           s!"{slicedRef}.pad({subPortWidth})"
                         else slicedRef
        [s!"  {inst.instName}.{portBase} := {paddedRef}"]
      else
        let receivingSg := ctx.sgNameMap[sgName]?
        let needsAsUInt := match receivingSg with
          | some sg => !needsVecDeclarationHelper ctx sg c
          | none => false
        let instRef := if needsAsUInt then
                        s!"{inst.instName}.{portBase}.asUInt"
                      else
                        s!"{inst.instName}.{portBase}"
        [s!"  {sgRef} := {instRef}"]
    else
      -- Sub-module has individual ports: connect via Cat (output) or individual assigns (input)
      -- Sort entries by port index
      let sortedEntries := entries.toArray.qsort (fun (p1, _) (p2, _) =>
        match extractPortIndex p1, extractPortIndex p2 with
        | some i1, some i2 => i1 < i2
        | some _, none => true
        | none, some _ => false
        | none, none => p1 < p2
      ) |>.toList
      if isInstanceInput then
        -- Decompose parent bus into individual instance port connections
        sortedEntries.map (fun (portName, wire) =>
          -- Use source wire's index within its signal group, not destination port index
          let idx := match ctx.indexMap[wire.name]? with
            | some bitIdx => bitIdx
            | none => match extractPortIndex portName with
              | some i => i
              | none => 0
          s!"  {inst.instName}.{portName} := {sgRef}({idx})"
        )
      else
        -- Instance outputs into parent bus
        let parentSgWidth := match ctx.sgNameMap[sgName]? with
          | some sg => sg.width
          | none => sortedEntries.length
        let isVecDecl := match ctx.sgNameMap[sgName]? with
          | some sg => needsVecDeclarationHelper ctx sg c
          | none => false
        if sortedEntries.length < parentSgWidth && isVecDecl then
          -- Partial coverage of a Vec: assign to specific bits
          sortedEntries.map (fun (portName, wire) =>
            let wireRefStr := wireRef ctx c wire
            s!"  {wireRefStr} := {inst.instName}.{portName}"
          )
        else
          -- Full bus or UInt: Cat individual instance outputs
          let catParts := sortedEntries.reverse.map (fun (portName, _) =>
            s!"{inst.instName}.{portName}"
          )
          let catExpr := "Cat(" ++ String.intercalate ", " catParts ++ ")"
          [s!"  {sgRef} := {catExpr}"]
  )

  -- 5b. Collect port bases handled by bus INPUT connections (to skip redundant standalone entries)
  --    Only track input-direction bus connections (where padding covers all port bits).
  --    Output-direction bus connections may be partial (only some bits from signal group).
  let busHandledInputPortBases := busGroups.filterMap (fun (_sgName, portBase, entries) =>
    let firstWire := entries.head?.map (·.2) |>.getD (Wire.mk "")
    let isInput := determinePortDirection ctx c allCircuits inst portBase firstWire
    -- Only mark as "handled" if the sub-module has a bus port (padding covers all bits).
    -- When sub-module has individual ports, extra bits may appear as standalone entries.
    let hasBusPort := subModuleHasBusPort allCircuits inst.moduleName portBase
    if isInput && hasBusPort then some portBase else none
  )

  -- 6. Group standalone entries by port base name (fast O(N) grouping)
  let standaloneFiltered := standaloneEntries.filter (fun (portName, _) =>
    let portBase := extractPortBaseName portName
    !busHandledInputPortBases.contains portBase
  )
  let standaloneGrouped : List (String × List (String × Wire)) := Id.run do
    let mut map : Std.HashMap String (Array (String × Wire)) := {}
    let mut order : Array String := #[]
    for (portName, wire) in standaloneFiltered do
      let shouldGroup :=
        if portName.contains '[' then true
        else match extractUnderscoreIndex portName with
          | some _ => subModuleHasBusPort allCircuits inst.moduleName (extractPortBaseName portName)
          | none => false
      let baseName := if shouldGroup then extractPortBaseName portName else portName
      if let some arr := map[baseName]? then
        map := map.insert baseName (arr.push (portName, wire))
      else
        order := order.push baseName
        map := map.insert baseName #[(portName, wire)]
    let mut res : List (String × List (String × Wire)) := []
    for k in order.toList.reverse do
      if let some arr := map[k]? then
        res := (k, arr.toList) :: res
    return res

  -- 7. Generate standalone wire connections (uses determinePortDirection)
  let standaloneConnections := standaloneGrouped.flatMap (fun (baseName, entries) =>
    if entries.length > 1 then
      -- Multiple entries with same base - generate Cat expression
      -- Sort by numeric index (not lexicographic) to handle indices >= 10 correctly
      let sortedEntries := entries.toArray.qsort (fun (p1, _) (p2, _) =>
        match extractPortIndex p1, extractPortIndex p2 with
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
        -- Output from instance - need to extract bits using baseName(index) notation
        sortedEntries.map (fun (portName, wire) =>
          let wireRefStr := wireRef ctx c wire
          -- Convert port name to Chisel index notation: q[0] → q(0), q_0 → q(0)
          let chiselPortName := match extractPortIndex portName with
            | some idx => s!"{baseName}({idx})"
            | none => convertPortNameToChisel portName
          s!"  {wireRefStr} := {inst.instName}.{chiselPortName}"
        )
    else
      -- Single entry - use direct connection with unified direction detection
      entries.map (fun (portName, wire) =>
        let wireRefStr := wireRef ctx c wire
        let chiselPortName := convertPortNameToChisel portName
        let portBaseForDir := extractPortBaseName portName
        let isInstanceInput := determinePortDirection ctx c allCircuits inst portBaseForDir wire

        -- Check if this single entry maps to a sub-module bus port (e.g., issue_opcode_5 → issue_opcode(5))
        let isBusEntry := match extractUnderscoreIndex portName with
          | some _ => subModuleHasBusPort allCircuits inst.moduleName portBaseForDir
          | none => false
        let chiselRef := if isBusEntry then
          match extractPortIndex portName with
          | some idx => s!"{inst.instName}.{portBaseForDir}({idx})"
          | none => s!"{inst.instName}.{chiselPortName}"
        else
          s!"{inst.instName}.{chiselPortName}"

        if isInstanceInput then
          s!"  {chiselRef} := {wireRefStr}"
        else
          s!"  {wireRefStr} := {chiselRef}"
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

  -- 8b. Generate DontCare for bus-grouped sub-module input ports missing from portMap
  let busDontCareConnections := match allCircuits.find? (fun sc => sc.name == inst.moduleName) with
    | none => []
    | some subMod =>
        -- Find all input port base names that are bus-grouped
        let inputBusBaseNames := subMod.inputs.filterMap (fun w =>
          let base := extractBaseName w.name
          if base != w.name then some base else none  -- Has _N suffix → part of a bus
        ) |>.eraseDups
        -- Filter to those not connected in portMap
        -- Normalize base names by stripping trailing underscores for comparison
        let normalize := fun (s : String) => s.dropEndWhile (· == '_')
        let connectedBasesNorm := inst.portMap.map (fun (pname, _) => normalize (extractPortBaseName pname)) |>.eraseDups
        let unconnectedBuses := inputBusBaseNames.filter (fun base =>
          !connectedBasesNorm.contains (normalize base) &&
          base != "clock" && base != "reset"
        )
        unconnectedBuses.map (fun base =>
          s!"  {inst.instName}.{base} := DontCare"
        )

  -- 8c. Generate DontCare for individual unconnected sub-module input ports
  --     Handles partially connected buses where the sub-module does NOT have a bus port
  --     (i.e., individual ports like tag_0, tag_1, ..., tag_6 where tag_6 is unconnected)
  let individualDontCareConnections := match allCircuits.find? (fun sc => sc.name == inst.moduleName) with
    | none => []
    | some subMod =>
        let connectedPortNames := inst.portMap.map (fun (pname, _) => pname)
        subMod.inputs.filter (fun w =>
          w.name != "clock" && w.name != "reset" &&
          !connectedPortNames.contains w.name &&
          let base := extractBaseName w.name
          base != w.name &&  -- Has _N suffix
          -- Only if the sub-module does NOT have a bus port for this base
          -- (if it does, the bus connection or busDontCare handles it)
          !subModuleHasBusPort allCircuits inst.moduleName base &&
          -- Only if some other ports with this base ARE connected (partial connection)
          inst.portMap.any (fun (pname, _) => extractPortBaseName pname == base)
        ) |>.map (fun w =>
          s!"  {inst.instName}.{w.name} := DontCare"
        )

  -- 9. Return instantiation + all connections
  [instantiation] ++ busConnections ++ standaloneConnections ++ renamedClockResetConnections ++ dontCareConnections ++ busDontCareConnections ++ individualDontCareConnections

/-- Post-process instance connections to fix multi-writer output buses.
    When multiple instances write to the same output bus (e.g., `q := reg_0.q.asUInt`
    repeated for each sub-register), replace with a single Cat assignment.
    Uses assignment order as Cat order (first assigned = LSB, reversed for Cat MSB-first). -/
private def postProcessMultiWriterOutputs (lines : List String) : List String :=
  -- Find lines matching pattern "  {target} := {source}" and detect duplicates
  let assignPattern := lines.filterMap (fun s =>
    let trimmed := s.trimAsciiStart.toString
    match trimmed.splitOn " := " with
    | [target, source] =>
      if target.length > 0 && !target.contains '.' then  -- Only top-level assignments (not inst.port)
        some (s, target.trimAscii.toString, source.trimAscii.toString)
      else none
    | _ => none)
  -- Group by target
  let targetGroups := assignPattern.foldl (fun acc (line, tgt, src) =>
    let existing := acc.find? (fun (t, _) => t == tgt) |>.map (·.2) |>.getD []
    let without := acc.filter (fun (t, _) => t != tgt)
    without ++ [(tgt, existing ++ [(line, src)])]) ([] : List (String × List (String × String)))
  -- Find targets with multiple writers
  let multiWriters := targetGroups.filter (fun (_, entries) => entries.length > 1)
  if multiWriters.isEmpty then lines
  else
    -- Collect lines to remove
    let linesToRemove := multiWriters.flatMap (fun (_, entries) => entries.map (·.1))
    -- Generate Cat replacements (reverse for MSB-first Cat ordering)
    let catAssigns := multiWriters.map (fun (tgt, entries) =>
      let catArgs := ", ".intercalate (entries.reverse.map (·.2))
      s!"  {tgt} := Cat({catArgs})")
    -- Replace: keep non-removed lines, append Cat assignments
    let filtered := lines.filter (fun s => !linesToRemove.contains s)
    filtered ++ catAssigns

/-- Generate all module instantiations -/
def generateInstances (ctx : Context) (c : Circuit) (allCircuits : List Circuit) : String :=
  let instances := c.instances.flatMap (generateInstance ctx c allCircuits)
  let processed := postProcessMultiWriterOutputs instances
  joinLines processed

/-! ## Register Generation (ShoumeiReg) -/

/-- Find all DFF gates in circuit -/
def findDFFs (c : Circuit) : List Gate :=
  c.gates.filter (fun g => g.gateType.isDFF)

/-- Compute the init value for a signal group by checking which wires are DFF_SET.
    Returns the integer init value (0 if all DFF, nonzero if some DFF_SET). -/
private def computeGroupInitVal (ctx : Context) (sg : SignalGroup) : Nat :=
  sg.wires.enum.foldl (fun acc ⟨i, w⟩ =>
    if ctx.dffSetOutputSet.contains w.name
    then acc + 2^i else acc) 0

/-- Generate register declaration using ShoumeiReg/ShoumeiRegInit helper -/
def generateRegisterDecl (ctx : Context) (_c : Circuit) (g : Gate) : String :=
  match g.inputs with
  | [_d, _clk, _rst] =>
      match ctx.groupMap[g.output.name]? with
      | some sg =>
          if sg.wires.head? == some g.output then
            let clockRef := "clock"
            let resetRef := if ctx.isSequential then
              "reset.asAsyncReset"
            else
              match ctx.resetWires.head? with
              | some rw => rw.name
              | none => "reset"
            let regName := s!"{sg.name}_reg"
            let initVal := computeGroupInitVal ctx sg
            if initVal == 0 then
              s!"  val {regName} = ShoumeiReg({sg.width}, {clockRef}, {resetRef})"
            else
              s!"  val {regName} = ShoumeiRegInit({sg.width}, BigInt(\"{initVal}\"), {clockRef}, {resetRef})"
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
      match ctx.groupMap[g.output.name]? with
      | some outputGroup =>
          if outputGroup.wires.head? == some g.output then
            let dName := match ctx.groupMap[d.name]? with
              | some dGroup =>
                  match parseIndexedName dGroup.name with
                  | some (baseName, vecIdx) => s!"{baseName}({vecIdx})"
                  | none => dGroup.name
              | none => wireRef ctx c d
            let regName := s!"{outputGroup.name}_reg"
            let dIsVec := match ctx.groupMap[d.name]? with
              | some dGroup => needsVecDeclarationHelper ctx dGroup c
              | none => false
            let dRef := if dIsVec then s!"{dName}.asUInt" else dName
            s!"  {regName} := {dRef}"
          else
            ""
      | none =>
          let dName := wireRef ctx c d
          let regName := s!"{g.output.name}_reg"
          s!"  {regName} := {dName}"
  | _ =>
      ""

/-- Generate wiring from internal registers to output IO ports AND internal Vec wires.
    excludedSet: wire names already driven by instance outputs (skip to avoid double-assignment) -/
def generateRegisterOutputWiring (ctx : Context) (_c : Circuit) (g : Gate) (excludedSet : Std.HashSet String) : String :=
  let isCircuitOutput := ctx.outputWireSet.contains g.output.name
  let isInternalGrouped := !isCircuitOutput && ctx.groupMap.contains g.output.name
  let isExcluded := excludedSet.contains g.output.name

  if (!isCircuitOutput && !isInternalGrouped) || isExcluded then
    ""
  else
    match ctx.groupMap[g.output.name]? with
    | some outputGroup =>
        if outputGroup.wires.head? == some g.output then
          let sgRef := match parseIndexedName outputGroup.name with
            | some (baseName, vecIdx) =>
                if isVecBase ctx baseName then
                  s!"{baseName}({vecIdx})"
                else
                  outputGroup.name
            | none => outputGroup.name
          s!"  {sgRef} := {outputGroup.name}_reg"
        else
          ""
    | none =>
        if isCircuitOutput then
          s!"  {g.output.name} := {g.output.name}_reg"
        else
          ""

/-- Generate all register logic.
    excludedWires: wire names already driven by instance outputs (skip output wiring) -/
def generateRegisters (ctx : Context) (c : Circuit) (excludedWires : List String := []) : String :=
  let dffs := findDFFs c
  let decls := dffs.map (generateRegisterDecl ctx c)
  let updates := dffs.map (generateRegisterUpdate ctx c)
  let excludedSet : Std.HashSet String := excludedWires.foldl (fun s w => s.insert w) {}
  let wirings := dffs.map (fun g => generateRegisterOutputWiring ctx c g excludedSet)

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

/-! ## Method Splitting for JVM 64KB Limit -/

/-- Split code into statements respecting multi-line expressions (paren depth tracking) -/
private def groupIntoStatements (lines : List String) : List String := Id.run do
  let mut stmts : Array (Array String) := #[]
  let mut parenDepth : Int := 0
  let mut braceDepth : Int := 0
  for line in lines do
    let mut po : Int := 0
    let mut pc : Int := 0
    let mut bo : Int := 0
    let mut bc : Int := 0
    for ch in line.toList do
      if ch == '(' then po := po + 1
      else if ch == ')' then pc := pc + 1
      else if ch == '{' then bo := bo + 1
      else if ch == '}' then bc := bc + 1
    if parenDepth == 0 && braceDepth == 0 then
      stmts := stmts.push #[line]
    else
      if stmts.size > 0 then
        let lastIdx := stmts.size - 1
        stmts := stmts.set! lastIdx (stmts[lastIdx]!.push line)
      else
        stmts := stmts.push #[line]
    parenDepth := parenDepth + po - pc
    braceDepth := braceDepth + bo - bc
  return stmts.toList.map (fun arr => String.intercalate "\n" arr.toList)

/-- Split a block of assignment-only code into Scala helper methods.
    All lines must be `:=` assignments (no `val` declarations).
    For blocks with `val` declarations, use splitMixedBlock instead. -/
private def splitIntoHelperMethods (code : String) (pfx : String) (chunkSize : Nat := 300) : String :=
  let lines := code.splitOn "\n" |>.filter (· != "")
  if lines.length ≤ chunkSize then
    code
  else
    let statements := groupIntoStatements lines
    -- Chunk statements
    let chunks := statements.foldl (init := #[#[]]) (fun acc stmt =>
      let lastIdx := acc.size - 1
      if acc[lastIdx]!.size < chunkSize then
        acc.set! lastIdx (acc[lastIdx]!.push stmt)
      else
        acc.push #[stmt]
    )
    let lbrace := "{"
    let rbrace := "}"
    let helpers := chunks.toList.enum.map (fun (i, chunk) =>
      let body := String.intercalate "\n" chunk.toList
      s!"  private def _{pfx}_{i}(): Unit = {lbrace}\n{body}\n  {rbrace}"
    )
    let calls := chunks.toList.enum.map (fun (i, _) =>
      s!"  _{pfx}_{i}()"
    )
    let helpersStr := String.intercalate "\n" helpers
    let callsStr := String.intercalate "\n" calls
    helpersStr ++ "\n" ++ callsStr

/-- Split a block with mixed `val` declarations and `:=` assignments.
    Keeps `val` declarations in the class body, moves assignments to helper methods. -/
private def splitMixedBlock (code : String) (pfx : String) (chunkSize : Nat := 300) : String :=
  let lines := code.splitOn "\n" |>.filter (· != "")
  if lines.length ≤ chunkSize then
    code
  else
    let statements := groupIntoStatements lines
    -- Classify each statement: is it a val declaration?
    let isValDecl (s : String) : Bool :=
      let trimmed := (s.splitOn "\n").head?.getD "" |>.trimAsciiStart.toString
      trimmed.startsWith "val "
    let valDecls := statements.filter isValDecl
    let assigns := statements.filter (fun s => !isValDecl s)
    -- Chunk assignments into helper methods
    let chunks := assigns.foldl (init := #[#[]]) (fun acc stmt =>
      let lastIdx := acc.size - 1
      if acc[lastIdx]!.size < chunkSize then
        acc.set! lastIdx (acc[lastIdx]!.push stmt)
      else
        acc.push #[stmt]
    )
    let lbrace := "{"
    let rbrace := "}"
    let helpers := chunks.toList.enum.map (fun (i, chunk) =>
      let body := String.intercalate "\n" chunk.toList
      s!"  private def _{pfx}_{i}(): Unit = {lbrace}\n{body}\n  {rbrace}"
    )
    let calls := chunks.toList.enum.map (fun (i, _) =>
      s!"  _{pfx}_{i}()"
    )
    let declStr := String.intercalate "\n" valDecls
    let helpersStr := String.intercalate "\n" helpers
    let callsStr := String.intercalate "\n" calls
    declStr ++ "\n" ++ helpersStr ++ "\n" ++ callsStr

/-! ## RAM Primitive Generation -/

/-- Generate Chisel code for a single RAMPrimitive.
    Uses ShoumeiMem (async read) or ShoumeiMem.syncRead (sync read). -/
def generateRAM (ctx : Context) (c : Circuit) (ram : RAMPrimitive) : String :=
  let memType := if ram.syncRead then "ShoumeiMem.syncRead" else "ShoumeiMem"
  let memDecl := s!"  val {ram.name} = {memType}({ram.depth}, {ram.width})"
  -- Write ports
  let writePorts := ram.writePorts.enum.map (fun (_, wp) =>
    let enRef := wireRef ctx c wp.en
    -- Build address: Cat(MSB, ..., LSB) for multi-bit addr
    let addrRefs := wp.addr.reverse.map (wireRef ctx c ·)
    let addrExpr := if addrRefs.length == 1 then addrRefs.head!
                    else "Cat(" ++ String.intercalate ", " addrRefs ++ ")"
    -- Build data: Cat(MSB, ..., LSB)
    let dataRefs := wp.data.reverse.map (wireRef ctx c ·)
    let dataExpr := if dataRefs.length == 1 then dataRefs.head!
                    else "Cat(" ++ String.intercalate ", " dataRefs ++ ")"
    joinLines [
      s!"  when ({enRef}) " ++ "{",
      s!"    {ram.name}.write({addrExpr}, {dataExpr})",
      "  }"
    ])
  -- Read ports (async)
  let readPorts := ram.readPorts.enum.map (fun (_, rp) =>
    let addrRefs := rp.addr.reverse.map (wireRef ctx c ·)
    let addrExpr := if addrRefs.length == 1 then addrRefs.head!
                    else "Cat(" ++ String.intercalate ", " addrRefs ++ ")"
    let readWire := s!"{ram.name}.read({addrExpr})"
    -- Check if all data wires belong to the same signal group for bulk assignment.
    -- Per-bit assignment to a UInt Wire after DontCare init causes Chisel
    -- "Cannot reassign to read-only" errors.
    let firstGroup := rp.data.head?.bind (fun w => ctx.groupMap[w.name]?)
    let allSameGroup := match firstGroup with
      | some sg => rp.data.length == sg.width &&
          rp.data.all (fun w =>
            match ctx.groupMap[w.name]? with
            | some sg' => sg'.name == sg.name
            | none => false)
      | none => false
    if allSameGroup then
      match firstGroup with
      | some sg => s!"  {sg.name} := {readWire}"
      | none => "" -- unreachable
    else
      let assigns := rp.data.enum.map (fun (idx, w) =>
        s!"  {wireRef ctx c w} := {readWire}({idx})")
      joinLines assigns)
  joinLines ([memDecl] ++ writePorts ++ readPorts)

/-- Generate all RAM primitives -/
def generateRAMs (ctx : Context) (c : Circuit) : String :=
  if c.rams.isEmpty then ""
  else
    let ramStrs := c.rams.map (generateRAM ctx c)
    joinLines ramStrs

/-! ## Module Generation -/

/-- Generate complete Chisel module for a circuit -/
def generateModule (c : Circuit) (allCircuits : List Circuit := []) : String :=
  let ctx := mkContext c

  -- Module or RawModule based on sequential/combinational
  let moduleType := if ctx.isSequential then "Module" else "RawModule"

  -- Collect imports for submodule instances in other packages (e.g. decoder modules)
  -- Skip instances that are co-generated (in allCircuits) since they share the same package
  let generatedNames := allCircuits.map (·.name)
  let decoderImports := c.instances.filterMap (fun inst =>
    if inst.moduleName.endsWith "Decoder" && !generatedNames.contains inst.moduleName then
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
  ] ++ (if c.rams.isEmpty then [] else ["import shoumei.ShoumeiMem"]) ++
  decoderImports ++ [
    "",
    "class " ++ c.name ++ " extends " ++ moduleType ++ " {"
  ])

  let io := generateIO ctx c

  -- Generate dontTouch for all output ports to prevent CIRCT DCE from removing them
  let outputDontTouch := c.outputs.filterMap (fun w =>
    if ctx.clockWires.contains w || ctx.resetWires.contains w then none
    else
      match ctx.groupMap[w.name]? with
      | some sg =>
          if sg.wires.head? == some w then
            some s!"  dontTouch({sg.name})"
          else none
      | none => some s!"  dontTouch({w.name})"
  )
  let dontTouchStr := joinLines outputDontTouch

  let internalWires := generateInternalWires ctx c

  -- Generate DontCare for undriven internal wires
  -- A wire is undriven if it's not a gate/DFF output and not an instance output port
  let normalize (s : String) : String :=
    let chars := s.toList.reverse.dropWhile (· == '_') |>.reverse
    if chars.isEmpty then s else String.ofList chars
  let instanceOutputNames := c.instances.flatMap (fun inst =>
    match allCircuits.find? (fun sc => sc.name == inst.moduleName) with
    | none =>
        inst.portMap.filter (fun (_, wire) =>
          !ctx.inputWireSet.contains wire.name
        ) |>.map (fun (_, wire) => wire.name)
    | some subMod =>
        inst.portMap.filter (fun (pname, _) =>
          let portBase := normalize (extractPortBaseName pname)
          subMod.outputs.any (fun w => normalize (extractBaseName w.name) == portBase)
        ) |>.map (fun (_, wire) => wire.name)
  )
  let drivenWireNamesSet : Std.HashSet String := Id.run do
    let mut s := ctx.gateOutputSet
    for w in ctx.inputWireSet do
      s := s.insert w
    for w in instanceOutputNames do
      s := s.insert w
    return s
  let undrivenWires := (findInternalWires c).filter (fun w => !drivenWireNamesSet.contains w.name)
  -- Generate DontCare for undriven signal groups (one per group)
  let undrivenDontCares := undrivenWires.filterMap (fun w =>
    match ctx.groupMap[w.name]? with
    | some sg =>
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
  let combGatesRaw := generateCombGates ctx c instanceOutputNames
  let instances := generateInstances ctx c allCircuits
  let rams := generateRAMs ctx c

  -- Estimate total body size to decide if trait splitting is needed
  let allBodyLines := [io, dontTouchStr, internalWires, undrivenStr,
                       registers, combGatesRaw, instances, rams]
  let totalBodyLines : Nat := allBodyLines.foldl (fun acc s => acc + (s.splitOn "\n").length) 0

  if totalBodyLines > 1500 then
    -- Large module: split into traits to avoid JVM 64KB method size limit.
    -- Each trait gets its own $init$ method in the JVM, sidestepping the limit.
    let traitChunkSize := 500  -- lines per trait
    -- Collect all body lines
    let bodyLines := (io ++ "\n" ++ dontTouchStr ++ "\n" ++ internalWires ++ "\n" ++
                      undrivenStr ++ "\n" ++ registers ++ "\n" ++ combGatesRaw ++ "\n" ++
                      instances ++ "\n" ++ rams).splitOn "\n"
    -- Group into statements (respecting multi-line expressions)
    let stmts := groupIntoStatements (bodyLines.filter (· != ""))
    -- Chunk statements into trait-sized groups
    let traitChunks := stmts.foldl (init := #[#[]]) (fun acc stmt =>
      let lastIdx := acc.size - 1
      let stmtLines := (stmt.splitOn "\n").length
      let currentSize := acc[lastIdx]!.foldl (fun n s => n + (s.splitOn "\n").length) 0
      if currentSize + stmtLines > traitChunkSize && currentSize > 0 then
        acc.push #[stmt]
      else
        acc.set! lastIdx (acc[lastIdx]!.push stmt)
    )
    let traitNames := traitChunks.toList.enum.map (fun (i, _) =>
      s!"{c.name}_Part{i}"
    )
    let lbrace := "{"
    let rbrace := "}"
    let traitDefs := traitChunks.toList.enum.map (fun (i, chunk) =>
      let body := String.intercalate "\n" chunk.toList
      s!"trait {c.name}_Part{i} {lbrace} self: {c.name} =>\n{body}\n{rbrace}"
    )
    let traitMixins := " with " ++ String.intercalate " with " traitNames
    let classDecl := "class " ++ c.name ++ " extends " ++ moduleType ++ traitMixins ++ " " ++ lbrace ++ "\n" ++ rbrace
    let traitsStr := String.intercalate "\n\n" traitDefs
    let preamble := joinLines ([
      s!"// Auto-generated by Shoumei Codegen V2",
      s!"// Source: {c.name}",
      "",
      "package generated",
      "",
      "import chisel3._",
      "import chisel3.util._",
      "import shoumei.ShoumeiReg",
      "import shoumei.ShoumeiRegInit"
    ] ++ (if c.rams.isEmpty then [] else ["import shoumei.ShoumeiMem"]) ++
    decoderImports ++ [""])
    preamble ++ "\n" ++ traitsStr ++ "\n\n" ++ classDecl
  else
    -- Small module: single class (no splitting needed)
    let body := joinLines [
      io,
      dontTouchStr,
      "",
      internalWires,
      undrivenStr,
      "",
      registers,
      "",
      combGatesRaw,
      "",
      instances,
      if rams.isEmpty then "" else "\n" ++ rams
    ]

    let footer := "}"

    joinLines [header, body, footer]

/-! ## Public API -/

/-- Generate Chisel code for a circuit.
    Pass allCircuits to enable sub-module port direction lookup for hierarchical modules. -/
def toChisel (c : Circuit) (allCircuits : List Circuit := []) : String :=
  generateModule c allCircuits

end Shoumei.Codegen.Chisel
