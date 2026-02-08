/-
Codegen/SystemC.lean - SystemC Code Generator

Generates SystemC simulation models from DSL circuits.

Design:
- Generates both .h (header) and .cpp (implementation) files
- SC_MODULE for all circuits
- SC_METHOD for combinational logic with sensitivity lists
- SC_CTHREAD for sequential logic (DFFs) with clock edges
- Hierarchical: submodule instances with port bindings
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
  | GateType.AND => "&&"
  | GateType.OR => "||"
  | GateType.NOT => "!"   -- Logical NOT for bool (not bitwise ~)
  | GateType.XOR => "!="  -- XOR is logical inequality for bool
  | GateType.BUF => ""    -- Buffer is direct assignment (no operator)
  | GateType.MUX => "?"   -- Ternary operator (special handling required)
  | GateType.DFF | GateType.DFF_SET => ""    -- DFFs use SC_CTHREAD, not operators

-- Helper: Get wire reference for SystemC (handles both individual and bundled I/O)
-- portNames/implPrefix: for PIMPL mode, internal wires get prefixed with "pImpl->"
def wireRef (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (w : Wire)
    (portNames : List String := []) (implPrefix : String := "") : String :=
  match inputToIndex.find? (fun p => p.fst.name == w.name) with
  | some (_wire, idx) => s!"inputs[{idx}]"
  | none =>
      match outputToIndex.find? (fun p => p.fst.name == w.name) with
      | some (_wire, idx) => s!"outputs[{idx}]"
      | none =>
        if implPrefix != "" && !portNames.contains w.name then implPrefix ++ w.name
        else w.name

-- Helper: find all internal wires (gate outputs and instance wires that are not circuit I/O)
def findInternalWires (c : Circuit) : List Wire :=
  let gateOutputs := c.gates.map (fun g => g.output)
  let instanceWires := c.instances.flatMap (fun inst => inst.portMap.map (·.snd))
  let allWires := gateOutputs ++ instanceWires
  (allWires.filter (fun w => !c.outputs.contains w && !c.inputs.contains w)).eraseDups

-- Helper: find wires that MUST be sc_signal (connected to submodule ports or DFF outputs)
-- These cannot be plain bool because SystemC port binding requires sc_signal.
def findSignalWires (c : Circuit) : List Wire :=
  let instanceWires := c.instances.flatMap (fun inst => inst.portMap.map (·.snd))
  let dffOutputs := c.gates.filter (fun g => g.gateType.isDFF) |>.map (fun g => g.output)
  -- DFF inputs (d) also need to be signals since they're read by seq_logic SC_CTHREAD
  let dffInputs := c.gates.filterMap (fun g =>
    if g.gateType.isDFF then
      match g.inputs with
      | [d, _, _] => some d
      | _ => none
    else none)
  (instanceWires ++ dffOutputs ++ dffInputs).eraseDups

-- Build a precomputed list of wire names that must be sc_signal.
-- Includes: I/O ports, instance-connected wires, DFF outputs, DFF inputs.
def buildSignalNameList (c : Circuit) : List String :=
  let signalWires := findSignalWires c
  (signalWires.map (·.name) ++ c.outputs.map (·.name) ++ c.inputs.map (·.name)).eraseDups

-- Check if a wire name is in the precomputed signal list
def isSignalName (sigNames : List String) (name : String) : Bool :=
  sigNames.contains name

-- Find sc_signal wires that are ALSO outputs of combinational gates.
-- These need shadow bool variables for correct single-pass comb_logic evaluation.
-- Without shadows, sc_signal .read() returns stale (previous delta-cycle) values
-- when the signal is both written and read within the same comb_logic method.
def findCombDrivenSignals (c : Circuit) : List String :=
  let sigNames := buildSignalNameList c
  let combGateOutputs := c.gates.filter (·.gateType.isCombinational) |>.map (·.output.name)
  let ioNames := (c.inputs.map (·.name) ++ c.outputs.map (·.name))
  -- A comb-driven signal is one that is an INTERNAL sc_signal AND a comb gate output
  -- Exclude I/O ports (they use sc_in/sc_out, not sc_signal, and don't need shadows)
  combGateOutputs.filter (fun n => sigNames.contains n && !ioNames.contains n) |>.eraseDups

-- Read expression for a wire: uses .read() for sc_signal, direct access for bool
-- combShadows: names of sc_signals that have shadow bool variables in comb_logic
def wireReadExpr (sigNames : List String) (inputToIndex : List (Wire × Nat))
    (outputToIndex : List (Wire × Nat)) (w : Wire)
    (combShadows : List String := [])
    (portNames : List String := []) (implPrefix : String := "") : String :=
  let ref := wireRef inputToIndex outputToIndex w portNames implPrefix
  -- Bundled I/O always uses .read()
  if inputToIndex.any (fun p => p.fst.name == w.name) then s!"{ref}.read()"
  else if outputToIndex.any (fun p => p.fst.name == w.name) then s!"{ref}.read()"
  -- Comb-driven sc_signals: read from shadow bool in comb_logic
  else if combShadows.contains w.name then s!"{ref}_shadow"
  -- sc_signal wires (ports, instance wires, DFF outputs) use .read()
  else if isSignalName sigNames w.name then s!"{ref}.read()"
  -- Plain bool intermediates use direct access
  else ref

-- Write statement for a wire: uses .write() for sc_signal, = for bool
-- combShadows: names of sc_signals that have shadow bool variables in comb_logic
def wireWriteStmt (sigNames : List String) (inputToIndex : List (Wire × Nat))
    (outputToIndex : List (Wire × Nat)) (w : Wire) (expr : String)
    (combShadows : List String := [])
    (portNames : List String := []) (implPrefix : String := "") : String :=
  let ref := wireRef inputToIndex outputToIndex w portNames implPrefix
  if inputToIndex.any (fun p => p.fst.name == w.name) then s!"  {ref}.write({expr});"
  else if outputToIndex.any (fun p => p.fst.name == w.name) then s!"  {ref}.write({expr});"
  -- Comb-driven sc_signals: write to shadow bool AND sc_signal
  else if combShadows.contains w.name then
    s!"  {ref}_shadow = {expr};\n  {ref}.write({ref}_shadow);"
  else if isSignalName sigNames w.name then s!"  {ref}.write({expr});"
  else s!"  {ref} = {expr};"

-- Helper: find all DFF output wires (need special handling)
def findDFFOutputs (c : Circuit) : List Wire :=
  c.gates.filter (fun g => g.gateType.isDFF)
    |>.map (fun g => g.output)

-- Helper: find all clock wires (from DFF inputs)
def findClockWires (c : Circuit) : List Wire :=
  let dffClocks := c.gates.filterMap (fun g =>
    if g.gateType.isDFF then
      match g.inputs with
      | [_d, clk, _reset] => some clk
      | _ => none
    else
      none)
  -- Also detect clocks from instance port connections
  let instanceClocks := c.instances.filterMap (fun inst =>
    inst.portMap.find? (fun (pname, _) => pname == "clock") |>.map (·.snd))
  (dffClocks ++ instanceClocks).eraseDups

-- Helper: find all reset wires (from DFF inputs)
def findResetWires (c : Circuit) : List Wire :=
  let dffResets := c.gates.filterMap (fun g =>
    if g.gateType.isDFF then
      match g.inputs with
      | [_d, _clk, reset] => some reset
      | _ => none
    else
      none)
  let instanceResets := c.instances.filterMap (fun inst =>
    inst.portMap.find? (fun (pname, _) => pname == "reset") |>.map (·.snd))
  (dffResets ++ instanceResets).eraseDups

-- Helper: check if circuit has sequential elements (DFFs or instances with clock)
def hasSequentialElements (c : Circuit) : Bool :=
  c.hasSequentialElements ||
  c.instances.any (fun inst =>
    inst.portMap.any (fun (pname, _) => pname == "clock"))

/-! ## Instance Support -/

/-- Get unique submodule types used by this circuit -/
def getInstanceModuleNames (c : Circuit) : List String :=
  (c.instances.map (·.moduleName)).eraseDups

/-- Generate #include directives for submodule headers -/
def generateInstanceIncludes (c : Circuit) : String :=
  let moduleNames := getInstanceModuleNames c
  if moduleNames.isEmpty then ""
  else
    let includes := moduleNames.map fun name => s!"#include \"{name}.h\""
    joinLines includes

/-- Generate submodule instance member declarations for header -/
def generateInstanceDeclarations (c : Circuit) : String :=
  if c.instances.isEmpty then ""
  else
    let decls := c.instances.map fun inst =>
      s!"  {inst.moduleName} {inst.instName};"
    joinLines decls

/-- Generate instance initializer list entries for constructor.
    Each submodule needs to be initialized with a string name. -/
def generateInstanceInitList (c : Circuit) : List String :=
  c.instances.map fun inst =>
    s!"    {inst.instName}(\"{inst.instName}\")"

/-- Parse a port map key to extract base name and optional bit index.
    "in0[3]" → some ("in0", 3), "sel[0]" → some ("sel", 0), "clock" → none -/
private def parsePortMapKey (portName : String) : Option (String × Nat) :=
  match portName.splitOn "[" with
  | [base, idxPart] =>
      let idxStr := String.ofList (idxPart.toList.takeWhile (· != ']'))
      match idxStr.toNat? with
      | some idx => some (base, idx)
      | none => none
  | _ =>
      -- Try trailing underscore+digits: "in_0" → ("in", 0)
      let chars := portName.toList
      let digitSuffix := chars.reverse.takeWhile Char.isDigit |>.reverse
      if digitSuffix.isEmpty then none
      else
        let idxStr := String.ofList digitSuffix
        let baseChars := chars.take (chars.length - digitSuffix.length)
        -- Strip trailing underscore from base
        let baseChars := if baseChars.getLast? == some '_' then baseChars.dropLast else baseChars
        match idxStr.toNat? with
        | some idx => some (String.ofList baseChars, idx)
        | none => none

/-- Build a mapping from possible portMap key names → actual wire names for a submodule.
    For each submodule port wire, generates candidate portMap key forms that might reference it. -/
private def buildPortNameMapping (allCircuits : List Circuit) (moduleName : String)
    : List (String × String) :=
  -- Returns: list of (candidatePortMapKey, actualWireName)
  match allCircuits.find? (fun sc => sc.name == moduleName) with
  | none => []
  | some subMod =>
      (subMod.inputs ++ subMod.outputs).flatMap fun w =>
        let name := w.name
        -- Always include identity mapping
        let candidates := [name]
        -- Parse trailing digits to generate alternate forms
        let chars := name.toList
        let digitSuffix := chars.reverse.takeWhile Char.isDigit |>.reverse
        let candidates := if digitSuffix.isEmpty then candidates
        else
          let idxStr := String.ofList digitSuffix
          let baseChars := chars.take (chars.length - digitSuffix.length)
          let baseStr := String.ofList baseChars
          -- Generate: base[idx], base_idx (with various base strippings)
          -- Strip trailing separators: "_b", "__", "_"
          let strippedBases : List String :=
            [baseStr] ++
            (if baseStr.endsWith "_b" then [(baseStr.dropEnd 2).toString] else []) ++
            (if baseStr.endsWith "__" then [(baseStr.dropEnd 2).toString] else []) ++
            (if baseStr.endsWith "_" then [(baseStr.dropEnd 1).toString] else [])
          let extraCandidates := strippedBases.flatMap fun b =>
            [s!"{b}[{idxStr}]", s!"{b}_{idxStr}", s!"{b}{idxStr}", b]
          candidates ++ extraCandidates
        candidates.map fun c => (c, name)

/-- Resolve a portMap key to the actual SystemC port name on the submodule. -/
private def resolvePortName (mapping : List (String × String)) (portName : String) : String :=
  match mapping.find? (fun (key, _) => key == portName) with
  | some (_, actualName) => actualName
  | none =>
      -- Fallback: simple bracket→underscore conversion
      let s := portName.replace "[" "_"
      s.replace "]" ""

/-- Generate port bindings for a single instance in the constructor body.
    Handles multiple portMap naming conventions:
    - Direct match: portMap key matches submodule wire name exactly
    - Indexed: portMap key "in0[3]" matches submodule wire "in0_b3"
    - Bare repeated: portMap key "a" repeated N times matches "a_0".."a_{N-1}" -/
def generateInstanceBindings (allCircuits : List Circuit) (inst : CircuitInstance) : String :=
  -- Check if submodule uses bundled IO (sc_vector)
  match allCircuits.find? (fun sc => sc.name == inst.moduleName) with
  | some subMod =>
    let useBundledIO := (subMod.inputs.length + subMod.outputs.length) > 500 && subMod.instances.isEmpty
    if useBundledIO then
      -- Bundled IO: map portMap entries to inputs[N] / outputs[N] positionally
      let inputNames := subMod.inputs.map (·.name)
      let outputNames := subMod.outputs.map (·.name)
      let mapping := buildPortNameMapping allCircuits inst.moduleName
      let (bindings, _bareIdxMap) := inst.portMap.foldl
        (fun (acc : List String × List (String × Nat)) (portName, wire) =>
          let (lines, bmap) := acc
          -- Resolve portMap key to actual submodule wire name
          let curIdx := (bmap.find? (fun (n, _) => n == portName)).map (·.2) |>.getD 0
          let candidates := mapping.filter (fun (key, _) => key == portName)
          let count := inst.portMap.filter (fun (pn, _) => pn == portName) |>.length
          let actualName := if count > 1 && curIdx < candidates.length then
            (candidates[curIdx]!).2
          else match candidates.head? with
            | some (_, n) => n
            | none => portName
          let newMap := if count > 1 then
            match bmap.find? (fun (n, _) => n == portName) with
            | some _ => bmap.map (fun (n, i) => if n == portName then (n, i + 1) else (n, i))
            | none => bmap ++ [(portName, 1)]
          else bmap
          -- Find position: is it an input or output?
          match inputNames.findIdx? (· == actualName) with
          | some idx =>
              (lines ++ [s!"    {inst.instName}.inputs[{idx}]({wire.name});"], newMap)
          | none =>
              match outputNames.findIdx? (· == actualName) with
              | some idx =>
                  (lines ++ [s!"    {inst.instName}.outputs[{idx}]({wire.name});"], newMap)
              | none =>
                  -- Direct port name (clock, reset, etc.)
                  (lines ++ [s!"    {inst.instName}.{actualName}({wire.name});"], newMap)
        ) ([], [])
      joinLines bindings
    else
      -- Individual ports: use name mapping
      generateInstanceBindingsNamed allCircuits inst
  | none =>
      -- Submodule not in allCircuits (e.g., hand-written decoder)
      generateInstanceBindingsNamed allCircuits inst
where
  /-- Generate bindings using named ports -/
  generateInstanceBindingsNamed (allCircuits : List Circuit) (inst : CircuitInstance) : String :=
    let mapping := buildPortNameMapping allCircuits inst.moduleName
    let (bindings, _) := inst.portMap.foldl (fun (acc : List String × List (String × Nat)) (portName, wire) =>
      let (lines, bareIdxMap) := acc
      match mapping.find? (fun (key, _) => key == portName) with
      | some (_, actualName) =>
          let count := inst.portMap.filter (fun (pn, _) => pn == portName) |>.length
          if count > 1 then
            let curIdx := (bareIdxMap.find? (fun (n, _) => n == portName)).map (·.2) |>.getD 0
            let candidates := mapping.filter (fun (key, _) => key == portName)
            let actualName := if curIdx < candidates.length then
              (candidates[curIdx]!).2
            else actualName
            let newMap := match bareIdxMap.find? (fun (n, _) => n == portName) with
              | some _ => bareIdxMap.map (fun (n, i) => if n == portName then (n, i + 1) else (n, i))
              | none => bareIdxMap ++ [(portName, 1)]
            (lines ++ [s!"    {inst.instName}.{actualName}({wire.name});"], newMap)
          else
            (lines ++ [s!"    {inst.instName}.{actualName}({wire.name});"], bareIdxMap)
      | none =>
          let s := portName.replace "[" "_"
          let scPortName := s.replace "]" ""
          (lines ++ [s!"    {inst.instName}.{scPortName}({wire.name});"], bareIdxMap)
    ) ([], [])
    joinLines bindings

/-- Generate all instance port bindings for the constructor body -/
def generateAllInstanceBindings (allCircuits : List Circuit) (c : Circuit) : String :=
  if c.instances.isEmpty then ""
  else
    let bindings := c.instances.map fun inst =>
      s!"    // {inst.instName} ({inst.moduleName})\n" ++
      generateInstanceBindings allCircuits inst
    joinLines bindings

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
-- Wires connected to submodule ports or DFFs must be sc_signal<bool>.
-- Pure combinational intermediates use plain bool for correct same-cycle evaluation.
def generateSignalDeclarations (c : Circuit) : String :=
  let internalWires := findInternalWires c
  if internalWires.isEmpty then
    ""
  else
    let sigNames := buildSignalNameList c
    let combDriven := findCombDrivenSignals c
    let decls := internalWires.map (fun w =>
      if isSignalName sigNames w.name then
        if combDriven.contains w.name then
          -- Comb-driven sc_signal: declare both sc_signal (for ports) and shadow bool (for comb_logic)
          s!"  sc_signal<bool> {w.name};\n  bool {w.name}_shadow = false;"
        else
          s!"  sc_signal<bool> {w.name};"
      else
        s!"  bool {w.name} = false;")
    joinLines decls

-- Generate sensitivity list for SC_METHOD (all non-clock/reset inputs for data)
def generateSensitivityList (c : Circuit) (useBundledIO : Bool) : String :=
  if useBundledIO then
    -- For large bundled I/O circuits, use dont_initialize()
    -- The simulator will trigger evaluation on any input change
    "    dont_initialize();"
  else
    -- Individual inputs (exclude clock/reset from combinational sensitivity)
    let isSeq := hasSequentialElements c
    let clocks := findClockWires c
    let resets := findResetWires c

    let dataInputs := if isSeq then
      c.inputs.filter (fun w => !clocks.contains w && !resets.contains w)
    else
      c.inputs

    -- Also include internal sc_signal wires that are driven by instances (submodule outputs)
    -- or DFFs. Plain bool intermediates don't need sensitivity (computed inline).
    let internalWires := findInternalWires c
    let sigNames := buildSignalNameList c
    let internalSignalWires := internalWires.filter (fun w =>
      isSignalName sigNames w.name)
    let allSenseWires := dataInputs ++ internalSignalWires

    if allSenseWires.isEmpty then
      "    // No data inputs for sensitivity list"
    else
      let inputNames := allSenseWires.map (fun w => w.name)
      let senseList := String.intercalate " << " inputNames
      s!"    sensitive << {senseList};"

-- Generate constructor (SC_CTOR) with process registration
def generateConstructor (c : Circuit) (useBundledIO : Bool) (allCircuits : List Circuit := []) : String :=
  let moduleName := c.name
  let hasInstances := !c.instances.isEmpty

  -- Build initializer list
  let initParts : List String :=
    -- Bundled I/O init
    (if useBundledIO then
      [s!"    inputs(\"inputs\", {c.inputs.length}), outputs(\"outputs\", {c.outputs.length})"]
    else []) ++
    -- Instance member init
    generateInstanceInitList c

  -- No SC_METHOD registration: evaluation is driven entirely by the
  -- testbench calling eval_seq_all()/eval_comb_all() each cycle.
  -- This avoids delta-cycle ordering issues in hierarchical designs.
  let processReg : List String := []

  -- Instance port bindings (in constructor body)
  let instanceBindings := if hasInstances then
    ["", "    // Submodule port bindings", generateAllInstanceBindings allCircuits c]
  else []

  let ctorLine := if initParts.isEmpty then
    s!"  SC_CTOR({moduleName}) " ++ "{"
  else
    s!"  SC_CTOR({moduleName})\n" ++
    "    : " ++ String.intercalate ",\n      " initParts ++ "\n  {"

  joinLines ([ctorLine] ++ processReg ++ instanceBindings ++ ["  }"])

-- Generate a single combinational gate assignment (for .cpp file)
-- Uses plain bool assignment for pure combinational intermediates,
-- and sc_signal .write()/.read() for wires connected to ports/DFFs.
def generateCombGateSystemC (sigNames : List String) (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (combShadows : List String) (g : Gate)
    (portNames : List String := []) (implPrefix : String := "") : String :=
  let op := gateTypeToOperator g.gateType
  let rd := fun w => wireReadExpr sigNames inputToIndex outputToIndex w combShadows portNames implPrefix
  let wr := fun expr => wireWriteStmt sigNames inputToIndex outputToIndex g.output expr combShadows portNames implPrefix

  match g.gateType with
  | GateType.NOT =>
      match g.inputs with
      | [i0] => wr s!"!{rd i0}"
      | _ => "  // ERROR: NOT gate should have 1 input"
  | GateType.BUF =>
      match g.inputs with
      | [i0] => wr (rd i0)
      | _ => "  // ERROR: BUF gate should have 1 input"
  | GateType.MUX =>
      -- Ternary operator: sel ? in1 : in0
      -- inputs: [in0, in1, sel]
      match g.inputs with
      | [in0, in1, sel] =>
          wr s!"{rd sel} ? {rd in1} : {rd in0}"
      | _ => "  // ERROR: MUX gate should have 3 inputs: [in0, in1, sel]"
  | GateType.DFF | GateType.DFF_SET =>
      ""  -- DFFs handled in seq_logic, not comb_logic
  | _ =>
      -- Binary operators: input1 op input2
      match g.inputs with
      | [i0, i1] =>
          wr s!"{rd i0} {op} {rd i1}"
      | _ => "  // ERROR: Binary gate should have 2 inputs"

-- Generate DFF logic for SC_CTHREAD
def generateDFFSystemC (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (g : Gate)
    (portNames : List String := []) (implPrefix : String := "") : String :=
  match g.inputs with
  | [d, _clk, reset] =>
      let dRef := wireRef inputToIndex outputToIndex d portNames implPrefix
      let resetRef := wireRef inputToIndex outputToIndex reset portNames implPrefix
      let qRef := wireRef inputToIndex outputToIndex g.output portNames implPrefix
      let resetVal := if g.gateType == GateType.DFF_SET then "true" else "false"
      joinLines [
        s!"    if ({resetRef}.read()) " ++ "{",
        s!"      {qRef}.write({resetVal});",
        "    } else {",
        s!"      {qRef}.write({dRef}.read());",
        "    }"
      ]
  | _ => "    // ERROR: DFF should have 3 inputs: [d, clk, reset]"

-- Topological sort of combinational gates.
-- Gates are sorted so that a gate's input wires are produced before they are consumed.
-- Wires that are circuit inputs, DFF outputs, or instance port outputs are "available"
-- from the start (they don't need to be produced by a comb gate).
def topSortCombGates (c : Circuit) : List Gate :=
  let combGates := c.gates.filter (fun g => g.gateType.isCombinational)
  -- Comb gate outputs that are also sc_signals use shadow bools,
  -- so they must NOT be treated as pre-available.
  let combGateOutputNames := combGates.map (·.output.name)
  -- Build set of wire names that are available without a comb gate producing them
  let inputNames := c.inputs.map (·.name)
  let dffOutputNames := c.gates.filter (·.gateType.isDFF) |>.map (·.output.name)
  let instOutputNames := List.flatten (c.instances.map (fun inst =>
    inst.portMap.map (fun p => p.2.name)))
  -- Filter out wires that are produced by comb gates (they must be topo-sorted)
  let available := (inputNames ++ dffOutputNames ++ instOutputNames).filter
    (fun n => !combGateOutputNames.contains n)
  -- Iteratively emit gates whose inputs are all available
  let rec loop (remaining : List Gate) (avail : List String) (sorted : List Gate)
      (fuel : Nat) : List Gate :=
    match fuel with
    | 0 => sorted ++ remaining  -- fallback: append unsorted remainder
    | fuel + 1 =>
      if remaining.isEmpty then sorted
      else
        let (ready, notReady) := remaining.partition (fun g =>
          g.inputs.all (fun w => avail.contains w.name))
        if ready.isEmpty then
          -- No progress; break cycle by emitting first remaining gate
          match remaining with
          | g :: rest => loop rest (avail ++ [g.output.name]) (sorted ++ [g]) fuel
          | [] => sorted
        else
          let newAvail := avail ++ ready.map (·.output.name)
          loop notReady newAvail (sorted ++ ready) fuel
  loop combGates available [] (combGates.length + 1)

-- Generate comb_logic method body
def generateCombMethod (c : Circuit) (useBundledIO : Bool)
    (portNames : List String := []) (implPrefix : String := "") : String :=
  let inputToIndex := if useBundledIO then c.inputs.enum.map (fun ⟨idx, w⟩ => (w, idx)) else []
  let outputToIndex := if useBundledIO then c.outputs.enum.map (fun ⟨idx, w⟩ => (w, idx)) else []

  let combGates := topSortCombGates c
  if combGates.isEmpty then ""
  else
    let sigNames := buildSignalNameList c
    let combShadows := findCombDrivenSignals c
    let assignments := combGates.map (fun g => generateCombGateSystemC sigNames inputToIndex outputToIndex combShadows g portNames implPrefix)
    joinLines [
      s!"void {c.name}::comb_logic() " ++ "{",
      joinLines assignments,
      "}"
    ]

-- Generate seq_logic method body (for sequential circuits)
def generateSeqMethod (c : Circuit) (useBundledIO : Bool)
    (portNames : List String := []) (implPrefix : String := "") : String :=
  let inputToIndex := if useBundledIO then c.inputs.enum.map (fun ⟨idx, w⟩ => (w, idx)) else []
  let outputToIndex := if useBundledIO then c.outputs.enum.map (fun ⟨idx, w⟩ => (w, idx)) else []

  let dffGates := c.gates.filter (fun g => g.gateType.isDFF)
  if dffGates.isEmpty then ""
  else
    let dffLogic := dffGates.map (fun g => generateDFFSystemC inputToIndex outputToIndex g portNames implPrefix)
    joinLines [
      s!"void {c.name}::seq_logic() " ++ "{",
      joinLines dffLogic,
      "}"
    ]

-- Main function: Generate SystemC header file (.h)
-- When a circuit has submodule instances, uses PIMPL pattern to keep headers thin.
-- Internal signals and submodule instances go behind struct Impl* in the .cpp.
def toSystemCHeader (c : Circuit) (allCircuits : List Circuit := []) : String :=
  let moduleName := c.name
  let guardName := moduleName.toUpper ++ "_H"
  let isSeq := hasSequentialElements c
  let useBundledIO := (c.inputs.length + c.outputs.length) > 500 && c.instances.isEmpty
  let usePimpl := !c.instances.isEmpty

  -- Port declarations
  let portDecls := generatePortDeclarations c useBundledIO

  -- Process method declarations
  let combGates := c.gates.filter (fun g => g.gateType.isCombinational)
  let hasCombLogic := !combGates.isEmpty
  let dffGates := c.gates.filter (fun g => g.gateType.isDFF)
  let hasDFFs := !dffGates.isEmpty

  let processDecls :=
    (if hasCombLogic then ["  void comb_logic();"] else []) ++
    (if isSeq && hasDFFs then ["  void seq_logic();"] else []) ++
    ["  void eval_comb_all();",
     "  void eval_seq_all();"]

  if usePimpl then
    -- PIMPL header: ports + method signatures only, no submodule includes
    let parts := [
      s!"#ifndef {guardName}",
      s!"#define {guardName}",
      "",
      "#include <systemc.h>",
      "",
      s!"SC_MODULE({moduleName}) " ++ "{",
      "  // Ports",
      portDecls,
      "",
      "  // PIMPL: internal signals and submodule instances in .cpp",
      "  struct Impl;",
      "  Impl* pImpl;",
      "",
      "  // Process methods"
    ] ++
    processDecls ++
    ["",
      s!"  SC_CTOR({moduleName});",
      s!"  ~{moduleName}();",
      "};",
      "",
      s!"#endif // {guardName}"
    ]
    joinLines parts
  else
    -- Non-PIMPL header: original behavior for leaf modules
    let instanceIncludes := generateInstanceIncludes c
    let signalDecls := generateSignalDeclarations c
    let instanceDecls := generateInstanceDeclarations c
    let ctor := generateConstructor c useBundledIO allCircuits

    let parts := [
      s!"#ifndef {guardName}",
      s!"#define {guardName}",
      "",
      "#include <systemc.h>"
    ] ++
    (if instanceIncludes.isEmpty then [] else [instanceIncludes]) ++
    ["",
      s!"SC_MODULE({moduleName}) " ++ "{",
      "  // Ports",
      portDecls
    ] ++
    (if signalDecls.isEmpty then [] else ["", "  // Internal signals", signalDecls]) ++
    (if instanceDecls.isEmpty then [] else ["", "  // Submodule instances", instanceDecls]) ++
    ["",
      "  // Process methods"
    ] ++
    processDecls ++
    ["",
      "  // Constructor",
      ctor,
      "};",
      "",
      s!"#endif // {guardName}"
    ]
    joinLines parts

-- Generate PIMPL-aware instance port bindings for the constructor body.
-- Instances and internal wires get "pImpl->" prefix; parent ports don't.
def generatePimplInstanceBindings (allCircuits : List Circuit) (c : Circuit) : String :=
  let portNames := (c.inputs ++ c.outputs).map (·.name)
  let bindings := c.instances.map fun inst =>
    let mapping := buildPortNameMapping allCircuits inst.moduleName
    let comment := s!"    // {inst.instName} ({inst.moduleName})"
    let (lines, _) := inst.portMap.foldl (fun (acc : List String × List (String × Nat)) (portName, wire) =>
      let (ls, bareIdxMap) := acc
      let candidates := mapping.filter (fun (key, _) => key == portName)
      let count := inst.portMap.filter (fun (pn, _) => pn == portName) |>.length
      let curIdx := (bareIdxMap.find? (fun (n, _) => n == portName)).map (·.2) |>.getD 0
      let actualName := if count > 1 && curIdx < candidates.length then
        (candidates[curIdx]!).2
      else match candidates.head? with
        | some (_, n) => n
        | none =>
          let s := portName.replace "[" "_"
          s.replace "]" ""
      let newMap := if count > 1 then
        match bareIdxMap.find? (fun (n, _) => n == portName) with
        | some _ => bareIdxMap.map (fun (n, i) => if n == portName then (n, i + 1) else (n, i))
        | none => bareIdxMap ++ [(portName, 1)]
      else bareIdxMap
      let wireExpr := if portNames.contains wire.name then wire.name
                      else s!"pImpl->{wire.name}"
      (ls ++ [s!"    pImpl->{inst.instName}.{actualName}({wireExpr});"], newMap)
    ) ([], [])
    comment ++ "\n" ++ joinLines lines
  joinLines bindings

-- Main function: Generate SystemC implementation file (.cpp)
def toSystemCImpl (c : Circuit) (allCircuits : List Circuit := []) : String :=
  let moduleName := c.name
  let isSeq := hasSequentialElements c
  let useBundledIO := (c.inputs.length + c.outputs.length) > 500 && c.instances.isEmpty
  let usePimpl := !c.instances.isEmpty
  let hasDFFs := !(c.gates.filter (·.gateType.isDFF)).isEmpty
  let hasCombLogic := !(c.gates.filter (·.gateType.isCombinational)).isEmpty

  -- PIMPL parameters for method generation
  let portNames := if usePimpl then (c.inputs ++ c.outputs).map (·.name) else []
  let implPrefix := if usePimpl then "pImpl->" else ""

  let combMethod := generateCombMethod c useBundledIO portNames implPrefix
  let seqMethod := if isSeq then generateSeqMethod c useBundledIO portNames implPrefix else ""

  -- eval_comb_all / eval_seq_all with PIMPL-aware instance calls
  let instPrefix := if usePimpl then "pImpl->" else ""
  let instCombCalls := c.instances.map (fun inst =>
    s!"  {instPrefix}{inst.instName}.eval_comb_all();")
  let evalCombAllBody :=
    (if hasCombLogic then ["  comb_logic();"] else []) ++
    instCombCalls
  let evalCombAll := joinLines [
    s!"void {moduleName}::eval_comb_all() " ++ "{",
    joinLines evalCombAllBody,
    "}"
  ]

  let instSeqCalls := c.instances.map (fun inst =>
    s!"  {instPrefix}{inst.instName}.eval_seq_all();")
  let ownSeq := if hasDFFs then ["  seq_logic();"] else []
  let evalSeqAll := joinLines [
    s!"void {moduleName}::eval_seq_all() " ++ "{",
    joinLines (instSeqCalls ++ ownSeq),
    "}"
  ]

  if usePimpl then
    -- Generate Impl struct with internal signals and submodule instances
    let signalDecls := generateSignalDeclarations c
    let instanceDecls := generateInstanceDeclarations c
    let initList := generateInstanceInitList c
    let initPart := if initList.isEmpty then ""
      else "\n    : " ++ String.intercalate ",\n      " initList

    -- Submodule includes
    let instanceIncludes := generateInstanceIncludes c

    -- Constructor + destructor
    let instanceBindings := generatePimplInstanceBindings allCircuits c

    let parts := [
      s!"#include \"{moduleName}.h\"",
      instanceIncludes,
      "",
      s!"struct {moduleName}::Impl " ++ "{"
    ] ++
    (if signalDecls.isEmpty then [] else ["  // Internal signals", signalDecls]) ++
    (if instanceDecls.isEmpty then [] else ["", "  // Submodule instances", instanceDecls]) ++
    [s!"",
     s!"  Impl(){initPart} " ++ "{}",
     "};",
     "",
     s!"{moduleName}::{moduleName}(sc_module_name name) : sc_module(name) " ++ "{",
     "  pImpl = new Impl();"
    ] ++
    (if instanceBindings.isEmpty then [] else ["", instanceBindings]) ++
    ["}",
     "",
     s!"{moduleName}::~{moduleName}() " ++ "{",
     "  delete pImpl;",
     "}"
    ] ++
    (if combMethod.isEmpty then [] else ["", combMethod]) ++
    (if seqMethod.isEmpty then [] else ["", seqMethod]) ++
    ["", evalCombAll, "", evalSeqAll]

    joinLines parts
  else
    -- Non-PIMPL: original behavior
    let parts := [
      s!"#include \"{moduleName}.h\"",
      ""
    ] ++
    (if combMethod.isEmpty then [] else [combMethod]) ++
    (if seqMethod.isEmpty then [] else ["", seqMethod]) ++
    ["", evalCombAll, "", evalSeqAll]

    joinLines parts

end Shoumei.Codegen.SystemC
