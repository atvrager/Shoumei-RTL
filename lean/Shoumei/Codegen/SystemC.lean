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
def wireRef (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (w : Wire) : String :=
  match inputToIndex.find? (fun p => p.fst.name == w.name) with
  | some (_wire, idx) => s!"inputs[{idx}]"
  | none =>
      match outputToIndex.find? (fun p => p.fst.name == w.name) with
      | some (_wire, idx) => s!"outputs[{idx}]"
      | none => w.name

-- Helper: find all internal wires (gate outputs and instance wires that are not circuit I/O)
def findInternalWires (c : Circuit) : List Wire :=
  let gateOutputs := c.gates.map (fun g => g.output)
  let instanceWires := c.instances.flatMap (fun inst => inst.portMap.map (·.snd))
  let allWires := gateOutputs ++ instanceWires
  (allWires.filter (fun w => !c.outputs.contains w && !c.inputs.contains w)).eraseDups

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
def generateSignalDeclarations (c : Circuit) : String :=
  let internalWires := findInternalWires c
  if internalWires.isEmpty then
    ""
  else
    let decls := internalWires.map (fun w => s!"  sc_signal<bool> {w.name};")
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

    -- Also include internal signals that are driven by instances (submodule outputs)
    -- These feed into the parent's combinational gates
    let internalWires := findInternalWires c
    let allSenseWires := dataInputs ++ internalWires

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

  -- Process registration
  let clocks := findClockWires c
  let clockName := if !clocks.isEmpty then clocks.head!.name else "clock"

  let combGates := c.gates.filter (fun g => g.gateType.isCombinational)
  let hasCombLogic := !combGates.isEmpty

  let processReg : List String :=
    -- Register comb_logic only if there are combinational gates
    (if hasCombLogic then
      ["    SC_METHOD(comb_logic);",
       generateSensitivityList c useBundledIO]
    else []) ++
    -- Register seq_logic only if this module has its own DFF gates
    -- (submodule instances handle their own clocking internally)
    (let dffGates := c.gates.filter (fun g => g.gateType.isDFF)
     if !dffGates.isEmpty then
      [s!"    SC_CTHREAD(seq_logic, {clockName}.pos());",
       "    reset_signal_is(reset, true);"]
    else [])

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
def generateCombGateSystemC (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (g : Gate) : String :=
  let op := gateTypeToOperator g.gateType
  let outRef := wireRef inputToIndex outputToIndex g.output

  match g.gateType with
  | GateType.NOT =>
      match g.inputs with
      | [i0] =>
          let i0Ref := wireRef inputToIndex outputToIndex i0
          s!"  {outRef}.write(!{i0Ref}.read());"
      | _ => "  // ERROR: NOT gate should have 1 input"
  | GateType.BUF =>
      match g.inputs with
      | [i0] =>
          let i0Ref := wireRef inputToIndex outputToIndex i0
          s!"  {outRef}.write({i0Ref}.read());"
      | _ => "  // ERROR: BUF gate should have 1 input"
  | GateType.MUX =>
      -- Ternary operator: sel ? in1 : in0
      -- inputs: [in0, in1, sel]
      match g.inputs with
      | [in0, in1, sel] =>
          let in0Ref := wireRef inputToIndex outputToIndex in0
          let in1Ref := wireRef inputToIndex outputToIndex in1
          let selRef := wireRef inputToIndex outputToIndex sel
          s!"  {outRef}.write({selRef}.read() ? {in1Ref}.read() : {in0Ref}.read());"
      | _ => "  // ERROR: MUX gate should have 3 inputs: [in0, in1, sel]"
  | GateType.DFF | GateType.DFF_SET =>
      ""  -- DFFs handled in seq_logic, not comb_logic
  | _ =>
      -- Binary operators: input1 op input2
      match g.inputs with
      | [i0, i1] =>
          let i0Ref := wireRef inputToIndex outputToIndex i0
          let i1Ref := wireRef inputToIndex outputToIndex i1
          s!"  {outRef}.write({i0Ref}.read() {op} {i1Ref}.read());"
      | _ => "  // ERROR: Binary gate should have 2 inputs"

-- Generate DFF logic for SC_CTHREAD
def generateDFFSystemC (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (g : Gate) : String :=
  match g.inputs with
  | [d, _clk, reset] =>
      let dRef := wireRef inputToIndex outputToIndex d
      let resetRef := wireRef inputToIndex outputToIndex reset
      let qRef := wireRef inputToIndex outputToIndex g.output
      let resetVal := if g.gateType == GateType.DFF_SET then "true" else "false"
      joinLines [
        s!"    if ({resetRef}.read()) " ++ "{",
        s!"      {qRef}.write({resetVal});",
        "    } else {",
        s!"      {qRef}.write({dRef}.read());",
        "    }"
      ]
  | _ => "    // ERROR: DFF should have 3 inputs: [d, clk, reset]"

-- Generate comb_logic method body
def generateCombMethod (c : Circuit) (useBundledIO : Bool) : String :=
  let inputToIndex := if useBundledIO then c.inputs.enum.map (fun ⟨idx, w⟩ => (w, idx)) else []
  let outputToIndex := if useBundledIO then c.outputs.enum.map (fun ⟨idx, w⟩ => (w, idx)) else []

  let combGates := c.gates.filter (fun g => g.gateType.isCombinational)
  if combGates.isEmpty then ""
  else
    let assignments := combGates.map (fun g => generateCombGateSystemC inputToIndex outputToIndex g)
    joinLines [
      s!"void {c.name}::comb_logic() " ++ "{",
      joinLines assignments,
      "}"
    ]

-- Generate seq_logic method body (for sequential circuits)
def generateSeqMethod (c : Circuit) (useBundledIO : Bool) : String :=
  let inputToIndex := if useBundledIO then c.inputs.enum.map (fun ⟨idx, w⟩ => (w, idx)) else []
  let outputToIndex := if useBundledIO then c.outputs.enum.map (fun ⟨idx, w⟩ => (w, idx)) else []

  let dffGates := c.gates.filter (fun g => g.gateType.isDFF)
  if dffGates.isEmpty then ""
  else
    let dffLogic := dffGates.map (fun g => generateDFFSystemC inputToIndex outputToIndex g)
    joinLines [
      s!"void {c.name}::seq_logic() " ++ "{",
      "  while (true) {",
      "    wait();  // Wait for clock edge",
      joinLines dffLogic,
      "  }",
      "}"
    ]

-- Main function: Generate SystemC header file (.h)
def toSystemCHeader (c : Circuit) (allCircuits : List Circuit := []) : String :=
  let moduleName := c.name
  let guardName := moduleName.toUpper ++ "_H"
  let isSeq := hasSequentialElements c
  -- Use bundled IO for very large circuits, but NOT if they have submodule instances
  -- (instances need named signals for port binding)
  let useBundledIO := (c.inputs.length + c.outputs.length) > 500 && c.instances.isEmpty

  -- Include directives for submodule headers
  let instanceIncludes := generateInstanceIncludes c

  -- Port declarations
  let portDecls := generatePortDeclarations c useBundledIO

  -- Signal declarations
  let signalDecls := generateSignalDeclarations c

  -- Instance declarations
  let instanceDecls := generateInstanceDeclarations c

  -- Process method declarations
  let combGates := c.gates.filter (fun g => g.gateType.isCombinational)
  let hasCombLogic := !combGates.isEmpty
  let dffGates := c.gates.filter (fun g => g.gateType.isDFF)
  let hasDFFs := !dffGates.isEmpty

  let processDecls :=
    (if hasCombLogic then ["  void comb_logic();"] else []) ++
    (if isSeq && hasDFFs then ["  void seq_logic();"] else [])

  -- Constructor
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

-- Main function: Generate SystemC implementation file (.cpp)
def toSystemCImpl (c : Circuit) (_allCircuits : List Circuit := []) : String :=
  let moduleName := c.name
  let isSeq := hasSequentialElements c
  let useBundledIO := (c.inputs.length + c.outputs.length) > 500 && c.instances.isEmpty

  let combMethod := generateCombMethod c useBundledIO
  let seqMethod := if isSeq then generateSeqMethod c useBundledIO else ""

  let parts := [
    s!"#include \"{moduleName}.h\"",
    ""
  ] ++
  (if combMethod.isEmpty then [] else [combMethod]) ++
  (if seqMethod.isEmpty then [] else ["", seqMethod])

  joinLines parts

end Shoumei.Codegen.SystemC
