/-
Codegen/CppSim.lean - Plain C++ Simulation Code Generator

Generates plain C++ simulation models from DSL circuits.
No SystemC dependency — uses bool variables and bool* pointers.

Design:
- Generates both .h (header) and .cpp (implementation) files
- struct for all circuits (no SC_MODULE)
- Direct bool assignment for combinational logic (no sensitivity lists)
- Plain function seq_tick() for sequential logic (DFFs)
- Hierarchical: submodule instances with pointer-based port bindings
- Supports both small and large circuits (bundled I/O with bool* arrays)

Target: C++17
-/

import Shoumei.DSL
import Shoumei.Codegen.Common

namespace Shoumei.Codegen.CppSim

open Shoumei.Codegen

-- Generate C++ operator for a combinational gate type
def gateTypeToOperator (gt : GateType) : String :=
  match gt with
  | GateType.AND => "&&"
  | GateType.OR => "||"
  | GateType.NOT => "!"
  | GateType.XOR => "!="
  | GateType.BUF => ""
  | GateType.MUX => "?"
  | GateType.DFF | GateType.DFF_SET => ""

-- Helper: Get wire reference (handles both individual and bundled I/O)
-- For bundled I/O: inputs[idx] / outputs[idx] (these are bool*)
-- For ports (in portNames): name (these are bool*)
-- For internal with implPrefix: pImpl->name (these are plain bool)
-- For internal without prefix: name (plain bool)
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

-- Check if a wire is a pointer (bundled I/O or port) — needs dereference for read/write
private def isPointerWire (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat))
    (portNames : List String) (w : Wire) : Bool :=
  inputToIndex.any (fun p => p.fst.name == w.name) ||
  outputToIndex.any (fun p => p.fst.name == w.name) ||
  portNames.contains w.name

-- Read expression for a wire: dereference for pointers, direct access for plain bool
def wireReadExpr (inputToIndex : List (Wire × Nat))
    (outputToIndex : List (Wire × Nat)) (w : Wire)
    (portNames : List String := []) (implPrefix : String := "") : String :=
  let ref := wireRef inputToIndex outputToIndex w portNames implPrefix
  if isPointerWire inputToIndex outputToIndex portNames w then s!"*{ref}"
  else ref

-- Write statement for a wire: dereference for pointers, direct assignment for plain bool
def wireWriteStmt (inputToIndex : List (Wire × Nat))
    (outputToIndex : List (Wire × Nat)) (w : Wire) (expr : String)
    (portNames : List String := []) (implPrefix : String := "") : String :=
  let ref := wireRef inputToIndex outputToIndex w portNames implPrefix
  if isPointerWire inputToIndex outputToIndex portNames w then s!"  *{ref} = {expr};"
  else s!"  {ref} = {expr};"

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

/-- Generate instance initializer list entries for constructor. -/
def generateInstanceInitList (c : Circuit) : List String :=
  c.instances.map fun inst =>
    s!"    {inst.instName}()"

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
      let chars := portName.toList
      let digitSuffix := chars.reverse.takeWhile Char.isDigit |>.reverse
      if digitSuffix.isEmpty then none
      else
        let idxStr := String.ofList digitSuffix
        let baseChars := chars.take (chars.length - digitSuffix.length)
        let baseChars := if baseChars.getLast? == some '_' then baseChars.dropLast else baseChars
        match idxStr.toNat? with
        | some idx => some (String.ofList baseChars, idx)
        | none => none

/-- Build a mapping from possible portMap key names → actual wire names for a submodule. -/
private def buildPortNameMapping (allCircuits : List Circuit) (moduleName : String)
    : List (String × String) :=
  match allCircuits.find? (fun sc => sc.name == moduleName) with
  | none => []
  | some subMod =>
      (subMod.inputs ++ subMod.outputs).flatMap fun w =>
        let name := w.name
        let candidates := [name]
        let chars := name.toList
        let digitSuffix := chars.reverse.takeWhile Char.isDigit |>.reverse
        let candidates := if digitSuffix.isEmpty then candidates
        else
          let idxStr := String.ofList digitSuffix
          let baseChars := chars.take (chars.length - digitSuffix.length)
          let baseStr := String.ofList baseChars
          let strippedBases : List String :=
            [baseStr] ++
            (if baseStr.endsWith "_b" then [(baseStr.dropEnd 2).toString] else []) ++
            (if baseStr.endsWith "__" then [(baseStr.dropEnd 2).toString] else []) ++
            (if baseStr.endsWith "_" then [(baseStr.dropEnd 1).toString] else [])
          let extraCandidates := strippedBases.flatMap fun b =>
            [s!"{b}[{idxStr}]", s!"{b}_{idxStr}", s!"{b}{idxStr}", b]
          candidates ++ extraCandidates
        candidates.map fun c => (c, name)

/-- Resolve a portMap key to the actual port name on the submodule. -/
private def resolvePortName (mapping : List (String × String)) (portName : String) : String :=
  match mapping.find? (fun (key, _) => key == portName) with
  | some (_, actualName) => actualName
  | none =>
      let s := portName.replace "[" "_"
      s.replace "]" ""

/-- Generate port bindings for a single instance in the constructor body.
    Uses pointer assignment: inst.port = &signal; -/
def generateInstanceBindings (allCircuits : List Circuit) (inst : CircuitInstance) : String :=
  match allCircuits.find? (fun sc => sc.name == inst.moduleName) with
  | some subMod =>
    let useBundledIO := (subMod.inputs.length + subMod.outputs.length) > 500 && subMod.instances.isEmpty
    if useBundledIO then
      let inputNames := subMod.inputs.map (·.name)
      let outputNames := subMod.outputs.map (·.name)
      let mapping := buildPortNameMapping allCircuits inst.moduleName
      let (bindings, _bareIdxMap) := inst.portMap.foldl
        (fun (acc : List String × List (String × Nat)) (portName, wire) =>
          let (lines, bmap) := acc
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
          match inputNames.findIdx? (· == actualName) with
          | some idx =>
              (lines ++ [s!"    {inst.instName}.inputs[{idx}] = &{wire.name};"], newMap)
          | none =>
              match outputNames.findIdx? (· == actualName) with
              | some idx =>
                  (lines ++ [s!"    {inst.instName}.outputs[{idx}] = &{wire.name};"], newMap)
              | none =>
                  (lines ++ [s!"    {inst.instName}.{actualName} = &{wire.name};"], newMap)
        ) ([], [])
      joinLines bindings
    else
      generateInstanceBindingsNamed allCircuits inst
  | none =>
      generateInstanceBindingsNamed allCircuits inst
where
  /-- Generate bindings using named ports with pointer assignment -/
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
            (lines ++ [s!"    {inst.instName}.{actualName} = &{wire.name};"], newMap)
          else
            (lines ++ [s!"    {inst.instName}.{actualName} = &{wire.name};"], bareIdxMap)
      | none =>
          let s := portName.replace "[" "_"
          let cppPortName := s.replace "]" ""
          (lines ++ [s!"    {inst.instName}.{cppPortName} = &{wire.name};"], bareIdxMap)
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
      s!"  bool* inputs[{inputCount}] = " ++ "{};    // " ++ s!"{inputCount} input ports",
      s!"  bool* outputs[{outputCount}] = " ++ "{};  // " ++ s!"{outputCount} output ports"
    ]
  else
    let inputDecls := c.inputs.map (fun w => s!"  bool* {w.name} = nullptr;")
    let outputDecls := c.outputs.map (fun w => s!"  bool* {w.name} = nullptr;")
    joinLines (inputDecls ++ outputDecls)

-- Generate internal signal declarations — all plain bool
def generateSignalDeclarations (c : Circuit) : String :=
  let internalWires := findInternalWires c
  if internalWires.isEmpty then
    ""
  else
    let decls := internalWires.map (fun w => s!"  bool {w.name} = false;")
    joinLines decls

-- Generate constructor
def generateConstructor (c : Circuit) (_useBundledIO : Bool) (allCircuits : List Circuit := []) : String :=
  let moduleName := c.name
  let hasInstances := !c.instances.isEmpty

  let initParts := generateInstanceInitList c

  -- Instance port bindings (in constructor body)
  let instanceBindings := if hasInstances then
    ["", "    // Submodule port bindings", generateAllInstanceBindings allCircuits c]
  else []

  let ctorLine := if initParts.isEmpty then
    s!"  {moduleName}(const char* name = \"\") " ++ "{"
  else
    s!"  {moduleName}(const char* name = \"\")\n" ++
    "    : " ++ String.intercalate ",\n      " initParts ++ "\n  {"

  joinLines ([ctorLine] ++ instanceBindings ++ ["  }"])

-- Generate a single combinational gate assignment
def generateCombGateCppSim (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (g : Gate)
    (portNames : List String := []) (implPrefix : String := "") : String :=
  let op := gateTypeToOperator g.gateType
  let rd := fun w => wireReadExpr inputToIndex outputToIndex w portNames implPrefix
  let wr := fun expr => wireWriteStmt inputToIndex outputToIndex g.output expr portNames implPrefix

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
      match g.inputs with
      | [in0, in1, sel] =>
          wr s!"{rd sel} ? {rd in1} : {rd in0}"
      | _ => "  // ERROR: MUX gate should have 3 inputs: [in0, in1, sel]"
  | GateType.DFF | GateType.DFF_SET =>
      ""
  | _ =>
      match g.inputs with
      | [i0, i1] =>
          wr s!"{rd i0} {op} {rd i1}"
      | _ => "  // ERROR: Binary gate should have 2 inputs"

-- Topological sort of combinational gates.
def topSortCombGates (c : Circuit) : List Gate :=
  let combGates := c.gates.filter (fun g => g.gateType.isCombinational)
  let combGateOutputNames := combGates.map (·.output.name)
  let inputNames := c.inputs.map (·.name)
  let dffOutputNames := c.gates.filter (·.gateType.isDFF) |>.map (·.output.name)
  let instOutputNames := List.flatten (c.instances.map (fun inst =>
    inst.portMap.map (fun p => p.2.name)))
  let available := (inputNames ++ dffOutputNames ++ instOutputNames).filter
    (fun n => !combGateOutputNames.contains n)
  let rec loop (remaining : List Gate) (avail : List String) (sorted : List Gate)
      (fuel : Nat) : List Gate :=
    match fuel with
    | 0 => sorted ++ remaining
    | fuel + 1 =>
      if remaining.isEmpty then sorted
      else
        let (ready, notReady) := remaining.partition (fun g =>
          g.inputs.all (fun w => avail.contains w.name))
        if ready.isEmpty then
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
    let assignments := combGates.map (fun g => generateCombGateCppSim inputToIndex outputToIndex g portNames implPrefix)
    joinLines [
      s!"void {c.name}::comb_logic() " ++ "{",
      joinLines assignments,
      "}"
    ]

-- Generate DFF reset initialization line
def generateDFFResetInit (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (g : Gate)
    (portNames : List String := []) (implPrefix : String := "") : String :=
  let qRef := wireRef inputToIndex outputToIndex g.output portNames implPrefix
  let resetVal := if g.gateType == GateType.DFF_SET then "true" else "false"
  -- DFF output is always internal (plain bool), direct assignment
  if isPointerWire inputToIndex outputToIndex portNames g.output then
    s!"    *{qRef} = {resetVal};"
  else
    s!"    {qRef} = {resetVal};"

-- Generate DFF latch line
def generateDFFLatch (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (g : Gate)
    (portNames : List String := []) (implPrefix : String := "") : String :=
  match g.inputs with
  | [d, _clk, _reset] =>
      let dExpr := wireReadExpr inputToIndex outputToIndex d portNames implPrefix
      let qRef := wireRef inputToIndex outputToIndex g.output portNames implPrefix
      if isPointerWire inputToIndex outputToIndex portNames g.output then
        s!"      *{qRef} = {dExpr};"
      else
        s!"      {qRef} = {dExpr};"
  | _ => "      // ERROR: DFF should have 3 inputs: [d, clk, reset]"

-- Generate seq_tick method: plain function version of DFF update.
def generateSeqTickMethod (c : Circuit) (_useBundledIO : Bool)
    (portNames : List String := []) (implPrefix : String := "") : String :=
  let inputToIndex : List (Wire × Nat) := []
  let outputToIndex : List (Wire × Nat) := []
  let dffGates := c.gates.filter (fun g => g.gateType.isDFF)
  if dffGates.isEmpty then ""
  else
    let resets := findResetWires c
    let resetName := match resets.head? with
      | some r => r.name
      | none => "reset"
    let resetExpr := if portNames.contains resetName then s!"*{resetName}"
      else implPrefix ++ resetName
    let resetInits := dffGates.map (fun g =>
      generateDFFResetInit inputToIndex outputToIndex g portNames implPrefix)
    let latchLines := dffGates.map (fun g =>
      generateDFFLatch inputToIndex outputToIndex g portNames implPrefix)
    joinLines [
      s!"void {c.name}::seq_tick() " ++ "{",
      s!"  if ({resetExpr}) " ++ "{",
      joinLines resetInits,
      "  } else {",
      joinLines latchLines,
      "  }",
      "}"
    ]

-- Generate eval_comb_all: own comb_logic + submodule eval_comb_all (recursive)
def generateEvalCombAll (c : Circuit) : String :=
  let hasCombLogic := !(c.gates.filter (·.gateType.isCombinational)).isEmpty
  let usePimpl := !c.instances.isEmpty
  let instCombCalls := c.instances.map (fun inst =>
    if usePimpl then s!"  pImpl->{inst.instName}.eval_comb_all();"
    else s!"  {inst.instName}.eval_comb_all();")
  let body :=
    (if hasCombLogic then ["  comb_logic();"] else []) ++
    instCombCalls
  joinLines [
    s!"void {c.name}::eval_comb_all() " ++ "{",
    joinLines body,
    "}"
  ]

-- Generate eval_seq_all: submodule eval_seq_all + own seq_tick (recursive)
def generateEvalSeqAll (c : Circuit) : String :=
  let hasDFFs := !(c.gates.filter (·.gateType.isDFF)).isEmpty
  let usePimpl := !c.instances.isEmpty
  let instSeqCalls := c.instances.map (fun inst =>
    if usePimpl then s!"  pImpl->{inst.instName}.eval_seq_all();"
    else s!"  {inst.instName}.eval_seq_all();")
  let ownSeq := if hasDFFs then ["  seq_tick();"] else []
  joinLines [
    s!"void {c.name}::eval_seq_all() " ++ "{",
    joinLines (instSeqCalls ++ ownSeq),
    "}"
  ]

-- Main function: Generate C++ simulation header file (.h)
def toCppSimHeader (c : Circuit) (allCircuits : List Circuit := []) : String :=
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
    (if isSeq && hasDFFs then ["  void seq_tick();"] else []) ++
    ["  void eval_comb_all();", "  void eval_seq_all();"]

  if usePimpl then
    let parts := [
      s!"#ifndef {guardName}",
      s!"#define {guardName}",
      "",
      "#include <cstdint>",
      "#include <cstdbool>",
      "",
      s!"struct {moduleName} " ++ "{",
      "  // Ports",
      portDecls,
      "",
      "  // PIMPL: internal signals and submodule instances in .cpp",
      "  struct Impl;",
      "  Impl* pImpl;",
      "",
      "  // Methods"
    ] ++
    processDecls ++
    ["",
      "  void bind_ports();",
      "",
      s!"  {moduleName}(const char* name = \"\");",
      s!"  ~{moduleName}();",
      "};",
      "",
      s!"#endif // {guardName}"
    ]
    joinLines parts
  else
    -- Non-PIMPL header: leaf modules with inline constructor
    let instanceIncludes := generateInstanceIncludes c
    let signalDecls := generateSignalDeclarations c
    let instanceDecls := generateInstanceDeclarations c
    let ctor := generateConstructor c useBundledIO allCircuits

    let parts := [
      s!"#ifndef {guardName}",
      s!"#define {guardName}",
      "",
      "#include <cstdint>",
      "#include <cstdbool>"
    ] ++
    (if instanceIncludes.isEmpty then [] else [instanceIncludes]) ++
    ["",
      s!"struct {moduleName} " ++ "{",
      "  // Ports",
      portDecls
    ] ++
    (if signalDecls.isEmpty then [] else ["", "  // Internal signals", signalDecls]) ++
    (if instanceDecls.isEmpty then [] else ["", "  // Submodule instances", instanceDecls]) ++
    ["",
      "  // Methods"
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
-- Uses pointer assignment: inst.port = &signal;
def generatePimplInstanceBindings (allCircuits : List Circuit) (c : Circuit) : String :=
  let portNames := (c.inputs ++ c.outputs).map (·.name)
  let bindings := c.instances.map fun inst =>
    let mapping := buildPortNameMapping allCircuits inst.moduleName
    let comment := s!"    // {inst.instName} ({inst.moduleName})"
    let subMod := allCircuits.find? (fun (sc : Circuit) => sc.name == inst.moduleName)
    let subUseBundled := match subMod with
      | some sm => (sm.inputs.length + sm.outputs.length) > 500 && sm.instances.isEmpty
      | none => false
    let subInputNames := match subMod with
      | some sm => sm.inputs.map Wire.name
      | none => []
    let subOutputNames := match subMod with
      | some sm => sm.outputs.map Wire.name
      | none => []
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
      -- Parent ports are already bool* pointers; internal wires are plain bool (need &)
      let isPort := portNames.contains wire.name
      let wireExpr := if isPort then wire.name else s!"&pImpl->{wire.name}"
      if subUseBundled then
        match subInputNames.findIdx? (· == actualName) with
        | some idx =>
            (ls ++ [s!"    pImpl->{inst.instName}.inputs[{idx}] = {wireExpr};"], newMap)
        | none =>
            match subOutputNames.findIdx? (· == actualName) with
            | some idx =>
                (ls ++ [s!"    pImpl->{inst.instName}.outputs[{idx}] = {wireExpr};"], newMap)
            | none =>
                (ls ++ [s!"    pImpl->{inst.instName}.{actualName} = {wireExpr};"], newMap)
      else
        (ls ++ [s!"    pImpl->{inst.instName}.{actualName} = {wireExpr};"], newMap)
    ) ([], [])
    comment ++ "\n" ++ joinLines lines
  joinLines bindings

-- Main function: Generate C++ simulation implementation file (.cpp)
def toCppSimImpl (c : Circuit) (allCircuits : List Circuit := []) : String :=
  let moduleName := c.name
  let useBundledIO := (c.inputs.length + c.outputs.length) > 500 && c.instances.isEmpty
  let usePimpl := !c.instances.isEmpty
  -- All ports are bool* pointers, so always pass port names for proper dereference
  let portNames := (c.inputs ++ c.outputs).map (·.name)
  let implPrefix := if usePimpl then "pImpl->" else ""

  let combMethod := generateCombMethod c useBundledIO portNames implPrefix

  if usePimpl then
    let signalDecls := generateSignalDeclarations c
    let instanceDecls := generateInstanceDeclarations c
    let initList := generateInstanceInitList c
    let initPart := if initList.isEmpty then ""
      else "\n    : " ++ String.intercalate ",\n      " initList

    let instanceIncludes := generateInstanceIncludes c

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
     s!"{moduleName}::{moduleName}(const char* name) " ++ "{",
     "  pImpl = new Impl();",
     "}",
     "",
     s!"void {moduleName}::bind_ports() " ++ "{"
    ] ++
    (if instanceBindings.isEmpty then [] else [instanceBindings]) ++
    -- Call bind_ports() on PIMPL sub-instances
    (let pimplSubInsts := c.instances.filter fun inst =>
       match allCircuits.find? (fun sc => sc.name == inst.moduleName) with
       | some sc => !sc.instances.isEmpty  -- has instances = uses PIMPL
       | none => false
     if pimplSubInsts.isEmpty then []
     else pimplSubInsts.map fun inst =>
       s!"  pImpl->{inst.instName}.bind_ports();") ++
    ["}",
     "",
     s!"{moduleName}::~{moduleName}() " ++ "{",
     "  delete pImpl;",
     "}"
    ] ++
    (if combMethod.isEmpty then [] else ["", combMethod]) ++
    (let seqTickMethod := generateSeqTickMethod c useBundledIO portNames implPrefix
     if seqTickMethod.isEmpty then [] else ["", seqTickMethod]) ++
    ["", generateEvalCombAll c, "", generateEvalSeqAll c]

    joinLines parts
  else
    let seqTickMethod := generateSeqTickMethod c useBundledIO portNames
    let parts := [
      s!"#include \"{moduleName}.h\"",
      ""
    ] ++
    (if combMethod.isEmpty then [] else [combMethod]) ++
    (if seqTickMethod.isEmpty then [] else ["", seqTickMethod]) ++
    ["", generateEvalCombAll c, "", generateEvalSeqAll c]

    joinLines parts

end Shoumei.Codegen.CppSim
