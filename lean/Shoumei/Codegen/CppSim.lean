/-
Codegen/CppSim.lean - Plain C++ Simulation Code Generator

Generates plain C++ simulation models from DSL circuits.
Uses bool variables and bool* pointers.

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
import Std.Data.HashSet
import Std.Data.HashMap

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
    (portNames : List String := []) (implPrefix : String := "") (portSet : Std.HashSet String := {}) : String :=
  match inputToIndex.find? (fun p => p.fst.name == w.name) with
  | some (_wire, idx) => s!"inputs[{idx}]"
  | none =>
      match outputToIndex.find? (fun p => p.fst.name == w.name) with
      | some (_wire, idx) => s!"outputs[{idx}]"
      | none =>
        let isPort := if !portSet.isEmpty then portSet.contains w.name else portNames.contains w.name
        if !isPort && w.name == "zero" then
          if implPrefix != "" then implPrefix ++ "const_false" else "const_false"
        else if !isPort && w.name == "one" then
          if implPrefix != "" then implPrefix ++ "const_true" else "const_true"
        else if implPrefix != "" && !isPort then implPrefix ++ w.name
        else w.name

-- Check if a wire is a pointer (bundled I/O or port) — needs dereference for read/write
private def isPointerWire (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat))
    (portNames : List String) (w : Wire) (portSet : Std.HashSet String := {}) : Bool :=
  inputToIndex.any (fun p => p.fst.name == w.name) ||
  outputToIndex.any (fun p => p.fst.name == w.name) ||
  (if !portSet.isEmpty then portSet.contains w.name else portNames.contains w.name)

-- Read expression for a wire: dereference for pointers, direct access for plain bool
def wireReadExpr (inputToIndex : List (Wire × Nat))
    (outputToIndex : List (Wire × Nat)) (w : Wire)
    (portNames : List String := []) (implPrefix : String := "") (portSet : Std.HashSet String := {}) : String :=
  let isPort := isPointerWire inputToIndex outputToIndex portNames w portSet
  if !isPort && w.name == "zero" then "false"
  else if !isPort && w.name == "one" then "true"
  else
    let ref := wireRef inputToIndex outputToIndex w portNames implPrefix portSet
    if isPort then s!"*{ref}"
    else ref

-- Write statement for a wire: dereference for pointers, direct assignment for plain bool
def wireWriteStmt (inputToIndex : List (Wire × Nat))
    (outputToIndex : List (Wire × Nat)) (w : Wire) (expr : String)
    (portNames : List String := []) (implPrefix : String := "") (portSet : Std.HashSet String := {}) : String :=
  let ref := wireRef inputToIndex outputToIndex w portNames implPrefix portSet
  if isPointerWire inputToIndex outputToIndex portNames w portSet then s!"  *{ref} = {expr};"
  else s!"  {ref} = {expr};"

-- Helper: find all internal wires (gate outputs and instance wires that are not circuit I/O)
def findInternalWires (c : Circuit) : List Wire := Id.run do
  let mut ioSet : Std.HashSet String := {}
  for w in c.inputs do ioSet := ioSet.insert w.name
  for w in c.outputs do ioSet := ioSet.insert w.name
  ioSet := ioSet.insert "zero"
  ioSet := ioSet.insert "one"

  let mut seen : Std.HashSet String := {}
  let mut result : Array Wire := #[]

  for g in c.gates do
    let w := g.output
    if !ioSet.contains w.name && !seen.contains w.name then
      seen := seen.insert w.name
      result := result.push w

  for inst in c.instances do
    for (_, w) in inst.portMap do
      if !ioSet.contains w.name && !seen.contains w.name then
        seen := seen.insert w.name
        result := result.push w

  for ram in c.rams do
    for wp in ram.writePorts do
      for w in [wp.en] ++ wp.addr ++ wp.data do
        if !ioSet.contains w.name && !seen.contains w.name then
          seen := seen.insert w.name
          result := result.push w
    for rp in ram.readPorts do
      for w in rp.addr ++ rp.data do
        if !ioSet.contains w.name && !seen.contains w.name then
          seen := seen.insert w.name
          result := result.push w

  result.toList

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
  dedupWires (dffClocks ++ instanceClocks)

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
  dedupWires (dffResets ++ instanceResets)

-- Helper: check if circuit has sequential elements (DFFs or instances with clock)
def hasSequentialElements (c : Circuit) : Bool :=
  c.hasSequentialElements ||
  c.instances.any (fun inst =>
    inst.portMap.any (fun (pname, _) => pname == "clock")) ||
  !c.rams.isEmpty

/-! ## Instance Support -/

/-- Get unique submodule types used by this circuit -/
def getInstanceModuleNames (c : Circuit) : List String :=
  dedupStrings (c.instances.map (·.moduleName))

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
    : Std.HashMap String (Array String) := Id.run do
  let mut map : Std.HashMap String (Array String) := {}
  match allCircuits.find? (fun sc => sc.name == moduleName) with
  | none => return map
  | some subMod =>
      for w in subMod.inputs ++ subMod.outputs do
        let name := w.name
        let mut candidates : Array String := #[name]
        let chars := name.toList
        let digitSuffix := chars.reverse.takeWhile Char.isDigit |>.reverse
        if !digitSuffix.isEmpty then
          let idxStr := String.ofList digitSuffix
          let baseChars := chars.take (chars.length - digitSuffix.length)
          let baseStr := String.ofList baseChars
          let strippedBases : List String :=
            [baseStr] ++
            (if baseStr.endsWith "_b" then [(baseStr.dropEnd 2).toString] else []) ++
            (if baseStr.endsWith "__" then [(baseStr.dropEnd 2).toString] else []) ++
            (if baseStr.endsWith "_" then [(baseStr.dropEnd 1).toString] else [])
          for b in strippedBases do
            candidates := candidates.push s!"{b}[{idxStr}]"
            candidates := candidates.push s!"{b}_{idxStr}"
            candidates := candidates.push s!"{b}{idxStr}"
            candidates := candidates.push b
        for c in candidates do
          let cur := map.getD c #[]
          map := map.insert c (cur.push name)
  return map

/-- Resolve a portMap key to the actual port name on the submodule. -/
private def resolvePortName (mapping : Std.HashMap String (Array String)) (portName : String) : String :=
  match mapping.get? portName with
  | some arr => arr[0]?.getD portName
  | none =>
      let s := portName.replace "[" "_"
      s.replace "]" ""

/-- Generate port bindings for a single instance in the constructor body.
    Uses pointer assignment: inst.port = &signal; -/
def generateInstanceBindings (allCircuits : List Circuit) (inst : CircuitInstance) : String := Id.run do
  match allCircuits.find? (fun sc => sc.name == inst.moduleName) with
  | some subMod =>
    let useBundledIO := (subMod.inputs.length + subMod.outputs.length) > 500 && subMod.instances.isEmpty
    if useBundledIO then
      let mapping := buildPortNameMapping allCircuits inst.moduleName
      let mut subInputMap : Std.HashMap String Nat := {}
      for (idx, w) in subMod.inputs.enum do
        subInputMap := subInputMap.insert w.name idx
      let mut subOutputMap : Std.HashMap String Nat := {}
      for (idx, w) in subMod.outputs.enum do
        subOutputMap := subOutputMap.insert w.name idx
      let mut portCounts : Std.HashMap String Nat := {}
      for (pn, _) in inst.portMap do
        portCounts := portCounts.insert pn (portCounts.getD pn 0 + 1)
      let mut lines : Array String := #[]
      let mut bareIdxMap : Std.HashMap String Nat := {}
      for (portName, wire) in inst.portMap do
        let curIdx := bareIdxMap.getD portName 0
        let candidates := mapping.getD portName #[]
        let count := portCounts.getD portName 0
        let actualName := if count > 1 && curIdx < candidates.size then
          candidates[curIdx]!
        else match candidates[0]? with
          | some n => n
          | none => portName
        if count > 1 then
          bareIdxMap := bareIdxMap.insert portName (curIdx + 1)
        let wireExpr :=
          if wire.name == "zero" then "&const_false"
          else if wire.name == "one" then "&const_true"
          else s!"&{wire.name}"
        match subInputMap.get? actualName with
        | some idx =>
            lines := lines.push s!"    {inst.instName}.inputs[{idx}] = {wireExpr};"
        | none =>
            match subOutputMap.get? actualName with
            | some idx =>
                lines := lines.push s!"    {inst.instName}.outputs[{idx}] = {wireExpr};"
            | none =>
                lines := lines.push s!"    {inst.instName}.{actualName} = {wireExpr};"
      joinLines lines.toList
    else
      generateInstanceBindingsNamed allCircuits inst
  | none =>
      generateInstanceBindingsNamed allCircuits inst
where
  /-- Generate bindings using named ports with pointer assignment -/
  generateInstanceBindingsNamed (allCircuits : List Circuit) (inst : CircuitInstance) : String := Id.run do
    let mapping := buildPortNameMapping allCircuits inst.moduleName
    let mut portCounts : Std.HashMap String Nat := {}
    for (pn, _) in inst.portMap do
      portCounts := portCounts.insert pn (portCounts.getD pn 0 + 1)
    let mut lines : Array String := #[]
    let mut bareIdxMap : Std.HashMap String Nat := {}
    for (portName, wire) in inst.portMap do
      let wireExpr :=
        if wire.name == "zero" then "&const_false"
        else if wire.name == "one" then "&const_true"
        else s!"&{wire.name}"
      let candidates := mapping.getD portName #[]
      let count := portCounts.getD portName 0
      let curIdx := bareIdxMap.getD portName 0
      let actualName := if count > 1 && curIdx < candidates.size then
        candidates[curIdx]!
      else match candidates[0]? with
        | some n => n
        | none =>
          let s := portName.replace "[" "_"
          s.replace "]" ""
      if count > 1 then
        bareIdxMap := bareIdxMap.insert portName (curIdx + 1)
      lines := lines.push s!"    {inst.instName}.{actualName} = {wireExpr};"
    joinLines lines.toList

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

-- Generate RAM storage declarations
def generateRAMDeclarations (c : Circuit) : String :=
  if c.rams.isEmpty then ""
  else
    let decls := c.rams.map (fun ram =>
      s!"  bool {ram.name}[{ram.depth}][{ram.width}] = " ++ "{};")
    joinLines decls

-- Generate internal signal declarations — all plain bool
def generateSignalDeclarations (c : Circuit) : String :=
  let internalWires := findInternalWires c
  let dffGates := c.gates.filter (fun g => g.gateType.isDFF)
  let dffSavedDecls := dffGates.map (fun g => s!"  bool d_saved_{g.output.name} = false;")
  let ramDecls := generateRAMDeclarations c
  let wireDecls := internalWires.map (fun w => s!"  bool {w.name} = false;")
  let constDecls := [
    "  bool const_false = false;",
    "  bool const_true = true;"
  ]
  let allDecls := constDecls ++ wireDecls ++ dffSavedDecls
  let base := joinLines allDecls
  if ramDecls.isEmpty then base
  else if base.isEmpty then ramDecls
  else base ++ "\n" ++ ramDecls

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
    s!"  {moduleName}(const char* = \"\") " ++ "{"
  else
    s!"  {moduleName}(const char* = \"\")\n" ++
    "    : " ++ String.intercalate ",\n      " initParts ++ "\n  {"

  joinLines ([ctorLine] ++ instanceBindings ++ ["  }"])

-- Generate a single combinational gate assignment
def generateCombGateCppSim (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (g : Gate)
    (portNames : List String := []) (implPrefix : String := "") (portSet : Std.HashSet String := {}) : String :=
  let op := gateTypeToOperator g.gateType
  let rd := fun w => wireReadExpr inputToIndex outputToIndex w portNames implPrefix portSet
  let wr := fun expr => wireWriteStmt inputToIndex outputToIndex g.output expr portNames implPrefix portSet

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
          if i0.name == i1.name then
            match g.gateType with
            | GateType.XOR => wr "false"
            | GateType.AND | GateType.OR => wr (rd i0)
            | _ => wr s!"{rd i0} {op} {rd i1}"
          else
            wr s!"{rd i0} {op} {rd i1}"
      | _ => "  // ERROR: Binary gate should have 2 inputs"

-- Topological sort of combinational gates using Kahn's algorithm (O(V + E)).
def topSortCombGates (c : Circuit) : List Gate := Id.run do
  let combGates := (c.gates.filter (fun g => g.gateType.isCombinational)).toArray
  let n := combGates.size
  if n == 0 then
    return []

  -- Set of all wires produced by combinational gates
  let mut combOutputs : Std.HashSet String := {}
  for g in combGates do
    combOutputs := combOutputs.insert g.output.name

  -- Dependency graph: for each comb wire name, which gate indices consume it?
  let mut consumers : Std.HashMap String (List Nat) := {}
  -- Unresolved in-degree for each gate
  let mut inDegree : Array Nat := Array.replicate n 0

  for i in [0:n] do
    let g := combGates[i]!
    let mut deg := 0
    for input in g.inputs do
      if combOutputs.contains input.name then
        deg := deg + 1
        let cur := match consumers.get? input.name with
          | some cs => cs
          | none => []
        consumers := consumers.insert input.name (i :: cur)
    inDegree := inDegree.set! i deg

  -- Queue of gates with in-degree 0
  let mut queue : Array Nat := #[]
  let mut inQueue : Array Bool := Array.replicate n false
  for i in [0:n] do
    if inDegree[i]! == 0 then
      queue := queue.push i
      inQueue := inQueue.set! i true

  let mut result : Array Gate := #[]
  let mut head := 0
  let mut nextUnvisited := 0

  for _ in [0:n] do
    if head < queue.size then
      let idx := queue[head]!
      head := head + 1
      let g := combGates[idx]!
      result := result.push g
      if let some cons := consumers.get? g.output.name then
        for consumerIdx in cons do
          let curDeg := inDegree[consumerIdx]!
          if curDeg > 0 then
            let newDeg := curDeg - 1
            inDegree := inDegree.set! consumerIdx newDeg
            if newDeg == 0 && !inQueue[consumerIdx]! then
              queue := queue.push consumerIdx
              inQueue := inQueue.set! consumerIdx true
    else
      -- Fallback for cyclic dependencies: pick the next unvisited gate
      for j in [nextUnvisited:n] do
        if !inQueue[j]! then
          nextUnvisited := j + 1
          inQueue := inQueue.set! j true
          let g := combGates[j]!
          result := result.push g
          if let some cons := consumers.get? g.output.name then
            for consumerIdx in cons do
              let curDeg := inDegree[consumerIdx]!
              if curDeg > 0 then
                let newDeg := curDeg - 1
                inDegree := inDegree.set! consumerIdx newDeg
                if newDeg == 0 && !inQueue[consumerIdx]! then
                  queue := queue.push consumerIdx
                  inQueue := inQueue.set! consumerIdx true
          break

  result.toList

-- Generate RAM read logic (async reads go in comb_logic)
def generateRAMReadLogic (c : Circuit) (inputToIndex : List (Wire × Nat))
    (outputToIndex : List (Wire × Nat)) (portNames : List String := [])
    (implPrefix : String := "") : String :=
  if c.rams.isEmpty then ""
  else
    let reads := c.rams.flatMap (fun ram =>
      ram.readPorts.map (fun rp =>
        -- Build address computation: addr = addr[n-1]*2^(n-1) + ... + addr[0]
        let addrParts := rp.addr.enum.map (fun (i, w) =>
          let ref := wireReadExpr inputToIndex outputToIndex w portNames implPrefix
          if i == 0 then ref
          else s!"({ref} ? {1 <<< i} : 0)")
        let addrExpr := if addrParts.length == 1 then s!"({addrParts.head!} ? 1 : 0)"
          else String.intercalate " + " addrParts
        -- Read each output bit
        let bitReads := rp.data.enum.map (fun (idx, w) =>
          let lhs := wireWriteStmt inputToIndex outputToIndex w
            s!"{implPrefix}{ram.name}[{addrExpr}][{idx}]" portNames implPrefix
          lhs)
        joinLines bitReads))
    joinLines reads

-- Generate RAM write logic (clocked writes go in seq_tick)
def generateRAMWriteLogic (c : Circuit) (inputToIndex : List (Wire × Nat))
    (outputToIndex : List (Wire × Nat)) (portNames : List String := [])
    (implPrefix : String := "") : String :=
  if c.rams.isEmpty then ""
  else
    let writes := c.rams.flatMap (fun ram =>
      ram.writePorts.map (fun wp =>
        let addrParts := wp.addr.enum.map (fun (i, w) =>
          let ref := wireReadExpr inputToIndex outputToIndex w portNames implPrefix
          if i == 0 then ref
          else s!"({ref} ? {1 <<< i} : 0)")
        let addrExpr := if addrParts.length == 1 then s!"({addrParts.head!} ? 1 : 0)"
          else String.intercalate " + " addrParts
        let enRef := wireReadExpr inputToIndex outputToIndex wp.en portNames implPrefix
        let bitWrites := wp.data.enum.map (fun (idx, w) =>
          let ref := wireReadExpr inputToIndex outputToIndex w portNames implPrefix
          s!"      {implPrefix}{ram.name}[addr][{idx}] = {ref};")
        joinLines [
          s!"    " ++ "{",
          s!"      int addr = {addrExpr};",
          s!"      if ({enRef}) " ++ "{",
          joinLines bitWrites,
          "      }",
          "    }"
        ]))
    joinLines writes

-- Generate comb_logic method body
def generateCombMethod (c : Circuit) (useBundledIO : Bool)
    (portNames : List String := []) (implPrefix : String := "") : String :=
  let inputToIndex := if useBundledIO then c.inputs.enum.map (fun ⟨idx, w⟩ => (w, idx)) else []
  let outputToIndex := if useBundledIO then c.outputs.enum.map (fun ⟨idx, w⟩ => (w, idx)) else []
  let portSet : Std.HashSet String := portNames.foldl (·.insert ·) {}

  let combGates := topSortCombGates c
  let ramReads := generateRAMReadLogic c inputToIndex outputToIndex portNames implPrefix
  if combGates.isEmpty && ramReads.isEmpty then ""
  else
    let assignments := combGates.map (fun g => generateCombGateCppSim inputToIndex outputToIndex g portNames implPrefix portSet)
    joinLines [
      s!"void {c.name}::comb_logic() " ++ "{",
      joinLines assignments,
      if ramReads.isEmpty then "" else "  // RAM async reads\n" ++ ramReads,
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

-- Generate DFF sample line (save d input to d_saved for two-phase evaluation)
def generateDFFSample (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (g : Gate)
    (portNames : List String := []) (implPrefix : String := "") : String :=
  match g.inputs with
  | [d, _clk, _reset] =>
      let dExpr := wireReadExpr inputToIndex outputToIndex d portNames implPrefix
      s!"  {implPrefix}d_saved_{g.output.name} = {dExpr};"
  | _ => "  // ERROR: DFF should have 3 inputs: [d, clk, reset]"

-- Generate DFF latch line (uses d_saved from two-phase sampling)
def generateDFFLatch (inputToIndex : List (Wire × Nat)) (outputToIndex : List (Wire × Nat)) (g : Gate)
    (portNames : List String := []) (implPrefix : String := "") : String :=
  let qRef := wireRef inputToIndex outputToIndex g.output portNames implPrefix
  let savedRef := s!"{implPrefix}d_saved_{g.output.name}"
  if isPointerWire inputToIndex outputToIndex portNames g.output then
    s!"      *{qRef} = {savedRef};"
  else
    s!"      {qRef} = {savedRef};"

-- Generate seq_tick method: plain function version of DFF update.
def generateSeqTickMethod (c : Circuit) (_useBundledIO : Bool)
    (portNames : List String := []) (implPrefix : String := "") : String :=
  let inputToIndex : List (Wire × Nat) := []
  let outputToIndex : List (Wire × Nat) := []
  let dffGates := c.gates.filter (fun g => g.gateType.isDFF)
  let ramWrites := generateRAMWriteLogic c inputToIndex outputToIndex portNames implPrefix
  if dffGates.isEmpty && ramWrites.isEmpty then ""
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
      if ramWrites.isEmpty then "" else "    // RAM clocked writes\n" ++ ramWrites,
      "  }",
      "}"
    ]

-- Generate seq_sample method: saves d inputs for two-phase DFF evaluation.
def generateSeqSampleMethod (c : Circuit) (_useBundledIO : Bool)
    (portNames : List String := []) (implPrefix : String := "") : String :=
  let inputToIndex : List (Wire × Nat) := []
  let outputToIndex : List (Wire × Nat) := []
  let dffGates := c.gates.filter (fun g => g.gateType.isDFF)
  if dffGates.isEmpty then ""
  else
    let sampleLines := dffGates.map (fun g =>
      generateDFFSample inputToIndex outputToIndex g portNames implPrefix)
    joinLines [
      s!"void {c.name}::seq_sample() " ++ "{",
      joinLines sampleLines,
      "}"
    ]

-- Generate eval_seq_sample_all: recursively sample all DFF d inputs
def generateEvalSeqSampleAll (c : Circuit) : String :=
  let hasDFFs := !(c.gates.filter (·.gateType.isDFF)).isEmpty
  let usePimpl := !c.instances.isEmpty
  let instSampleCalls := c.instances.map (fun inst =>
    if usePimpl then s!"  pImpl->{inst.instName}.eval_seq_sample_all();"
    else s!"  {inst.instName}.eval_seq_sample_all();")
  let ownSample := if hasDFFs then ["  seq_sample();"] else []
  joinLines [
    s!"void {c.name}::eval_seq_sample_all() " ++ "{",
    joinLines (instSampleCalls ++ ownSample),
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
    (if isSeq && hasDFFs then ["  void seq_sample();", "  void seq_tick();"] else []) ++
    ["  void eval_comb_all();", "  void eval_seq_sample_all();", "  void eval_seq_all();"]

  if usePimpl then
    let parts := [
      "// Auto-generated by Shoumei RTL - do not edit",
      s!"#ifndef {guardName}",
      s!"#define {guardName}",
      "",
      "#include <cstdint>",
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
      s!"  {moduleName}(const char* = \"\");",
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
      "// Auto-generated by Shoumei RTL - do not edit",
      s!"#ifndef {guardName}",
      s!"#define {guardName}",
      "",
      "#include <cstdint>"
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
      "  void bind_ports() {}",
      "",
      "  // Constructor",
      ctor,
      "};",
      "",
      s!"#endif // {guardName}"
    ]
    joinLines parts

-- Generate PIMPL-aware instance port bindings for the constructor body.
-- Uses pointer assignment: inst.port = &signal;
def generatePimplInstanceBindings (allCircuits : List Circuit) (c : Circuit) : String := Id.run do
  let portNameSet : Std.HashSet String := (c.inputs ++ c.outputs).foldl (fun s w => s.insert w.name) {}

  let mut cache : Std.HashMap String (Std.HashMap String (Array String) × Bool × Std.HashMap String Nat × Std.HashMap String Nat) := {}
  for inst in c.instances do
    if !cache.contains inst.moduleName then
      let mapping := buildPortNameMapping allCircuits inst.moduleName
      let subMod := allCircuits.find? (fun (sc : Circuit) => sc.name == inst.moduleName)
      let subUseBundled := match subMod with
        | some sm => (sm.inputs.length + sm.outputs.length) > 500 && sm.instances.isEmpty
        | none => false
      let mut subInputMap : Std.HashMap String Nat := {}
      if let some sm := subMod then
        for (idx, w) in sm.inputs.enum do
          subInputMap := subInputMap.insert w.name idx
      let mut subOutputMap : Std.HashMap String Nat := {}
      if let some sm := subMod then
        for (idx, w) in sm.outputs.enum do
          subOutputMap := subOutputMap.insert w.name idx
      cache := cache.insert inst.moduleName (mapping, subUseBundled, subInputMap, subOutputMap)

  let mut bindings : Array String := #[]
  for inst in c.instances do
    let comment := s!"    // {inst.instName} ({inst.moduleName})"
    let (mapping, subUseBundled, subInputMap, subOutputMap) := match cache[inst.moduleName]? with
      | some info => info
      | none => ({}, false, {}, {})

    -- Precompute port name counts for this instance
    let mut portCounts : Std.HashMap String Nat := {}
    for (pn, _) in inst.portMap do
      portCounts := portCounts.insert pn (portCounts.getD pn 0 + 1)

    let mut lines : Array String := #[]
    let mut bareIdxMap : Std.HashMap String Nat := {}

    for (portName, wire) in inst.portMap do
      let candidates := mapping.getD portName #[]
      let count := portCounts.getD portName 0
      let curIdx := bareIdxMap.getD portName 0
      let actualName := if count > 1 && curIdx < candidates.size then
        candidates[curIdx]!
      else match candidates[0]? with
        | some n => n
        | none =>
          let s := portName.replace "[" "_"
          s.replace "]" ""
      if count > 1 then
        bareIdxMap := bareIdxMap.insert portName (curIdx + 1)

      -- Parent ports are already bool* pointers; internal wires are plain bool (need &)
      let isPort := portNameSet.contains wire.name
      let wireExpr := if isPort then wire.name
        else if wire.name == "zero" then "&pImpl->const_false"
        else if wire.name == "one" then "&pImpl->const_true"
        else s!"&pImpl->{wire.name}"

      if subUseBundled then
        match subInputMap.get? actualName with
        | some idx =>
            lines := lines.push s!"    pImpl->{inst.instName}.inputs[{idx}] = {wireExpr};"
        | none =>
            match subOutputMap.get? actualName with
            | some idx =>
                lines := lines.push s!"    pImpl->{inst.instName}.outputs[{idx}] = {wireExpr};"
            | none =>
                lines := lines.push s!"    pImpl->{inst.instName}.{actualName} = {wireExpr};"
      else
        lines := lines.push s!"    pImpl->{inst.instName}.{actualName} = {wireExpr};"

    bindings := bindings.push (comment ++ "\n" ++ joinLines lines.toList)

  joinLines bindings.toList

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
      "// Auto-generated by Shoumei RTL - do not edit",
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
     s!"{moduleName}::{moduleName}(const char*) " ++ "{",
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
    (let seqSampleMethod := generateSeqSampleMethod c useBundledIO portNames implPrefix
     if seqSampleMethod.isEmpty then [] else ["", seqSampleMethod]) ++
    (let seqTickMethod := generateSeqTickMethod c useBundledIO portNames implPrefix
     if seqTickMethod.isEmpty then [] else ["", seqTickMethod]) ++
    ["", generateEvalCombAll c, "", generateEvalSeqSampleAll c, "", generateEvalSeqAll c]

    joinLines parts
  else
    let seqTickMethod := generateSeqTickMethod c useBundledIO portNames
    let parts := [
      "// Auto-generated by Shoumei RTL - do not edit",
      s!"#include \"{moduleName}.h\"",
      ""
    ] ++
    (if combMethod.isEmpty then [] else [combMethod]) ++
    (let seqSampleMethod := generateSeqSampleMethod c useBundledIO portNames
     if seqSampleMethod.isEmpty then [] else ["", seqSampleMethod]) ++
    (if seqTickMethod.isEmpty then [] else ["", seqTickMethod]) ++
    ["", generateEvalCombAll c, "", generateEvalSeqSampleAll c, "", generateEvalSeqAll c]

    joinLines parts

end Shoumei.Codegen.CppSim
