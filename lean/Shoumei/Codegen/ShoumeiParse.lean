/-
Codegen/ShoumeiParse.lean - Shoumei Text Format Parser

Parses `.shoumei` text files back into `Circuit` values.
Hand-rolled recursive descent using `String.Pos.Raw`-based parsing.
-/

import Shoumei.DSL

namespace Shoumei.Codegen.ShoumeiParse

open String.Pos.Raw in
structure ParseState where
  input : String
  pos   : String.Pos.Raw

private def endPos (s : ParseState) : Nat := s.input.utf8ByteSize

private def atEnd (s : ParseState) : Bool := s.pos.byteIdx >= endPos s

private def curr (s : ParseState) : Char :=
  String.Pos.Raw.get s.input s.pos

private def adv (s : ParseState) : ParseState :=
  { s with pos := String.Pos.Raw.next s.input s.pos }

private def extract (s : ParseState) (start stop : String.Pos.Raw) : String :=
  String.Pos.Raw.extract s.input start stop

/-! ## Lexer -/

private def skipWhile (p : Char → Bool) (s : ParseState) : ParseState :=
  let rec loop (st : ParseState) (fuel : Nat) : ParseState :=
    match fuel with
    | 0 => st
    | fuel + 1 =>
      if atEnd st then st
      else if p (curr st) then loop (adv st) fuel else st
  loop s (endPos s - s.pos.byteIdx + 1)

private def skipWS (s : ParseState) : ParseState :=
  let rec loop (st : ParseState) (fuel : Nat) : ParseState :=
    match fuel with
    | 0 => st
    | fuel + 1 =>
      if atEnd st then st
      else
        let c := curr st
        if c == ' ' || c == '\n' || c == '\r' || c == '\t' then
          loop (adv st) fuel
        else if c == '/' then
          let st2 := adv st
          if !atEnd st2 && curr st2 == '/' then
            -- skip to end of line
            loop (skipWhile (· != '\n') st2) fuel
          else st
        else st
  loop s (endPos s - s.pos.byteIdx + 1)

private def err (msg : String) (s : ParseState) : Except String α :=
  .error s!"{msg} at byte {s.pos.byteIdx}"

private def expect (c : Char) (s : ParseState) : Except String ParseState :=
  if atEnd s then err s!"expected '{c}', got EOF" s
  else if curr s == c then .ok (adv s)
  else err s!"expected '{c}', got '{curr s}'" s

private def expectStr (str : String) (s : ParseState) : Except String ParseState :=
  let bytes := str.toUTF8
  let rec loop (i : Nat) (st : ParseState) : Except String ParseState :=
    if i >= bytes.size then .ok st
    else if atEnd st then .error s!"expected '{str}', got EOF"
    else if curr st == Char.ofNat bytes[i]!.toNat then loop (i + 1) (adv st)
    else err s!"expected '{str}'" s
  loop 0 s

private def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
private def isIdentCont (c : Char) : Bool := c.isAlphanum || c == '_'

private def parseIdent (s : ParseState) : Except String (String × ParseState) :=
  if atEnd s then err "expected identifier, got EOF" s
  else if isIdentStart (curr s) then
    let start := s.pos
    let s' := skipWhile isIdentCont (adv s)
    .ok (extract s' start s'.pos, s')
  else err s!"expected identifier, got '{curr s}'" s

private def parseNat (s : ParseState) : Except String (Nat × ParseState) :=
  if atEnd s then err "expected digit, got EOF" s
  else if (curr s).isDigit then
    let start := s.pos
    let s' := skipWhile Char.isDigit (adv s)
    let numStr := extract s' start s'.pos
    match numStr.toNat? with
    | some n => .ok (n, s')
    | none => .error s!"invalid number '{numStr}'"
  else err s!"expected digit, got '{curr s}'" s

/-! ## Wire Reference -/

private inductive WireRef
  | scalar (name : String)
  | indexed (bus : String) (idx : Nat)
  | loopVar (bus : String) (var : String)

private def wireRefToWire (ref : WireRef) (loopBinding : Option (String × Nat) := none) : Wire :=
  match ref with
  | .scalar name => Wire.mk name
  | .indexed bus idx => Wire.mk s!"{bus}_{idx}"
  | .loopVar bus var =>
    match loopBinding with
    | some (v, i) => if var == v then Wire.mk s!"{bus}_{i}" else Wire.mk s!"{bus}_{var}"
    | none => Wire.mk s!"{bus}_{var}"

private def parseWireRef (s : ParseState) : Except String (WireRef × ParseState) := do
  let (name, s) ← parseIdent s
  if atEnd s then return (.scalar name, s)
  else if curr s == '[' then
    let s ← expect '[' s
    if atEnd s then .error "unexpected EOF in wire index"
    else if (curr s).isDigit then do
      let (idx, s) ← parseNat s
      let s ← expect ']' s
      return (.indexed name idx, s)
    else if isIdentStart (curr s) then do
      let (var, s) ← parseIdent s
      let s ← expect ']' s
      return (.loopVar name var, s)
    else err s!"unexpected char in index" s
  else return (.scalar name, s)

/-! ## Port List -/

private structure PortDecl where
  name : String
  width : Option Nat

private def parsePortDecl (s : ParseState) : Except String (PortDecl × ParseState) := do
  let (name, s) ← parseIdent s
  if !atEnd s && curr s == '[' then do
    let s ← expect '[' s
    let (w, s) ← parseNat s
    let s ← expect ']' s
    return ({ name, width := some w }, s)
  else return ({ name, width := none }, s)

private partial def parsePortList (s : ParseState) : Except String (List PortDecl × ParseState) := do
  let s := skipWS s
  if atEnd s || curr s == '-' || curr s == ')' then return ([], s)
  else do
    let (port, s) ← parsePortDecl s
    let s := skipWS s
    if !atEnd s && curr s == ',' then do
      let (rest, s) ← parsePortList (adv s)
      return (port :: rest, s)
    else return ([port], s)

private def expandPort (p : PortDecl) : List Wire × Option SignalGroup :=
  match p.width with
  | none => ([Wire.mk p.name], none)
  | some w =>
    let wires := (List.range w).map (fun i => Wire.mk s!"{p.name}_{i}")
    (wires, some { name := p.name, width := w, wires })

/-! ## Gate Type -/

private def parseGateType (name : String) : Except String GateType :=
  match name with
  | "AND" => .ok .AND | "OR" => .ok .OR | "NOT" => .ok .NOT
  | "XOR" => .ok .XOR | "BUF" => .ok .BUF | "MUX" => .ok .MUX
  | "DFF" => .ok .DFF | "DFF_SET" => .ok .DFF_SET
  | _ => .error s!"unknown gate type '{name}'"

/-! ## Body Statements -/

private inductive Stmt
  | wireDecl (name : String) (width : Nat)
  | gate (output : WireRef) (gateType : GateType) (inputs : List WireRef)
           (forVar : Option (String × Nat × Nat))
  | inst (moduleName : String) (instName : String) (portMap : List (String × WireRef))

private partial def parseWireRefList (s : ParseState) : Except String (List WireRef × ParseState) := do
  let s := skipWS s
  if atEnd s || curr s == ')' then return ([], s)
  else do
    let (ref, s) ← parseWireRef s
    let s := skipWS s
    if !atEnd s && curr s == ',' then do
      let (rest, s) ← parseWireRefList (skipWS (adv s))
      return (ref :: rest, s)
    else return ([ref], s)

private def parseForSuffix (s : ParseState) : Except String (Option (String × Nat × Nat) × ParseState) := do
  let s := skipWS s
  if atEnd s || curr s != 'f' then return (none, s)
  else
    match expectStr "for" s with
    | .ok s' =>
      -- Ensure "for" is a keyword, not a prefix of an identifier like "force"
      if !atEnd s' && isIdentCont (curr s') then return (none, s)
      else do
        let s := skipWS s'
        let (var, s) ← parseIdent s
        let s := skipWS s
        let s ← expectStr "in" s
        let s := skipWS s
        let (startN, s) ← parseNat s
        let s ← expectStr ".." s
        let (endN, s) ← parseNat s
        return (some (var, startN, endN), s)
    | .error _ => return (none, s)

private def parsePortMapping (s : ParseState) : Except String (List (String × WireRef) × ParseState) := do
  let (baseName, s) ← parseIdent s
  if !atEnd s && curr s == '[' then do
    let s ← expect '[' s
    -- Check for bracket-style bus compression: name[[width]]
    if !atEnd s && curr s == '[' then do
      let s ← expect '[' s
      let (n, s) ← parseNat s
      let s ← expect ']' s
      let s ← expect ']' s
      let s := skipWS s
      let s ← expect '=' s
      let s := skipWS s
      let (ref, s) ← parseWireRef s
      match ref with
      | .scalar busName =>
        -- Bracket-style bus: baseName[[N]] = bus → baseName_0..baseName_(N-1)
        let mappings := (List.range n).map fun i =>
          (s!"{baseName}_{i}", WireRef.indexed busName i)
        return (mappings, s)
      | _ => err "expected scalar bus name after bracket bus compression" s
    else do
      let (n, s) ← parseNat s
      let s ← expect ']' s
      let s := skipWS s
      let s ← expect '=' s
      let s := skipWS s
      let (ref, s) ← parseWireRef s
      match ref with
      | .scalar busName =>
        if n >= 2 then
          -- Bus compression: prefix[width] = busName → expand to N ports
          let mappings := (List.range n).map fun i =>
            (s!"{baseName}{i}", WireRef.indexed busName i)
          return (mappings, s)
        else
          return ([(s!"{baseName}_{n}", ref)], s)
      | _ =>
        return ([(s!"{baseName}_{n}", ref)], s)
  else do
    let s := skipWS s
    let s ← expect '=' s
    let s := skipWS s
    let (ref, s) ← parseWireRef s
    return ([(baseName, ref)], s)

private partial def parsePortMappings (s : ParseState) : Except String (List (String × WireRef) × ParseState) := do
  let s := skipWS s
  if atEnd s || curr s == ')' || curr s == '-' then return ([], s)
  else do
    let (mappings, s) ← parsePortMapping s
    let s := skipWS s
    if !atEnd s && curr s == ',' then do
      let (rest, s) ← parsePortMappings (skipWS (adv s))
      return (mappings ++ rest, s)
    else return (mappings, s)

private def parseStmt (s : ParseState) : Except String (Stmt × ParseState) := do
  let s := skipWS s
  let (ident, s) ← parseIdent s
  let s := skipWS s
  match ident with
  | "wire" => do
    let (name, s) ← parseIdent s
    let s ← expect '[' s
    let (width, s) ← parseNat s
    let s ← expect ']' s
    return (.wireDecl name width, s)
  | "inst" => do
    let (moduleName, s) ← parseIdent s
    let s := skipWS s
    let (instName, s) ← parseIdent s
    let s := skipWS s
    let s ← expect '(' s
    let (inputPorts, s) ← parsePortMappings s
    let s := skipWS s
    let (outputPorts, s) ←
      if !atEnd s && curr s == '-' then do
        let s ← expectStr "->" s
        parsePortMappings (skipWS s)
      else pure ([], s)
    let s := skipWS s
    let s ← expect ')' s
    return (.inst moduleName instName (inputPorts ++ outputPorts), s)
  | _ => do
    -- output wire ref (we already parsed the ident)
    let (outRef, s) ←
      if !atEnd s && curr s == '[' then do
        let s ← expect '[' s
        if atEnd s then .error "unexpected EOF"
        else if (curr s).isDigit then do
          let (idx, s) ← parseNat s
          let s ← expect ']' s
          pure (WireRef.indexed ident idx, s)
        else if isIdentStart (curr s) then do
          let (var, s) ← parseIdent s
          let s ← expect ']' s
          pure (WireRef.loopVar ident var, s)
        else err "unexpected in index" s
      else pure (WireRef.scalar ident, s)
    let s := skipWS s
    let s ← expect '=' s
    let s := skipWS s
    let (gtName, s) ← parseIdent s
    let gateType ← parseGateType gtName
    let s ← expect '(' s
    let (inputs, s) ← parseWireRefList s
    let s ← expect ')' s
    let (forSuffix, s) ← parseForSuffix s
    return (.gate outRef gateType inputs forSuffix, s)

/-! ## Module -/

private def expandGate (output : WireRef) (gateType : GateType) (inputs : List WireRef)
    (forClause : Option (String × Nat × Nat)) : List Gate :=
  match forClause with
  | none =>
    [{ gateType, inputs := inputs.map wireRefToWire, output := wireRefToWire output }]
  | some (var, startN, endN) =>
    (List.range (endN - startN)).map (fun offset =>
      let i := startN + offset
      let binding := some (var, i)
      { gateType
        inputs := inputs.map (wireRefToWire · binding)
        output := wireRefToWire output binding }
    )

private partial def parseBody (s : ParseState) :
    Except String (List Gate × List CircuitInstance × List SignalGroup × ParseState) := do
  let s := skipWS s
  if atEnd s then .error "unexpected EOF in body"
  else if curr s == '}' then return ([], [], [], s)
  else do
    let (stmt, s) ← parseStmt s
    let (restGates, restInsts, restGroups, s) ← parseBody s
    match stmt with
    | .wireDecl name width =>
      let wires := (List.range width).map (fun i => Wire.mk s!"{name}_{i}")
      let sg : SignalGroup := { name, width, wires }
      return (restGates, restInsts, sg :: restGroups, s)
    | .gate output gateType inputs forClause =>
      let gates := expandGate output gateType inputs forClause
      return (gates ++ restGates, restInsts, restGroups, s)
    | .inst moduleName instName portMap =>
      let resolvedPorts := portMap.map (fun (pn, ref) => (pn, wireRefToWire ref))
      let ci : CircuitInstance := { moduleName, instName, portMap := resolvedPorts }
      return (restGates, ci :: restInsts, restGroups, s)

private def parseAnnotations (s : ParseState) : Except String (Bool × ParseState) :=
  let rec loop (st : ParseState) (kh : Bool) (fuel : Nat) : Except String (Bool × ParseState) :=
    match fuel with
    | 0 => .ok (kh, st)
    | fuel + 1 =>
      let st := skipWS st
      if atEnd st then .ok (kh, st)
      else if curr st == '@' then
        match parseIdent (adv st) with
        | .ok (ann, st) => loop st (if ann == "keepHierarchy" then true else kh) fuel
        | .error e => .error e
      else .ok (kh, st)
  loop s false 10

private def parseModule (s : ParseState) : Except String (Circuit × ParseState) := do
  let s := skipWS s
  let s ← expectStr "module" s
  let s := skipWS s
  let (name, s) ← parseIdent s
  let s ← expect '(' s
  let (inputPorts, s) ← parsePortList s
  let s := skipWS s
  let s ← expectStr "->" s
  let s := skipWS s
  let (outputPorts, s) ← parsePortList s
  let s ← expect ')' s
  let (keepHierarchy, s) ← parseAnnotations s
  let s := skipWS s
  let s ← expect '{' s
  let (gates, instances, internalGroups, s) ← parseBody s
  let s := skipWS s
  let s ← expect '}' s
  let inputData := inputPorts.map expandPort
  let outputData := outputPorts.map expandPort
  let portGroups := (inputData ++ outputData).filterMap (·.2)
  return ({
    name
    inputs := inputData.flatMap (·.1)
    outputs := outputData.flatMap (·.1)
    gates, instances
    signalGroups := portGroups ++ internalGroups
    keepHierarchy
  }, s)

def parseShoumei (input : String) : Except String Circuit := do
  let (circuit, _) ← parseModule { input, pos := ⟨0⟩ }
  return circuit

end Shoumei.Codegen.ShoumeiParse
