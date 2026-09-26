/-
Sva2Lean.lean - Pure Lean 4 SVA assertion to BitVec theorem translator.

Ingests the `ifdef FORMAL assertion block of a human-written specification
(verification/specs/*.sv) together with the Lean model of that same
specification (produced by `smt2lean` from Yosys), and emits one Lean theorem
per assertion, stated over the model's step function and discharged by
`bv_decide`.

Why this exists: the assertions in the specs were decorative.  CI only
compiles them (`verilator --assert --lint-only`), and the handful that were
transcribed into Lean by hand drifted -- three of Queue1_spec's four
properties were carried over and `a_pop_effect` was silently dropped.

  spec.sv  --yosys + smt2lean-->  Model.step          (the body)
  spec.sv  --sva2lean---------->  theorem             (the claims)
  netlist  --SEC bridge-------->  netlist == Model    (the lift)

so a claim proven of the spec body holds of the emitted netlist through the
SEC theorem.

Supported subset (everything the specs currently use):
  operators   ! ~ && || == != < > <= >= + - & | ^
  literals    4'd3  2'b01  1'b1  '0  '1  decimals
  selects     bus[constant]; a WIDTH'(expr) cast substitutes the parameter
  builtins    $past(x[, n])  $stable(x)  $onehot(x)
  shapes      assert (e);  assert property (e);
              assert property (a |-> c);  assert property (a |=> c);
              default disable iff (reset);  default clocking ...;

Anything outside the subset is a hard error naming the construct, so a
property can never be dropped silently.
-/

namespace Shoumei.Sva2Lean

set_option maxRecDepth 262144

/-! ## Expression syntax -/

inductive E where
  /-- A port or state variable of the model. -/
  | ident (name : String)
  /-- Literal with an optional explicit width (`4'd3` has 4, `'0` has none). -/
  | lit (value : Nat) (width : Option Nat)
  /-- Binary operator, spelled as in the source. -/
  | bin (op : String) (a b : E)
  /-- Unary `!` or `~`. -/
  | un (op : String) (a : E)
  /-- Constant bit select. -/
  | sel (a : E) (idx : Nat)
  /-- Variable bit select (`out[in]`). -/
  | selDyn (a : E) (idx : E)
  /-- `PARAM'(expr)`, resolved against the instantiated parameter map. -/
  | cast (param : String) (a : E)
  | past (a : E) (n : Nat)
  | stable (a : E)
  | onehot (a : E)
  deriving Repr, Inhabited

inductive Shape where
  | invariant   (e : E)
  | impliesSame (a c : E)
  | impliesNext (a c : E)
  deriving Repr, Inhabited

structure Assertion where
  name : String
  shape : Shape
  /-- Per-property `disable iff` override: `none` inherits the module default,
      `some ""` means the property opted out (`disable iff (1'b0)`), and
      `some r` disables on signal `r`. -/
  disable : Option String := none
  deriving Repr, Inhabited

/-! ## Tokenizer -/

inductive Tok where
  | id (s : String)
  | lit (text : String) (value : Nat) (width : Option Nat)
  | op (s : String)
  | lp | rp | lb | rb | comma | apos
  deriving Repr, Inhabited, DecidableEq

/-- Longest match first; the temporal operators must precede `|`. -/
def operators : List String :=
  ["|=>", "|->", "==", "!=", "<=", ">=", "&&", "||",
   "+", "-", "*", "&", "|", "^", "!", "~", "<", ">", "="]

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '$'

/-- Consume `4'd3` / `2'b01` / `'0` / `17` into (value, explicit width? ...). -/
partial def lexNumber (cs : List Char) : Nat × Option Nat × List Char :=
  let rec digits (cs : List Char) (v : Nat) : Nat × List Char :=
    match cs with
    | d :: rest => if d.isDigit then digits rest (v * 10 + (d.toNat - '0'.toNat)) else (v, cs)
    | [] => (v, [])
  match cs with
    | '\'' :: b :: rest =>
      if b == 'd' then
        let (v, left) := digits rest 0
        (v, some 0, left)          -- width filled by caller from the leading digits
      else if b == 'b' then
        let (v, left) := digits rest 0
        (v, some 0, left)
      else if b == '0' then (0, none, rest)
      else if b == '1' then (1, none, rest)
      else (0, none, cs)
    | _ =>
      let (v, left) := digits cs 0
      (v, none, left)

partial def tokenize (s : String) : List Tok :=
  let rec go (cs : List Char) (acc : List Tok) : List Tok :=
    match cs with
    | [] => acc.reverse
    | c :: rest =>
      if c.isWhitespace then go rest acc
      else if c == '(' then go rest (.lp :: acc)
      else if c == ')' then go rest (.rp :: acc)
      else if c == '[' then go rest (.lb :: acc)
      else if c == ']' then go rest (.rb :: acc)
      else if c == ',' then go rest (.comma :: acc)
      else if c == '\'' && rest.head? == some '0' then
        go rest.tail! (.lit "'0" 0 none :: acc)
      else if c == '\'' && rest.head? == some '1' then
        go rest.tail! (.lit "'1" 1 none :: acc)
      else if c == '\'' then go rest (.apos :: acc)
      else if c.isDigit then
        let rec lead (ds : List Char) (text : List Char) : Nat × List Char :=
          match ds with
          | d :: rt => if d.isDigit then lead rt (d :: text) else (0, ds)
          | [] => (0, [])
        let leading := (cs.takeWhile (·.isDigit)).map (·.toNat - '0'.toNat)
        let width := leading.foldl (fun a d => a * 10 + d) 0
        let _ := lead
        let afterDigits := cs.dropWhile (·.isDigit)
        let (value, w, left) := lexNumber afterDigits
        let w := match w with
          | some 0 => some width
          | other => other
        let text := String.ofList (cs.take (cs.length - left.length))
        go left (.lit text value w :: acc)
      else if isWordChar c then
        let rec take (ds : List Char) (a : List Char) : List Char × List Char :=
          match ds with
          | d :: rt => if isWordChar d then take rt (d :: a) else (ds, a)
          | [] => ([], a)
        let (left, a) := take rest [c]
        go left (.id (String.ofList a.reverse) :: acc)
      else
        let cands := operators.filter (fun o =>
          let ol := o.toList
          (ol.zip (c :: rest)).all (fun (x, y) => x == y))
        match cands with
        | [] => go rest acc
        | _ =>
          let best := cands.foldl (fun (b : String) o => if o.length > b.length then o else b) ""
          go ((c :: rest).drop best.length) (.op best :: acc)
  go s.toList []

/-! ## Parser -/

structure S where
  toks : List Tok
  deriving Inhabited

def peekOp (s : S) : Option String :=
  match s.toks with
  | .op o :: _ => some o
  | _ => none

/-- Precedence levels, loosest first. -/
def levels : List (List String) :=
  [["||"], ["&&"], ["==", "!=", "<", ">", "<=", ">="], ["+", "-"], ["&", "|", "^"]]

partial def parseExpr (s : S) : Option (E × S) := parseLvl 0 s
where
  parseLvl (lv : Nat) (s : S) : Option (E × S) :=
    if lv >= levels.length then parseUnary s
    else
      match parseLvl (lv + 1) s with
      | none => none
      | some (lhs, s1) =>
        let ops := levels.getD lv []
        let rec loop (l : E) (s : S) : Option (E × S) :=
          match peekOp s with
          | some o =>
            if ops.contains o then
              match parseLvl (lv + 1) ⟨s.toks.drop 1⟩ with
              | some (r, s2) => loop (.bin o l r) s2
              | none => some (l, s)
            else some (l, s)
          | none => some (l, s)
        loop lhs s1
  parseUnary (s : S) : Option (E × S) :=
    match peekOp s with
    | some "!" =>
      match parseUnary ⟨s.toks.drop 1⟩ with
      | some (a, s1) => some (.un "!" a, s1)
      | none => none
    | some "~" =>
      match parseUnary ⟨s.toks.drop 1⟩ with
      | some (a, s1) => some (.un "~" a, s1)
      | none => none
    | _ => parsePostfix s
  parsePostfix (s : S) : Option (E × S) :=
    match parsePrimary s with
    | none => none
    | some (e, s1) =>
      match s1.toks with
      | .lb :: .lit _ k _ :: .rb :: rest => some (.sel e k, ⟨rest⟩)
      | .lb :: rest =>
        match parseExpr ⟨rest⟩ with
        | some (i, s2) =>
          match s2.toks with
          | .rb :: rest2 => some (.selDyn e i, ⟨rest2⟩)
          | _ => none
        | none => none
      | _ => some (e, s1)
  parsePrimary (s : S) : Option (E × S) :=
    match s.toks with
    | .op "(" :: rest => parseParen ⟨rest⟩
    | .lp :: rest => parseParen ⟨rest⟩
    | .lit _ v w :: rest => some (.lit v w, ⟨rest⟩)
    | .id "(" :: rest => parseParen ⟨rest⟩
    | .id n :: .apos :: .lp :: rest =>
      match parseExpr ⟨rest⟩ with
      | some (e, s1) =>
        match s1.toks with
        | .rp :: rest2 => some (.cast n e, ⟨rest2⟩)
        | _ => none
      | none => none
    | .id "$past" :: .lp :: rest =>
      match parseExpr ⟨rest⟩ with
      | some (e, s1) =>
        match s1.toks with
        | .rp :: rest2 => some (.past e 1, ⟨rest2⟩)
        | .comma :: .lit _ n _ :: .rp :: rest2 => some (.past e n, ⟨rest2⟩)
        | _ => none
      | none => none
    | .id "$stable" :: .lp :: rest =>
      match parseExpr ⟨rest⟩ with
      | some (e, s1) =>
        match s1.toks with
        | .rp :: rest2 => some (.stable e, ⟨rest2⟩)
        | _ => none
      | none => none
    | .id "$onehot" :: .lp :: rest =>
      match parseExpr ⟨rest⟩ with
      | some (e, s1) =>
        match s1.toks with
        | .rp :: rest2 => some (.onehot e, ⟨rest2⟩)
        | _ => none
      | none => none
    | .id n :: rest => some (.ident n, ⟨rest⟩)
    | _ => none
  parseParen (s : S) : Option (E × S) :=
    match parseExpr s with
    | some (e, s1) =>
      match s1.toks with
      | .rp :: rest => some (e, ⟨rest⟩)
      | _ => none
    | none => none

/-! ## Source extraction -/

/-- Match the identifier quoting used by `smt2lean`, so references to model
    fields resolve identically. -/
def sanitizeIdent (s : String) : String :=
  let s := s.map fun c => if c.isAlphanum || c == '_' then c else '_'
  let s := if s.startsWith "_" then "v" ++ s else s
  if ["in", "out", "where", "def", "let", "open", "structure", "inductive",
      "match", "with", "if", "then", "else", "do", "for"].contains s then
    "«" ++ s ++ "»"
  else s

/-- Drop `//` comments. -/
def stripComments (src : String) : String :=
  String.intercalate "\n" <| src.splitOn "\n" |>.map fun line =>
    match line.splitOn "//" with
    | [] => line
    | first :: _ => first

/-- Text between `` `ifdef FORMAL `` and its `` `endif ``. -/
def formalRegion (src : String) : Except String String := do
  let lines := (stripComments src).splitOn "\n"
  let mut inside := false
  let mut acc : List String := []
  let mut seen := false
  for l in lines do
    let t := l.trimAscii.toString
    if t.startsWith "`ifdef FORMAL" then
      inside := true
      seen := true
    else if inside && t.startsWith "`endif" then
      inside := false
    else if inside then
      acc := acc ++ [l]
  if !seen then
    throw "no `ifdef FORMAL block"
  return String.intercalate "\n" acc

/-- Split on `;` at paren/bracket depth zero. -/
def statements (region : String) : List String :=
  let rec go (cs : List Char) (depth : Nat) (cur : List Char) (acc : List String) : List String :=
    match cs with
    | [] => acc ++ [String.ofList cur.reverse]
    | c :: rest =>
      if c == '(' || c == '[' then go rest (depth + 1) (c :: cur) acc
      else if c == ')' || c == ']' then go rest (depth - 1) (c :: cur) acc
      else if c == ';' && depth == 0 then go rest depth [] (acc ++ [String.ofList cur.reverse])
      else go rest depth (c :: cur) acc
  (go region.toList 0 [] []).map (·.trimAscii.toString) |>.filter (·.length > 0)

/-- The reset signal named by `default disable iff (...)`; `none` if absent.
    Scanned per line: `endclocking` carries no semicolon, so statement
    splitting would merge it with the following declaration. -/
def disableReset (region : String) : Option String :=
  let hit := (region.splitOn "\n").find? fun line =>
    line.trimAscii.toString.startsWith "default disable iff"
  match hit with
  | none => none
  | some line =>
    match (line.splitOn "(").drop 1 with
    | [] => none
    | rest =>
      let body := String.intercalate "(" rest
      match body.splitOn ")" with
      | x :: _ => some (x.trimAscii.toString)
      | [] => none

/-- Split a concurrent property body on its top-level temporal operator. -/
def splitTemporal (toks : List Tok) : Option (String × List Tok × List Tok) :=
  let rec go (depth : Nat) (seen : List Tok) (rest : List Tok) : Option (String × List Tok × List Tok) :=
    match rest with
    | [] => none
    | .op o :: more =>
      if depth == 0 && (o == "|=>" || o == "|->") then
        some (o, seen.reverse, more)
      else go depth (rest.head! :: seen) more
    | .lp :: more => go (depth + 1) (.lp :: seen) more
    | .rp :: more => go (depth - 1) (.rp :: seen) more
    | t :: more => go depth (t :: seen) more
  go 0 [] toks

/-- Tokens following a balanced parenthesis group starting at `ts`. -/
partial def skipParens (ts : List Tok) (depth : Nat) : List Tok :=
  match ts with
  | .lp :: rest => skipParens rest (depth + 1)
  | .rp :: rest => if depth <= 1 then rest else skipParens rest (depth - 1)
  | _ :: rest => skipParens rest depth
  | [] => []

/-- The tokens inside a balanced parenthesis group, and the tokens after it. -/
partial def takeParenBody (rs : List Tok) (acc : List Tok) (depth : Nat) : List Tok × List Tok :=
  match rs with
  | .lp :: more => takeParenBody more (.lp :: acc) (depth + 1)
  | .rp :: more => if depth == 0 then (acc.reverse, more) else takeParenBody more (.rp :: acc) (depth - 1)
  | x :: more => takeParenBody more (x :: acc) depth
  | [] => (acc.reverse, [])

/-- A leading clocking event and/or `disable iff` clause inside a property
    body.  Returns the stripped tokens plus the disable override, where
    `some ""` means the property opted out with `disable iff (1'b0)`.
    The tokenizer drops `@`, so `@(posedge clk)` arrives as `( posedge clk )`. -/
partial def stripPrefixGo (ts : List Tok) (dis : Option String) : List Tok × Option String :=
  match ts with
  | .op "@" :: rest => stripPrefixGo (skipParens rest 0) dis
  | .lp :: .id "posedge" :: rest => stripPrefixGo (skipParens (.lp :: .id "posedge" :: rest) 0) dis
  | .lp :: .id "negedge" :: rest => stripPrefixGo (skipParens (.lp :: .id "negedge" :: rest) 0) dis
  | .id "disable" :: .id "iff" :: .lp :: rest =>
    let (body, after) := takeParenBody rest [] 0
    let dis := match body with
      | [.lit _ 0 _] => some ""            -- `1'b0`: opted out
      | [.id n] => some n
      | _ => some ""
    stripPrefixGo after dis
  | _ => (ts, dis)

def stripPropertyPrefix (toks : List Tok) : List Tok × Option String :=
  stripPrefixGo toks none

/-- Split an assertion statement into its `if` guard, if any, and the tokens of
    the asserted expression.  Working on tokens matters: `if (c) assert (e)`
    means `c -> e`, so the guard's parentheses must not be mistaken for the
    argument of `assert`. -/
def assertParts (toks : List Tok) : Except String (Option E × List Tok) := do
  let idx := toks.findIdx? (fun t => t == .id "assert")
  let i ← match idx with
    | some i => pure i
    | none => throw "statement carries no `assert`"
  let pre := toks.take i
  let guard ←
    if pre.any (fun t => t == .id "if") then
      match pre.findIdx? (fun t => t == .lp) with
      | some j =>
        let (inner, _) := takeParenBody (pre.drop (j + 1)) [] 0
        match stripPropertyPrefix inner with
        | (e, _) =>
          match parseExpr ⟨e⟩ with
          | some (g, _) => pure (some g)
          | none => throw "cannot parse an `if` guard"
      | none => throw "`if` without a parenthesized guard"
    else pure none
  let after := (toks.drop (i + 1)).dropWhile (fun t => t == .id "property")
  match after with
  | .lp :: rest =>
    let (body, _) := takeParenBody rest [] 0
    if body.isEmpty then throw "empty assertion body"
    pure (guard, body)
  | _ => throw "no parenthesized argument follows `assert`"

/-- The label of `label: assert ...`, or a synthetic name. -/
def assertName (stmt : String) (idx : Nat) : String :=
  match stmt.splitOn ":" with
  | label :: _ =>
    let l := label.trimAscii.toString
    if !l.isEmpty && l.all (fun c => c.isAlphanum || c == '_') then l else s!"prop_{idx}"
  | [] => s!"prop_{idx}"

/-- Parse one assertion statement into its name and temporal shape. -/
def parseAssert (stmt : String) (idx : Nat) : Except String Assertion := do
  if !stmt.contains "assert" then
    throw s!"not an assertion: {stmt}"
  let (guard, rawBody) := ← assertParts (tokenize stmt)
  let (toks, disableOverride) := stripPropertyPrefix rawBody
  -- Reject leftover tokens: dropping part of a property is exactly the
  -- failure this tool exists to prevent.
  let whole (what : String) (r : Option (E × S)) : Except String E :=
    match r with
    | some (e, s') =>
      let extra := s'.toks.filter (fun t => t != .rp && t != .lb && t != .rb)
      if extra.isEmpty then pure e
      else throw s!"unparsed trailing tokens in {what} of {stmt}: {repr extra}"
    | none => throw s!"cannot parse {what} of {stmt}"
  let base ←
    match splitTemporal toks with
    | some ("|=>", lhs, rhs) =>
      pure (.impliesNext (← whole "|=> antecedent" (parseExpr ⟨lhs⟩))
                         (← whole "|=> consequent" (parseExpr ⟨rhs⟩)))
    | some ("|->", lhs, rhs) =>
      pure (.impliesSame (← whole "|-> antecedent" (parseExpr ⟨lhs⟩))
                         (← whole "|-> consequent" (parseExpr ⟨rhs⟩)))
    | _ =>
      pure (.invariant (← whole "expression" (parseExpr ⟨toks⟩)))
  -- An immediate assertion under an `if` guard is a same-cycle implication.
  let shape := match guard with
    | some g =>
      match base with
      | .invariant e => .impliesSame g e
      | other => other
    | none => base
  return { name := assertName stmt idx, shape := shape, disable := disableOverride }

/-! ## Model introspection -/

structure Model where
  ns : String
  inputs : List (String × Nat)
  outputs : List (String × Nat)
  state : List (String × Nat)
  deriving Inhabited

/-- Read field names and widths out of a generated model module. -/
def parseModel (src : String) : Except String Model := do
  let lines := src.splitOn "\n"
  let ns :=
    match lines.find? (fun l => l.trimAscii.toString.startsWith "namespace ") with
    | some l => (l.trimAscii.toString.drop 10).toString.trimAscii.toString
    | none => ""
  if ns.isEmpty then throw "model has no namespace"
  let fieldsOf (structName : String) : List (String × Nat) := Id.run do
    let mut started := false
    let mut acc : List (String × Nat) := []
    for l in lines do
      let t := l.trimAscii.toString
      if t == s!"structure {structName} where" then started := true
      else if started && t.startsWith "deriving" then break
      else if started then
        match t.splitOn ":" with
        | [name, ty] =>
          let ty := ty.trimAscii.toString
          if ty.startsWith "BitVec " then
            let n := (ty.drop 7).toString.trimAscii.toString
            if let some w := n.toNat? then
              -- `smt2lean` quotes reserved words as `«in»`/«out»; hold the plain
              -- name here and re-quote on emission via sanitizeIdent.
              let raw := name.trimAscii.toString
              let raw := (raw.dropWhile (· == '«')).dropEndWhile (· == '»')
              acc := acc ++ [(raw.toString, w)]
        | _ => ()
    acc
  return { ns, inputs := fieldsOf "Inputs", outputs := fieldsOf "Outputs", state := fieldsOf "State" }

/-! ## Rendering -/

structure Ctx where
  model : Model
  params : List (String × Nat)
  step : String
  i0 : String
  s0 : String
  i1 : String
  deriving Inhabited

def lookupW (ctx : Ctx) (name : String) : Option Nat :=
  (ctx.model.outputs.find? (·.1 == name) |>.map (·.2))
    <|> (ctx.model.inputs.find? (·.1 == name) |>.map (·.2))
    <|> (ctx.model.state.find? (·.1 == name) |>.map (·.2))

/-- Width of an expression, where it can be known without a target. -/
partial def wOf (ctx : Ctx) (e : E) : Option Nat :=
  match e with
  | .ident n => lookupW ctx n
  | .lit _ (some w) => some w
  | .lit _ none => none
  | .sel _ _ => some 1
  | .selDyn _ _ => some 1
  | .cast p a => (ctx.params.find? (·.1 == p) |>.map (·.2)) <|> wOf ctx a
  | .past a _ => wOf ctx a
  | .stable _ => some 1
  | .onehot _ => some 1
  | .un "!" _ => some 1
  | .un _ a => wOf ctx a
  | .bin op a b =>
    if ["==", "!=", "<", ">", "<=", ">=", "&&", "||"].contains op then some 1
    else
      match wOf ctx a, wOf ctx b with
      | some x, some y => some (max x y)
      | some x, none => some x
      | none, some y => some y
      | none, none => none

/-- The model's step function applied once, from cycle 0. -/
def s1Of (ctx : Ctx) : String := s!"({ctx.step} {ctx.i0} {ctx.s0}).2"

/-- Reference a port or state variable at cycle `c`. -/
partial def refAt (ctx : Ctx) (c : Nat) (name : String) : Except String String := do
  let n := sanitizeIdent name
  let inOut := ctx.model.outputs.any (·.1 == name)
  let inIn := ctx.model.inputs.any (·.1 == name)
  let inSt := ctx.model.state.any (·.1 == name)
  if !(inOut || inIn || inSt) then
    throw s!"'{name}' is not a port or state variable of {ctx.model.ns}; internal signals cannot be referenced"
  if inOut then
    match c with
    | 0 => return s!"({ctx.step} {ctx.i0} {ctx.s0}).1.{n}"
    | 1 => return s!"({ctx.step} {ctx.i1} {s1Of ctx}).1.{n}"
    | _ => throw s!"output {name} sampled beyond cycle 1"
  else if inIn then
    return (if c == 0 then s!"{ctx.i0}.{n}" else s!"{ctx.i1}.{n}")
  else
    return (if c == 0 then s!"{ctx.s0}.{n}" else s!"({s1Of ctx}).{n}")

mutual

/-- Render an expression as a term at cycle `c`. -/
partial def rend (ctx : Ctx) (c : Nat) (e : E) : Except String String := do
  match e with
  | .ident n => refAt ctx c n
  | .lit v (some w) => return s!"{v}#{w}"
  | .lit _ none => throw "untyped literal outside a sized context"
  | .sel a k =>
    let a' ← rend ctx c a
    return s!"(BitVec.extractLsb' {k} 1 {a'})"
  | .selDyn a idx =>
    let w := (wOf ctx a).getD 0
    if w == 0 then throw "variable bit select of an operand of unknown width"
    let a' ← rend ctx c a
    let iw := (wOf ctx idx).getD 1
    let idx' ← rendW ctx c idx iw
    -- index outside the bus reads as a zero bit, as in SystemVerilog
    let mut acc := "0#1"
    for k in (List.range w).reverse do
      acc := s!"(bif {idx'} == {k}#{iw} then (BitVec.extractLsb' {k} 1 {a'}) else {acc})"
    return acc
  | .cast p a =>
    match ctx.params.find? (·.1 == p) with
    | some (_, w) => rendW ctx c a w
    | none => throw s!"cast to unknown parameter '{p}'; pass PARAM=VALUE"
  | .past a n =>
    if c < n then throw s!"$past at cycle {c} with depth {n} exceeds the modelled window"
    rend ctx (c - n) a
  | .stable a =>
    if c == 0 then throw "$stable needs a previous cycle"
    let now ← rend ctx c a
    let prev ← rend ctx (c - 1) a
    return s!"(bif {now} == {prev} then 1#1 else 0#1)"
  | .onehot a =>
    let w := (match a with | .ident n => lookupW ctx n | _ => none).getD 1
    let a' ← rendW ctx c a w
    return s!"(bif {a'} != 0#{w} then (bif ({a'} &&& ({a'} - 1#{w})) == 0#{w} then 1#1 else 0#1) else 0#1)"
  | .un _ a =>
    let a' ← rend ctx c a
    return s!"(~~~{a'})"
  | .bin op a b =>
    match op with
    | "==" | "!=" | "<" | ">" | "<=" | ">=" =>
      let w := (wOf ctx a <|> wOf ctx b).getD 1
      let a' ← rendW ctx c a w
      let b' ← rendW ctx c b w
      let cmp := match op with
        | "==" => s!"{a'} == {b'}"
        | "!=" => s!"{a'} != {b'}"
        | "<"  => s!"BitVec.ult {a'} {b'}"
        | ">"  => s!"BitVec.ult {b'} {a'}"
        | "<=" => s!"BitVec.ule {a'} {b'}"
        | _    => s!"BitVec.ule {b'} {a'}"
      return s!"(bif {cmp} then 1#1 else 0#1)"
    | "&&" =>
      let a' ← rendW ctx c a 1
      let b' ← rendW ctx c b 1
      return s!"({a'} &&& {b'})"
    | "||" =>
      let a' ← rendW ctx c a 1
      let b' ← rendW ctx c b 1
      return s!"({a'} ||| {b'})"
    | _ =>
      let w := (wOf ctx a <|> wOf ctx b).getD 1
      let a' ← rendW ctx c a w
      let b' ← rendW ctx c b w
      let op' := match op with
        | "+" => "+" | "-" => "-" | "&" => "&&&" | "|" => "|||" | "^" => "^^^"
        | _ => op
      return s!"({a'} {op'} {b'})"

/-- Render `e` as a term of exactly width `w`. -/
partial def rendW (ctx : Ctx) (c : Nat) (e : E) (w : Nat) : Except String String := do
  match e with
  | .lit v none => return s!"{v}#{w}"
  | _ =>
    let t ← rend ctx c e
    match wOf ctx e with
    | some wt =>
      if wt == w then return t
      else if wt < w then return s!"(0#{w - wt} ++ {t})"
      else return s!"(BitVec.extractLsb' 0 {w} {t})"
    | none => return t

end

/-! ## Theorem emission -/

/-- Positional destructuring pattern for an n-field structure. -/
def pat (n : Nat) (tag : String) : String :=
  "⟨" ++ String.intercalate ", " ((List.range n).map fun k => s!"{tag}{k}") ++ "⟩"

def destructLines (ctx : Ctx) (cyc : Nat) : String := Id.run do
  let one (v : String) (n : Nat) : String :=
    if n == 0 then s!"  obtain ⟨⟩ := {v}" else s!"  obtain {pat n v} := {v}"
  let mut ls : List String := [one ctx.s0 ctx.model.state.length]
  ls := ls ++ [one ctx.i0 ctx.model.inputs.length]
  if cyc > 0 then
    ls := ls ++ [one ctx.i1 ctx.model.inputs.length]
  return String.intercalate "\n" ls

/-- Positive (non-negated) occurrences of a signal in an expression. -/
partial def occursPos (name : String) (e : E) : Bool :=
  match e with
  | .ident n => n == name
  | .lit _ _ => false
  | .un "!" _ => false                       -- negated, so not a positive use
  | .un _ a => occursPos name a
  | .sel a _ => occursPos name a
  | .selDyn a i => occursPos name a || occursPos name i
  | .cast _ a => occursPos name a
  | .past a _ => occursPos name a
  | .stable a => occursPos name a
  | .onehot a => occursPos name a
  | .bin _ a b => occursPos name a || occursPos name b

def emitTheorem (ctx : Ctx) (resetOpt : Option String) (a : Assertion) : Except String String := do
  -- A property whose antecedent assumes the very signal it is disabled on can
  -- never fail; refusing it is the point of this tool.
  let effDisable : Option String := match a.disable with
    | some d => if d.isEmpty then none else some d
    | none => resetOpt
  let antecedentOf : Option E := match a.shape with
    | .invariant e => some e
    | .impliesSame ante _ => some ante
    | .impliesNext ante _ => some ante
  match effDisable, antecedentOf with
  | some r, some ante =>
    if occursPos r ante then
      throw s!"assertion '{a.name}' is vacuous: it is disabled on '{r}' yet its antecedent assumes '{r}'; give the property its own `disable iff (1'b0)`"
  | _, _ => pure ()
  let rst := effDisable.getD ""
  let rstHyp (iv : String) : String :=
    if rst.isEmpty then "" else s!"\n    (h_rst{iv.drop 1} : {iv}.{sanitizeIdent rst} = 0#1)"
  let proof (cyc : Nat) : String :=
    destructLines ctx cyc ++ "\n  simp only [" ++ ctx.step ++ "] at *\n  bv_decide"
  let binders (cyc : Nat) : String :=
    if cyc == 0 then s!"({ctx.i0} : {ctx.model.ns}.Inputs) ({ctx.s0} : {ctx.model.ns}.State)"
    else s!"({ctx.i0} {ctx.i1} : {ctx.model.ns}.Inputs) ({ctx.s0} : {ctx.model.ns}.State)"
  match a.shape with
  | .invariant e =>
    let g ← rend ctx 0 e
    return s!"/-- SVA {a.name}: invariant. -/\ntheorem {a.name} {binders 0}{rstHyp ctx.i0} :\n    {g} = 1#1 := by\n{proof 0}\n"
  | .impliesSame ante cons =>
    let ga ← rend ctx 0 ante
    let gc ← rend ctx 0 cons
    return s!"/-- SVA {a.name}: same-cycle implication. -/\ntheorem {a.name} {binders 0}{rstHyp ctx.i0} :\n    {ga} = 1#1 → {gc} = 1#1 := by\n{proof 0}\n"
  | .impliesNext ante cons =>
    let ga ← rend ctx 0 ante
    let gc ← rend ctx 1 cons
    return s!"/-- SVA {a.name}: next-cycle implication. -/\ntheorem {a.name} {binders 1}{rstHyp ctx.i0}{rstHyp ctx.i1} :\n    {ga} = 1#1 → {gc} = 1#1 := by\n{proof 1}\n"

def header (ns : String) (src : String) : String :=
  s!"/-\nGenerated by `lake exe sva2lean` from {src} -- do not edit.\nEach theorem states one assertion of the specification, checked against the\nLean model of that same specification.\n-/\nimport {ns}\nimport Std.Tactic.BVDecide\n\nnamespace {ns}Props\n\nset_option linter.unusedVariables false\nset_option maxRecDepth 262144\n\n"

def emit (ns : String) (assertions : List Assertion) (ctx : Ctx)
    (resetOpt : Option String) (src : String) : Except String String := do
  let mut body := ""
  for a in assertions do
    body := body ++ (← emitTheorem ctx resetOpt a) ++ "\n"
  return header ns src ++ body ++ s!"end {ns}Props\n"

def run (args : List String) : IO UInt32 := do
  match args with
  | specPath :: modelPath :: outPath :: rest =>
    try
      let params : List (String × Nat) := rest.filterMap fun a =>
        match a.splitOn "=" with
        | [k, v] => v.toNat?.map (fun n => (k, n))
        | _ => none
      let src ← IO.FS.readFile specPath
      let region ← IO.ofExcept (formalRegion src)
      let stmts := (statements region).filter (fun s => s.contains "assert")
      if stmts.isEmpty then
        IO.eprintln s!"sva2lean: {specPath} has no assertions"
        return 1
      let mut assertions : List Assertion := []
      let mut i := 0
      for s in stmts do
        assertions := assertions ++ [← IO.ofExcept (parseAssert s i)]
        i := i + 1
      let msrc ← IO.FS.readFile modelPath
      let model ← IO.ofExcept (parseModel msrc)
      let ctx : Ctx := { model, params, step := s!"{model.ns}.step", i0 := "i0", s0 := "s0", i1 := "i1" }
      let out ← IO.ofExcept (emit model.ns assertions ctx (disableReset region) specPath)
      IO.FS.writeFile outPath out
      IO.println s!"sva2lean: {assertions.length} assertion(s) from {specPath} -> {outPath}"
      return 0
    catch e =>
      IO.eprintln s!"sva2lean: {e.toString}"
      return 1
  | _ =>
    IO.eprintln "Usage: sva2lean <spec.sv> <model.lean> <out.lean> [PARAM=VALUE ...]"
    return 1

end Shoumei.Sva2Lean

/-- Entry point. -/
def main (args : List String) : IO UInt32 := Shoumei.Sva2Lean.run args
