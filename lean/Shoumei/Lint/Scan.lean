/-
  Shoumei.Lint.Scan - the shared scanner for the Lean linter and its fixer.

  The scan tags every character with the region it belongs to. A rule can then
  tell code from a comment and from a string literal:

  - code
  - a string literal, raw strings (`r"..."`, `r#"..."#`) included
  - the `{...}` term of an interpolated string, with its nested literals
  - a character literal
  - a line comment
  - a block comment of any nesting depth

  A block comment and a string literal both continue over a line break, so the
  scan walks the whole file.  A line comment ends at the line break.

  An interpolated string can hold a string literal in its term:

      s!"{String.intercalate ", " xs}"
                             ^^^^ nested literal, not code

  A scan that ends the outer literal at the first quote takes `, ` for code.
-/

namespace Shoumei.Lint

/-- A character that continues a Lean identifier, for a word boundary test. -/
def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\''

/-- The region a character belongs to. -/
inductive Spot where
  | code
  | str
  /-- The `{...}` term of an interpolated string, braces included. -/
  | interp
  | char
  | lineComment
  | blockComment
  deriving BEq, Inhabited

/-- One line as characters, each with the region it belongs to. -/
abbrev ScannedLine := List (Char × Spot)

/-- The text of a scanned line. -/
def textOf (line : ScannedLine) : String :=
  String.ofList (line.map Prod.fst)

/-- The width of the part of a line that is not inside a string literal.
    The term of an interpolated string counts as part of the literal. -/
def codeWidth (line : ScannedLine) : Nat :=
  (line.filter (fun (_, spot) => spot != .str && spot != .interp)).length

/-- The commands that read a plain string literal as an interpolated one. -/
def interpolatingCommands : List String :=
  ["throwError", "logInfo", "logWarning", "logError"]

/-- The identifier that ends before a position, with the spaces between
    skipped.  `before` holds the line so far, last character first. -/
def identBefore (before : ScannedLine) : String :=
  let rest := before.dropWhile (fun (c, _) => c == ' ')
  String.ofList ((rest.takeWhile (fun (c, _) => isIdentChar c)).map Prod.fst).reverse

/-- True when a string literal that opens here takes `{...}` interpolation.
    Such a literal follows `s!`, `m!` or `f!`, or a command that reads its
    literal as interpolated. -/
def opensInterpolated (before : ScannedLine) : Bool :=
  match before.dropWhile (fun (c, _) => c == ' ') with
  | ('!', _) :: _ => true
  | _ => interpolatingCommands.contains (identBefore before)

/-- The count of `#` marks when a string literal that opens here is a raw
    string (`r"..."`, `r#"..."#`), or `none` for a normal string. -/
def rawOpener (before : ScannedLine) : Option Nat :=
  let hashes := (before.takeWhile (fun (c, _) => c == '#')).length
  match before.drop hashes with
  | ('r', _) :: rest =>
    match rest.head? with
    | some (previous, _) => if isIdentChar previous then none else some hashes
    | none => some hashes
  | _ => none

/-- The scanner state between two characters. -/
structure ScanState where
  spot : Spot := .code
  /-- The nesting depth of the open block comment. -/
  depth : Nat := 0
  /-- The previous character was a backslash in a string or character literal. -/
  escape : Bool := false
  /-- The `#` count of an open raw string. -/
  raw : Option Nat := none
  /-- The open string literal takes `{...}` interpolation. -/
  interp : Bool := false
  /-- The brace depth of the open interpolation term. -/
  braces : Nat := 0
  /-- The brace depths of the interpolation terms that hold the open literal,
      innermost first. -/
  outer : List Nat := []
  deriving Inhabited

/-- Open a string literal.  `enclosing` holds the brace depths of the
    interpolation terms around it. -/
def openString (s : ScanState) (before : ScannedLine) (enclosing : List Nat) : ScanState :=
  let raw := rawOpener before
  { s with spot := .str, escape := false, raw := raw,
           interp := raw.isNone && opensInterpolated before, outer := enclosing }

/-- Close a string literal: back to code, or back to the term that holds it. -/
def closeString (s : ScanState) : ScanState :=
  match s.outer with
  | [] => { s with spot := .code, escape := false, raw := none, interp := false }
  | b :: rest =>
    { s with spot := .interp, escape := false, raw := none, braces := b, outer := rest }

/-- True when the quote at the head of `rest`'s predecessor closes a raw
    string with `hashes` marks: the next `hashes` characters are all `#`. -/
def closesRaw (hashes : Nat) (rest : List Char) : Bool :=
  let marks := rest.take hashes
  marks.length == hashes && marks.all (· == '#')

/-- The state after one character.  `rest` is the text after it, `before`
    the line before it, last character first. -/
def step (s : ScanState) (c : Char) (rest : List Char) (before : ScannedLine) : ScanState :=
  match s.spot with
  | .str =>
    match s.raw with
    | some hashes => if c == '"' && closesRaw hashes rest then closeString s else s
    | none =>
      if s.escape then { s with escape := false }
      else if c == '\\' then { s with escape := true }
      else if c == '"' then closeString s
      else if c == '{' && s.interp then { s with spot := .interp, braces := 1 }
      else s
  | .interp =>
    -- The term of an interpolation.  A quote opens a nested literal.  The
    -- brace that ends the term returns to the outer literal.
    if c == '"' then openString s before (s.braces :: s.outer)
    else if c == '{' then { s with braces := s.braces + 1 }
    else if c == '}' then
      if s.braces == 1 then { s with spot := .str, interp := true, braces := 0 }
      else { s with braces := s.braces - 1 }
    else s
  | .char =>
    if s.escape then { s with escape := false }
    else if c == '\\' then { s with escape := true }
    else if c == '\'' then { s with spot := .code }
    else s
  | .lineComment => s
  | .blockComment =>
    -- An opener deepens the comment.  A closer ends one level, and the
    -- end of the outermost level returns to code.
    if c == '/' && rest.head? == some '-' then { s with depth := s.depth + 1 }
    else if c == '-' && rest.head? == some '/' then
      { s with spot := if s.depth == 1 then .code else .blockComment, depth := s.depth - 1 }
    else s
  | .code =>
    if c == '-' && rest.head? == some '-' then { s with spot := .lineComment }
    else if c == '/' && rest.head? == some '-' then { s with spot := .blockComment, depth := 1 }
    else if c == '"' then openString s before []
    else if c == '\'' then
      -- A prime continues an identifier.  A quote opens a character
      -- literal only after a character that cannot end an identifier.
      match before.head? with
      | some (previous, _) => if isIdentChar previous then s else { s with spot := .char }
      | none => { s with spot := .char }
    else s

/-- The lines of a file, each character tagged with its region.
    A block comment and a string literal both continue over a line break. -/
partial def scanLines (chars : List Char) : List ScannedLine :=
  let rec go (cs : List Char) (s : ScanState) (line : ScannedLine)
      (acc : List ScannedLine) : List ScannedLine :=
    match cs with
    | [] => (line.reverse :: acc).reverse
    | c :: rest =>
      if c == '\n' then
        -- A line comment ends at the line break.  A block comment and a
        -- string literal continue, so their state carries over.
        let s' := if s.spot == .lineComment then { s with spot := .code } else s
        go rest s' [] (line.reverse :: acc)
      else
        let s' := step s c rest line
        -- The brace that opens an interpolation belongs to the term.
        let here := if s.spot == .str && s'.spot == .interp then Spot.interp else s.spot
        go rest s' ((c, here) :: line) acc
  go chars {} [] []

end Shoumei.Lint
