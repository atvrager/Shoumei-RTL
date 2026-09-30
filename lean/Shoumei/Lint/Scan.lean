/-
  Shoumei.Lint.Scan - the shared scanner for the Lean linter and its fixer.

  The scan tags every character with the region it belongs to. A rule can then
  tell code from a comment and from a string literal:

  - code
  - a string literal
  - a character literal
  - a line comment
  - a block comment of any nesting depth

  A block comment and a string literal both continue over a line break, so the
  scan walks the whole file.  A line comment ends at the line break.
-/

namespace Shoumei.Lint

/-- A character that continues a Lean identifier, for a word boundary test. -/
def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\''

/-- The region a character belongs to. -/
inductive Spot where
  | code
  | str
  | char
  | lineComment
  | blockComment
  deriving BEq, Inhabited

/-- One line as characters, each with the region it belongs to. -/
abbrev ScannedLine := List (Char × Spot)

/-- The text of a scanned line. -/
def textOf (line : ScannedLine) : String :=
  String.ofList (line.map Prod.fst)

/-- The width of the part of a line that is not inside a string literal. -/
def codeWidth (line : ScannedLine) : Nat :=
  (line.filter (fun (_, spot) => spot != .str)).length

/-- The lines of a file, each character tagged with its region.
    A block comment and a string literal both continue over a line break. -/
partial def scanLines (chars : List Char) : List ScannedLine :=
  let rec go (cs : List Char) (depth : Nat) (state : Spot) (escape : Bool)
      (line : ScannedLine) (acc : List ScannedLine) : List ScannedLine :=
    match cs with
    | [] => (line.reverse :: acc).reverse
    | c :: rest =>
      if c == '\n' then
        -- A line comment ends at the line break.  A block comment and a
        -- string literal continue, so their state carries over.
        go rest depth (if state == .lineComment then .code else state) escape []
          (line.reverse :: acc)
      else
        let here := state
        let (state', depth', escape') :=
          match state with
          | .str =>
            if escape then (.str, depth, false)
            else if c == '\\' then (.str, depth, true)
            else if c == '"' then (.code, depth, false)
            else (.str, depth, false)
          | .char =>
            if escape then (.char, depth, false)
            else if c == '\\' then (.char, depth, true)
            else if c == '\'' then (.code, depth, false)
            else (.char, depth, false)
          | .lineComment => (.lineComment, depth, false)
          | .blockComment =>
            -- An opener deepens the comment.  A closer ends one level, and the
            -- end of the outermost level returns to code.
            if c == '/' && rest.head? == some '-' then (.blockComment, depth + 1, false)
            else if c == '-' && rest.head? == some '/' then
              (if depth == 1 then .code else .blockComment, depth - 1, false)
            else (.blockComment, depth, false)
          | .code =>
            if c == '-' && rest.head? == some '-' then (.lineComment, depth, false)
            else if c == '/' && rest.head? == some '-' then (.blockComment, 1, false)
            else if c == '"' then (.str, depth, false)
            else if c == '\'' then
              -- A prime continues an identifier.  A quote opens a character
              -- literal only after a character that cannot end an identifier.
              match line.head? with
              | some (previous, _) =>
                if isIdentChar previous then (.code, depth, false) else (.char, depth, false)
              | none => (.char, depth, false)
            else (.code, depth, false)
        go rest depth' state' escape' ((c, here) :: line) acc
  go chars 0 .code false [] []

end Shoumei.Lint
