/-
  Shoumei.Lint.Style - a style linter for the Lean sources.

  The linter reads each file as text and settles the rules that a mechanical
  check can decide:

  LEAN001  `sorry` or `admit` in the code          error
  LEAN002  an `axiom` or `constant` declaration    error
  LEAN003  a `#eval`, `#check`, `#print` or `#reduce` debug command  error
  LEAN004  trailing whitespace                     error
  LEAN005  a tab character                         error
  LEAN006  a line whose code is longer than the column limit  error

  The scanner blanks comments and string literals before the code rules run, so
  a banned word inside a comment does not count.  A blanked line keeps its
  length and its newline, so a reported line number is the file's line.

  A line that carries the marker `lean-lint: ignore` is skipped.  Use it for
  text that a rule cannot split, such as a long string literal.

  One finding prints as:

      file:line:col: severity: message [RULE]

  The exit status is 1 when an error is reported.
-/

import Shoumei.Lint.Scan

namespace Shoumei.Lint

/-- One reported problem. -/
structure Finding where
  file : String
  line : Nat
  col : Nat
  /-- True for a rule that fails the run. -/
  fatal : Bool
  rule : String
  message : String

/-- Drop trailing characters that satisfy the test. -/
def dropTrailing (s : String) (test : Char → Bool) : String :=
  String.ofList (s.toList.reverse.dropWhile test |>.reverse)

/-- The lines of a file, without a trailing carriage return. -/
def splitLines (text : String) : List String :=
  (text.splitOn "\n").map (fun s => dropTrailing s (fun c => c == '\r'))

/-- Replace a character by a space, but keep a newline.
    The line structure of the file survives the blanking. -/
def blank (c : Char) : Char :=
  if c == '\n' then '\n' else ' '

/--
Blank every comment and string literal.

The scan keeps one of six states: code, a line comment, a block comment of any
nesting depth, a string literal, or a character literal.  Inside a comment or a
literal every character becomes a space, except a newline, which stays.
-/
partial def blankNonCode (chars : List Char) : List Char :=
  let rec go (cs : List Char) (depth : Nat) (state : Nat) (acc : List Char) : List Char :=
    match cs with
    | [] => acc.reverse
    | c :: rest =>
      match state with
      | 1 =>
        if c == '\\' then
          match rest with
          | _ :: rest' => go rest' depth 1 (blank c :: acc)
          | [] => acc.reverse
        else if c == '"' then go rest depth 0 (blank c :: acc)
        else go rest depth 1 (blank c :: acc)
      | 2 =>
        if c == '\\' then
          match rest with
          | _ :: rest' => go rest' depth 2 (blank c :: acc)
          | [] => acc.reverse
        else if c == '\'' then go rest depth 0 (blank c :: acc)
        else go rest depth 2 (blank c :: acc)
      | 3 =>
        if c == '\n' then go rest depth 0 (c :: acc) else go rest depth 3 (blank c :: acc)
      | _ =>
        if depth > 0 then
          -- A block comment.  An opener deepens it and a closer ends one level.
          if c == '/' && rest.head? == some '-' then
            go rest (depth + 1) 0 (blank c :: acc)
          else if c == '-' && rest.head? == some '/' then
            go rest (depth - 1) 0 (blank c :: acc)
          else
            go rest depth 0 (blank c :: acc)
        else if c == '-' && rest.head? == some '-' then
          go rest depth 3 (blank c :: acc)
        else if c == '/' && rest.head? == some '-' then
          go rest.tail! 1 0 (blank c :: acc)
        else if c == '"' then go rest depth 1 (blank c :: acc)
        else if c == '\'' then go rest depth 2 (blank c :: acc)
        else go rest depth 0 (c :: acc)
  go chars 0 0 []

/-- Blank the comments and the string literals of a file. -/
def stripNonCode (text : String) : List String :=
  splitLines (String.ofList (blankNonCode text.toList))

/-- The column of a whole word in a line, or 0 when the line holds no such word. -/
def findWord (line : String) (word : String) : Nat :=
  let chars := line.toList
  let target := word.toList
  let rec scanFrom (pos : Nat) (rest : List Char) : Nat :=
    match rest with
    | [] => 0
    | c :: tail =>
      if c == target.head! && target.isPrefixOf (c :: tail) then
        let before := if pos == 0 then none else chars[pos - 1]?
        let after := ((c :: tail).drop target.length).head?
        if before.all (fun b => !isIdentChar b) && after.all (fun a => !isIdentChar a) then
          pos + 1
        else
          scanFrom (pos + 1) tail
      else
        scanFrom (pos + 1) tail
  scanFrom 0 chars

/-- Drop leading spaces. -/
def dropSpaces (s : String) : String :=
  (s.dropWhile (fun c => c == ' ')).toString

/-- Drop one optional keyword from the head of a declaration line. -/
def dropKeyword (keyword : String) (s : String) : String :=
  if s.startsWith (keyword ++ " ") then
    dropSpaces (s.drop (keyword.length + 1)).toString
  else
    s

/-- True when the text starts with a keyword, and not with a longer
    identifier that begins the same way. -/
def startsWithKeyword (text : String) (keyword : String) : Bool :=
  text.startsWith keyword && !isIdentChar ((text.drop keyword.length).toString.toList.headD ' ')

/-- True when the line declares an axiom or a constant. -/
def declaresAxiom (line : String) : Bool :=
  let t := dropKeyword "unsafe" (dropKeyword "noncomputable"
    (dropKeyword "protected" (dropKeyword "private" (dropSpaces line))))
  startsWithKeyword t "axiom" || startsWithKeyword t "constant"

/-- True when the line holds a debugging command. -/
def isDebugCommand (line : String) : Bool :=
  let t := dropSpaces line
  ["#eval", "#check", "#print", "#reduce"].any (fun name =>
    t.startsWith name && !isIdentChar ((t.drop name.length).toString.toList.headD ' '))

/-- The first column of a character that satisfies the test, or 0. -/
def firstColumn (line : String) (test : Char → Bool) : Nat :=
  let rec go (pos : Nat) (cs : List Char) : Nat :=
    match cs with
    | [] => 0
    | c :: rest => if test c then pos + 1 else go (pos + 1) rest
  go 0 line.toList

/-- The column limit of LEAN006. -/
def columnLimit : Nat := 100

/-- A line with this marker is skipped. -/
def ignoreMarker : String := "lean-lint: ignore"

/-- Lint one file.  `text` is the file content, `path` its display name. -/
def lintText (path : String) (text : String) : List Finding := Id.run do
  let rawLines := splitLines text
  let codeLines := stripNonCode text
  let scanned := scanLines text.toList
  let add (out : List Finding) (lineno col : Nat) (fatal : Bool)
      (rule message : String) : List Finding :=
    out.concat
      { file := path, line := lineno, col := col, fatal := fatal, rule := rule
        message := message }
  let mut out : List Finding := []
  let mut lineno := 0
  for raw in rawLines do
    lineno := lineno + 1
    if raw.contains ignoreMarker then
      continue
    let code := codeLines.getD (lineno - 1) ""
    -- LEAN004: trailing whitespace.
    let trimmed := dropTrailing raw (fun c => c == ' ' || c == '\t')
    if trimmed.length != raw.length then
      out := add out lineno (trimmed.length + 1) true "LEAN004" "trailing whitespace"
    -- LEAN005: tab character.
    let tabCol := firstColumn raw (fun c => c == '\t')
    if tabCol != 0 then
      out := add out lineno tabCol true "LEAN005" "tab character"
    -- LEAN001, LEAN002 and LEAN003 read the blanked line.
    let sorryCol := max (findWord code "sorry") (findWord code "admit")
    if sorryCol != 0 then
      out := add out lineno sorryCol true "LEAN001" "`sorry` or `admit` in the code"
    if declaresAxiom code then
      out := add out lineno 1 true "LEAN002" "axiom or constant declaration"
    if isDebugCommand code then
      out := add out lineno 1 true "LEAN003" "debugging command left in the source"
    -- LEAN006: the code on the line is wider than the limit.  The interior of
    -- a string literal does not count, because a break in it would change the
    -- value.
    let width := codeWidth (scanned.getD (lineno - 1) [])
    if width > columnLimit then
      out := add out lineno (columnLimit + 1) true "LEAN006"
        s!"line holds {width} columns of code, over the limit of {columnLimit}"
  return out

/-- Every `.lean` file under a directory. -/
partial def findLeanFiles (dir : System.FilePath) : IO (List System.FilePath) := do
  let mut results : List System.FilePath := []
  for entry in ← dir.readDir do
    let path := entry.path
    if (← path.isDir) then
      results := results ++ (← findLeanFiles path)
    else if path.extension == some "lean" then
      results := results.concat path
  return results

/-- Lint one file on disk. -/
def lintFile (path : System.FilePath) : IO (List Finding) := do
  let text ← IO.FS.readFile path
  return lintText path.toString text

/-- Lint every `.lean` file under the given roots. -/
def lintRoots (roots : List System.FilePath) : IO (List Finding) := do
  let mut out : List Finding := []
  for root in roots do
    if (← root.isDir) then
      for file in ← findLeanFiles root do
        out := out ++ (← lintFile file)
    else if (← root.pathExists) then
      out := out ++ (← lintFile root)
    else
      IO.eprintln s!"lean-lint: no such path: {root}"
  return out

end Shoumei.Lint
