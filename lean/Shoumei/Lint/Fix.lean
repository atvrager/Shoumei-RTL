/-
  Shoumei.Lint.Fix - the reflow fixer for LEAN006.

  `lean_lint --fix` calls this module.  It splits every line longer than the
  column limit and rewrites the file in place.

  The split point comes from the scanner in `Shoumei.Lint.Scan`, so the fixer
  never breaks a token:

  - code: a space is a split point, and the continuation is indented two spaces
  - a string literal or an interpolation term: no split point, because a
    break would change the value
  - a character literal: no split point
  - a line comment: a split point, and the continuation repeats the marker
  - a block comment: a split point, and the continuation is indented

  The fixer leaves a line alone when the scan of it can be wrong: the line
  starts inside a literal, or a plain literal on it holds a brace.

  A line with no split point stays as it is.  The linter reports it, and the
  marker `lean-lint: ignore` is the escape for such a line.
-/
import Shoumei.Lint.Scan
import Shoumei.Lint.Style

namespace Shoumei.Lint.Fix

/-- The leading whitespace of a line. -/
def indentation (line : String) : String :=
  String.ofList (line.toList.takeWhile (fun c => c == ' '))

/-- True at a character where a line break keeps the meaning of the code. -/
def splittable (spot : Spot) : Bool :=
  spot == .code || spot == .lineComment || spot == .blockComment

/-- The last index before `limit` at which the scanner allows a split.
    The index must sit after the leading indentation, so a cut never lands in
    the indentation itself.  Zero means the line holds no split point. -/
def lastSplit (limit indentLen : Nat) (line : ScannedLine) : Nat :=
  let rec go (idx : Nat) (width : Nat) (best : Nat) (rest : ScannedLine) : Nat :=
    match rest with
    | [] => best
    | (c, spot) :: tail =>
      if width > limit then
        best
      else
        -- `width` is the width of the first `idx` characters, so a cut here
        -- leaves a head that fits the limit.
        let usable := idx > indentLen && c == ' ' && splittable spot
        go (idx + 1) (width + (String.ofList [c]).length) (if usable then idx else best) tail
  go 0 0 0 line

/-- True when the fixer must leave a line as it is.  The scan of such a
    line can be wrong:
    - The line starts inside a literal that an earlier line opened.
    - A plain literal on the line holds a brace.  It can be an interpolated
      string that the scanner does not know, for example
      `throwErrorAt ref "{x}"`. -/
def unsafeLine (line : ScannedLine) : Bool :=
  let startsInLiteral := match line.head? with
    | some (_, spot) => spot == .str || spot == .interp
    | none => false
  let braceInLiteral := line.any (fun (c, spot) => spot == .str && (c == '{' || c == '}'))
  startsInLiteral || braceInLiteral

/-- Split one long line into pieces that fit the limit.
    A line with no split point comes back unchanged.  `fuel` bounds the
    recursion, so a line that resists the split cannot spin. -/
partial def splitLine (limit : Nat) (fuel : Nat) (line : ScannedLine) : List ScannedLine :=
  if (textOf line).length <= limit || fuel == 0 then
    [line]
  else
    let indentLen := (indentation (textOf line)).length
    let cut := lastSplit limit indentLen line
    if cut == 0 then
      [line]
    else
      let headText := dropTrailing (textOf (line.take cut)) (fun c => c == ' ')
      -- The tail keeps the state of every character, so a later split cannot
      -- land inside a string literal.
      let tailChars := (line.drop (cut + 1)).dropWhile (fun (c, _) => c == ' ')
      let indent := indentation (textOf line) ++ "  "
      let inComment := (line.drop cut).head?.map Prod.snd == some .lineComment
      let indentPrefix := if inComment then indent ++ "-- " else indent
      let indentPrefixSpot := if inComment then Spot.lineComment else Spot.code
      let rest := indentPrefix.toList.map (fun c => (c, indentPrefixSpot)) ++ tailChars
      (headText.toList.map (fun c => (c, Spot.code))) :: splitLine limit (fuel - 1) rest

/-- Reflow a file.  Returns the new text and the count of lines that stayed
    over the limit because the line holds no split point. -/
def fixText (limit : Nat) (text : String) : String × Nat :=
  let lines := scanLines text.toList
  let fixed := lines.map (fun l => if unsafeLine l then [l] else splitLine limit 64 l)
  let overLimit (l : ScannedLine) : Bool := (textOf l).length > limit
  let unfixable := fixed.foldl
    (fun count pieces => count + (pieces.filter overLimit).length)
    0
  let joined := fixed.map (fun pieces => String.intercalate "\n" (pieces.map textOf))
  (String.intercalate "\n" joined, unfixable)

/-- The `.lean` files under the given roots.  The scan reports and skips a
    missing root. -/
def leanFilesOf (roots : List System.FilePath) : IO (List System.FilePath) := do
  let mut all := []
  for root in roots do
    if (← root.isDir) then
      all := all ++ (← findLeanFiles root)
    else if (← root.pathExists) then
      all := all.concat root
    else
      IO.eprintln s!"lean-lint: no such path: {root}"
  return all

/-- Reflow every `.lean` file under the given roots.  Returns the count of
    rewritten files and the count of lines that stayed over the limit. -/
def fixRoots (roots : List System.FilePath) : IO (Nat × Nat) := do
  let mut changed := 0
  let mut unfixable := 0
  for file in ← leanFilesOf roots do
    let text ← IO.FS.readFile file
    let (newText, unf) := fixText columnLimit text
    unfixable := unfixable + unf
    if newText != text then
      IO.FS.writeFile file newText
      changed := changed + 1
  return (changed, unfixable)

/-- Print the reflowed text of every `.lean` file under the roots, and write
    nothing.  A preview of `--fix`. -/
def printRoots (roots : List System.FilePath) : IO Unit := do
  for file in ← leanFilesOf roots do
    IO.print (fixText columnLimit (← IO.FS.readFile file)).1

end Shoumei.Lint.Fix
