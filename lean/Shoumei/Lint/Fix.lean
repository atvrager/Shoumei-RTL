/-
  Shoumei.Lint.Fix - the reflow fixer for LEAN006.

  `lean_lint --fix` calls this module.  It splits every line longer than the
  column limit and rewrites the file in place.

  The split point comes from a scanner that tracks five states, so the fixer
  never breaks a token:

  - code: a space is a split point, and the continuation is indented two spaces
  - a string literal: no split point, because a break would change the value
  - a character literal: no split point
  - a line comment: a split point, and the continuation repeats the marker
  - a block comment: a split point, and the continuation is indented

  A line with no split point stays as it is.  The linter reports it, and the
  marker `lean-lint: ignore` is the escape for such a line.
-/
import Shoumei.Lint.Scan
import Shoumei.Lint.Style

namespace Shoumei.Lint.Fix

/-- The leading whitespace of a line. -/
def indentation (line : String) : String :=
  String.ofList (line.toList.takeWhile (fun c => c == ' '))

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
        let usable := idx > indentLen && c == ' ' && spot != .str && spot != .char
        go (idx + 1) (width + (String.ofList [c]).length) (if usable then idx else best) tail
  go 0 0 0 line

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
  let fixed := lines.map (splitLine limit 64)
  let overLimit (l : ScannedLine) : Bool := (textOf l).length > limit
  let unfixable := fixed.foldl
    (fun count pieces => count + (pieces.filter overLimit).length)
    0
  let joined := fixed.map (fun pieces => String.intercalate "\n" (pieces.map textOf))
  (String.intercalate "\n" joined, unfixable)

/-- Reflow every `.lean` file under the given roots.  Returns the count of
    rewritten files and the count of lines that stayed over the limit. -/
def fixRoots (roots : List System.FilePath) : IO (Nat × Nat) := do
  let mut changed := 0
  let mut unfixable := 0
  for root in roots do
    let files ←
      if (← root.isDir) then
        findLeanFiles root
      else if (← root.pathExists) then
        pure [root]
      else do
        IO.eprintln s!"lean-lint: no such path: {root}"
        pure []
    for file in files do
      let text ← IO.FS.readFile file
      let (newText, unf) := fixText columnLimit text
      unfixable := unfixable + unf
      if newText != text then
        IO.FS.writeFile file newText
        changed := changed + 1
  return (changed, unfixable)

end Shoumei.Lint.Fix
