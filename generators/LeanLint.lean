/-
  LeanLint - run the style linter over the Lean sources.

  Usage: lean_lint [--fix] [--update-baseline] [--baseline FILE] [--warn-limit N] [path...]

  The default paths are `lean` and `generators`.  The other rules fail the run
  on any finding.  The line-width rule (LEAN006) is a ratchet: a file may hold
  no more over-length lines than the baseline file records, and the count may
  only fall.  `--fix` reflows the long lines, and `--update-baseline` records
  the result.
-/
import Shoumei.Lint.Fix
import Shoumei.Lint.Style

open Shoumei.Lint

/-- The command line summary. -/
def usage : String := "usage: lean_lint [--fix] [--update-baseline] [--baseline FILE] [--warn-limit N] [path...]"

/-- The default baseline file. -/
def baselineFile : String := "lean-lint-baseline.txt"

/-- Sort the findings by file, line and column. -/
def sortFindings (findings : List Finding) : Array Finding :=
  findings.toArray.qsort (fun a b =>
    a.file < b.file ||
      (a.file == b.file && (a.line < b.line || (a.line == b.line && a.col < b.col))))

/-- Parse a baseline file.  Each line reads `count path`. -/
def parseBaseline (text : String) : List (String × Nat) :=
  (text.splitOn "\n").filterMap fun line =>
    let trimmed := (line.dropWhile (fun c => c == ' ')).toString
    match trimmed.splitOn " " with
    | count :: path :: _ =>
      match count.toNat? with
      | some n => some (path, n)
      | none => none
    | _ => none

/-- The count a baseline records for one file.  A missing entry allows 0. -/
def recordedCount (baseline : List (String × Nat)) (file : String) : Nat :=
  match baseline.find? (fun entry => entry.1 == file) with
  | some entry => entry.2
  | none => 0

/-- Count the findings of one rule per file. -/
def countByFile (rule : String) (findings : Array Finding) : List (String × Nat) :=
  let names := (findings.filter (fun f => f.rule == rule)).map (fun f => f.file)
  names.foldl
    (fun acc name =>
      match acc.find? (fun entry => entry.1 == name) with
      | some (_, n) => acc.map (fun entry => if entry.1 == name then (name, n + 1) else entry)
      | none => acc.concat (name, 1))
    []

/-- The count of over-length lines a run found for one file. -/
def countFor (counts : List (String × Nat)) (file : String) : Nat :=
  match counts.find? (fun entry => entry.1 == file) with
  | some entry => entry.2
  | none => 0

/-- The text of a baseline file, sorted by path. -/
def renderBaseline (counts : List (String × Nat)) : String :=
  let rows := (counts.filter (fun entry => entry.2 > 0)).toArray.qsort (fun a b => a.1 < b.1)
  String.intercalate "\n" (rows.toList.map (fun entry => s!"{entry.2} {entry.1}")) ++ "\n"

def main (args : List String) : IO UInt32 := do
  let mut warnLimit := 10
  let mut roots : List System.FilePath := []
  let mut expectLimit := false
  let mut expectBaseline := false
  let mut fix := false
  let mut updateBaseline := false
  let mut baselinePath := baselineFile
  for arg in args do
    if expectLimit then
      warnLimit := arg.toNat?.getD warnLimit
      expectLimit := false
    else if expectBaseline then
      baselinePath := arg
      expectBaseline := false
    else if arg == "--fix" then
      fix := true
    else if arg == "--update-baseline" then
      updateBaseline := true
    else if arg == "--baseline" then
      expectBaseline := true
    else if arg == "--warn-limit" then
      expectLimit := true
    else if arg == "--help" || arg == "-h" then
      IO.println usage
      IO.println "  LEAN001  sorry or admit in the code"
      IO.println "  LEAN002  axiom or constant declaration"
      IO.println "  LEAN003  debugging command left in the source"
      IO.println "  LEAN004  trailing whitespace"
      IO.println "  LEAN005  tab character"
      IO.println "  LEAN006  line whose code is over 100 columns, against a ratchet baseline"
      return 0
    else
      roots := roots.concat (System.FilePath.mk arg)

  let searchRoots :=
    if roots.isEmpty then [System.FilePath.mk "lean", System.FilePath.mk "generators"]
    else roots

  if fix then
    let (changed, unfixable) ← Fix.fixRoots searchRoots
    IO.println s!"lean-lint: reflowed {changed} file(s), {unfixable} line(s) left alone"

  let findings ← lintRoots searchRoots
  let sorted := sortFindings findings
  let lineCounts := countByFile "LEAN006" sorted
  let baseline : List (String × Nat) ←
    if ← (System.FilePath.mk baselinePath).pathExists then
      pure (parseBaseline (← IO.FS.readFile (System.FilePath.mk baselinePath)))
    else
      pure []

  if updateBaseline then
    IO.FS.writeFile (System.FilePath.mk baselinePath) (renderBaseline lineCounts)
    IO.println s!"lean-lint: wrote {baselinePath}"

  -- The ratchet: a file may not exceed its recorded count.
  let mut errors : List Finding := []
  let mut ratchetPass := true
  for (file, count) in lineCounts do
    let allowed := recordedCount baseline file
    if count > allowed then
      ratchetPass := false
      errors := errors.concat
        { file := file, line := 0, col := 1, fatal := true, rule := "LEAN006"
          message := s!"{count} over-length lines, the baseline allows {allowed}" }
  for f in sorted do
    if f.rule != "LEAN006" then
      errors := errors.concat f
  for f in errors do
    IO.println s!"{f.file}:{f.line}:{f.col}: error: {f.message} [{f.rule}]"

  let over := (lineCounts.filter (fun entry => entry.2 > 0)).length
  let loose := baseline.filter (fun entry => countFor lineCounts entry.1 < entry.2) |>.length

  IO.println s!"lean-lint: {errors.length} error(s), {over} file(s) with over-length lines, {loose} baseline entr(ies) ready to shrink"
  return if errors.isEmpty then 0 else 1
