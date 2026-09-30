/-
  LeanLint - run the style linter over the Lean sources.

  Usage: lean_lint [--warn-limit N] [path...]

  The default paths are `lean` and `generators`.  A warning is reported but it
  does not fail the run.  A fatal finding prints and the exit status is 1.
-/
import Shoumei.Lint.Style

open Shoumei.Lint

/-- The command line summary. -/
def usage : String := "usage: lean_lint [--warn-limit N] [path...]"

/-- Sort the findings by file, line and column. -/
def sortFindings (findings : List Finding) : Array Finding :=
  findings.toArray.qsort (fun a b =>
    a.file < b.file ||
      (a.file == b.file && (a.line < b.line || (a.line == b.line && a.col < b.col))))

def main (args : List String) : IO UInt32 := do
  let mut warnLimit := 10
  let mut roots : List System.FilePath := []
  let mut expectLimit := false
  for arg in args do
    if expectLimit then
      warnLimit := arg.toNat?.getD warnLimit
      expectLimit := false
    else if arg == "--warn-limit" then
      expectLimit := true
    else if arg == "--help" || arg == "-h" then
      IO.println usage
      IO.println "  LEAN001  sorry or admit in the code"
      IO.println "  LEAN002  axiom or constant declaration"
      IO.println "  LEAN003  debugging command left in the source"
      IO.println "  LEAN004  trailing whitespace"
      IO.println "  LEAN005  tab character"
      IO.println "  LEAN006  line over 100 columns (warning)"
      return 0
    else
      roots := roots.concat (System.FilePath.mk arg)

  let searchRoots :=
    if roots.isEmpty then [System.FilePath.mk "lean", System.FilePath.mk "generators"]
    else roots

  let findings ← lintRoots searchRoots
  let sorted := sortFindings findings
  let errors := sorted.filter (fun f => f.fatal)
  let warnings := sorted.filter (fun f => !f.fatal)

  for f in errors do
    IO.println s!"{f.file}:{f.line}:{f.col}: error: {f.message} [{f.rule}]"

  let mut shown := 0
  for f in warnings do
    if shown < warnLimit then
      IO.println s!"{f.file}:{f.line}:{f.col}: warning: {f.message} [{f.rule}]"
      shown := shown + 1

  if warnings.size > warnLimit then
    IO.println s!"... {warnings.size - warnLimit} more warning(s)"

  IO.println s!"lean-lint: {sorted.size} finding(s), {errors.size} error(s), {warnings.size} warning(s)"
  return if errors.isEmpty then 0 else 1
