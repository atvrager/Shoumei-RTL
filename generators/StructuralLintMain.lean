/-
StructuralLintMain.lean - Standalone CLI for SystemVerilog structural linting.
-/

import Shoumei.Verification.StructuralLint

def parseArg (pfx : String) (args : List String) : Option String :=
  args.findSome? (fun a =>
    if a.startsWith pfx then some (a.drop pfx.length).toString else none)

def main (args : List String) : IO Unit := do
  let svDir := parseArg "--sv-dir=" args
    |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "output/sv-from-lean")
  let rc ← Shoumei.Verification.StructuralLint.run svDir
  if rc != 0 then IO.Process.exit rc.toUInt8
