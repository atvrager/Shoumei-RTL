/-
ProjectMapMain.lean - Standalone CLI for generating docs/project-map.md.
-/

import Shoumei.Codegen.ProjectMap

def parseArg (pfx : String) (args : List String) : Option String :=
  args.findSome? (fun a =>
    if a.startsWith pfx then some (a.drop pfx.length).toString else none)

def main (args : List String) : IO Unit := do
  if let some workspace ← IO.getEnv "BUILD_WORKSPACE_DIRECTORY" then
    IO.Process.setCurrentDir workspace
  let outPath := parseArg "--out=" args
    |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "docs/project-map.md")
  let rc ← Shoumei.Codegen.ProjectMap.generate outPath
  if rc != 0 then IO.Process.exit rc.toUInt8
