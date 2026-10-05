/-
LeanRootMain.lean - Standalone CLI for generating and checking lean/Shoumei/All.lean.
-/

import Shoumei.Codegen.LeanRoot

def main (args : List String) : IO Unit := do
  if let some workspace ← IO.getEnv "BUILD_WORKSPACE_DIRECTORY" then
    IO.Process.setCurrentDir workspace
  let checkOnly := args.contains "--check-lean-root" || !args.contains "--gen-lean-root"
  let rc ← Shoumei.Codegen.LeanRoot.run (checkOnly := checkOnly)
  if rc != 0 then IO.Process.exit rc.toUInt8
