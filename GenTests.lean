/-
  GenTests.lean - Test Generator Executable

  Generates .S assembly files for all test patterns into testbench/tests/generated/.
  Usage: lake exe gen_tests
-/

import Shoumei.TestGen.Patterns

def main : IO Unit := do
  let outDir := "testbench/tests/generated"
  IO.FS.createDirAll outDir

  let patterns := Shoumei.TestGen.allPatterns
  IO.println s!"Generating {patterns.length} test programs..."

  for prog in patterns do
    let path := s!"{outDir}/{prog.name}.S"
    IO.FS.writeFile path prog.toAsm
    IO.println s!"  {path}"

  IO.println "Done."
