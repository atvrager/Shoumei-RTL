/-
Main.lean - Code Generation Entry Point

This is the main entry point for the codegen executable.
It calls the code generation functions from Examples.
-/

import Shoumei.Examples.Adder
import Shoumei.Examples.QueueExample

-- Main code generation entry point
-- Generates FullAdder, DFlipFlop, and structural Queue modules
def main : IO Unit := do
  -- Generate combinational circuits (FullAdder) and sequential circuits (DFlipFlop)
  Shoumei.Examples.main
  IO.println ""
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""
  -- Generate structural Queue from DFFs
  Shoumei.Examples.queueMain
