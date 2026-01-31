/-
Main.lean - Code Generation Entry Point

This is the main entry point for the codegen executable.
It calls the code generation functions from Examples and Circuits.
-/

import Shoumei.Examples.Adder
import Shoumei.Examples.QueueExample
import Shoumei.Circuits.Combinational.RippleCarryAdderCodegen
import Shoumei.Circuits.Combinational.SubtractorCodegen
import Shoumei.Circuits.Combinational.ComparatorCodegen
import Shoumei.Circuits.Combinational.LogicUnitCodegen

-- Main code generation entry point
-- Generates FullAdder, DFlipFlop, Queue, and RippleCarryAdder modules
def main : IO Unit := do
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  証明 Shoumei RTL - Code Generation"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""

  -- Phase 0: Basic circuits
  IO.println "==> Phase 0: Foundation Circuits"
  IO.println ""
  Shoumei.Examples.main
  IO.println ""
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""
  Shoumei.Examples.queueMain

  -- Phase 1: Arithmetic circuits
  IO.println ""
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""
  IO.println "==> Phase 1: Arithmetic Building Blocks"
  IO.println ""
  Shoumei.Circuits.Combinational.generateRippleCarryAdders
  IO.println ""
  Shoumei.Circuits.Combinational.generateSubtractors
  IO.println ""
  Shoumei.Circuits.Combinational.generateComparators
  IO.println ""
  Shoumei.Circuits.Combinational.generateLogicUnits
