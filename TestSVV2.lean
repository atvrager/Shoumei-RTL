/-
TestSVV2.lean - Test SystemVerilog V2 Code Generation

Quick test to generate SVV2 output for selected circuits to verify
the new hierarchical code generator works correctly.

Usage: lake exe test_svv2
-/

import Shoumei.Codegen.Unified

-- Import some test circuits
import Shoumei.Circuits.Combinational.RippleCarryAdder
import Shoumei.Circuits.Combinational.MuxTree
import Shoumei.Circuits.Sequential.Register
import Shoumei.Circuits.Sequential.QueueComponents

open Shoumei.Codegen.Unified
open Shoumei.Circuits.Combinational
open Shoumei.Circuits.Sequential

-- Test circuits (small selection for quick testing)
def testCircuits : List Circuit := [
  mkRippleCarryAdder32,
  mkMuxTree 4 8,
  mkRegisterN 32,
  mkQueuePointer 6
]

def main : IO Unit := do
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  証明 Shoumei RTL - Test SVV2 Generation"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""

  -- Initialize output directories
  initOutputDirs

  -- Generate SVV2 for test circuits
  let mut count := 0
  for c in testCircuits do
    writeCircuitSVV2 c
    IO.println s!"✓ Generated {c.name}.sv (V2)"
    count := count + 1

  IO.println ""
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println s!"✓ Generated {count} circuits (SVV2)"
  IO.println "  Output: output/sv-from-lean-v2/"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
