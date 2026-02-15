/-
TestCppSim.lean - Quick test for C++ simulation code generation

Generates C++ simulation code for FullAdder and DFlipFlop to verify the generator works.
-/

import Shoumei.Examples.Adder
import Shoumei.Circuits.Sequential.DFF
import Shoumei.Codegen.CppSim

open Shoumei.Examples
open Shoumei.Circuits.Sequential
open Shoumei.Codegen.CppSim

def main : IO Unit := do
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  C++ Simulation Code Generation Test"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  -- Test 1: FullAdder (combinational)
  IO.println "\n==> Generating FullAdder (combinational)"
  let faHeader := toCppSimHeader fullAdderCircuit
  let faImpl := toCppSimImpl fullAdderCircuit

  IO.println "--- FullAdder.h ---"
  IO.println faHeader
  IO.println "\n--- FullAdder.cpp ---"
  IO.println faImpl

  -- Test 2: DFlipFlop (sequential)
  IO.println "\n==> Generating DFlipFlop (sequential)"
  let dffHeader := toCppSimHeader dff
  let dffImpl := toCppSimImpl dff

  IO.println "--- DFlipFlop.h ---"
  IO.println dffHeader
  IO.println "\n--- DFlipFlop.cpp ---"
  IO.println dffImpl

  IO.println "\n✓ C++ simulation generation test complete"
