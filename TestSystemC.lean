/-
TestSystemC.lean - Quick test for SystemC code generation

Generates SystemC code for FullAdder and DFlipFlop to verify the generator works.
-/

import Shoumei.Examples.Adder
import Shoumei.Circuits.Sequential.DFF
import Shoumei.Codegen.SystemC

open Shoumei.Examples
open Shoumei.Circuits.Sequential
open Shoumei.Codegen.SystemC

def main : IO Unit := do
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  SystemC Code Generation Test"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  -- Test 1: FullAdder (combinational)
  IO.println "\n==> Generating FullAdder (combinational)"
  let faHeader := toSystemCHeader fullAdderCircuit
  let faImpl := toSystemCImpl fullAdderCircuit

  IO.println "--- FullAdder.h ---"
  IO.println faHeader
  IO.println "\n--- FullAdder.cpp ---"
  IO.println faImpl

  -- Test 2: DFlipFlop (sequential)
  IO.println "\n==> Generating DFlipFlop (sequential)"
  let dffHeader := toSystemCHeader dff
  let dffImpl := toSystemCImpl dff

  IO.println "--- DFlipFlop.h ---"
  IO.println dffHeader
  IO.println "\n--- DFlipFlop.cpp ---"
  IO.println dffImpl

  IO.println "\n✓ SystemC generation test complete"
