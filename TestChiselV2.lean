/-
TestChiselV2.lean - Test Chisel V2 Code Generation

Generates Chisel V2 code for the three circuits annotated in Phase 1:
- Queue1_32 (simple sequential)
- ALU32 (combinational)
- ReservationStation4 (hierarchical sequential)

Usage: lake exe test_chisel_v2
-/

import Shoumei.Codegen.ChiselV2
import Shoumei.Circuits.Sequential.Queue
import Shoumei.Circuits.Combinational.ALU
import Shoumei.RISCV.Execution.ReservationStation

open Shoumei.Codegen.ChiselV2
open Shoumei.Circuits.Sequential
open Shoumei.Circuits.Combinational
open Shoumei.RISCV.Execution

def chiselV2OutputDir : String := "chisel/src/main/scala/generated_v2"

def writeChiselV2 (c : Circuit) : IO Unit := do
  let chisel := toChiselV2 c
  let path := s!"{chiselV2OutputDir}/{c.name}.scala"
  IO.FS.writeFile path chisel
  IO.println s!"✓ Generated {c.name} (V2)"

def main : IO Unit := do
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  Chisel V2 Code Generation Test"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""

  -- Initialize output directory
  IO.FS.createDirAll chiselV2OutputDir

  -- Generate the three annotated circuits
  IO.println "Generating annotated circuits..."
  writeChiselV2 (mkQueue1StructuralComplete 32)
  writeChiselV2 mkALU32
  writeChiselV2 mkReservationStation4

  IO.println ""
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "✓ Generated 3 circuits (Chisel V2)"
  IO.println s!"  Output: {chiselV2OutputDir}/"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
