/-
GenerateSystemC.lean - SystemC Code Generation Entry Point

Generates SystemC (.h and .cpp) files for all Shoumei RTL circuits.
Output directory: output/systemc/
-/

import Shoumei.Examples.Adder
import Shoumei.Examples.QueueExample
import Shoumei.Circuits.Combinational.RippleCarryAdder
import Shoumei.Circuits.Combinational.Subtractor
import Shoumei.Circuits.Combinational.Comparator
import Shoumei.Circuits.Combinational.LogicUnit
import Shoumei.Circuits.Combinational.Shifter
import Shoumei.Circuits.Combinational.ALU
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Combinational.MuxTree
import Shoumei.Circuits.Sequential.DFF
import Shoumei.Circuits.Sequential.Register
import Shoumei.Circuits.Sequential.Queue
import Shoumei.Codegen.SystemC

open Shoumei.Examples
open Shoumei.Circuits.Combinational
open Shoumei.Circuits.Sequential
open Shoumei.Codegen.SystemC

-- Helper: Write SystemC .h and .cpp files for a circuit
def writeSystemCFiles (c : Circuit) : IO Unit := do
  let header := toSystemCHeader c
  let impl := toSystemCImpl c

  let hPath := s!"output/systemc/{c.name}.h"
  let cppPath := s!"output/systemc/{c.name}.cpp"

  IO.FS.writeFile hPath header
  IO.FS.writeFile cppPath impl
  IO.println s!"✓ Generated: {c.name}.h / {c.name}.cpp"

-- Phase 0: Foundation circuits
def generateFoundation : IO Unit := do
  IO.println "==> Phase 0: Foundation Circuits"
  IO.println ""
  writeSystemCFiles fullAdderCircuit
  writeSystemCFiles dff

-- Phase 0b: Queue variants
def generateQueues : IO Unit := do
  IO.println "==> Phase 0b: Queue Variants"
  IO.println ""
  writeSystemCFiles (mkQueue1StructuralComplete 8)
  writeSystemCFiles (mkQueue1StructuralComplete 32)

-- Phase 0c: Register variants
def generateRegisters : IO Unit := do
  IO.println "==> Phase 0c: Register Variants"
  IO.println ""
  writeSystemCFiles mkRegister8
  writeSystemCFiles mkRegister32

-- Phase 1: Ripple Carry Adders
def generateRippleCarryAdders : IO Unit := do
  IO.println "==> Phase 1a: Ripple Carry Adders"
  IO.println ""
  writeSystemCFiles mkRippleCarryAdder4
  writeSystemCFiles mkRippleCarryAdder8
  writeSystemCFiles mkRippleCarryAdder32

-- Phase 1: Subtractors
def generateSubtractors : IO Unit := do
  IO.println "==> Phase 1b: Subtractors"
  IO.println ""
  writeSystemCFiles mkSubtractor4
  writeSystemCFiles mkSubtractor8
  writeSystemCFiles mkSubtractor32

-- Phase 1: Comparators
def generateComparators : IO Unit := do
  IO.println "==> Phase 1c: Comparators"
  IO.println ""
  writeSystemCFiles mkComparator4
  writeSystemCFiles mkComparator8
  writeSystemCFiles mkComparator32

-- Phase 1: Logic Units
def generateLogicUnits : IO Unit := do
  IO.println "==> Phase 1d: Logic Units"
  IO.println ""
  writeSystemCFiles mkLogicUnit4
  writeSystemCFiles mkLogicUnit8
  writeSystemCFiles mkLogicUnit32

-- Phase 1: Shifters
def generateShifters : IO Unit := do
  IO.println "==> Phase 1e: Shifters"
  IO.println ""
  writeSystemCFiles mkShifter4
  writeSystemCFiles mkShifter32

-- Phase 1: ALUs
def generateALUs : IO Unit := do
  IO.println "==> Phase 1f: ALU"
  IO.println ""
  writeSystemCFiles mkALU32

-- Phase 2: Decoders
def generateDecoders : IO Unit := do
  IO.println "==> Phase 2: Binary Decoders"
  IO.println ""
  writeSystemCFiles mkDecoder2
  writeSystemCFiles mkDecoder3
  writeSystemCFiles mkDecoder5

-- Phase 3: MuxTree variants
def generateMuxTrees : IO Unit := do
  IO.println "==> Phase 3: MuxTree Variants"
  IO.println ""
  writeSystemCFiles mkMux2x8
  writeSystemCFiles mkMux4x8
  writeSystemCFiles mkMux32x6
  writeSystemCFiles mkMux64x32

-- Main entry point
def main : IO Unit := do
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  証明 Shoumei RTL - SystemC Generation"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""

  -- Create output directory if it doesn't exist
  IO.FS.createDirAll "output/systemc"

  -- Generate all circuits
  generateFoundation
  IO.println ""
  generateQueues
  IO.println ""
  generateRegisters
  IO.println ""
  generateRippleCarryAdders
  IO.println ""
  generateSubtractors
  IO.println ""
  generateComparators
  IO.println ""
  generateLogicUnits
  IO.println ""
  generateShifters
  IO.println ""
  generateALUs
  IO.println ""
  generateDecoders
  IO.println ""
  generateMuxTrees

  IO.println ""
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "✓ SystemC code generation complete"
  IO.println "  Output: output/systemc/*.h, *.cpp"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
