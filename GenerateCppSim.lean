/-
GenerateCppSim.lean - C++ Simulation Code Generation Entry Point

Generates C++ simulation (.h and .cpp) files for all Shoumei RTL circuits.
Output directory: output/cpp_sim/
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
import Shoumei.Circuits.Sequential.QueueN
import Shoumei.Circuits.Sequential.QueueComponents
import Shoumei.RISCV.Renaming.RAT
import Shoumei.RISCV.Renaming.FreeList
import Shoumei.RISCV.Renaming.PhysRegFile
import Shoumei.Codegen.CppSim

open Shoumei.Examples
open Shoumei.Circuits.Combinational
open Shoumei.Circuits.Sequential
open Shoumei.RISCV.Renaming
open Shoumei.Codegen.CppSim

-- Helper: Write C++ simulation .h and .cpp files for a circuit
def writeCppSimFiles (c : Circuit) : IO Unit := do
  let header := toCppSimHeader c
  let impl := toCppSimImpl c

  let hPath := s!"output/cpp_sim/{c.name}.h"
  let cppPath := s!"output/cpp_sim/{c.name}.cpp"

  IO.FS.writeFile hPath header
  IO.FS.writeFile cppPath impl
  IO.println s!"✓ Generated: {c.name}.h / {c.name}.cpp"

-- Phase 0: Foundation circuits
def generateFoundation : IO Unit := do
  IO.println "==> Phase 0: Foundation Circuits"
  IO.println ""
  writeCppSimFiles fullAdderCircuit
  writeCppSimFiles dff

-- Phase 0b: Queue variants
def generateQueues : IO Unit := do
  IO.println "==> Phase 0b: Queue Variants"
  IO.println ""
  writeCppSimFiles (mkQueue1StructuralComplete 8)
  writeCppSimFiles (mkQueue1StructuralComplete 32)

-- Phase 0c: Register variants
def generateRegisters : IO Unit := do
  IO.println "==> Phase 0c: Register Variants"
  IO.println ""
  writeCppSimFiles mkRegister8
  writeCppSimFiles mkRegister32

-- Phase 1: Ripple Carry Adders
def generateRippleCarryAdders : IO Unit := do
  IO.println "==> Phase 1a: Ripple Carry Adders"
  IO.println ""
  writeCppSimFiles mkRippleCarryAdder4
  writeCppSimFiles mkRippleCarryAdder8
  writeCppSimFiles mkRippleCarryAdder32

-- Phase 1: Subtractors
def generateSubtractors : IO Unit := do
  IO.println "==> Phase 1b: Subtractors"
  IO.println ""
  writeCppSimFiles mkSubtractor4
  writeCppSimFiles mkSubtractor8
  writeCppSimFiles mkSubtractor32

-- Phase 1: Comparators
def generateComparators : IO Unit := do
  IO.println "==> Phase 1c: Comparators"
  IO.println ""
  writeCppSimFiles mkComparator4
  writeCppSimFiles mkComparator8
  writeCppSimFiles mkComparator32

-- Phase 1: Logic Units
def generateLogicUnits : IO Unit := do
  IO.println "==> Phase 1d: Logic Units"
  IO.println ""
  writeCppSimFiles mkLogicUnit4
  writeCppSimFiles mkLogicUnit8
  writeCppSimFiles mkLogicUnit32

-- Phase 1: Shifters
def generateShifters : IO Unit := do
  IO.println "==> Phase 1e: Shifters"
  IO.println ""
  writeCppSimFiles mkShifter4
  writeCppSimFiles mkShifter32

-- Phase 1: ALUs
def generateALUs : IO Unit := do
  IO.println "==> Phase 1f: ALU"
  IO.println ""
  writeCppSimFiles mkALU32

-- Phase 2: Decoders
def generateDecoders : IO Unit := do
  IO.println "==> Phase 2: Binary Decoders"
  IO.println ""
  writeCppSimFiles mkDecoder2
  writeCppSimFiles mkDecoder3
  writeCppSimFiles mkDecoder5

-- Phase 3: MuxTree variants
def generateMuxTrees : IO Unit := do
  IO.println "==> Phase 3: MuxTree Variants"
  IO.println ""
  writeCppSimFiles mkMux2x8
  writeCppSimFiles mkMux4x8
  writeCppSimFiles mkMux32x6
  writeCppSimFiles mkMux64x32
  writeCppSimFiles (mkMuxTree 64 6)

-- Phase 4: QueueN variants (parametric queues)
def generateQueueNVariants : IO Unit := do
  IO.println "==> Phase 4: QueueN Variants"
  IO.println ""
  -- Queue2_8
  writeCppSimFiles (mkQueueNStructural 2 8)
  writeCppSimFiles (mkQueueRAM 2 8)
  writeCppSimFiles (mkQueuePointer 1)
  writeCppSimFiles (mkQueueCounterUpDown 2)
  -- Queue4_8
  writeCppSimFiles (mkQueueNStructural 4 8)
  writeCppSimFiles (mkQueueRAM 4 8)
  writeCppSimFiles (mkQueuePointer 2)
  writeCppSimFiles (mkQueueCounterUpDown 3)
  -- Queue64_32
  writeCppSimFiles (mkQueueNStructural 64 32)
  writeCppSimFiles (mkQueueRAM 64 32)
  -- Queue64_6
  writeCppSimFiles (mkQueueNStructural 64 6)
  writeCppSimFiles (mkQueueRAM 64 6)
  -- Shared submodules for depth-64 queues
  writeCppSimFiles (mkQueuePointer 6)
  writeCppSimFiles (mkQueueCounterUpDown 7)
  writeCppSimFiles (mkDecoder 6)

-- Phase 5: RAT (Register Alias Table)
def generateRAT : IO Unit := do
  IO.println "==> Phase 5: RAT (Register Alias Table)"
  IO.println ""
  writeCppSimFiles mkRAT64

-- Phase 6: FreeList
def generateFreeList : IO Unit := do
  IO.println "==> Phase 6: FreeList (Free Physical Register List)"
  IO.println ""
  writeCppSimFiles mkFreeList64

-- Phase 7: PhysRegFile
def generatePhysRegFile : IO Unit := do
  IO.println "==> Phase 7: PhysRegFile (Physical Register File)"
  IO.println ""
  writeCppSimFiles mkPhysRegFile64

-- Main entry point
def main : IO Unit := do
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  証明 Shoumei RTL - C++ Simulation Generation"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""

  -- Create output directory if it doesn't exist
  IO.FS.createDirAll "output/cpp_sim"

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
  generateQueueNVariants
  IO.println ""
  generateRAT
  IO.println ""
  generateFreeList
  IO.println ""
  generatePhysRegFile

  IO.println ""
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "✓ C++ simulation code generation complete"
  IO.println "  Output: output/cpp_sim/*.h, *.cpp"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
