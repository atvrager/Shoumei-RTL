/-
RISCV/Renaming/FreeListCodegen.lean - Code generation for Free List

Generates SystemVerilog and Chisel output for the Free List circuit and its
submodules (QueueRAM, QueuePointer, QueueCounterUpDown, Decoder, MuxTree).
-/

import Shoumei.DSL
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel
import Shoumei.RISCV.Renaming.FreeList
import Shoumei.Circuits.Sequential.QueueComponents
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Combinational.MuxTree

namespace Shoumei.RISCV.Renaming.FreeListCodegen

open Shoumei
open Shoumei.Codegen
open Shoumei.Circuits.Sequential
open Shoumei.Circuits.Combinational
open Shoumei.RISCV.Renaming

def writeCircuit (c : Circuit) : IO Unit := do
  let sv := SystemVerilog.toSystemVerilog c
  let chisel := Chisel.toChisel c

  let svPath := s!"output/sv-from-lean/{c.name}.sv"
  let chiselPath := s!"chisel/src/main/scala/generated/{c.name}.scala"

  IO.FS.writeFile svPath sv
  IO.FS.writeFile chiselPath chisel

  IO.println s!"  Generated {c.name}: {c.gates.length} gates, {c.instances.length} instances"

-- Helper: log2 ceiling
private def log2Ceil (n : Nat) : Nat :=
  if n <= 1 then 0
  else Nat.log2 n + (if 2^(Nat.log2 n) < n then 1 else 0)

def generateFreeList : IO Unit := do
  IO.println "Generating FreeList (Free Physical Register List)..."

  let numPhysRegs := 64
  let tagWidth := log2Ceil numPhysRegs  -- 6
  let ptrWidth := tagWidth              -- 6
  let countWidth := log2Ceil (numPhysRegs + 1)  -- 7

  -- Generate top-level FreeList circuit
  let freelist := mkFreeList64
  writeCircuit freelist

  -- Generate submodules
  let ram := mkQueueRAM numPhysRegs tagWidth
  writeCircuit ram

  let ptr := mkQueuePointer ptrWidth
  writeCircuit ptr

  let cnt := mkQueueCounterUpDown countWidth
  writeCircuit cnt

  -- QueueRAM submodules
  let dec := mkDecoder ptrWidth
  writeCircuit dec

  let mux := mkMuxTree numPhysRegs tagWidth
  writeCircuit mux

  IO.println "  FreeList generation complete."

def main : IO Unit := do
  generateFreeList

end Shoumei.RISCV.Renaming.FreeListCodegen
