/-
Circuits/Sequential/QueueNCodegen.lean - Code generation for QueueN
-/

import Shoumei.DSL
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel
import Shoumei.Circuits.Sequential.QueueN
import Shoumei.Circuits.Sequential.QueueComponents
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Combinational.MuxTree

namespace Shoumei.Circuits.Sequential

open Shoumei.Circuits.Combinational

open Shoumei
open Shoumei.Codegen


-- Helper: Compute log2 ceiling
private def log2Ceil (n : Nat) : Nat :=
  if n <= 1 then 0
  else Nat.log2 n + (if 2^(Nat.log2 n) < n then 1 else 0)

def writeCircuit (c : Circuit) : IO Unit := do
  let sv := SystemVerilog.toSystemVerilog c
  let chisel := Chisel.toChisel c
  
  let svPath := s!"output/sv-from-lean/{c.name}.sv"
  let chiselPath := s!"chisel/src/main/scala/generated/{c.name}.scala"
  
  IO.FS.writeFile svPath sv
  IO.FS.writeFile chiselPath chisel
  
  IO.println s!"✓ Generated {c.name}: {svPath} and {chiselPath}"

def generateQueueN (depth width : Nat) : IO Unit := do
  -- Generate top level
  let circuit := mkQueueNStructural depth width
  
  -- Generate submodules
  let ptrWidth := log2Ceil depth
  let countWidth := log2Ceil (depth + 1)
  
  let ram := mkQueueRAM depth width
  let ptr := mkQueuePointer ptrWidth
  let cnt := mkQueueCounterUpDown countWidth
  
  -- QueueRAM submodules
  let dec := mkDecoder ptrWidth
  let mux := mkMuxTree depth width
  
  writeCircuit circuit
  writeCircuit ram
  writeCircuit ptr
  writeCircuit cnt
  writeCircuit dec
  writeCircuit mux

def main : IO Unit := do
  IO.println "Generating QueueN circuits..."
  generateQueueN 2 8   -- Small test case
  generateQueueN 4 8   -- Small test case
  generateQueueN 64 6  -- Free List queue
  generateQueueN 64 32 -- Potential ROB/Dispatch queue
  IO.println "Done."

end Shoumei.Circuits.Sequential
