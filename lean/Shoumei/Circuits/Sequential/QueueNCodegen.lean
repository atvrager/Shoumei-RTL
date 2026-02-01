/-
Circuits/Sequential/QueueNCodegen.lean - Code generation for QueueN
-/

import Shoumei.DSL
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel
import Shoumei.Circuits.Sequential.QueueN

namespace Shoumei.Circuits.Sequential

open Shoumei
open Shoumei.Codegen

def generateQueueN (depth width : Nat) : IO Unit := do
  let circuit := mkQueueNStructural depth width
  let sv := SystemVerilog.toSystemVerilog circuit
  let chisel := Chisel.toChisel circuit
  
  let svPath := s!"output/sv-from-lean/{circuit.name}.sv"
  let chiselPath := s!"chisel/src/main/scala/generated/{circuit.name}.scala"
  
  IO.FS.writeFile svPath sv
  IO.FS.writeFile chiselPath chisel
  
  IO.println s!"✓ Generated {circuit.name}: {svPath} and {chiselPath}"

def main : IO Unit := do
  IO.println "Generating QueueN circuits..."
  generateQueueN 2 8   -- Small test case
  generateQueueN 4 8   -- Small test case
  generateQueueN 64 6  -- Free List queue
  generateQueueN 64 32 -- Potential ROB/Dispatch queue
  IO.println "Done."

end Shoumei.Circuits.Sequential
