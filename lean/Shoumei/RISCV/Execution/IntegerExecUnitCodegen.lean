/-
RISCV/Execution/IntegerExecUnitCodegen.lean - Code generation for IntegerExecUnit

Generates SystemVerilog and Chisel output for the Integer Execution Unit.

Note: IntegerExecUnit instances ALU32, which was already generated in Phase 1.
This codegen only generates the wrapper that adds tag pass-through for CDB broadcast.
-/

import Shoumei.DSL
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel
import Shoumei.RISCV.Execution.IntegerExecUnit
import Shoumei.Circuits.Combinational.ALU

namespace Shoumei.RISCV.Execution.IntegerExecUnitCodegen

open Shoumei
open Shoumei.Codegen
open Shoumei.Circuits.Combinational
open Shoumei.RISCV.Execution

def writeCircuit (c : Circuit) : IO Unit := do
  let sv := SystemVerilog.toSystemVerilog c
  let chisel := Chisel.toChisel c

  let svPath := s!"output/sv-from-lean/{c.name}.sv"
  let chiselPath := s!"chisel/src/main/scala/generated/{c.name}.scala"

  IO.FS.writeFile svPath sv
  IO.FS.writeFile chiselPath chisel

  IO.println s!"  Generated {c.name}: {c.gates.length} gates, {c.instances.length} instances"

def generateIntegerExecUnit : IO Unit := do
  IO.println "Generating IntegerExecUnit..."

  -- Generate the IntegerExecUnit wrapper
  let intExecUnit := mkIntegerExecUnit
  writeCircuit intExecUnit

  IO.println "  Note: IntegerExecUnit instances ALU32 (already generated in Phase 1)"
  IO.println "  IntegerExecUnit generation complete."

end Shoumei.RISCV.Execution.IntegerExecUnitCodegen
