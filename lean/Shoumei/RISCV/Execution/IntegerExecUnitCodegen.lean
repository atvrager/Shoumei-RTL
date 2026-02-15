/-
RISCV/Execution/IntegerExecUnitCodegen.lean - Code generation for IntegerExecUnit

Generates SystemVerilog, Chisel, and C++ Sim output for the Integer Execution Unit.

Note: IntegerExecUnit instances ALU32, which was already generated in Phase 1.
This codegen only generates the wrapper that adds tag pass-through for CDB broadcast.
-/

import Shoumei.Codegen.Unified
import Shoumei.RISCV.Execution.IntegerExecUnit

namespace Shoumei.RISCV.Execution.IntegerExecUnitCodegen

open Shoumei.Codegen.Unified
open Shoumei.RISCV.Execution

def generateIntegerExecUnit : IO Unit := do
  IO.println "Generating IntegerExecUnit..."

  -- Initialize output directories
  initOutputDirs

  -- Generate the IntegerExecUnit wrapper (all 3 formats: SV, Chisel, C++ Sim)
  let intExecUnit := mkIntegerExecUnit
  writeCircuit intExecUnit

  IO.println "  Note: IntegerExecUnit instances ALU32 (already generated in Phase 1)"
  IO.println "  IntegerExecUnit generation complete."

end Shoumei.RISCV.Execution.IntegerExecUnitCodegen

