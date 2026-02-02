/-
RISCV/Execution/MemoryExecUnitCodegen.lean - Code generation for MemoryExecUnit

Generates SystemVerilog, Chisel, and SystemC output for the Memory Execution Unit
(Address Generation Unit).

Note: MemoryExecUnit instances RippleCarryAdder32, which was already generated in Phase 1.
This codegen only generates the wrapper that adds tag pass-through for CDB broadcast.
-/

import Shoumei.Codegen.Unified
import Shoumei.RISCV.Execution.MemoryExecUnit

namespace Shoumei.RISCV.Execution.MemoryExecUnitCodegen

open Shoumei.Codegen.Unified
open Shoumei.RISCV.Execution

def generateMemoryExecUnit : IO Unit := do
  IO.println "Generating MemoryExecUnit..."

  -- Initialize output directories
  initOutputDirs

  -- Generate the MemoryExecUnit wrapper (all 3 formats: SV, Chisel, SystemC)
  let memExecUnit := mkMemoryExecUnit
  writeCircuit memExecUnit

  IO.println "  Note: MemoryExecUnit instances RippleCarryAdder32 (already generated in Phase 1)"
  IO.println "  MemoryExecUnit generation complete."

end Shoumei.RISCV.Execution.MemoryExecUnitCodegen
