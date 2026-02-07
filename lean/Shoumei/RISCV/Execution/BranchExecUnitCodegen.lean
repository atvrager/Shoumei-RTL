/-
RISCV/Execution/BranchExecUnitCodegen.lean - Code generation for BranchExecUnit
-/

import Shoumei.Codegen.Unified
import Shoumei.RISCV.Execution.BranchExecUnit

namespace Shoumei.RISCV.Execution.BranchExecUnitCodegen

open Shoumei.Codegen.Unified
open Shoumei.RISCV.Execution

def generateBranchExecUnit : IO Unit := do
  IO.println "Generating BranchExecUnit..."
  initOutputDirs
  let branchExecUnit := mkBranchExecUnit
  writeCircuit branchExecUnit
  IO.println "  BranchExecUnit generation complete."

end Shoumei.RISCV.Execution.BranchExecUnitCodegen
