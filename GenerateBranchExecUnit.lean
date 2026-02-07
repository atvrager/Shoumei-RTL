/-
GenerateBranchExecUnit.lean - Build target for BranchExecUnit code generation

Usage:
  lake exe generate_branch_exec
-/

import Shoumei.RISCV.Execution.BranchExecUnitCodegen

open Shoumei.RISCV.Execution.BranchExecUnitCodegen

def main : IO Unit := do
  generateBranchExecUnit
