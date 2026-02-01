/-
GenerateIntegerExecUnit.lean - Build target for IntegerExecUnit code generation

Usage:
  lake exe generate_integer_exec
-/

import Shoumei.RISCV.Execution.IntegerExecUnitCodegen

open Shoumei.RISCV.Execution.IntegerExecUnitCodegen

def main : IO Unit := do
  generateIntegerExecUnit
