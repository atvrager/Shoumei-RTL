/-
RISCV/Matrix/MatrixExecUnitCodegen.lean - Code generation for Matrix Execution Unit
-/

import Shoumei.RISCV.Matrix.MatrixExecUnit
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel

namespace Shoumei.RISCV.Matrix

open Shoumei

def generateMatrixExecUnit : IO Unit := do
  IO.println "Generating MatrixExecUnit..."

  let sv := Codegen.SystemVerilog.toSystemVerilog mkMatrixExecUnit
  IO.FS.writeFile "output/sv-from-lean/MatrixExecUnit.sv" sv

  let chisel := Codegen.Chisel.toChisel mkMatrixExecUnit
  IO.FS.writeFile "chisel/src/main/scala/generated/MatrixExecUnit.scala" chisel

  IO.println "  MatrixExecUnit code generation complete!"

end Shoumei.RISCV.Matrix
