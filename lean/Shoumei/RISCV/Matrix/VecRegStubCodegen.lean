/-
RISCV/Matrix/VecRegStubCodegen.lean - Code generation for VecRegStub

Temporary stub. When V extension branch merges, this file is removed.
-/

import Shoumei.RISCV.Matrix.VecRegStub
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel

namespace Shoumei.RISCV.Matrix

open Shoumei

def generateVecRegStub : IO Unit := do
  IO.println "Generating VecRegStub32x128..."

  let sv := Codegen.SystemVerilog.toSystemVerilog mkVecRegStub32x128
  IO.FS.writeFile "output/sv-from-lean/VecRegStub32x128.sv" sv

  let chisel := Codegen.Chisel.toChisel mkVecRegStub32x128
  IO.FS.writeFile "chisel/src/main/scala/generated/VecRegStub32x128.scala" chisel

  IO.println "  VecRegStub code generation complete!"

end Shoumei.RISCV.Matrix
