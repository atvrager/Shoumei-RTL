/-
Code generation for ALU32
-/

import Shoumei.Circuits.Combinational.ALU
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel

namespace Shoumei.Circuits.Combinational

open Shoumei

def generateALUs : IO Unit := do
  -- SystemVerilog generation
  IO.println "Generating SystemVerilog for ALU..."

  let sv32 := Codegen.SystemVerilog.toSystemVerilog mkALU32
  IO.FS.writeFile "output/sv-from-lean/ALU32.sv" sv32
  IO.println "  ✓ ALU32.sv"

  -- Chisel generation
  IO.println "Generating Chisel for ALU..."

  let chisel32 := Codegen.Chisel.toChisel mkALU32
  IO.FS.writeFile "output/chisel-src/ALU32.scala" chisel32
  IO.FS.writeFile "chisel/src/main/scala/generated/ALU32.scala" chisel32
  IO.println "  ✓ ALU32.scala"

  IO.println "ALU code generation complete!"

end Shoumei.Circuits.Combinational
