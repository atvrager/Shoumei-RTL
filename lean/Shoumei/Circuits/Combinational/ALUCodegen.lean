/-
Code generation for ALU32
-/

import Shoumei.Circuits.Combinational.ALU
import Shoumei.Codegen.SystemVerilog

namespace Shoumei.Circuits.Combinational

open Shoumei

def generateALUs : IO Unit := do
  -- SystemVerilog generation
  IO.println "Generating SystemVerilog for ALU..."

  let sv32 := Codegen.SystemVerilog.toSystemVerilog mkALU32
  IO.FS.writeFile "output/sv-from-lean/ALU32.sv" sv32
  IO.println "  ✓ ALU32.sv"

  IO.println "ALU code generation complete!"

end Shoumei.Circuits.Combinational
