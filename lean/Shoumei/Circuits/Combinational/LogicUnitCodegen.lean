/-
Circuits/Combinational/LogicUnitCodegen.lean - Code generation for Logic Units

Generates SystemVerilog for all LogicUnit variants.
-/

import Shoumei.Circuits.Combinational.LogicUnit
import Shoumei.Codegen.SystemVerilog

namespace Shoumei.Circuits.Combinational

open Shoumei

def generateLogicUnits : IO Unit := do
  -- SystemVerilog generation
  IO.println "Generating SystemVerilog for LogicUnits..."

  let sv4 := Codegen.SystemVerilog.toSystemVerilog mkLogicUnit4
  IO.FS.writeFile "output/sv-from-lean/LogicUnit4.sv" sv4
  IO.println "  ✓ LogicUnit4.sv"

  let sv8 := Codegen.SystemVerilog.toSystemVerilog mkLogicUnit8
  IO.FS.writeFile "output/sv-from-lean/LogicUnit8.sv" sv8
  IO.println "  ✓ LogicUnit8.sv"

  let sv32 := Codegen.SystemVerilog.toSystemVerilog mkLogicUnit32
  IO.FS.writeFile "output/sv-from-lean/LogicUnit32.sv" sv32
  IO.println "  ✓ LogicUnit32.sv"

  IO.println "LogicUnit code generation complete!"

end Shoumei.Circuits.Combinational
