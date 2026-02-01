/-
Circuits/Combinational/LogicUnitCodegen.lean - Code generation for Logic Units

Generates SystemVerilog and Chisel for all LogicUnit variants.
-/

import Shoumei.Circuits.Combinational.LogicUnit
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel

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

  -- Chisel generation
  IO.println "Generating Chisel for LogicUnits..."

  let chisel4 := Codegen.Chisel.toChisel mkLogicUnit4
  IO.FS.writeFile "output/chisel-src/LogicUnit4.scala" chisel4
  IO.FS.writeFile "chisel/src/main/scala/generated/LogicUnit4.scala" chisel4
  IO.println "  ✓ LogicUnit4.scala"

  let chisel8 := Codegen.Chisel.toChisel mkLogicUnit8
  IO.FS.writeFile "output/chisel-src/LogicUnit8.scala" chisel8
  IO.FS.writeFile "chisel/src/main/scala/generated/LogicUnit8.scala" chisel8
  IO.println "  ✓ LogicUnit8.scala"

  let chisel32 := Codegen.Chisel.toChisel mkLogicUnit32
  IO.FS.writeFile "output/chisel-src/LogicUnit32.scala" chisel32
  IO.FS.writeFile "chisel/src/main/scala/generated/LogicUnit32.scala" chisel32
  IO.println "  ✓ LogicUnit32.scala"

  IO.println "LogicUnit code generation complete!"

end Shoumei.Circuits.Combinational
