/-
Circuits/Combinational/ShifterCodegen.lean - Code generation for Shifters

Generates SystemVerilog and Chisel for Shifter variants.
-/

import Shoumei.Circuits.Combinational.Shifter
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel

namespace Shoumei.Circuits.Combinational

open Shoumei

def generateShifters : IO Unit := do
  -- SystemVerilog generation
  IO.println "Generating SystemVerilog for Shifters..."

  let sv4 := Codegen.SystemVerilog.toSystemVerilog mkShifter4
  IO.FS.writeFile "output/sv-from-lean/Shifter4.sv" sv4
  IO.println "  ✓ Shifter4.sv"

  let sv32 := Codegen.SystemVerilog.toSystemVerilog mkShifter32
  IO.FS.writeFile "output/sv-from-lean/Shifter32.sv" sv32
  IO.println "  ✓ Shifter32.sv"

  -- Chisel generation
  IO.println "Generating Chisel for Shifters..."

  let chisel4 := Codegen.Chisel.toChisel mkShifter4
  IO.FS.writeFile "output/chisel-src/Shifter4.scala" chisel4
  IO.FS.writeFile "chisel/src/main/scala/generated/Shifter4.scala" chisel4
  IO.println "  ✓ Shifter4.scala"

  let chisel32 := Codegen.Chisel.toChisel mkShifter32
  IO.FS.writeFile "output/chisel-src/Shifter32.scala" chisel32
  IO.FS.writeFile "chisel/src/main/scala/generated/Shifter32.scala" chisel32
  IO.println "  ✓ Shifter32.scala"

  IO.println "Shifter code generation complete!"

end Shoumei.Circuits.Combinational
