/-
Circuits/Combinational/ComparatorCodegen.lean - Code generation for Comparators

Generates SystemVerilog and Chisel for all Comparator variants.
-/

import Shoumei.Circuits.Combinational.Comparator
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel

namespace Shoumei.Circuits.Combinational

open Shoumei

def generateComparators : IO Unit := do
  -- SystemVerilog generation
  IO.println "Generating SystemVerilog for Comparators..."

  let sv4 := Codegen.SystemVerilog.toSystemVerilog mkComparator4
  IO.FS.writeFile "output/sv-from-lean/Comparator4.sv" sv4
  IO.println "  ✓ Comparator4.sv"

  let sv8 := Codegen.SystemVerilog.toSystemVerilog mkComparator8
  IO.FS.writeFile "output/sv-from-lean/Comparator8.sv" sv8
  IO.println "  ✓ Comparator8.sv"

  let sv32 := Codegen.SystemVerilog.toSystemVerilog mkComparator32
  IO.FS.writeFile "output/sv-from-lean/Comparator32.sv" sv32
  IO.println "  ✓ Comparator32.sv"

  -- Chisel generation
  IO.println "Generating Chisel for Comparators..."

  let chisel4 := Codegen.Chisel.toChisel mkComparator4
  IO.FS.writeFile "output/chisel-src/Comparator4.scala" chisel4
  IO.FS.writeFile "chisel/src/main/scala/generated/Comparator4.scala" chisel4
  IO.println "  ✓ Comparator4.scala"

  let chisel8 := Codegen.Chisel.toChisel mkComparator8
  IO.FS.writeFile "output/chisel-src/Comparator8.scala" chisel8
  IO.FS.writeFile "chisel/src/main/scala/generated/Comparator8.scala" chisel8
  IO.println "  ✓ Comparator8.scala"

  let chisel32 := Codegen.Chisel.toChisel mkComparator32
  IO.FS.writeFile "output/chisel-src/Comparator32.scala" chisel32
  IO.FS.writeFile "chisel/src/main/scala/generated/Comparator32.scala" chisel32
  IO.println "  ✓ Comparator32.scala"

  IO.println "Comparator code generation complete!"

end Shoumei.Circuits.Combinational
