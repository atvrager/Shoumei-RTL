/-
Circuits/Combinational/ComparatorCodegen.lean - Code generation for Comparators

Generates SystemVerilog for all Comparator variants.
-/

import Shoumei.Circuits.Combinational.Comparator
import Shoumei.Codegen.SystemVerilog

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

  -- EqualityComparator32 (XOR + OR-tree, no subtraction)
  let sv_eq32 := Codegen.SystemVerilog.toSystemVerilog mkEqualityComparator32
  IO.FS.writeFile "output/sv-from-lean/EqualityComparator32.sv" sv_eq32
  IO.println "  ✓ EqualityComparator32.sv"

  IO.println "Comparator code generation complete!"

end Shoumei.Circuits.Combinational
