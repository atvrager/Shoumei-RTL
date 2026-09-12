/-
Circuits/Combinational/ShifterCodegen.lean - Code generation for Shifters

Generates SystemVerilog for Shifter variants.
-/

import Shoumei.Circuits.Combinational.Shifter
import Shoumei.Codegen.SystemVerilog

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

  IO.println "Shifter code generation complete!"

end Shoumei.Circuits.Combinational
