/-
  Code Generation Test - Generate both SystemVerilog and Chisel
-/

import Shoumei.RISCV.ISA
import Shoumei.RISCV.OpcodeParser
import Shoumei.RISCV.InstructionList
import Shoumei.RISCV.CodegenSystemVerilog
import Shoumei.RISCV.CodegenChisel
import Shoumei.RISCV.CodegenSystemC

namespace Shoumei.RISCV

/-- Generate SystemVerilog, Chisel, and SystemC decoders -/
def generateDecoders (defs : List InstructionDef) : IO Unit := do
  IO.println "==================================================\n"
  IO.println "Generating RV32I Decoder Code\n"
  IO.println "==================================================\n"

  -- Create output directories
  IO.println "Creating output directories..."
  let _ ← IO.Process.run {
    cmd := "mkdir"
    args := #["-p", "output/sv-from-lean", "output/chisel-src", "output/systemc"]
  }

  -- Generate SystemVerilog
  IO.println "\nGenerating SystemVerilog decoder..."
  writeSystemVerilogDecoder defs "output/sv-from-lean/RV32IDecoder.sv"
  IO.println "✓ SystemVerilog generation complete"

  -- Generate Chisel
  IO.println "\nGenerating Chisel decoder..."
  writeChiselDecoder defs "chisel/src/main/scala/generated/RV32IDecoder.scala"
  IO.println "✓ Chisel generation complete"

  -- Generate SystemC
  IO.println "\nGenerating SystemC decoder..."
  writeSystemCDecoderHeader defs "output/systemc/RV32IDecoder.h"
  writeSystemCDecoderImpl defs "output/systemc/RV32IDecoder.cpp"
  IO.println "✓ SystemC generation complete"

  IO.println "\n==================================================\n"
  IO.println "Code generation summary:"
  IO.println s!"  - SystemVerilog (from LEAN): output/sv-from-lean/RV32IDecoder.sv"
  IO.println s!"  - Chisel source (from LEAN): chisel/src/main/scala/generated/RV32IDecoder.scala"
  IO.println s!"  - SystemC header (from LEAN): output/systemc/RV32IDecoder.h"
  IO.println s!"  - SystemC impl (from LEAN):   output/systemc/RV32IDecoder.cpp"
  IO.println s!"  - Instructions:               {defs.length} RV32I operations"
  IO.println "\n✓ Code generation complete!"

end Shoumei.RISCV
