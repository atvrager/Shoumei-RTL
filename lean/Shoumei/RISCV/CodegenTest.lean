/-
  Code Generation Test - Generate both SystemVerilog and Chisel
-/

import Shoumei.RISCV.ISA
import Shoumei.RISCV.OpcodeParser
import Shoumei.RISCV.InstructionList
import Shoumei.RISCV.CodegenSystemVerilog
import Shoumei.RISCV.CodegenChisel

namespace Shoumei.RISCV

/-- Generate both SystemVerilog and Chisel decoders -/
def generateDecoders (defs : List InstructionDef) : IO Unit := do
  IO.println "==================================================\n"
  IO.println "Generating RV32I Decoder Code\n"
  IO.println "==================================================\n"

  -- Create output directories
  IO.println "Creating output directories..."
  let _ ← IO.Process.run {
    cmd := "mkdir"
    args := #["-p", "output/sv-from-lean", "output/chisel-src"]
  }

  -- Generate SystemVerilog
  IO.println "\nGenerating SystemVerilog decoder..."
  writeSystemVerilogDecoder defs "output/sv-from-lean/rv32i_decoder.sv"
  IO.println "✓ SystemVerilog generation complete"

  -- Generate Chisel
  IO.println "\nGenerating Chisel decoder..."
  writeChiselDecoder defs "output/chisel-src/RV32IDecoder.scala"
  IO.println "✓ Chisel generation complete"

  IO.println "\n==================================================\n"
  IO.println "Code generation summary:"
  IO.println s!"  - SystemVerilog (from LEAN): output/sv-from-lean/rv32i_decoder.sv"
  IO.println s!"  - Chisel source (from LEAN):  output/chisel-src/RV32IDecoder.scala"
  IO.println s!"  - Instructions:               {defs.length} RV32I operations"
  IO.println "\nNext steps:"
  IO.println "  - Copy Chisel to chisel/src/main/scala/shoumei/riscv/"
  IO.println "  - Run: cd chisel && sbt 'Test/runMain shoumei.riscv.EmitRV32IDecoder'"
  IO.println "  - SystemVerilog from Chisel will be in: output/sv-from-chisel/"
  IO.println "\n✓ Code generation complete!"

end Shoumei.RISCV
