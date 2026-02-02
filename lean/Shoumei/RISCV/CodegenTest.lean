/-
  Code Generation - Generate SystemVerilog, Chisel, and SystemC decoders
  Produces both RV32I (base) and RV32IM (with M extension) decoder variants.
-/

import Shoumei.RISCV.ISA
import Shoumei.RISCV.OpcodeParser
import Shoumei.RISCV.InstructionList
import Shoumei.RISCV.CodegenSystemVerilog
import Shoumei.RISCV.CodegenChisel
import Shoumei.RISCV.CodegenSystemC

namespace Shoumei.RISCV

/-- Check if any instruction belongs to the M extension -/
def hasMExtension (defs : List InstructionDef) : Bool :=
  defs.any (fun d => d.extension.any (· == "rv_m"))

/-- Filter to only base I extension instructions -/
def filterBaseI (defs : List InstructionDef) : List InstructionDef :=
  defs.filter (fun d => d.extension.all (fun ext => ext != "rv_m"))

/-- Generate all decoder variants from instruction definitions -/
def generateDecoders (defs : List InstructionDef) : IO Unit := do
  IO.println "==================================================\n"
  IO.println "Generating RISC-V Decoder Code\n"
  IO.println "==================================================\n"

  -- Create output directories
  IO.println "Creating output directories..."
  let _ ← IO.Process.run {
    cmd := "mkdir"
    args := #["-p", "output/sv-from-lean", "output/chisel-src", "output/systemc"]
  }

  let baseDefs := filterBaseI defs

  -- Always generate RV32I (base) decoder
  IO.println s!"\n── RV32IDecoder ({baseDefs.length} instructions) ──"
  writeSystemVerilogDecoder baseDefs "output/sv-from-lean/RV32IDecoder.sv" "RV32IDecoder"
  writeChiselDecoder baseDefs "chisel/src/main/scala/generated/RV32IDecoder.scala" "RV32IDecoder"
  writeSystemCDecoderHeader baseDefs "output/systemc/RV32IDecoder.h" "RV32IDecoder"
  writeSystemCDecoderImpl baseDefs "output/systemc/RV32IDecoder.cpp" "RV32IDecoder"
  IO.println "✓ RV32IDecoder complete"

  -- Generate RV32IM decoder if M extension instructions are present
  if hasMExtension defs then
    IO.println s!"\n── RV32IMDecoder ({defs.length} instructions) ──"
    writeSystemVerilogDecoder defs "output/sv-from-lean/RV32IMDecoder.sv" "RV32IMDecoder"
    writeChiselDecoder defs "chisel/src/main/scala/generated/RV32IMDecoder.scala" "RV32IMDecoder"
    writeSystemCDecoderHeader defs "output/systemc/RV32IMDecoder.h" "RV32IMDecoder"
    writeSystemCDecoderImpl defs "output/systemc/RV32IMDecoder.cpp" "RV32IMDecoder"
    IO.println "✓ RV32IMDecoder complete"

  IO.println "\n==================================================\n"
  IO.println "Code generation summary:"
  IO.println s!"  - RV32IDecoder:  {baseDefs.length} instructions (SV + Chisel + SystemC)"
  if hasMExtension defs then
    IO.println s!"  - RV32IMDecoder: {defs.length} instructions (SV + Chisel + SystemC)"
  IO.println "\n✓ Code generation complete!"

end Shoumei.RISCV
