/-
  Code Generation - Generate SystemVerilog, Chisel, and C++ simulation decoder
  Produces a single decoder matching the defaultCPUConfig ISA string.
-/

import Shoumei.RISCV.ISA
import Shoumei.RISCV.OpcodeParser
import Shoumei.RISCV.InstructionList
import Shoumei.RISCV.CodegenSystemVerilog
import Shoumei.RISCV.CodegenChisel
import Shoumei.RISCV.CodegenCppSim
import Shoumei.RISCV.Config

namespace Shoumei.RISCV

/-- Check if instruction is an F-extension instruction -/
private def isFExtInstruction (d : InstructionDef) : Bool :=
  d.extension.any (· == "rv_f")

/-- Sort instructions: non-FP first (preserving order), then FP.
    This ensures integer opcodes get low enum positions (< 64)
    so the existing 6-bit integer RS can handle them. -/
def sortIntFirst (defs : List InstructionDef) : List InstructionDef :=
  let int := defs.filter (fun d => !isFExtInstruction d)
  let fp := defs.filter isFExtInstruction
  int ++ fp

private def writeDecoder (defs : List InstructionDef) (name : String) : IO Unit := do
  writeSystemVerilogDecoder defs s!"output/sv-from-lean/{name}.sv" name
  writeChiselDecoder defs s!"chisel/src/main/scala/generated/{name}.scala" name
  writeCppSimDecoderHeader defs s!"output/cpp_sim/{name}.h" name
  writeCppSimDecoderImpl defs s!"output/cpp_sim/{name}.cpp" name

/-- Generate a decoder for a given config from the full instruction list -/
def generateDecoderForConfig (allDefs : List InstructionDef) (config : CPUConfig) : IO Unit := do
  let decoderName := config.isaString ++ "Decoder"
  let enabled := config.enabledExtensions
  let defs := allDefs.filter fun d => d.extension.any (enabled.contains ·)
  let sortedDefs := sortIntFirst defs
  IO.println s!"\n── {decoderName} ({sortedDefs.length} instructions) ──"
  writeDecoder sortedDefs decoderName
  IO.println s!"✓ {decoderName} complete"

/-- Generate decoders for all active configs -/
def generateDecoders (defs : List InstructionDef) : IO Unit := do
  IO.println "==================================================\n"
  IO.println "Generating RISC-V Decoders\n"
  IO.println "==================================================\n"

  -- Create output directories
  IO.println "Creating output directories..."
  let _ ← IO.Process.run {
    cmd := "mkdir"
    args := #["-p", "output/sv-from-lean", "output/chisel-src", "output/cpp_sim"]
  }

  -- Generate decoder for the default config (includes VME if enabled)
  generateDecoderForConfig defs defaultCPUConfig

  IO.println "\n==================================================\n"
  IO.println "\n✓ Code generation complete!"

end Shoumei.RISCV
