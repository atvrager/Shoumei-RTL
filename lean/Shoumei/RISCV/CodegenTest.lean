/-
  Code Generation - Generate SystemVerilog, Chisel, and C++ simulation decoders
  Produces RV32I (base), RV32IM, and RV32IMF decoder variants as needed.
-/

import Shoumei.RISCV.ISA
import Shoumei.RISCV.OpcodeParser
import Shoumei.RISCV.InstructionList
import Shoumei.RISCV.CodegenSystemVerilog
import Shoumei.RISCV.CodegenChisel
import Shoumei.RISCV.CodegenCppSim

namespace Shoumei.RISCV

/-- Check if any instruction belongs to the M extension -/
def hasMExtension (defs : List InstructionDef) : Bool :=
  defs.any (fun d => d.extension.any (· == "rv_m"))

/-- Check if any instruction belongs to the F extension -/
def hasFExtension (defs : List InstructionDef) : Bool :=
  defs.any (fun d => d.extension.any (· == "rv_f"))

/-- Check if any instruction belongs to the D extension -/
def hasDExtension (defs : List InstructionDef) : Bool :=
  defs.any (fun d => d.extension.any (· == "rv_d"))

/-- Filter to only base I extension instructions (no M, no F, no D) -/
def filterBaseI (defs : List InstructionDef) : List InstructionDef :=
  defs.filter (fun d => d.extension.all (fun ext => ext != "rv_m" && ext != "rv_f" && ext != "rv_d"))

/-- Filter to I + M (no F, no D) -/
def filterIM (defs : List InstructionDef) : List InstructionDef :=
  defs.filter (fun d => d.extension.all (fun ext => ext != "rv_f" && ext != "rv_d"))

/-- Filter to I + F (no M, no D) -/
def filterIF (defs : List InstructionDef) : List InstructionDef :=
  defs.filter (fun d => d.extension.all (fun ext => ext != "rv_m" && ext != "rv_d"))

/-- Filter to I + M + F (no D) -/
def filterIMF (defs : List InstructionDef) : List InstructionDef :=
  defs.filter (fun d => d.extension.all (fun ext => ext != "rv_d"))

/-- Check if instruction is an FP-extension instruction (F or D) -/
private def isFpExtInstruction (d : InstructionDef) : Bool :=
  d.extension.any (fun ext => ext == "rv_f" || ext == "rv_d")

/-- Sort instructions: Integer first (preserving order), then FP (F and D).
    This ensures integer opcodes get low enum positions (< 64)
    so the existing 6-bit integer RS can handle them. -/
def sortIMFirst (defs : List InstructionDef) : List InstructionDef :=
  let im := defs.filter (fun d => !isFpExtInstruction d)
  let f := defs.filter isFpExtInstruction
  im ++ f

/-- Sort IF instructions: I first (preserving order), then FP. -/
def sortIFirst (defs : List InstructionDef) : List InstructionDef :=
  let i := defs.filter (fun d => !isFpExtInstruction d)
  let f := defs.filter isFpExtInstruction
  i ++ f

private def writeDecoder (defs : List InstructionDef) (name : String) : IO Unit := do
  writeSystemVerilogDecoder defs s!"output/sv-from-lean/{name}.sv" name
  writeChiselDecoder defs s!"chisel/src/main/scala/generated/{name}.scala" name
  writeCppSimDecoderHeader defs s!"output/cpp_sim/{name}.h" name
  writeCppSimDecoderImpl defs s!"output/cpp_sim/{name}.cpp" name

/-- Generate all decoder variants from instruction definitions -/
def generateDecoders (defs : List InstructionDef) : IO Unit := do
  IO.println "==================================================\n"
  IO.println "Generating RISC-V Decoder Code\n"
  IO.println "==================================================\n"

  -- Create output directories
  IO.println "Creating output directories..."
  let _ ← IO.Process.run {
    cmd := "mkdir"
    args := #["-p", "output/sv-from-lean", "output/chisel-src", "output/cpp_sim"]
  }

  let baseDefs := filterBaseI defs

  -- Always generate RV32I (base) decoder
  IO.println s!"\n── RV32IDecoder ({baseDefs.length} instructions) ──"
  writeDecoder baseDefs "RV32IDecoder"
  IO.println "✓ RV32IDecoder complete"

  let hasM := hasMExtension defs
  let hasF := hasFExtension defs
  let hasD := hasDExtension defs

  -- Generate RV32IM decoder if M extension instructions are present
  if hasM then
    let imDefs := filterIM defs
    IO.println s!"\n── RV32IMDecoder ({imDefs.length} instructions) ──"
    writeDecoder imDefs "RV32IMDecoder"
    IO.println "✓ RV32IMDecoder complete"

  -- Generate RV32IFDecoder if F extension instructions are present
  if hasF then
    let ifDefs := sortIFirst (filterIF defs)
    IO.println s!"\n── RV32IFDecoder ({ifDefs.length} instructions) ──"
    writeDecoder ifDefs "RV32IFDecoder"
    IO.println "✓ RV32IFDecoder complete"

  -- Generate RV32IMF decoder if both M+F present (all instructions except D, sorted I+M first)
  if hasM && hasF then
    let imfDefs := sortIMFirst (filterIMF defs)
    IO.println s!"\n── RV32IMFDecoder ({imfDefs.length} instructions) ──"
    writeDecoder imfDefs "RV32IMFDecoder"
    IO.println "✓ RV32IMFDecoder complete"

  -- Generate RV32G decoder if M+F+D present (all instructions, sorted I+M first)
  if hasM && hasF && hasD then
    let gDefs := sortIMFirst defs
    IO.println s!"\n── RV32GDecoder ({gDefs.length} instructions) ──"
    writeDecoder gDefs "RV32GDecoder"
    IO.println "✓ RV32GDecoder complete"

  IO.println "\n==================================================\n"
  IO.println "Code generation summary:"
  IO.println s!"  - RV32IDecoder:  {baseDefs.length} instructions (SV + Chisel + C++)"
  if hasM then
    IO.println s!"  - RV32IMDecoder: {(filterIM defs).length} instructions (SV + Chisel + C++)"
  if hasF then
    IO.println s!"  - RV32IFDecoder: {(filterIF defs).length} instructions (SV + Chisel + C++)"
  if hasM && hasF then
    IO.println s!"  - RV32IMFDecoder: {(filterIMF defs).length} instructions (SV + Chisel + C++)"
  if hasM && hasF && hasD then
    IO.println s!"  - RV32GDecoder:   {defs.length} instructions (SV + Chisel + C++)"
  IO.println "\n✓ Code generation complete!"

end Shoumei.RISCV
