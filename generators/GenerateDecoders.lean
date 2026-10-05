/-
GenerateDecoders.lean - Standalone CLI for generating RISC-V decoders.
-/

import Shoumei.RISCV.CodegenTest
import Shoumei.RISCV.OpcodeParser

def riscvDecoderModules : List String :=
  ["RV64GDecoder"]

def parseArg (pfx : String) (args : List String) : Option String :=
  args.findSome? (fun a =>
    if a.startsWith pfx then some (a.drop pfx.length).toString else none)

def main (args : List String) : IO Unit := do
  let outSv := parseArg "--out-sv=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "output/sv-from-lean")
  let outNetlist := parseArg "--out-netlist=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "output/sv-netlist")
  let outCppSim := parseArg "--out-cpp-sim=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "output/cpp_sim")
  let outAsap7 := parseArg "--out-asap7=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "output/sv-asap7")
  let outGf180 := parseArg "--out-gf180=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "output/sv-gf180")
  let instrDict := parseArg "--instr-dict=" args |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk "third_party/riscv-opcodes/instr_dict.json")

  -- Create all directories required by subsystem contract
  IO.FS.createDirAll outSv
  IO.FS.createDirAll outNetlist
  IO.FS.createDirAll outCppSim
  IO.FS.createDirAll outAsap7
  IO.FS.createDirAll outGf180

  unless (← instrDict.pathExists) do
    IO.eprintln s!"instr_dict.json is missing at {instrDict}"
    IO.eprintln "Build it with: bazel build //generators:instr_dict"
    IO.Process.exit 1

  IO.println "Generating RISC-V decoders..."
  let defs ← Shoumei.RISCV.loadInstrDictFromFile instrDict
  Shoumei.RISCV.generateDecoders defs riscvDecoderModules outSv outCppSim
  IO.println "✓ Generated RISC-V decoders"
