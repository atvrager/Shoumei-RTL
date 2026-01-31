/-
  RISC-V Instruction List Generator

  This file contains the actual RV32I instruction definitions,
  generated from riscv-opcodes instr_dict.json
-/

import Shoumei.RISCV.ISA
import Shoumei.RISCV.OpcodeParser

namespace Shoumei.RISCV

/--
  Generate instruction list from JSON file

  This can be called at the REPL or in IO context:
  #eval loadAndPrintInstructions
-/
def loadAndPrintInstructions : IO Unit := do
  IO.println "Loading RISC-V instruction definitions from JSON..."

  let defs ← loadInstrDictFromFile instrDictPath

  IO.println s!"Loaded {defs.length} instructions:"
  for instrDef in defs do
    IO.println s!"  {instrDef.name}: mask={instrDef.maskBits}, match={instrDef.matchBits}, fields={instrDef.variableFields.length}"

/--
  Main entry point for instruction list generator executable
-/
def main : IO Unit := do
  let defs ← loadInstrDictFromFile instrDictPath

  IO.println "-- Auto-generated from riscv-opcodes instr_dict.json"
  IO.println "-- DO NOT EDIT MANUALLY"
  IO.println ""
  IO.println "import Shoumei.RISCV.ISA"
  IO.println ""
  IO.println "namespace Shoumei.RISCV"
  IO.println ""
  IO.println "/-- All RV32I instruction definitions -/"
  IO.println "def rv32i_instructions : List InstructionDef := ["

  for instrDef in defs do
    let fields := instrDef.variableFields.map (fun f => s!".{f}")
    let extensions := instrDef.extension.map (fun e => "\"" ++ e ++ "\"")
    IO.println ("  { name := \"" ++ instrDef.name ++ "\"")
    IO.println s!"    opType := .{instrDef.opType}"
    IO.println ("    encoding := \"" ++ instrDef.encoding ++ "\"")
    IO.println s!"    variableFields := [{String.intercalate ", " fields}]"
    IO.println s!"    extension := [{String.intercalate ", " extensions}]"
    IO.println s!"    matchBits := {instrDef.matchBits}"
    IO.println s!"    maskBits := {instrDef.maskBits} },"

  IO.println "]"
  IO.println ""
  IO.println "end Shoumei.RISCV"

end Shoumei.RISCV
