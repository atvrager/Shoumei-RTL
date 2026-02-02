/-
  RISC-V Instruction List Generator

  Generates instruction definition lists from riscv-opcodes instr_dict.json,
  filtered by CPUConfig extensions.
-/

import Shoumei.RISCV.ISA
import Shoumei.RISCV.Config
import Shoumei.RISCV.OpcodeParser

namespace Shoumei.RISCV

/--
  Generate instruction list from JSON file (config-aware)

  This can be called at the REPL or in IO context:
  #eval loadAndPrintInstructions
-/
def loadAndPrintInstructions (config : CPUConfig := rv32imConfig) : IO Unit := do
  IO.println s!"Loading RISC-V instruction definitions for extensions: {config.enabledExtensions}..."

  let defs ← loadInstrDefsForConfig config

  IO.println s!"Loaded {defs.length} instructions:"
  for instrDef in defs do
    IO.println s!"  {instrDef.name}: ext={instrDef.extension}, mask={instrDef.maskBits}, match={instrDef.matchBits}, fields={instrDef.variableFields.length}"

/--
  Main entry point for instruction list generator executable.
  Generates Lean source code for the instruction definition list.

  Default config is rv32imConfig (includes M extension).
  Pass --rv32i on command line to generate RV32I-only list.
-/
def main (args : List String) : IO Unit := do
  let config := if args.contains "--rv32i" then rv32iConfig else rv32imConfig
  let configName := if config.enableM then "rv32im" else "rv32i"

  let defs ← loadInstrDefsForConfig config

  IO.println "-- Auto-generated from riscv-opcodes instr_dict.json"
  IO.println s!"-- Configuration: {configName}"
  IO.println "-- DO NOT EDIT MANUALLY"
  IO.println ""
  IO.println "import Shoumei.RISCV.ISA"
  IO.println ""
  IO.println "namespace Shoumei.RISCV"
  IO.println ""
  IO.println s!"/-- All {configName.toUpper} instruction definitions -/"
  IO.println s!"def {configName}_instructions : List InstructionDef := ["

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
