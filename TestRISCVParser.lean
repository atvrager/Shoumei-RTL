import Shoumei.RISCV.ISA
import Shoumei.RISCV.OpcodeParser
import Shoumei.RISCV.InstructionList
import Shoumei.RISCV.Decoder
import Shoumei.RISCV.DecoderTest
import Shoumei.RISCV.Semantics
import Shoumei.RISCV.SemanticsTestSimple

open Shoumei.RISCV

def main : IO Unit := do
  -- Load instruction definitions
  let defs ← loadInstrDictFromFile instrDictPath

  IO.println s!"Loaded {defs.length} RV32I instructions from riscv-opcodes\n"

  -- Run decoder test suite
  testAllInstructions defs

  IO.println "\n==================================================\n"

  -- Run semantics tests
  testKeySemantics defs
