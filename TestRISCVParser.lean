import Shoumei.RISCV.ISA
import Shoumei.RISCV.OpcodeParser
import Shoumei.RISCV.InstructionList
import Shoumei.RISCV.Decoder
import Shoumei.RISCV.DecoderTest

open Shoumei.RISCV

def main : IO Unit := do
  -- Load instruction definitions
  let defs ← loadInstrDictFromFile instrDictPath

  IO.println s!"Loaded {defs.length} RV32I instructions from riscv-opcodes\n"

  -- Run comprehensive test suite
  testAllInstructions defs
