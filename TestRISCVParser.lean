import Shoumei.RISCV.ISA
import Shoumei.RISCV.OpcodeParser
import Shoumei.RISCV.InstructionList
import Shoumei.RISCV.Decoder

open Shoumei.RISCV

def main : IO Unit := do
  -- Load instruction definitions
  let defs ← loadInstrDictFromFile instrDictPath

  IO.println s!"Loaded {defs.length} RV32I instructions\n"

  -- Test decoder
  testDecoder defs
