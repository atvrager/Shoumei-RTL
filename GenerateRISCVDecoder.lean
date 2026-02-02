import Shoumei.RISCV.ISA
import Shoumei.RISCV.OpcodeParser
import Shoumei.RISCV.InstructionList
import Shoumei.RISCV.CodegenSystemVerilog
import Shoumei.RISCV.CodegenChisel
import Shoumei.RISCV.CodegenTest

open Shoumei.RISCV

def main : IO Unit := do
  -- Load instruction definitions
  let defs ← loadInstrDictFromFile instrDictPath

  IO.println s!"Loaded {defs.length} instructions from riscv-opcodes\n"

  -- Generate decoder variants (RV32I always; RV32IM if M-ext present)
  generateDecoders defs
