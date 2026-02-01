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

  IO.println s!"Loaded {defs.length} RV32I instructions from riscv-opcodes\n"

  -- Generate both SystemVerilog and Chisel decoders
  generateDecoders defs
