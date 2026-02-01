-- Generate Free List (Free Physical Register List) circuits
-- Executable wrapper for FreeList code generation

import Shoumei.RISCV.Renaming.FreeListCodegen

def main : IO Unit :=
  Shoumei.RISCV.Renaming.FreeListCodegen.main
