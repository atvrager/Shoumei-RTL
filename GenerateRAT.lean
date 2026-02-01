-- Generate RAT (Register Alias Table) circuits
-- Executable wrapper for RAT code generation

import Shoumei.RISCV.Renaming.RATCodegen

def main : IO Unit :=
  Shoumei.RISCV.Renaming.RATCodegen.main
