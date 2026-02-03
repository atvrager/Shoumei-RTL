/-
RISCV/Memory/LSUCodegen.lean - Code Generation for LSU

Generates SystemVerilog, Chisel, and SystemC code for the LSU module.
-/

import Shoumei.RISCV.Memory.LSU
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel
import Shoumei.Codegen.SystemC

open System (FilePath)
open Shoumei.Codegen

namespace Shoumei.RISCV.Memory

/-- Generate SystemVerilog, Chisel, and SystemC for LSU. -/
def generateLSU : IO Unit := do
  -- SystemVerilog generation
  let sv_content := SystemVerilog.generate mkLSU
  let sv_path := FilePath.mk "output/sv-from-lean/LSU.sv"
  IO.FS.writeFile sv_path sv_content
  IO.println s!"✓ Generated SystemVerilog: {sv_path}"

  -- Chisel generation
  let chisel_content := Chisel.generate mkLSU
  let chisel_path := FilePath.mk "chisel/src/main/scala/generated/LSU.scala"
  IO.FS.writeFile chisel_path chisel_content
  IO.println s!"✓ Generated Chisel: {chisel_path}"

  -- SystemC generation
  let (header, impl) := SystemC.generate mkLSU
  let systemc_header_path := FilePath.mk "output/systemc/LSU.h"
  let systemc_impl_path := FilePath.mk "output/systemc/LSU.cpp"
  IO.FS.writeFile systemc_header_path header
  IO.FS.writeFile systemc_impl_path impl
  IO.println s!"✓ Generated SystemC: {systemc_header_path}, {systemc_impl_path}"

end Shoumei.RISCV.Memory
