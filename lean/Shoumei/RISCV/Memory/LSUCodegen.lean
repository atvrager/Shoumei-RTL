/-
RISCV/Memory/LSUCodegen.lean - Code Generation for LSU

Generates SystemVerilog, Chisel, and C++ simulation code for the LSU module.
-/

import Shoumei.RISCV.Memory.LSU
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel
import Shoumei.Codegen.CppSim

open System (FilePath)
open Shoumei.Codegen

namespace Shoumei.RISCV.Memory

/-- Generate SystemVerilog, Chisel, and C++ simulation for LSU. -/
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

  -- C++ simulation generation
  let header := CppSim.toCppSimHeader mkLSU
  let impl := CppSim.toCppSimImpl mkLSU
  let cppsim_header_path := FilePath.mk "output/cpp_sim/LSU.h"
  let cppsim_impl_path := FilePath.mk "output/cpp_sim/LSU.cpp"
  IO.FS.writeFile cppsim_header_path header
  IO.FS.writeFile cppsim_impl_path impl
  IO.println s!"✓ Generated C++ simulation: {cppsim_header_path}, {cppsim_impl_path}"

end Shoumei.RISCV.Memory
