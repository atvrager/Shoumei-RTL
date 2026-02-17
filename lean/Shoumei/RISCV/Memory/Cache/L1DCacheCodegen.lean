/-
RISCV/Memory/Cache/L1DCacheCodegen.lean - Code Generation for L1D Cache
-/

import Shoumei.RISCV.Memory.Cache.L1DCache
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel
import Shoumei.Codegen.CppSim

open Shoumei.Codegen

namespace Shoumei.RISCV.Memory.Cache

def generateL1DCache : IO Unit := do
  let sv := SystemVerilog.toSystemVerilog mkL1DCache
  IO.FS.writeFile "output/sv-from-lean/L1DCache.sv" sv

  let chisel := Chisel.toChisel mkL1DCache
  IO.FS.writeFile "chisel/src/main/scala/generated/L1DCache.scala" chisel

  let header := CppSim.toCppSimHeader mkL1DCache
  let impl := CppSim.toCppSimImpl mkL1DCache
  IO.FS.writeFile "output/cpp_sim/L1DCache.h" header
  IO.FS.writeFile "output/cpp_sim/L1DCache.cpp" impl

end Shoumei.RISCV.Memory.Cache
