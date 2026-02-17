/-
RISCV/Memory/Cache/L1ICacheCodegen.lean - Code Generation for L1I Cache
-/

import Shoumei.RISCV.Memory.Cache.L1ICache
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel
import Shoumei.Codegen.CppSim

open System (FilePath)
open Shoumei.Codegen

namespace Shoumei.RISCV.Memory.Cache

def generateL1ICache : IO Unit := do
  let sv := SystemVerilog.toSystemVerilog mkL1ICache
  IO.FS.writeFile "output/sv-from-lean/L1ICache.sv" sv

  let chisel := Chisel.toChisel mkL1ICache
  IO.FS.writeFile "chisel/src/main/scala/generated/L1ICache.scala" chisel

  let header := CppSim.toCppSimHeader mkL1ICache
  let impl := CppSim.toCppSimImpl mkL1ICache
  IO.FS.writeFile "output/cpp_sim/L1ICache.h" header
  IO.FS.writeFile "output/cpp_sim/L1ICache.cpp" impl

end Shoumei.RISCV.Memory.Cache
