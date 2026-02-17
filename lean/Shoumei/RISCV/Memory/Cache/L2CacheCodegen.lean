/-
RISCV/Memory/Cache/L2CacheCodegen.lean - Code Generation for L2 Cache
-/

import Shoumei.RISCV.Memory.Cache.L2Cache
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel
import Shoumei.Codegen.CppSim

open Shoumei.Codegen

namespace Shoumei.RISCV.Memory.Cache

def generateL2Cache : IO Unit := do
  let sv := SystemVerilog.toSystemVerilog mkL2Cache
  IO.FS.writeFile "output/sv-from-lean/L2Cache.sv" sv

  let chisel := Chisel.toChisel mkL2Cache
  IO.FS.writeFile "chisel/src/main/scala/generated/L2Cache.scala" chisel

  let header := CppSim.toCppSimHeader mkL2Cache
  let impl := CppSim.toCppSimImpl mkL2Cache
  IO.FS.writeFile "output/cpp_sim/L2Cache.h" header
  IO.FS.writeFile "output/cpp_sim/L2Cache.cpp" impl

end Shoumei.RISCV.Memory.Cache
