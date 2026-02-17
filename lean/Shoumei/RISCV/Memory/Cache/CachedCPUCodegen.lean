/-
RISCV/Memory/Cache/CachedCPUCodegen.lean - Code Generation for CachedCPU
-/

import Shoumei.RISCV.Memory.Cache.CachedCPU
import Shoumei.RISCV.Config
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel
import Shoumei.Codegen.CppSim

open Shoumei.Codegen
open Shoumei.RISCV

namespace Shoumei.RISCV.Memory.Cache

def generateCachedCPU : IO Unit := do
  let circuit := mkCachedCPU rv32imConfig

  let sv := SystemVerilog.toSystemVerilog circuit
  IO.FS.writeFile "output/sv-from-lean/CachedCPU_RV32IM.sv" sv

  let chisel := Chisel.toChisel circuit
  IO.FS.writeFile "chisel/src/main/scala/generated/CachedCPU_RV32IM.scala" chisel

  let header := CppSim.toCppSimHeader circuit
  let impl := CppSim.toCppSimImpl circuit
  IO.FS.writeFile "output/cpp_sim/CachedCPU_RV32IM.h" header
  IO.FS.writeFile "output/cpp_sim/CachedCPU_RV32IM.cpp" impl

end Shoumei.RISCV.Memory.Cache
