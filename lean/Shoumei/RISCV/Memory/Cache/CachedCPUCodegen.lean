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
  let circuit := mkCachedCPU defaultCPUConfig

  let sv := SystemVerilog.toSystemVerilog circuit
  IO.FS.writeFile s!"output/sv-from-lean/{circuit.name}.sv" sv

  let chisel := Chisel.toChisel circuit
  IO.FS.writeFile s!"chisel/src/main/scala/generated/{circuit.name}.scala" chisel

  let header := CppSim.toCppSimHeader circuit
  let impl := CppSim.toCppSimImpl circuit
  IO.FS.writeFile s!"output/cpp_sim/{circuit.name}.h" header
  IO.FS.writeFile s!"output/cpp_sim/{circuit.name}.cpp" impl

end Shoumei.RISCV.Memory.Cache
