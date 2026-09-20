/-
RISCV/CPUTestbench.lean - Testbench Configuration for CachedCPU

Maps the CachedCPU circuit's ports to the 256-bit cache-line memory interface
for automatic testbench generation.
-/

import Shoumei.Codegen.Testbench
import Shoumei.RISCV.Config
import Shoumei.RISCV.Memory.Cache.CachedCPU

namespace Shoumei.RISCV.CPUTestbench

open Shoumei.Codegen.Testbench
open Shoumei.RISCV.Memory.Cache

/-- Testbench configuration for a configured CachedCPU (CPU + L1I/L1D/L2).
    Uses a cache-line memory interface instead of separate IMEM/DMEM; the line
    width follows the cache geometry. -/
def cpuTestbenchConfigFor (config : CPUConfig) (tbName : String) : TestbenchConfig := {
  circuit := mkCachedCPU config
  imemPort := { addrSignal := "unused" }
  dmemPort := { addrSignal := "unused" }
  cacheLineMemPort := some {
    reqValidSignal := "mem_req_valid"
    reqAddrSignal := "mem_req_addr"
    reqWeSignal := "mem_req_we"
    reqDataSignal := "mem_req_data"
    respValidSignal := "mem_resp_valid"
    respDataSignal := "mem_resp_data"
    lineWords := config.cacheGeom.lineWords
  }
  tbName := some tbName
  memSizeWords := config.memSizeWords
  tohostAddr := 0x1000
  putcharAddr := some 0x1004
  timeoutCycles := config.timeoutCycles
  spikeIsa := config.spikeIsa
}

/-- Testbench configuration for the default CachedCPU. -/
def cpuTestbenchConfig : TestbenchConfig := cpuTestbenchConfigFor defaultCPUConfig "tb_cpu"

end Shoumei.RISCV.CPUTestbench
