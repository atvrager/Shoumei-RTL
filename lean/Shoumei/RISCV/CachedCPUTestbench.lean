/-
RISCV/CachedCPUTestbench.lean - Testbench Configuration for CachedCPU

Maps the CachedCPU circuit's ports to the 256-bit cache-line memory interface
for automatic testbench generation.
-/

import Shoumei.Codegen.Testbench
import Shoumei.RISCV.Config
import Shoumei.RISCV.Memory.Cache.CachedCPU

namespace Shoumei.RISCV.CachedCPUTestbench

open Shoumei.Codegen.Testbench
open Shoumei.RISCV.Memory.Cache

/-- Testbench configuration for the CachedCPU (CPU + L1I/L1D/L2).
    Uses 256-bit cache-line memory interface instead of separate IMEM/DMEM. -/
def cachedCpuTestbenchConfig : TestbenchConfig := {
  circuit := mkCachedCPU rv32imfConfig
  imemPort := { addrSignal := "unused" }
  dmemPort := { addrSignal := "unused" }
  cacheLineMemPort := some {
    reqValidSignal := "mem_req_valid"
    reqAddrSignal := "mem_req_addr"
    reqWeSignal := "mem_req_we"
    reqDataSignal := "mem_req_data"
    respValidSignal := "mem_resp_valid"
    respDataSignal := "mem_resp_data"
  }
  constantPorts := [("zero", false), ("one", true)]
  tbName := some "tb_cached_cpu"
  memSizeWords := 16384    -- 64KB
  tohostAddr := 0x1000
  putcharAddr := some 0x1004
  timeoutCycles := 100000
  spikeIsa := "rv32imf_zicsr_zifencei"
}

end Shoumei.RISCV.CachedCPUTestbench
