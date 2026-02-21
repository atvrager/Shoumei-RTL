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
  circuit := mkCachedCPU defaultCPUConfig
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
  vecMemPort := if defaultCPUConfig.enableVector then some {
    reqValidSignal := "vec_dmem_req_valid"
    reqWeSignal := "vec_dmem_req_we"
    reqAddrSignal := "vec_dmem_req_addr"
    reqDataSignal := "vec_dmem_req_data"
    reqSizeSignal := "vec_dmem_req_size"
    reqReadySignal := "vec_dmem_req_ready"
    respValidSignal := "vec_dmem_resp_valid"
    respDataSignal := "vec_dmem_resp_rdata"
  } else none
  constantPorts := [("zero", false), ("one", true)]
  tbName := some "tb_cpu"
  memSizeWords := defaultCPUConfig.memSizeWords
  tohostAddr := 0x1000
  putcharAddr := some 0x1004
  timeoutCycles := defaultCPUConfig.timeoutCycles
  spikeIsa := defaultCPUConfig.spikeIsa
}

end Shoumei.RISCV.CachedCPUTestbench
