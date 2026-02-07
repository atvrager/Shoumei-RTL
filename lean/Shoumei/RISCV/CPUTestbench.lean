/-
RISCV/CPUTestbench.lean - Testbench Configuration for CPU_RV32IM

Maps the CPU_RV32IM circuit's ports to semantic memory interfaces
for automatic testbench generation.

Port mapping (from CPU.lean mkCPU_RV32IM):
  Inputs:  clock, reset, zero, one, imem_resp_data[31:0],
           dmem_req_ready, dmem_resp_valid, dmem_resp_data[31:0]
  Outputs: fetch_pc[31:0], fetch_stalled, global_stall_out,
           dmem_req_valid, dmem_req_we, dmem_req_addr[31:0],
           dmem_req_data[31:0], rob_empty
-/

import Shoumei.Codegen.Testbench
import Shoumei.RISCV.CPU

namespace Shoumei.RISCV.CPUTestbench

open Shoumei.Codegen.Testbench
open Shoumei.RISCV.CPU

/-- Testbench configuration for the RV32IM CPU.
    Maps fetch_pc → instruction memory read address,
    dmem_req_* → data memory request interface. -/
def cpuTestbenchConfig : TestbenchConfig := {
  circuit := mkCPU_RV32IM
  imemPort := {
    addrSignal := "fetch_pc"
    dataInSignal := some "imem_resp_data"
  }
  dmemPort := {
    addrSignal := "dmem_req_addr"
    dataOutSignal := some "dmem_req_data"
    validSignal := some "dmem_req_valid"
    readySignal := some "dmem_req_ready"
    weSignal := some "dmem_req_we"
    respValidSignal := some "dmem_resp_valid"
    respDataSignal := some "dmem_resp_data"
  }
  memSizeWords := 16384    -- 64KB
  tohostAddr := 0x1000
  timeoutCycles := 100000
  constantPorts := [("zero", false), ("one", true)]
  tbName := some "tb_cpu"
}

end Shoumei.RISCV.CPUTestbench
