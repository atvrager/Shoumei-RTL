/-
SoC/ShoumeiSoCProofs.lean - Structural Verification for Shoumei SoC
-/

import Shoumei.SoC.ShoumeiSoC
import Shoumei.RISCV.Config

namespace Shoumei.SoC

open Shoumei
open Shoumei.RISCV

/-- Shoumei SoC preserves hierarchy. -/
theorem shoumei_soc_keeps_hierarchy :
    (mkShoumeiSoC defaultCPUConfig).keepHierarchy = true := by native_decide

/-- Shoumei SoC contains exactly 9 submodules:
    ResetSync, CachedCPU, TLXbar8, BootROM, ACLINT, APLIC, UART, GPIO, SRAM. -/
theorem shoumei_soc_instance_count :
    (mkShoumeiSoC defaultCPUConfig).instances.length = 9 := by native_decide

/-- Shoumei SoC top-level glue logic gate count. -/
theorem shoumei_soc_gate_count :
    (mkShoumeiSoC defaultCPUConfig).gates.length = 258 := by native_decide

/-- Shoumei SoC primary inputs count:
    clock, reset_n, zero, one, uart_rx, mem_resp_valid (6)
    + 8 gpio_i + 256 mem_resp_data = 270 inputs. -/
theorem shoumei_soc_inputs_count :
    (mkShoumeiSoC defaultCPUConfig).inputs.length = 270 := by native_decide

/-- Shoumei SoC primary outputs count:
    uart_tx, rob_empty, mem_req_valid, mem_req_we (4)
    + 32 mem_req_addr + 256 mem_req_data + 8 gpio_o + 8 gpio_oen = 308 outputs. -/
theorem shoumei_soc_outputs_count :
    (mkShoumeiSoC defaultCPUConfig).outputs.length = 308 := by native_decide

end Shoumei.SoC
