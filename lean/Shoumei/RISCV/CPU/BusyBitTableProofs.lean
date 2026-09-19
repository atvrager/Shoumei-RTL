/-
RISCV/CPU/BusyBitTableProofs.lean - Structural proofs for Scoreboard Busy Bit Tables
-/

import Shoumei.RISCV.CPU.BusyBitTable

namespace Shoumei.RISCV.CPU.BusyBitTableProofs

open Shoumei
open Shoumei.RISCV.CPU

/-- Verify BusyTable_W2 module name -/
theorem busyTable_w2_name : mkBusyTable_W2.name = "BusyTable_W2" := by
  rfl

/-- Verify BusyTable_W2 instance count (4 Decoder6 + 64 DFlipFlop) -/
theorem busyTable_w2_instances : mkBusyTable_W2.instances.length = 68 := by
  native_decide

/-- Verify BusyTable_W2 port counts -/
theorem busyTable_w2_ports : mkBusyTable_W2.inputs.length = 66 ∧ mkBusyTable_W2.outputs.length = 8 := by
  native_decide

/-- Verify FPBusyTable module name -/
theorem fpBusyTable_name : mkFPBusyTable.name = "FPBusyTable" := by
  rfl

/-- Verify FPBusyTable instance count (2 Decoder6 + 64 DFlipFlop) -/
theorem fpBusyTable_instances : mkFPBusyTable.instances.length = 66 := by
  native_decide

/-- Verify FPBusyTable port counts -/
theorem fpBusyTable_ports : mkFPBusyTable.inputs.length = 44 ∧ mkFPBusyTable.outputs.length = 3 := by
  native_decide

end Shoumei.RISCV.CPU.BusyBitTableProofs
