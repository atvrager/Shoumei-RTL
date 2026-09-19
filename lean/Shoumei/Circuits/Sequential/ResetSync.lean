/-
Circuits/Sequential/ResetSync.lean - Asynchronous-Assert Synchronous-Deassert Reset Synchronizer

A 2-stage D-flip-flop synchronizer:
- Asynchronous assert: any low pulse on `async_reset_n` immediately forces the output low.
- Synchronous deassert: when `async_reset_n` is released high, `sync_reset_n` rises cleanly
  on the 2nd clock edge, preventing recovery/removal timing violations and metastability.
-/

import Shoumei.DSL
import Shoumei.Circuits.Sequential.DFF

namespace Shoumei.Circuits.Sequential

open Shoumei

/-- 2-stage Reset Synchronizer circuit. -/
def mkResetSync : Circuit :=
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let one := Wire.mk "one"
  let sync_reset := Wire.mk "sync_reset"
  let stage1_q := Wire.mk "rst_sync_stage1"
  let stage2_q := Wire.mk "rst_sync_stage2"
  let not_stage2 := Wire.mk "not_stage2"

  { name := "ResetSync"
    inputs := [clock, reset, one]
    outputs := [sync_reset]
    gates := [
      Gate.mkDFF one clock reset stage1_q,
      Gate.mkDFF stage1_q clock reset stage2_q,
      Gate.mkNOT stage2_q not_stage2,
      Gate.mkBUF not_stage2 sync_reset
    ]
    instances := []
  }

def resetSyncCircuit : Circuit := mkResetSync

end Shoumei.Circuits.Sequential
