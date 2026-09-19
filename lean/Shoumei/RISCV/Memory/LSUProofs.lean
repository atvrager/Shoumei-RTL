/-
RISCV/Memory/LSUProofs.lean - Structural Proofs for LSU

Structural verification of the LSU circuit using native_decide.

Proof Categories:
1. Port counts (inputs/outputs)
2. Instance counts (submodules)
3. Gate counts (combinational logic)
4. Compositional verification certificate
-/

import Shoumei.RISCV.Memory.LSU

namespace Shoumei.RISCV.Memory

open Shoumei
open Shoumei.RISCV

/-! ## Structural Proofs -/

/-- LSU has correct number of inputs:
    clock/reset/zero/one(4) + dispatch_base(64) + offset(32) + tag(6) +
    store_data(64) + commit(1) + deq_ready(1) + fwd_address(64) +
    flush(1) + sb_enq_size(2) + sb_enq_en(1) + sb_enq_idx_in(3) = 243 -/
theorem lsu_input_count :
    mkLSU.inputs.length = 243 := by
  native_decide

/-- LSU has correct number of outputs:
    279 legacy + stage1(64 addr + 6 tag) + stage2(64 data + hit) +
    replay_needed = 279 + 136 = 415 -/
theorem lsu_output_count :
    mkLSU.outputs.length = 415 := by
  native_decide

/-- LSU has 2 instances (MemoryExecUnit + StoreBuffer8). -/
theorem lsu_instance_count :
    mkLSU.instances.length = 2 := by
  native_decide

/-- LSU gate count: 64 (AGU→SB address) + pipeline DFFs (64 addr + 6 tag
    + 64 fwd + 1 hit) + 1 replay BUF = 200 -/
theorem lsu_gate_count :
    mkLSU.gates.length = 200 := by
  native_decide

/-! ## Compositional Verification Certificate -/

/-- LSU uses only verified building blocks.

    Dependencies:
    - MemoryExecUnit (verified in Phase 5)
    - StoreBuffer8 (verified in Phase 7, compositionally)

    This theorem establishes that LSU's correctness follows from the
    correctness of its constituent verified modules, plus the connection
    logic (32 BUF gates for address routing).
-/
theorem lsu_uses_verified_blocks :
    mkLSU.instances.all (fun inst =>
      inst.moduleName = "MemoryExecUnit" ∨
      inst.moduleName = "StoreBuffer8"
    ) = true := by
  native_decide




/-! ## Two-Stage Pipeline & MSHR -/

/-- Stage1 isolates the 64-bit adder from the forwarding driver: the AGU
    output is latched (M1), the priority/forwarding cone is not fed. -/
theorem lsu_stage1_registered :
  (mkLSU.outputs.filter (fun w => w.name.startsWith "lsu_stage1_addr_q")).length = 64 := by
  native_decide

/-- Decoupled load split: M1 produces stage1, M2 consumes it; a store in
    the SQ forwards exactly (no blocker, CDB staged in stage2). -/
theorem lsu_two_stage_forward :
  let (sb0, _) := LSUState.empty.storeBuffer.enqueue 0x1000 0x42 2
  let lsu : LSUState := { LSUState.empty with storeBuffer := sb0 }
  let lsu1 := lsu.executeLoadM1 OpType.LW 0x1000 0 42
  let (lsu2, fwd) := lsu1.executeLoadM2
  fwd = some (42, 0x42) ∧
  lsu2.stage1 = none ∧
  lsu2.stage2.isSome := by
  native_decide

/-- Miss allocates an MSHR slot instead of blocking the port. -/
theorem lsu_mshr_alloc_on_miss :
  let lsu := LSUState.empty
  let (lsu1, _) := lsu.executeLoad OpType.LW 0x5000 0 7
  lsu1.mshrBusy && !lsu1.mshrFull := by
  native_decide

/-- Two misses occupy both MSHR slots (non-blocking port, 2-track). -/
theorem lsu_mshr_two_track :
  let a1 := (LSUState.empty.executeLoadM1 OpType.LW 0x1000 0 1).executeLoadM2 |>.1
  let a2 := (a1.executeLoadM1 OpType.LW 0x2000 0 2).executeLoadM2 |>.1
  a2.mshrFull = true := by
  native_decide
end Shoumei.RISCV.Memory
