/-
CPU Behavioral Model - Pipeline State Types and Step Function

Extracted from CPU.lean. Contains:
- RVVI queue types (PCQueue, InsnQueue)
- DecodeState, CPUState structures
- cpuStep: one-cycle pipeline orchestration (7 stages)
-/

import Shoumei.RISCV.Config
import Shoumei.RISCV.Fetch
import Shoumei.RISCV.Decoder
import Shoumei.RISCV.Renaming.RenameStage
import Shoumei.RISCV.Execution.ReservationStation
import Shoumei.RISCV.Execution.Dispatch
import Shoumei.RISCV.Execution.IntegerExecUnit
import Shoumei.RISCV.Execution.BranchExecUnit
import Shoumei.RISCV.Execution.MemoryExecUnit
import Shoumei.RISCV.Execution.MulDivExecUnit
import Shoumei.RISCV.Execution.FPExecUnit
import Shoumei.RISCV.Retirement.ROB
import Shoumei.RISCV.Retirement.Queue16x32
import Shoumei.RISCV.Memory.LSU
import Shoumei.RISCV.CDBMux
import Shoumei.RISCV.CPUControl

namespace Shoumei.RISCV.CPU

open Shoumei.RISCV
open Shoumei.RISCV.Control
open Shoumei.RISCV.Execution
open Shoumei.RISCV.Renaming
open Shoumei.RISCV.Retirement (ROBState CommittedRATState)
open Shoumei.RISCV.Memory (LSUState)

/-
RVVI-TRACE Infrastructure (Future Cosimulation)

These queues track PC and instruction words alongside ROB entries.
Written at ROB allocation, read at ROB commit for RVVI output.
-/

/-- PC queue: stores fetch PC alongside each ROB entry.
    Indexed by ROB slot, allocated/freed in lockstep with ROB. -/
structure PCQueue where
  /-- Array of PCs, indexed by ROB slot (0-15) -/
  entries : Fin 16 → UInt32

def PCQueue.init : PCQueue :=
  { entries := fun _ => 0 }

/-- Write PC to queue at ROB allocation -/
def PCQueue.write (queue : PCQueue) (idx : Fin 16) (pc : UInt32) : PCQueue :=
  { queue with entries := fun i => if i == idx then pc else queue.entries i }

/-- Read PC from queue at ROB commit -/
def PCQueue.read (queue : PCQueue) (idx : Fin 16) : UInt32 :=
  queue.entries idx

/-- Instruction word queue: stores encoding alongside each ROB entry.
    Indexed by ROB slot, allocated/freed in lockstep with ROB. -/
structure InsnQueue where
  /-- Array of instruction words, indexed by ROB slot (0-15) -/
  entries : Fin 16 → UInt32

def InsnQueue.init : InsnQueue :=
  { entries := fun _ => 0 }

/-- Write instruction word to queue at ROB allocation -/
def InsnQueue.write (queue : InsnQueue) (idx : Fin 16) (insn : UInt32) : InsnQueue :=
  { queue with entries := fun i => if i == idx then insn else queue.entries i }

/-- Read instruction word from queue at ROB commit -/
def InsnQueue.read (queue : InsnQueue) (idx : Fin 16) : UInt32 :=
  queue.entries idx

/-
Decode Stage State

Simple wrapper around fetched instruction. In the behavioral model,
decode is purely combinational (happens within the same cycle).
PC is tracked alongside the instruction for branch target calculation.
-/

/--
Decode Stage State — N-slot (superscalar).

Holds up to N decoded instructions per cycle.
For N=1: fetchedInstrs = [some instr] (or [none] for bubble).
For N=2: fetchedInstrs = [some i0, some i1] (2nd = none if only 1 fetched).
-/
structure DecodeState where
  /-- Fetched instruction words (one per slot). -/
  fetchedInstrs : List (Option UInt32)
  /-- Decoded instructions (one per slot). -/
  decodedInstrs : List (Option DecodedInstruction)
  /-- Program counters per slot (PC, PC+4, ...) -/
  pcs : List UInt32
  /-- Dispatch width for this decode group (how many slots are valid) -/
  dispatchWidth : Nat
deriving Repr

-- Backwards-compatible aliases for single-slot access
def DecodeState.fetchedInstr (ds : DecodeState) : Option UInt32 := ds.fetchedInstrs.head?.join
def DecodeState.decodedInstr  (ds : DecodeState) : Option DecodedInstruction := ds.decodedInstrs.head?.join
def DecodeState.pc            (ds : DecodeState) : UInt32 := ds.pcs.headD 0

def DecodeState.empty : DecodeState :=
  { fetchedInstrs  := [none]
    decodedInstrs  := [none]
    pcs            := [0]
    dispatchWidth  := 1 }

/-
Top-Level CPU State

Composes all pipeline stages, reservation stations, and control state.
Config-parameterized for M extension enable/disable.
-/

structure CPUState (config : CPUConfig) where
  -- ==== Pipeline Front-End ====
  /-- Fetch stage state -/
  fetch : FetchState
  /-- Decode stage state -/
  decode : DecodeState
  /-- Rename stage state (RAT + FreeList + PhysRegFile) -/
  rename : RenameStageState

  -- ==== Reservation Stations ====
  /-- Integer ALU reservation station (4 entries) -/
  rsInteger : RSState 4
  /-- Memory (load/store) reservation station (4 entries) -/
  rsMemory : RSState 4
  /-- Branch reservation station (4 entries) -/
  rsBranch : RSState 4
  /-- MulDiv reservation station (4 entries, only if M extension enabled) -/
  rsMulDiv : if config.enableM then RSState 4 else Unit
  /-- FP reservation station (4 entries, only if F extension enabled) -/
  rsFPExec : if config.enableF then RSState 4 else Unit

  -- ==== Back-End ====
  /-- Reorder Buffer (16 entries) -/
  rob : ROBState
  /-- Load-Store Unit with store buffer -/
  lsu : LSUState
  /-- Committed RAT for flush recovery -/
  committedRAT : CommittedRATState

  -- ==== Execution Unit State ====
  /-- MulDiv execution state (pipelined multiplier + divider, only if M extension enabled) -/
  mulDivExecState : if config.enableM then MulDivExecState else Unit
  /-- FP execution state (multi-cycle div/sqrt, only if F extension enabled) -/
  fpExecState : if config.enableF then FPExecState else Unit

  -- ==== FCSR State (F extension) ====
  /-- Floating-point exception flags (fflags CSR 0x001): NV|DZ|OF|UF|NX -/
  fflags : UInt32 := 0
  /-- Floating-point rounding mode (frm CSR 0x002): 3 bits -/
  frm : UInt32 := 0

  -- ==== RVVI Infrastructure (Future Cosimulation) ====
  /-- PC queue for RVVI-TRACE output -/
  pcQueue : PCQueue
  /-- Instruction word queue for RVVI-TRACE output -/
  insnQueue : InsnQueue

  -- ==== Control State ====
  /-- Global stall signal (pipeline frozen) -/
  globalStall : Bool
  /-- Flush in progress (branch misprediction recovery) -/
  flushing : Bool
  /-- FENCE.I draining: pipeline drain in progress for instruction fence -/
  fenceIDraining : Bool
  /-- PC of the FENCE.I instruction (for redirect to PC+4 after drain) -/
  fenceIPC : UInt32
  /-- Cycle counter for simulation statistics -/
  cycleCount : Nat

/-
CPU Initialization

Initialize all pipeline stages to empty/reset state.
Uses config.entryPoint for fetch PC initialization.
-/

def CPUState.init (config : CPUConfig) : CPUState config :=
  let mulDivRS : if config.enableM then RSState 4 else Unit :=
    if h : config.enableM then
      cast (by simp [h]) (RSState.init 4)
    else
      cast (by simp [h]) ()
  let mulDivExec : if config.enableM then MulDivExecState else Unit :=
    if h : config.enableM then
      cast (by simp [h]) MulDivExecState.init
    else
      cast (by simp [h]) ()
  let fpRS : if config.enableF then RSState 4 else Unit :=
    if h : config.enableF then
      cast (by simp [h]) (RSState.init 4)
    else
      cast (by simp [h]) ()
  let fpExec : if config.enableF then FPExecState else Unit :=
    if h : config.enableF then
      cast (by simp [h]) FPExecState.init
    else
      cast (by simp [h]) ()
  { fetch := FetchState.init config.entryPoint
    decode := DecodeState.empty
    rename := RenameStageState.init
    rsInteger := RSState.init 4
    rsMemory := RSState.init 4
    rsBranch := RSState.init 4
    rsMulDiv := mulDivRS
    rsFPExec := fpRS
    rob := ROBState.empty
    lsu := LSUState.empty
    committedRAT := CommittedRATState.init
    mulDivExecState := mulDivExec
    fpExecState := fpExec
    pcQueue := PCQueue.init
    insnQueue := InsnQueue.init
    globalStall := false
    flushing := false
    fenceIDraining := false
    fenceIPC := 0
    cycleCount := 0 }

/-
Helper Functions for CPU State Queries
-/

/-- Check if CPU is idle (no instructions in pipeline) -/
def CPUState.isIdle (cpu : CPUState config) : Bool :=
  ROBState.isEmpty cpu.rob &&
  cpu.decode.decodedInstr.isNone &&
  cpu.fetch.fetchedInstr.isNone &&
  !cpu.fenceIDraining

/-- Get current cycle count -/
def CPUState.getCycleCount (cpu : CPUState config) : Nat :=
  cpu.cycleCount

/-- Get current PC -/
def CPUState.getPC (cpu : CPUState config) : UInt32 :=
  cpu.fetch.pc

/-
CPU Step Function - Pipeline Orchestration

Executes one cycle of the entire Tomasulo pipeline. Stages execute in
REVERSE ORDER (commit → fetch) to avoid structural hazards and simplify
data dependencies.

Stage order: Commit → Execute → CDB Snoop → Dispatch → Rename → Decode → Fetch

This is a simplified behavioral model focusing on correctness.
Decoder integration deferred (requires static instruction definitions).
-/

/-- CDB Broadcast Entry: tag + data from execution unit -/
structure CDBBroadcast where
  valid : Bool
  tag : Fin 64
  data : UInt32
  exception : Bool := false
  mispredicted : Bool := false

/-- Execute one CPU cycle.

    Full pipeline orchestration with all stages.
    Decoder integration deferred (cpuStepWithDecoder will add it).

    Parameters:
    - cpu: Current CPU state
    - imem: Instruction memory function
    - decodedInstr: Optional decoded instruction (for testing, will be automated later)

    Returns: Updated CPU state
-/
def cpuStep
    (cpu : CPUState config)
    (imem : SimpleIMem)
    (decodedInstr : Option DecodedInstruction := none)
    : CPUState config :=

  -- ========== STAGE 7: ROB COMMIT ==========
  -- Commit head entry if complete, update committedRAT, deallocate old phys reg
  let commitResult := if cpu.rob.isEmpty then
      none
    else
      let headEntry := cpu.rob.entries cpu.rob.head
      if headEntry.valid && headEntry.complete then
        some (headEntry.archRd, headEntry.physRd, headEntry.oldPhysRd,
              headEntry.hasPhysRd, headEntry.hasOldPhysRd,
              headEntry.exception, headEntry.isBranch, headEntry.branchMispredicted)
      else
        none

  let (rob_afterCommit, rename_afterCommit, flushPC) := match commitResult with
    | none => (cpu.rob, cpu.rename, none)
    | some (archRd, physRd, oldPhysRd, hasPhysRd, hasOldPhysRd, exception, isBranch, mispredicted) =>
        -- Advance ROB head
        -- Note: count must be > 0 since we have a valid entry, but proving this requires ROB invariants
        -- For behavioral model, we use a conservative bound check
        let newCount := if cpu.rob.count > 0 then cpu.rob.count - 1 else 0
        let newCountBound : newCount <= 16 := by
          unfold newCount
          by_cases h : cpu.rob.count > 0
          · simp [h]
            have := cpu.rob.h_count
            omega
          · simp [h]
        let rob' := { cpu.rob with
          head := ⟨(cpu.rob.head.val + 1) % 16, by omega⟩
          count := newCount
          h_count := newCountBound
          entries := fun i => if i == cpu.rob.head then Retirement.ROBEntry.empty else cpu.rob.entries i
        }

        -- Update committedRAT if has destination
        let rename' := if hasPhysRd && archRd.val ≠ 0 then
          { cpu.rename with
            rat := cpu.rename.rat.allocate archRd physRd }
        else
          cpu.rename

        -- Deallocate old physical register if applicable
        let rename'' := if hasOldPhysRd then
          { rename' with freeList := rename'.freeList.deallocate oldPhysRd }
        else
          rename'

        -- Check for flush (exception or branch misprediction)
        let flush := if exception || (isBranch && mispredicted) then
          some cpu.fetch.pc  -- Simplified: would compute actual target
        else
          none

        (rob', rename'', flush)

  -- ========== FLUSH HANDLING ==========
  -- If commit triggered flush, clear pipeline and RS
  let (rob_postFlush, rename_postFlush, rsInteger_postFlush, rsMemory_postFlush,
       rsBranch_postFlush, rsMulDiv_postFlush, rsFPExec_postFlush,
       decode_postFlush, globalStall_postFlush) :=
    match flushPC with
    | some _ =>
        -- Clear all speculative state
        let robEmpty := ROBState.empty
        let renameRestored := cpu.rename  -- In real impl, would restore from committedRAT
        let rsIntEmpty := RSState.init 4
        let rsMemEmpty := RSState.init 4
        let rsBrEmpty := RSState.init 4
        let rsMulDivEmpty : if config.enableM then RSState 4 else Unit :=
          if h : config.enableM then
            cast (by rw [if_pos h]) (RSState.init 4)
          else
            cast (by rw [if_neg h]) ()
        let rsFPExecEmpty : if config.enableF then RSState 4 else Unit :=
          if h : config.enableF then
            cast (by rw [if_pos h]) (RSState.init 4)
          else
            cast (by rw [if_neg h]) ()
        let decodeEmpty := DecodeState.empty
        (robEmpty, renameRestored, rsIntEmpty, rsMemEmpty, rsBrEmpty, rsMulDivEmpty, rsFPExecEmpty, decodeEmpty, false)
    | none =>
        (rob_afterCommit, rename_afterCommit, cpu.rsInteger, cpu.rsMemory,
         cpu.rsBranch, cpu.rsMulDiv, cpu.rsFPExec, cpu.decode, cpu.globalStall)

  -- ========== STAGE 6: EXECUTE & CDB BROADCAST ==========

  -- MulDiv execution state update (only if M extension enabled)
  -- Must be computed before CDB broadcasts to be available for final state assembly
  let (mulDivExecState', mulDivBC) := if h : config.enableM then
      let rs : RSState 4 := cast (by rw [if_pos h]) rsMulDiv_postFlush
      let execState : MulDivExecState := cast (by rw [if_pos h]) cpu.mulDivExecState

      -- Check if RS has ready instruction to dispatch
      match rs.selectReady with
      | some idx =>
          let (_, dispatchResult) := rs.dispatch idx
          match dispatchResult with
          | some (opcode, src1, src2, _src3, destTag, _immediate, _pc) =>
              -- Use mulDivStep with proper state tracking
              let op := Execution.opTypeToMulDivOpcode opcode
              let (newExecState, result) := Execution.mulDivStep execState src1 src2 destTag op true
              let broadcast := match result with
                | some (tag, data) => [{ valid := true, tag := tag, data := data, exception := false, mispredicted := false }]
                | none => []
              (cast (by rw [if_pos h]) newExecState, broadcast)
          | none =>
              -- No dispatch, but still step the exec state (to advance pipelines)
              let (newExecState, result) := Execution.mulDivStep execState 0 0 0 0 false
              let broadcast := match result with
                | some (tag, data) => [{ valid := true, tag := tag, data := data, exception := false, mispredicted := false }]
                | none => []
              (cast (by rw [if_pos h]) newExecState, broadcast)
      | none =>
          -- No ready instruction, still step exec state
          let (newExecState, result) := Execution.mulDivStep execState 0 0 0 0 false
          let broadcast := match result with
            | some (tag, data) => [{ valid := true, tag := tag, data := data, exception := false, mispredicted := false }]
            | none => []
          (cast (by rw [if_pos h]) newExecState, broadcast)
    else
      (cpu.mulDivExecState, [])

  -- FP execution state update (only if F extension enabled)
  -- Returns (newExecState, cdbBroadcasts, newFflags)
  let (fpExecState', fpBC, fflags') := if h : config.enableF then
      let rs : RSState 4 := cast (by rw [if_pos h]) rsFPExec_postFlush
      let execState : FPExecState := cast (by rw [if_pos h]) cpu.fpExecState
      -- Decode frm CSR to RoundingMode
      let rm : Shoumei.Circuits.Combinational.FPU.RoundingMode :=
        match cpu.frm.toNat with
        | 1 => .RTZ | 2 => .RDN | 3 => .RUP | 4 => .RMM | _ => .RNE

      match rs.selectReady with
      | some idx =>
          let (_, dispatchResult) := rs.dispatch idx
          match dispatchResult with
          | some (opcode, src1, src2, src3, destTag, _immediate, _pc) =>
              let (newExecState, result) := Execution.fpExecStep execState opcode src1 src2 src3 rm destTag true
              let (broadcast, newFflags) := match result with
                | some (tag, data, exceptions) =>
                    ([{ valid := true, tag := tag, data := data, exception := false, mispredicted := false }],
                     cpu.fflags ||| exceptions.toBits)
                | none => ([], cpu.fflags)
              (cast (by rw [if_pos h]) newExecState, broadcast, newFflags)
          | none =>
              let (newExecState, result) := Execution.fpExecStep execState .ADD 0 0 0 .RNE 0 false
              let (broadcast, newFflags) := match result with
                | some (tag, data, exceptions) =>
                    ([{ valid := true, tag := tag, data := data, exception := false, mispredicted := false }],
                     cpu.fflags ||| exceptions.toBits)
                | none => ([], cpu.fflags)
              (cast (by rw [if_pos h]) newExecState, broadcast, newFflags)
      | none =>
          let (newExecState, result) := Execution.fpExecStep execState .ADD 0 0 0 .RNE 0 false
          let (broadcast, newFflags) := match result with
            | some (tag, data, exceptions) =>
                ([{ valid := true, tag := tag, data := data, exception := false, mispredicted := false }],
                 cpu.fflags ||| exceptions.toBits)
            | none => ([], cpu.fflags)
          (cast (by rw [if_pos h]) newExecState, broadcast, newFflags)
    else
      (cpu.fpExecState, [], cpu.fflags)

  -- Select ready entries from each RS and execute
  -- Returns CDB broadcasts and optional branch redirect target
  let (cdbBroadcasts, branchRedirectTarget) : (List CDBBroadcast × Option UInt32) :=
    -- Integer RS execution (ALU operations)
    -- Uses verified IntegerExecUnit (executeInteger)
    let intBC : List CDBBroadcast := match rsInteger_postFlush.selectReady with
      | some idx =>
          let (_, dispatchResult) := rsInteger_postFlush.dispatch idx
          match dispatchResult with
          | some (opcode, src1, src2, _src3, destTag, _immediate, _pc) =>
              let (_, result) := Execution.executeInteger opcode src1 src2 destTag
              [{ valid := true, tag := destTag, data := result, exception := false, mispredicted := false }]
          | none => []
      | none => []

    -- Memory RS execution (loads/stores)
    -- Uses verified MemoryExecUnit (calculateMemoryAddress) with proper immediate values
    let memBC : List CDBBroadcast := match rsMemory_postFlush.selectReady with
      | some idx =>
          let (_, dispatchResult) := rsMemory_postFlush.dispatch idx
          match dispatchResult with
          | some (opcode, src1, _src2, _src3, destTag, immediate, _pc) =>
              -- Use proper immediate value from RS entry
              let offset : Int := immediate.getD 0
              let addr := Execution.calculateMemoryAddress src1 offset
              -- TODO: Full LSU integration with executeLoad/executeStore, store buffer, forwarding
              [{ valid := true, tag := destTag, data := addr, exception := false, mispredicted := false }]
          | none => []
      | none => []

    -- Branch RS execution
    -- Uses verified BranchExecUnit (evaluateBranchCondition and executeBranch)
    let (branchBC, branchRedirect) : (List CDBBroadcast × Option UInt32) := match rsBranch_postFlush.selectReady with
      | some idx =>
          let (_, dispatchResult) := rsBranch_postFlush.dispatch idx
          match dispatchResult with
          | some (opcode, src1, src2, _src3, destTag, immediate, pc) =>
              -- Use proper branch condition evaluation from BranchExecUnit
              let offset : Int := immediate.getD 0
              let branchResult := Execution.executeBranch opcode src1 src2 pc offset destTag
              -- Broadcast link register value (PC+4) for JAL/JALR
              let result := pc + 4
              -- If branch was taken, return target for redirect
              let redirect := if branchResult.taken then some branchResult.target_pc else none
              ([{ valid := true, tag := destTag, data := result, exception := false, mispredicted := branchResult.taken }], redirect)
          | none => ([], none)
      | none => ([], none)

    (intBC ++ memBC ++ branchBC ++ mulDivBC ++ fpBC, branchRedirect)

  -- ========== UPDATE RS AFTER DISPATCH ==========
  -- Dispatch clears the dispatched entries from RS
  let rsInteger_postExec := match rsInteger_postFlush.selectReady with
    | some idx => rsInteger_postFlush.dispatch idx |>.1
    | none => rsInteger_postFlush

  let rsMemory_postExec := match rsMemory_postFlush.selectReady with
    | some idx => rsMemory_postFlush.dispatch idx |>.1
    | none => rsMemory_postFlush

  let rsBranch_postExec := match rsBranch_postFlush.selectReady with
    | some idx => rsBranch_postFlush.dispatch idx |>.1
    | none => rsBranch_postFlush

  let rsMulDiv_postExec := if h : config.enableM then
      let rs : RSState 4 := cast (by rw [if_pos h]) rsMulDiv_postFlush
      let rs' := match rs.selectReady with
        | some idx => rs.dispatch idx |>.1
        | none => rs
      cast (by rw [if_pos h]) rs'
    else
      rsMulDiv_postFlush

  let rsFPExec_postExec := if h : config.enableF then
      let rs : RSState 4 := cast (by rw [if_pos h]) rsFPExec_postFlush
      let rs' := match rs.selectReady with
        | some idx => rs.dispatch idx |>.1
        | none => rs
      cast (by rw [if_pos h]) rs'
    else
      rsFPExec_postFlush

  -- ========== CDB WRITEBACK TO PHYSREGFILE ==========
  -- Write execution results to physical register file (both int and FP)
  -- TODO: Separate int/FP CDB buses; for now all broadcasts go to both PRFs
  let rename_postExecute := cdbBroadcasts.foldl (fun (ren : RenameStageState) (bc : CDBBroadcast) =>
    if bc.valid then
      { ren with
        physRegFile := ren.physRegFile.write bc.tag bc.data
        fpPhysRegFile := ren.fpPhysRegFile.write bc.tag bc.data }
    else
      ren
  ) rename_postFlush

  -- ========== STAGE 5: CDB SNOOP ==========
  -- All RS and ROB snoop CDB broadcasts in parallel
  let rob_postCDB := cdbBroadcasts.foldl (fun (rob : ROBState) (bc : CDBBroadcast) =>
    if bc.valid then
      rob.cdbBroadcast bc.tag bc.exception bc.mispredicted
    else
      rob
  ) rob_postFlush

  let rsInteger_postCDB := cdbBroadcasts.foldl (fun (rs : RSState 4) (bc : CDBBroadcast) =>
    if bc.valid then rs.cdbBroadcast bc.tag bc.data else rs
  ) rsInteger_postFlush

  let rsMemory_postCDB := cdbBroadcasts.foldl (fun (rs : RSState 4) (bc : CDBBroadcast) =>
    if bc.valid then rs.cdbBroadcast bc.tag bc.data else rs
  ) rsMemory_postFlush

  let rsBranch_postCDB := cdbBroadcasts.foldl (fun (rs : RSState 4) (bc : CDBBroadcast) =>
    if bc.valid then rs.cdbBroadcast bc.tag bc.data else rs
  ) rsBranch_postFlush

  let rsMulDiv_postCDB := if h : config.enableM then
      let rs := cast (by simp [h]) rsMulDiv_postFlush
      let rs' := cdbBroadcasts.foldl (fun (rs : RSState 4) (bc : CDBBroadcast) =>
        if bc.valid then rs.cdbBroadcast bc.tag bc.data else rs
      ) rs
      cast (by simp [h]) rs'
    else
      rsMulDiv_postFlush

  let rsFPExec_postCDB := if h : config.enableF then
      let rs := cast (by simp [h]) rsFPExec_postFlush
      let rs' := cdbBroadcasts.foldl (fun (rs : RSState 4) (bc : CDBBroadcast) =>
        if bc.valid then rs.cdbBroadcast bc.tag bc.data else rs
      ) rs
      cast (by simp [h]) rs'
    else
      rsFPExec_postFlush

  -- (Stages 3+4 RENAME and DISPATCH are now positioned AFTER stage 2+FENCE.I below,
  --  because they consume decode_postFenceI which is bound later.)
  -- Keep these binding names available for FENCE.I FSM's rob_postDispatch reference:
  let rob_preDispatch   := rob_postCDB
  let rename_preDispatch := rename_postExecute

  -- ========== STAGE 2: DECODE ==========
  -- Decode fetched instruction words into DecodedInstruction per slot
  let dispW := config.dispatchWidth
  let decode' : DecodeState :=
    match cpu.fetch.fetchedInstr with
    | none =>
        { fetchedInstrs := List.replicate dispW none
          decodedInstrs := List.replicate dispW none
          pcs := (List.range dispW).map fun k => cpu.fetch.pc - 4 + (k.toUInt32 * 4)
          dispatchWidth := dispW }
    | some instr =>
        -- Primary slot: use provided/auto-decoded instruction
        let di0 := decodedInstr
        -- Secondary slot: in behavioral model, TODO plumb second fetch
        -- For now: second slot bubble (will be filled in by Fetch widening)
        let di1 : Option DecodedInstruction := none
        let allDI := if dispW >= 2 then [di0, di1] else [di0]
        { fetchedInstrs := [some instr] ++ List.replicate (dispW - 1) none
          decodedInstrs := allDI
          pcs := (List.range dispW).map fun k => cpu.fetch.pc - 4 + (k.toUInt32 * 4)
          dispatchWidth := dispW }

  -- ========== FENCE.I SERIALIZATION FSM ==========
  -- Detect FENCE.I in any decoded slot
  let fenceIDetected := decode'.decodedInstrs.any fun mdi =>
    mdi.map (fun di => di.opType == .FENCE_I) |>.getD false

  -- FSM transitions:
  -- idle + FENCE.I detected → draining (stall fetch, wait for ROB + SB empty)
  -- draining + ROB empty + SB empty → complete (redirect fetch to PC+4, resume)
  -- Uses rob_preDispatch for FENCE.I drain check (before dispatch happens)
  let robEmpty := rob_preDispatch.isEmpty
  let sbEmpty := cpu.lsu.storeBuffer.isEmpty
  let drainComplete := cpu.fenceIDraining && robEmpty && sbEmpty

  let fenceIDraining' := if fenceIDetected && !cpu.fenceIDraining then
    true   -- Start draining
  else if drainComplete then
    false  -- Drain complete, resume
  else
    cpu.fenceIDraining  -- Hold current state

  let fenceIPC' := if fenceIDetected && !cpu.fenceIDraining then
    decode'.pc  -- Capture PC of FENCE.I instruction
  else
    cpu.fenceIPC

  -- When draining, suppress the FENCE.I from entering the pipeline
  let decode_postFenceI := if fenceIDetected && !cpu.fenceIDraining then
    -- Squash the decoded FENCE.I (don't let it enter rename/dispatch)
    DecodeState.empty
  else if cpu.fenceIDraining then
    -- While draining, keep decode empty
    DecodeState.empty
  else
    decode'

  -- FENCE.I redirect: when drain completes, redirect fetch to FENCE.I PC + 4
  let fenceIRedirect := if drainComplete then
    some (cpu.fenceIPC + 4)
  else
    none

  -- ========== STAGE 3+4: RENAME + DISPATCH (consumes decode_postFenceI) ==========
  let (rename_postRename, renamedInstrs) : (RenameStageState × List (Option RenamedInstruction)) :=
    let validInstrs := decode_postFenceI.decodedInstrs.filterMap id
    if validInstrs.isEmpty then
      (rename_preDispatch, decode_postFenceI.decodedInstrs.map fun _ => none)
    else
      let (st', results, _stalled) := renameInstructionGroup rename_preDispatch validInstrs
      (st', results)

  let prf := rename_postRename.physRegFile
  let isBranchOp := fun op => Execution.classifyToUnit op config == .Branch
  let (rob_postDispatch, rsInteger_postDispatch, rsMemory_postDispatch,
       rsBranch_postDispatch, rsMulDiv_postDispatch, rsFPExec_postDispatch) :=
    renamedInstrs.foldl
      (fun (rob, rsInt, rsMem, rsBr, rsMD, rsFP) optRI =>
        match optRI with
        | none => (rob, rsInt, rsMem, rsBr, rsMD, rsFP)
        | some ri =>
            let physRd  := ri.physRd.getD ⟨0, by omega⟩
            let hasPhRd := ri.physRd.isSome
            let oldPhRd := ri.oldPhysRd.getD ⟨0, by omega⟩
            let hasOPR  := ri.oldPhysRd.isSome
            let archRd  : Fin 32 := ⟨0, by omega⟩  -- placeholder; add archRd to RenamedInstruction later
            let isBr    := isBranchOp ri.opType
            let (rob', robIdx?) := rob.allocate
              physRd hasPhRd oldPhRd hasOPR archRd ri.opType.hasFpRd isBr
            match robIdx? with
            | none => (rob, rsInt, rsMem, rsBr, rsMD, rsFP)
            | some _idx =>
                match Execution.classifyToUnit ri.opType config with
                | .Integer =>
                    let (rsInt', _) := rsInt.issue ri prf; (rob', rsInt', rsMem, rsBr, rsMD, rsFP)
                | .Branch =>
                    let (rsBr', _) := rsBr.issue ri prf;  (rob', rsInt, rsMem, rsBr', rsMD, rsFP)
                | .Memory =>
                    let (rsMem', _) := rsMem.issue ri prf; (rob', rsInt, rsMem', rsBr, rsMD, rsFP)
                | .MulDiv =>
                    if h : config.enableM then
                      let rs : RSState 4 := cast (by rw [if_pos h]) rsMD
                      let (rs', _) := rs.issue ri prf
                      (rob', rsInt, rsMem, rsBr, cast (by rw [if_pos h]) rs', rsFP)
                    else (rob', rsInt, rsMem, rsBr, rsMD, rsFP)
                | .FPExec =>
                    if h : config.enableF then
                      let rs : RSState 4 := cast (by rw [if_pos h]) rsFP
                      let (rs', _) := rs.issue ri prf
                      (rob', rsInt, rsMem, rsBr, rsMD, cast (by rw [if_pos h]) rs')
                    else (rob', rsInt, rsMem, rsBr, rsMD, rsFP)
                | .System | .Illegal => (rob', rsInt, rsMem, rsBr, rsMD, rsFP)
      )
      (rob_preDispatch,
       rsInteger_postCDB, rsMemory_postCDB, rsBranch_postCDB,
       rsMulDiv_postCDB, rsFPExec_postCDB)

  -- ========== STAGE 1: FETCH ==========
  let stall := globalStall_postFlush || fenceIDraining'
  -- Priority: FENCE.I redirect > branch redirect from execution > flush from commit
  let branchRedirect := match fenceIRedirect with
    | some target => some target
    | none => match branchRedirectTarget with
      | some target => some target
      | none => flushPC
  let fetch' := fetchStep cpu.fetch imem stall branchRedirect

  -- ========== ASSEMBLE FINAL STATE ==========
  { cpu with
    fetch := fetch'
    decode := decode_postFenceI
    rename := rename_postRename
    rsInteger := rsInteger_postDispatch
    rsMemory := rsMemory_postDispatch
    rsBranch := rsBranch_postDispatch
    rsMulDiv := rsMulDiv_postDispatch
    rsFPExec := rsFPExec_postDispatch
    rob := rob_postDispatch
    mulDivExecState := mulDivExecState'
    fpExecState := fpExecState'
    fflags := fflags'
    globalStall := globalStall_postFlush
    flushing := flushPC.isSome
    fenceIDraining := fenceIDraining'
    fenceIPC := fenceIPC'
    cycleCount := cpu.cycleCount + 1 }

end Shoumei.RISCV.CPU
