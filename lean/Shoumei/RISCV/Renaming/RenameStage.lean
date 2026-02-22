/-
RISCV/Renaming/RenameStage.lean - Register Renaming Stage

Integrates RAT + FreeList + PhysRegFile into a composite RenameStage that
transforms decoded instructions (architectural register references) into
renamed instructions (physical register tags).

Design:
- Behavioral model: Composes RATState, FreeListState, PhysRegFileState
- Structural circuit: Instantiates RAT_32x6, FreeList_64, PhysRegFile_64x32
- Handles x0 special case (never allocate, never update RAT)
- Stalls when FreeList is empty and allocation is needed
- Tracks old physical register mapping for ROB retirement

Core operation:
1. RAT lookup rs1 → physRs1, RAT lookup rs2 → physRs2
2. If instruction has rd AND rd != x0: FreeList allocate → newPhysRd
3. If allocation succeeded: save old mapping, RAT update rd → newPhysRd
4. If FreeList empty and rd needed: stall (return None)
5. x0 special: never allocate, never update RAT, physRd = None
-/

import Shoumei.DSL
import Shoumei.RISCV.Decoder
import Shoumei.RISCV.ISA
import Shoumei.RISCV.Renaming.RAT
import Shoumei.RISCV.Renaming.FreeList
import Shoumei.RISCV.Renaming.BitmapFreeList
import Shoumei.RISCV.Renaming.PhysRegFile

namespace Shoumei.RISCV.Renaming

open Shoumei
open Shoumei.RISCV
/-! ## RenamedInstruction Type -/

/-- Renamed instruction with physical register tags.
    Output of register renaming stage, ready for dispatch to execution units. -/
structure RenamedInstruction where
  /-- Operation type (ADD, SUB, etc.) - pass-through from DecodedInstruction -/
  opType : OpType
  /-- Physical destination register tag (None for x0 or no-dest instructions) -/
  physRd : Option (Fin 64)
  /-- Physical source register 1 tag (from RAT lookup) -/
  physRs1 : Option (Fin 64)
  /-- Physical source register 2 tag (from RAT lookup) -/
  physRs2 : Option (Fin 64)
  /-- Physical source register 3 tag (from RAT lookup, R4-type FP fused ops) -/
  physRs3 : Option (Fin 64) := none
  /-- Rounding mode (from decoded instruction, F extension) -/
  rm : Option (Fin 8) := none
  /-- Immediate value - pass-through from DecodedInstruction -/
  imm : Option Int
  /-- Previous physical register mapped to rd (for ROB retirement/deallocation) -/
  oldPhysRd : Option (Fin 64)
  /-- Program counter - for branch target calculation and RVVI tracking -/
  pc : UInt32
  deriving Repr

/-- Default RenamedInstruction for Inhabited instance -/
instance : Inhabited RenamedInstruction where
  default := {
    opType := .ADD
    physRd := none
    physRs1 := none
    physRs2 := none
    physRs3 := none
    rm := none
    imm := none
    oldPhysRd := none
    pc := 0
  }

/-! ## Behavioral Model -/

/-- RenameStage state: composite of RAT, FreeList, and PhysRegFile
    for both integer and floating-point register files -/
structure RenameStageState where
  /-- Integer Register Alias Table: arch int reg → phys int reg mapping -/
  rat : RATState 64
  /-- Integer Free List: pool of available physical integer registers -/
  freeList : FreeListState 64
  /-- Integer Physical Register File: storage for 64 physical registers -/
  physRegFile : PhysRegFileState 64
  /-- FP Register Alias Table: arch FP reg → phys FP reg mapping -/
  fpRat : RATState 64 := RATState.init (by omega)
  /-- FP Free List: pool of available physical FP registers -/
  fpFreeList : FreeListState 64 := mkFreeList64Init
  /-- FP Physical Register File: storage for 64 physical FP registers -/
  fpPhysRegFile : PhysRegFileState 64 := PhysRegFileState.init 64

/-- Initialize RenameStage with identity RAT mapping, FreeList with regs 32-63 free,
    and PhysRegFile all zeros (both integer and FP) -/
def RenameStageState.init : RenameStageState :=
  { rat := RATState.init (by omega)           -- Identity mapping (0→0, 1→1, ..., 31→31)
    freeList := mkFreeList64Init              -- Registers 32-63 free
    physRegFile := PhysRegFileState.init 64   -- All zeros
    fpRat := RATState.init (by omega)         -- FP identity mapping
    fpFreeList := mkFreeList64Init            -- FP registers 32-63 free
    fpPhysRegFile := PhysRegFileState.init 64 -- FP all zeros
  }

/-- Core rename operation: transform DecodedInstruction → RenamedInstruction.
    Returns updated state and optionally renamed instruction (None = stall).
    FP-aware: uses integer or FP RAT/FreeList based on OpType classification. -/
def renameInstruction
    (state : RenameStageState)
    (instr : DecodedInstruction)
    : RenameStageState × Option RenamedInstruction :=
  let op := instr.opType
  -- 1. Lookup physical tags for source registers from appropriate RAT
  let physRs1 := instr.rs1.map (if op.hasFpRs1 then state.fpRat.lookup else state.rat.lookup)
  let physRs2 := instr.rs2.map (if op.hasFpRs2 then state.fpRat.lookup else state.rat.lookup)
  let physRs3 := instr.rs3.map state.fpRat.lookup  -- rs3 is always FP (R4-type)

  -- 2. Handle destination register (if exists and not x0)
  let useFpDest := op.hasFpRd
  match instr.rd with
  | none =>
      -- No destination (branches, stores, etc.)
      (state, some {
        opType := op
        physRd := none
        physRs1 := physRs1
        physRs2 := physRs2
        physRs3 := physRs3
        rm := instr.rm
        imm := instr.imm
        oldPhysRd := none
        pc := instr.pc
      })
  | some rd =>
      if !useFpDest && rd.val = 0 then
        -- x0 special case: never allocate, never update RAT (FP has no x0 equiv)
        (state, some {
          opType := op
          physRd := none
          physRs1 := physRs1
          physRs2 := physRs2
          physRs3 := physRs3
          rm := instr.rm
          imm := instr.imm
          oldPhysRd := none
          pc := instr.pc
        })
      else if useFpDest then
        -- FP destination: allocate from FP free list and update FP RAT
        let oldPhysRd := state.fpRat.lookup rd
        let (fpFreeList', newPhysRd) := state.fpFreeList.allocate
        match newPhysRd with
        | none => (state, none)  -- Stall: no free FP physical registers
        | some physRd =>
            let fpRat' := state.fpRat.allocate rd physRd
            ({ state with fpRat := fpRat', fpFreeList := fpFreeList' },
             some {
               opType := op
               physRd := some physRd
               physRs1 := physRs1
               physRs2 := physRs2
               physRs3 := physRs3
               rm := instr.rm
               imm := instr.imm
               oldPhysRd := some oldPhysRd
               pc := instr.pc
             })
      else
        -- Integer destination: allocate from integer free list and update integer RAT
        let oldPhysRd := state.rat.lookup rd
        let (freeList', newPhysRd) := state.freeList.allocate
        match newPhysRd with
        | none => (state, none)  -- Stall: no free integer physical registers
        | some physRd =>
            let rat' := state.rat.allocate rd physRd
            ({ state with rat := rat', freeList := freeList' },
             some {
               opType := op
               physRd := some physRd
               physRs1 := physRs1
               physRs2 := physRs2
               physRs3 := physRs3
               rm := instr.rm
               imm := instr.imm
               oldPhysRd := some oldPhysRd
               pc := instr.pc
             })

/-- Rename a sequence of instructions, threading state through.
    Returns final state and list of renamed instructions (None for stalls). -/
def renameSequence
    (state : RenameStageState)
    (instrs : List DecodedInstruction)
    : RenameStageState × List (Option RenamedInstruction) :=
  instrs.foldl (fun (st, results) instr =>
    let (st', result) := renameInstruction st instr
    (st', results ++ [result])
  ) (state, [])

/-- N-wide group rename for superscalar dispatch.

    Renames `N` instructions IN PROGRAM ORDER, threading the RAT state through
    each slot so that intra-group forwarding is handled correctly:
    - Slot[k] sees rd writes from all slots[0..k-1] in the same group
    - This is the behavioral model equivalent of the N-1 bypass MUXes in hardware

    Stall policy: **all-or-nothing**.
    If slot[k] stalls (FreeList empty when it needs a physRd), all slots[k+1..N-1]
    also return None, and the state is rolled back to before the failing slot.
    This simplifies dispatch logic (the CPU never has a half-renamed group).

    Returns: (updated state, results list of length N, stalled: Bool)
    - results[k] = some ri  → slot k renamed OK
    - results[k] = none     → slot k stalled (all subsequent are also none)
    - stalled = true        → at least one slot stalled; state may be partial
-/
def renameInstructionGroup
    (state : RenameStageState)
    (instrs : List DecodedInstruction)
    : RenameStageState × List (Option RenamedInstruction) × Bool :=
  -- Thread state through each slot. On first stall, stop and fill remaining with None.
  let (finalState, results, stalled) :=
    instrs.foldl (fun (st, results, stalledSoFar) instr =>
      if stalledSoFar then
        -- Already stalled — propagate None without touching state
        (st, results ++ [none], true)
      else
        -- Try to rename this slot with current state
        let stateBeforeThisSlot := st
        let (st', result) := renameInstruction st instr
        match result with
        | none =>
            -- Stall on this slot — roll back to state before this slot
            (stateBeforeThisSlot, results ++ [none], true)
        | some ri =>
            (st', results ++ [some ri], false)
    ) (state, [], false)
  -- If stalled, revert to original state (no partial updates escape)
  let outState := if stalled then state else finalState
  (outState, results, stalled)

/-- Convenience wrapper: rename exactly 2 instructions (N=2 dual-dispatch). -/
def renameInstructionPair
    (state : RenameStageState)
    (i0 i1 : DecodedInstruction)
    : RenameStageState × Option RenamedInstruction × Option RenamedInstruction × Bool :=
  let (st', results, stalled) := renameInstructionGroup state [i0, i1]
  let r0 := results.head?.join
  let r1 := results.tail.head?.join
  (st', r0, r1, stalled)


/-- Read operand values from physical register file (for dispatch to execution units).
    Returns pair of 32-bit values for the given physical register tags. -/
def readOperands
    (state : RenameStageState)
    (tag1 tag2 : Fin 64)
    : UInt32 × UInt32 :=
  state.physRegFile.readPair tag1 tag2

/-- CDB writeback: update physical register file with result from execution unit. -/
def writeBack
    (state : RenameStageState)
    (tag : Fin 64)
    (val : UInt32)
    : RenameStageState :=
  { state with physRegFile := state.physRegFile.write tag val }

/-- Retire instruction: deallocate old physical register back to free list.
    Called by ROB when instruction commits. -/
def retire
    (state : RenameStageState)
    (oldTag : Fin 64)
    : RenameStageState :=
  { state with freeList := state.freeList.deallocate oldTag }

/-! ## Structural Circuit -/

/-- Helper: Compute log2 ceiling -/
private def log2Ceil (n : Nat) : Nat :=
  if n <= 1 then 0
  else Nat.log2 n + (if 2^(Nat.log2 n) < n then 1 else 0)

/--
Build a RenameStage structural circuit.

Instantiates RAT, FreeList, and PhysRegFile as submodules with control glue logic.

Port interface:
- Inputs: clock, reset, zero, one, instr_valid, has_rd,
          rs1_addr[4:0], rs2_addr[4:0], rd_addr[4:0],
          cdb_valid, cdb_tag[5:0], cdb_data[31:0],
          retire_valid, retire_tag[5:0]
- Outputs: rename_valid, stall,
           rs1_phys[5:0], rs2_phys[5:0], rd_phys[5:0],
           rs1_data[31:0], rs2_data[31:0]

Architecture:
- RAT_32x6 instance for rs1/rs2 lookup and rd allocation
- FreeList_64 instance for physical register allocation
- PhysRegFile_64x32 instance for operand value storage
- Control logic: x0 detection, stall generation, handshaking
-/
def mkRenameStage : Circuit :=
  -- === W=2: Dual-issue RenameStage ===
  --
  -- Slot 0 keeps original port names (backwards compatible with W=1 test benches).
  -- Slot 1 adds a parallel set with suffix "_1".
  -- Two commit channels (commit_valid_0/1, commit_archRd_0/1, commit_physRd_0/1).
  -- Intra-group forwarding: slot 1's rs1/rs2 bypass slot 0's rd if addresses match.
  let tagWidth  := 6
  let archWidth := 5
  let dataWidth := 32

  -- === Global signals ===
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero  := Wire.mk "zero"
  let one   := Wire.mk "one"

  -- === Slot 0 instruction inputs (original names, backwards-compatible) ===
  let instr_valid_0  := Wire.mk "instr_valid"
  let has_rd_0       := Wire.mk "has_rd"
  let rs1_addr_0     := (List.range archWidth).map fun i => Wire.mk s!"rs1_addr_{i}"
  let rs2_addr_0     := (List.range archWidth).map fun i => Wire.mk s!"rs2_addr_{i}"
  let rs3_addr_0     := (List.range archWidth).map fun i => Wire.mk s!"rs3_addr_{i}"
  let rd_addr_0      := (List.range archWidth).map fun i => Wire.mk s!"rd_addr_{i}"
  let force_alloc_0  := Wire.mk "force_alloc"

  -- === Slot 1 instruction inputs ===
  let instr_valid_1  := Wire.mk "instr_valid_1"
  let has_rd_1       := Wire.mk "has_rd_1"
  let rs1_addr_1     := (List.range archWidth).map fun i => Wire.mk s!"rs1_addr_1_{i}"
  let rs2_addr_1     := (List.range archWidth).map fun i => Wire.mk s!"rs2_addr_1_{i}"
  let rs3_addr_1     := (List.range archWidth).map fun i => Wire.mk s!"rs3_addr_1_{i}"
  let rd_addr_1      := (List.range archWidth).map fun i => Wire.mk s!"rd_addr_1_{i}"
  let force_alloc_1  := Wire.mk "force_alloc_1"

  -- === Commit channel 0 ===
  let flush_en            := Wire.mk "flush_en"
  let commit_valid_0      := Wire.mk "commit_valid"
  let commit_archRd_0     := (List.range archWidth).map fun i => Wire.mk s!"commit_archRd_{i}"
  let commit_physRd_0     := (List.range tagWidth).map  fun i => Wire.mk s!"commit_physRd_{i}"
  let commit_hasPhysRd_0  := Wire.mk "commit_hasPhysRd"
  let commit_hasAllocSlot_0 := Wire.mk "commit_hasAllocSlot"

  -- === Commit channel 1 ===
  let commit_valid_1      := Wire.mk "commit_valid_1"
  let commit_archRd_1     := (List.range archWidth).map fun i => Wire.mk s!"commit_archRd_1_{i}"
  let commit_physRd_1     := (List.range tagWidth).map  fun i => Wire.mk s!"commit_physRd_1_{i}"
  let commit_hasPhysRd_1  := Wire.mk "commit_hasPhysRd_1"
  let commit_hasAllocSlot_1 := Wire.mk "commit_hasAllocSlot_1"

  -- === CDB / retire ===
  let cdb_valid_0  := Wire.mk "cdb_valid"
  let cdb_tag_0    := (List.range tagWidth).map  fun i => Wire.mk s!"cdb_tag_0_{i}"
  let cdb_data_0   := (List.range dataWidth).map fun i => Wire.mk s!"cdb_data_0_{i}"
  let cdb_valid_1  := Wire.mk "cdb_valid_1"
  let cdb_tag_1    := (List.range tagWidth).map  fun i => Wire.mk s!"cdb_tag_1_{i}"
  let cdb_data_1   := (List.range dataWidth).map fun i => Wire.mk s!"cdb_data_1_{i}"

  let retire_valid := Wire.mk "retire_valid"
  let retire_tag   := (List.range tagWidth).map fun i => Wire.mk s!"retire_tag_{i}"
  let rd_tag4      := (List.range tagWidth).map  fun i => Wire.mk s!"rd_tag4_{i}"
  let rd_data4     := (List.range dataWidth).map fun i => Wire.mk s!"rd_data4_{i}"

  -- === Slot 0 outputs ===
  let rs1_phys_out_0  := (List.range tagWidth).map fun i => Wire.mk s!"rs1_phys_out_{i}"
  let rs2_phys_out_0  := (List.range tagWidth).map fun i => Wire.mk s!"rs2_phys_out_{i}"
  let rs3_phys_out_0  := (List.range tagWidth).map fun i => Wire.mk s!"rs3_phys_out_{i}"
  let rd_phys_out_0   := (List.range tagWidth).map fun i => Wire.mk s!"rd_phys_out_{i}"
  let old_rd_phys_0   := (List.range tagWidth).map fun i => Wire.mk s!"old_rd_phys_out_{i}"
  let rename_valid_0  := Wire.mk "rename_valid"
  let stall_0         := Wire.mk "stall"
  let rs1_data_0      := (List.range dataWidth).map fun i => Wire.mk s!"rs1_data_{i}"
  let rs2_data_0      := (List.range dataWidth).map fun i => Wire.mk s!"rs2_data_{i}"
  let rd_data3_0      := (List.range dataWidth).map fun i => Wire.mk s!"rd_data3_{i}"

  -- === Slot 1 outputs ===
  let rs1_phys_out_1  := (List.range tagWidth).map fun i => Wire.mk s!"rs1_phys_out_1_{i}"
  let rs2_phys_out_1  := (List.range tagWidth).map fun i => Wire.mk s!"rs2_phys_out_1_{i}"
  let rs3_phys_out_1  := (List.range tagWidth).map fun i => Wire.mk s!"rs3_phys_out_1_{i}"
  let rd_phys_out_1   := (List.range tagWidth).map fun i => Wire.mk s!"rd_phys_out_1_{i}"
  let old_rd_phys_1   := (List.range tagWidth).map fun i => Wire.mk s!"old_rd_phys_out_1_{i}"
  let rename_valid_1  := Wire.mk "rename_valid_1"
  let stall_1         := Wire.mk "stall_1"
  let rs1_data_1      := (List.range dataWidth).map fun i => Wire.mk s!"rs1_data_1_{i}"
  let rs2_data_1      := (List.range dataWidth).map fun i => Wire.mk s!"rs2_data_1_{i}"

  -- === Internal: speculative RAT read/write wires ===
  let rs1_phys_0   := (List.range tagWidth).map fun i => Wire.mk s!"rs1p0_{i}"
  let rs2_phys_0   := (List.range tagWidth).map fun i => Wire.mk s!"rs2p0_{i}"
  let rs3_phys_0   := (List.range tagWidth).map fun i => Wire.mk s!"rs3p0_{i}"
  let rd_phys_0    := (List.range tagWidth).map fun i => Wire.mk s!"rdp0_{i}"
  let old_rd_raw_0 := (List.range tagWidth).map fun i => Wire.mk s!"old_rd_raw0_{i}"

  -- Slot 1: RAT reads from speculative RAT (after slot 0 write), with intra-group bypass
  let rs1_phys_1_rat := (List.range tagWidth).map fun i => Wire.mk s!"rs1p1_rat_{i}"
  let rs2_phys_1_rat := (List.range tagWidth).map fun i => Wire.mk s!"rs2p1_rat_{i}"
  let rs3_phys_1_rat := (List.range tagWidth).map fun i => Wire.mk s!"rs3p1_rat_{i}"
  let rd_phys_1      := (List.range tagWidth).map fun i => Wire.mk s!"rdp1_{i}"
  let old_rd_raw_1   := (List.range tagWidth).map fun i => Wire.mk s!"old_rd_raw1_{i}"

  -- === x0 detection (per slot) ===
  let rd_or_0 := (List.range archWidth).map fun i => Wire.mk s!"rd_or0_{i}"
  let rd_or_1 := (List.range archWidth).map fun i => Wire.mk s!"rd_or1_{i}"
  let x0_0    := Wire.mk "x0_det_0"
  let x0_1    := Wire.mk "x0_det_1"
  let x0_gates_0 :=
    [Gate.mkOR rd_addr_0[0]! rd_addr_0[1]! rd_or_0[0]!] ++
    (List.range 3).map (fun i => Gate.mkOR rd_or_0[i]! rd_addr_0[i+2]! rd_or_0[i+1]!) ++
    [Gate.mkNOT rd_or_0[3]! x0_0]
  let x0_gates_1 :=
    [Gate.mkOR rd_addr_1[0]! rd_addr_1[1]! rd_or_1[0]!] ++
    (List.range 3).map (fun i => Gate.mkOR rd_or_1[i]! rd_addr_1[i+2]! rd_or_1[i+1]!) ++
    [Gate.mkNOT rd_or_1[3]! x0_1]

  -- needs_alloc_{k} = has_rd_{k} AND NOT(x0_{k})
  let not_x0_0      := Wire.mk "not_x0_0"
  let not_x0_1      := Wire.mk "not_x0_1"
  let needs_alloc_0 := Wire.mk "needs_alloc_0"
  let needs_alloc_1 := Wire.mk "needs_alloc_1"
  let needs_alloc_gates :=
    [Gate.mkNOT x0_0 not_x0_0, Gate.mkAND has_rd_0 not_x0_0 needs_alloc_0,
     Gate.mkNOT x0_1 not_x0_1, Gate.mkAND has_rd_1 not_x0_1 needs_alloc_1]

  -- === FreeList W2 port wires ===
  let freelist_enq_ready := Wire.mk "fl_enq_ready"
  let alloc_avail_0 := Wire.mk "alloc_avail_0"
  let alloc_avail_1 := Wire.mk "alloc_avail_1"
  let fl_deq_data_0 := (List.range tagWidth).map fun i => Wire.mk s!"fl_deq0_{i}"
  let fl_deq_data_1 := (List.range tagWidth).map fun i => Wire.mk s!"fl_deq1_{i}"
  let fl_deq_ready_0 := Wire.mk "fl_deq_ready_0"
  let fl_deq_ready_1 := Wire.mk "fl_deq_ready_1"

  -- Stall: global stall if either slot needs alloc but it's unavailable
  let not_avail_0 := Wire.mk "not_avail_0"; let not_avail_1 := Wire.mk "not_avail_1"
  let stall_raw0  := Wire.mk "stall_raw_0"; let stall_raw1  := Wire.mk "stall_raw_1"
  let stall_any   := Wire.mk "stall_any"
  let stall_gates :=
    [Gate.mkNOT alloc_avail_0 not_avail_0,
     Gate.mkNOT alloc_avail_1 not_avail_1,
     Gate.mkAND needs_alloc_0 not_avail_0 stall_raw0,
     Gate.mkAND needs_alloc_1 not_avail_1 stall_raw1,
     Gate.mkOR  stall_raw0 stall_raw1 stall_any,
     Gate.mkBUF stall_any stall_0,
     Gate.mkBUF stall_any stall_1]

  -- rename_valid_{k} = instr_valid_{k} AND NOT stall_any
  let not_stall := Wire.mk "not_stall_w2"
  let rvalid_gates :=
    [Gate.mkNOT stall_any not_stall,
     Gate.mkAND instr_valid_0 not_stall rename_valid_0,
     Gate.mkAND instr_valid_1 not_stall rename_valid_1]

  -- allocate_fire_{k} = needs_alloc_{k} AND rename_valid_{k}
  let alloc_fire_0 := Wire.mk "alloc_fire_0"; let alloc_fire_1 := Wire.mk "alloc_fire_1"
  let ff0 := Wire.mk "ff_fire_0";  let ff1 := Wire.mk "ff_fire_1"
  let cnt0 := Wire.mk "counter_advance_0"; let cnt1 := Wire.mk "counter_advance_1"
  let fire_gates :=
    [Gate.mkAND needs_alloc_0 rename_valid_0 alloc_fire_0,
     Gate.mkAND force_alloc_0 rename_valid_0 ff0,
     Gate.mkOR  alloc_fire_0 ff0 cnt0,
     Gate.mkAND needs_alloc_1 rename_valid_1 alloc_fire_1,
     Gate.mkAND force_alloc_1 rename_valid_1 ff1,
     Gate.mkOR  alloc_fire_1 ff1 cnt1,
     Gate.mkBUF cnt0 fl_deq_ready_0,
     Gate.mkBUF cnt1 fl_deq_ready_1]

  let rat_we_0 := Wire.mk "rat_we_0"; let rat_we_1 := Wire.mk "rat_we_1"
  let rat_we_gates :=
    [Gate.mkBUF alloc_fire_0 rat_we_0, Gate.mkBUF alloc_fire_1 rat_we_1]

  let rd_phys_0_gates := (List.range tagWidth).map fun i =>
    Gate.mkAND fl_deq_data_0[i]! cnt0 rd_phys_0[i]!
  let rd_phys_1_gates := (List.range tagWidth).map fun i =>
    Gate.mkAND fl_deq_data_1[i]! cnt1 rd_phys_1[i]!

  -- === Intra-group bypass for slot 1 ===
  -- If rd_addr_0 == src_addr_1 AND rat_we_0: forward rd_phys_0 to slot 1's rs
  let mkBypass (pfx2 : String) (src_addr : List Wire) (rat_out : List Wire)
      : List Gate × List Wire :=
    let xors  := (List.range archWidth).map fun i => Wire.mk s!"{pfx2}_x{i}"
    let xnors := (List.range archWidth).map fun i => Wire.mk s!"{pfx2}_xn{i}"
    let xor_gates  := (List.range archWidth).map fun i =>
      Gate.mkXOR rd_addr_0[i]! src_addr[i]! xors[i]!
    let xnor_gates := (List.range archWidth).map fun i =>
      Gate.mkNOT xors[i]! xnors[i]!
    let a1 := Wire.mk s!"{pfx2}_a1"; let a2 := Wire.mk s!"{pfx2}_a2"
    let a3 := Wire.mk s!"{pfx2}_a3"; let eq := Wire.mk s!"{pfx2}_eq"
    let and_gates := [Gate.mkAND xnors[0]! xnors[1]! a1,
                      Gate.mkAND xnors[2]! xnors[3]! a2,
                      Gate.mkAND a1 a2 a3, Gate.mkAND a3 xnors[4]! eq]
    let bypass_active := Wire.mk s!"{pfx2}_ba"
    let ba_gate := Gate.mkAND eq rat_we_0 bypass_active
    let mux_outs := (List.range tagWidth).map fun i => Wire.mk s!"{pfx2}_o{i}"
    let mux_gates := (List.range tagWidth).map fun i =>
      Gate.mkMUX rat_out[i]! rd_phys_0[i]! bypass_active mux_outs[i]!
    (xor_gates ++ xnor_gates ++ and_gates ++ [ba_gate] ++ mux_gates, mux_outs)

  let (bypass_rs1_gates, rs1_phys_1) := mkBypass "bp_rs1" rs1_addr_1 rs1_phys_1_rat
  let (bypass_rs2_gates, rs2_phys_1) := mkBypass "bp_rs2" rs2_addr_1 rs2_phys_1_rat

  -- === Committed RAT write-enable per channel ===
  let mkCratWe (pfx2 : String) (v : Wire) (arch : List Wire) (hasPR : Wire) : List Gate × Wire :=
    let or1 := Wire.mk s!"{pfx2}_cor1"; let or2 := Wire.mk s!"{pfx2}_cor2"
    let or3 := Wire.mk s!"{pfx2}_cor3"; let or4 := Wire.mk s!"{pfx2}_cor4"
    let is_x0 := Wire.mk s!"{pfx2}_is_x0"; let not_x0w := Wire.mk s!"{pfx2}_nx0"
    let vh := Wire.mk s!"{pfx2}_vh";  let we := Wire.mk s!"{pfx2}_we"
    ([Gate.mkOR arch[0]! arch[1]! or1, Gate.mkOR or1 arch[2]! or2,
      Gate.mkOR or2 arch[3]! or3, Gate.mkOR or3 arch[4]! or4,
      Gate.mkNOT or4 is_x0, Gate.mkNOT is_x0 not_x0w,
      Gate.mkAND v hasPR vh, Gate.mkAND vh not_x0w we], we)

  let (crat_we_gates_0, crat_we_0) := mkCratWe "c0" commit_valid_0 commit_archRd_0 commit_hasPhysRd_0
  let (crat_we_gates_1, crat_we_1) := mkCratWe "c1" commit_valid_1 commit_archRd_1 commit_hasPhysRd_1

  let crat_alloc_0 := Wire.mk "commit_alloc_adv_0"
  let crat_alloc_1 := Wire.mk "commit_alloc_adv_1"
  let crat_alloc_gates :=
    [Gate.mkAND commit_valid_0 commit_hasAllocSlot_0 crat_alloc_0,
     Gate.mkAND commit_valid_1 commit_hasAllocSlot_1 crat_alloc_1]

  let crat_dump := (List.range 32).map fun i =>
    (List.range tagWidth).map fun j => Wire.mk s!"crat_dump_{i}_{j}"

  -- === Sub-instances ===

  -- Dual committed RAT (daisy-chained): crat_0 (commit_0) → crat_1 (commit_1)
  let crat_mid_dump := (List.range 32).map fun i =>
    (List.range tagWidth).map fun j => Wire.mk s!"crat_mid_{i}_{j}"
  let crat_0_inst : CircuitInstance := {
    moduleName := "RAT_32x6"
    instName := "u_crat_0"
    portMap :=
      [("clock", clock), ("reset", reset), ("write_en", crat_we_0)] ++
      (commit_archRd_0.enum.map fun ⟨i,w⟩ => (s!"write_addr_{i}", w)) ++
      (commit_physRd_0.enum.map fun ⟨i,w⟩ => (s!"write_data_{i}", w)) ++
      ((List.range archWidth).map fun i => (s!"rs1_addr_{i}", zero)) ++
      ((List.range archWidth).map fun i => (s!"rs2_addr_{i}", zero)) ++
      ((List.range archWidth).map fun i => (s!"rs3_addr_{i}", zero)) ++
      ((List.range tagWidth).map fun i => (s!"rs1_data_{i}", Wire.mk s!"c0_rs1u_{i}")) ++
      ((List.range tagWidth).map fun i => (s!"rs2_data_{i}", Wire.mk s!"c0_rs2u_{i}")) ++
      ((List.range tagWidth).map fun i => (s!"rs3_data_{i}", Wire.mk s!"c0_rs3u_{i}")) ++
      ((List.range tagWidth).map fun i => (s!"old_rd_data_{i}", Wire.mk s!"c0_oldu_{i}")) ++
      [("restore_en", zero)] ++
      ((List.range 32).map fun i => (List.range tagWidth).map fun j =>
        (s!"restore_data_{i}_{j}", zero)).flatten ++
      ((List.range 32).map fun i => (List.range tagWidth).map fun j =>
        (s!"dump_data_{i}_{j}", crat_mid_dump[i]![j]!)).flatten
  }
  let crat_1_inst : CircuitInstance := {
    moduleName := "RAT_32x6"
    instName := "u_crat_1"
    portMap :=
      [("clock", clock), ("reset", reset), ("write_en", crat_we_1)] ++
      (commit_archRd_1.enum.map fun ⟨i,w⟩ => (s!"write_addr_{i}", w)) ++
      (commit_physRd_1.enum.map fun ⟨i,w⟩ => (s!"write_data_{i}", w)) ++
      ((List.range archWidth).map fun i => (s!"rs1_addr_{i}", zero)) ++
      ((List.range archWidth).map fun i => (s!"rs2_addr_{i}", zero)) ++
      ((List.range archWidth).map fun i => (s!"rs3_addr_{i}", zero)) ++
      ((List.range tagWidth).map fun i => (s!"rs1_data_{i}", Wire.mk s!"c1_rs1u_{i}")) ++
      ((List.range tagWidth).map fun i => (s!"rs2_data_{i}", Wire.mk s!"c1_rs2u_{i}")) ++
      ((List.range tagWidth).map fun i => (s!"rs3_data_{i}", Wire.mk s!"c1_rs3u_{i}")) ++
      ((List.range tagWidth).map fun i => (s!"old_rd_data_{i}", Wire.mk s!"c1_oldu_{i}")) ++
      [("restore_en", zero)] ++
      ((List.range 32).map fun i => (List.range tagWidth).map fun j =>
        (s!"restore_data_{i}_{j}", zero)).flatten ++
      ((List.range 32).map fun i => (List.range tagWidth).map fun j =>
        (s!"dump_data_{i}_{j}", crat_dump[i]![j]!)).flatten
  }

  -- Speculative RAT: daisy-chained to support two write ports (slot 0 → slot 1)
  let srat_0_dump := (List.range 32).map fun i =>
    (List.range tagWidth).map fun j => Wire.mk s!"srat0_dump_{i}_{j}"
  let rat_inst_0 : CircuitInstance := {
    moduleName := "RAT_32x6"
    instName := "u_rat_0"
    portMap :=
      [("clock", clock), ("reset", reset), ("write_en", rat_we_0)] ++
      (rd_addr_0.enum.map fun ⟨i,w⟩ => (s!"write_addr_{i}", w)) ++
      (rd_phys_0.enum.map fun ⟨i,w⟩ => (s!"write_data_{i}", w)) ++
      (rs1_addr_0.enum.map fun ⟨i,w⟩ => (s!"rs1_addr_{i}", w)) ++
      (rs2_addr_0.enum.map fun ⟨i,w⟩ => (s!"rs2_addr_{i}", w)) ++
      (rs3_addr_0.enum.map fun ⟨i,w⟩ => (s!"rs3_addr_{i}", w)) ++
      (rs1_phys_0.enum.map fun ⟨i,w⟩ => (s!"rs1_data_{i}", w)) ++
      (rs2_phys_0.enum.map fun ⟨i,w⟩ => (s!"rs2_data_{i}", w)) ++
      (rs3_phys_0.enum.map fun ⟨i,w⟩ => (s!"rs3_data_{i}", w)) ++
      (old_rd_raw_0.enum.map fun ⟨i,w⟩ => (s!"old_rd_data_{i}", w)) ++
      [("restore_en", flush_en)] ++
      ((List.range 32).map fun i => (List.range tagWidth).map fun j =>
        (s!"restore_data_{i}_{j}", crat_dump[i]![j]!)).flatten ++
      ((List.range 32).map fun i => (List.range tagWidth).map fun j =>
        (s!"dump_data_{i}_{j}", srat_0_dump[i]![j]!)).flatten
  }
  let rat_inst_1 : CircuitInstance := {
    moduleName := "RAT_32x6"
    instName := "u_rat_1"
    portMap :=
      [("clock", clock), ("reset", reset), ("write_en", rat_we_1)] ++
      (rd_addr_1.enum.map fun ⟨i,w⟩ => (s!"write_addr_{i}", w)) ++
      (rd_phys_1.enum.map fun ⟨i,w⟩ => (s!"write_data_{i}", w)) ++
      (rs1_addr_1.enum.map fun ⟨i,w⟩ => (s!"rs1_addr_{i}", w)) ++
      (rs2_addr_1.enum.map fun ⟨i,w⟩ => (s!"rs2_addr_{i}", w)) ++
      (rs3_addr_1.enum.map fun ⟨i,w⟩ => (s!"rs3_addr_{i}", w)) ++
      (rs1_phys_1_rat.enum.map fun ⟨i,w⟩ => (s!"rs1_data_{i}", w)) ++
      (rs2_phys_1_rat.enum.map fun ⟨i,w⟩ => (s!"rs2_data_{i}", w)) ++
      (rs3_phys_1_rat.enum.map fun ⟨i,w⟩ => (s!"rs3_data_{i}", w)) ++
      (old_rd_raw_1.enum.map fun ⟨i,w⟩ => (s!"old_rd_data_{i}", w)) ++
      [("restore_en", flush_en)] ++
      -- Slot 1 RAT restores from slot 0's dump (post-slot0-write state)
      ((List.range 32).map fun i => (List.range tagWidth).map fun j =>
        (s!"restore_data_{i}_{j}", srat_0_dump[i]![j]!)).flatten ++
      ((List.range 32).map fun i => (List.range tagWidth).map fun j =>
        (s!"dump_data_{i}_{j}", Wire.mk s!"srat1_dump_{i}_{j}")).flatten
  }

  -- BitmapFreeList W2 instance
  let freelist_inst : CircuitInstance := {
    moduleName := "BitmapFreeList_64_W2"
    instName := "u_freelist"
    portMap :=
      [("clock", clock), ("reset", reset), ("zero", zero), ("one", one)] ++
      (retire_tag.enum.map fun ⟨i,w⟩ => (s!"enq_data_{i}", w)) ++
      [("enq_valid", retire_valid),
       ("deq_ready_0", fl_deq_ready_0), ("deq_ready_1", fl_deq_ready_1)] ++
      (fl_deq_data_0.enum.map fun ⟨i,w⟩ => (s!"deq_data_0_{i}", w)) ++
      [("deq_valid_0", alloc_avail_0)] ++
      (fl_deq_data_1.enum.map fun ⟨i,w⟩ => (s!"deq_data_1_{i}", w)) ++
      [("deq_valid_1", alloc_avail_1),
       ("enq_ready", freelist_enq_ready),
       ("flush_en", flush_en),
       ("commit_alloc_en", crat_alloc_0)] ++
      (commit_physRd_0.enum.map fun ⟨i,w⟩ => (s!"commit_alloc_tag_{i}", w))
  }

  -- PhysRegFile (shared, dual write port from CDB)
  let physregfile_inst : CircuitInstance := {
    moduleName := "PhysRegFile_64x32"
    instName := "u_prf"
    portMap :=
      [("clock", clock), ("reset", reset),
       ("wr_en_0", cdb_valid_0), ("wr_en_1", cdb_valid_1)] ++
      (rs1_phys_0.enum.map fun ⟨i,w⟩ => (s!"rd_tag1_{i}", w)) ++
      (rs2_phys_0.enum.map fun ⟨i,w⟩ => (s!"rd_tag2_{i}", w)) ++
      (rs1_phys_1.enum.map fun ⟨i,w⟩ => (s!"rd_tag3_{i}", w)) ++
      (rs2_phys_1.enum.map fun ⟨i,w⟩ => (s!"rd_tag4_{i}", w)) ++
      (cdb_tag_0.enum.map fun ⟨i,w⟩ => (s!"wr_tag_0_{i}", w)) ++
      (cdb_data_0.enum.map fun ⟨i,w⟩ => (s!"wr_data_0_{i}", w)) ++
      (cdb_tag_1.enum.map fun ⟨i,w⟩ => (s!"wr_tag_1_{i}", w)) ++
      (cdb_data_1.enum.map fun ⟨i,w⟩ => (s!"wr_data_1_{i}", w)) ++
      (rs1_data_0.enum.map fun ⟨i,w⟩ => (s!"rd_data1_{i}", w)) ++
      (rs2_data_0.enum.map fun ⟨i,w⟩ => (s!"rd_data2_{i}", w)) ++
      (rs1_data_1.enum.map fun ⟨i,w⟩ => (s!"rd_data3_{i}", w)) ++
      (rs2_data_1.enum.map fun ⟨i,w⟩ => (s!"rd_data4_{i}", w))
  }

  -- Output buffer gates
  let out_gates_0 :=
    (List.range tagWidth).map (fun i => Gate.mkBUF rs1_phys_0[i]! rs1_phys_out_0[i]!) ++
    (List.range tagWidth).map (fun i => Gate.mkBUF rs2_phys_0[i]! rs2_phys_out_0[i]!) ++
    (List.range tagWidth).map (fun i => Gate.mkBUF rs3_phys_0[i]! rs3_phys_out_0[i]!) ++
    (List.range tagWidth).map (fun i => Gate.mkBUF rd_phys_0[i]!  rd_phys_out_0[i]!) ++
    (List.range tagWidth).map (fun i => Gate.mkBUF old_rd_raw_0[i]! old_rd_phys_0[i]!)
  let out_gates_1 :=
    (List.range tagWidth).map (fun i => Gate.mkBUF rs1_phys_1[i]! rs1_phys_out_1[i]!) ++
    (List.range tagWidth).map (fun i => Gate.mkBUF rs2_phys_1[i]! rs2_phys_out_1[i]!) ++
    (List.range tagWidth).map (fun i => Gate.mkBUF rs3_phys_1_rat[i]! rs3_phys_out_1[i]!) ++
    (List.range tagWidth).map (fun i => Gate.mkBUF rd_phys_1[i]!  rd_phys_out_1[i]!) ++
    (List.range tagWidth).map (fun i => Gate.mkBUF old_rd_raw_1[i]! old_rd_phys_1[i]!)

  -- === Assemble ===
  let all_inputs :=
    [clock, reset, zero, one,
     instr_valid_0, has_rd_0, force_alloc_0] ++
    rs1_addr_0 ++ rs2_addr_0 ++ rs3_addr_0 ++ rd_addr_0 ++
    [instr_valid_1, has_rd_1, force_alloc_1] ++
    rs1_addr_1 ++ rs2_addr_1 ++ rs3_addr_1 ++ rd_addr_1 ++
    [flush_en, commit_valid_0] ++ commit_archRd_0 ++ commit_physRd_0 ++
    [commit_hasPhysRd_0, commit_hasAllocSlot_0,
     commit_valid_1] ++ commit_archRd_1 ++ commit_physRd_1 ++
    [commit_hasPhysRd_1, commit_hasAllocSlot_1,
     cdb_valid_0] ++ cdb_tag_0 ++ cdb_data_0 ++
    [cdb_valid_1] ++ cdb_tag_1 ++ cdb_data_1 ++
    [retire_valid] ++ retire_tag ++ rd_tag4

  let all_outputs :=
    [rename_valid_0, stall_0] ++ rs1_phys_out_0 ++ rs2_phys_out_0 ++ rs3_phys_out_0 ++
    rd_phys_out_0 ++ old_rd_phys_0 ++ rs1_data_0 ++ rs2_data_0 ++ rd_data3_0 ++ rd_data4 ++
    [rename_valid_1, stall_1] ++ rs1_phys_out_1 ++ rs2_phys_out_1 ++ rs3_phys_out_1 ++
    rd_phys_out_1 ++ old_rd_phys_1 ++ rs1_data_1 ++ rs2_data_1

  let all_gates :=
    x0_gates_0 ++ x0_gates_1 ++ needs_alloc_gates ++ stall_gates ++ rvalid_gates ++
    fire_gates ++ rat_we_gates ++ rd_phys_0_gates ++ rd_phys_1_gates ++
    bypass_rs1_gates ++ bypass_rs2_gates ++
    crat_we_gates_0 ++ crat_we_gates_1 ++ crat_alloc_gates ++
    out_gates_0 ++ out_gates_1

  let all_instances :=
    [crat_0_inst, crat_1_inst, rat_inst_0, rat_inst_1, freelist_inst, physregfile_inst]

  { name := "RenameStage_W2"
    inputs := all_inputs
    outputs := all_outputs
    gates := all_gates
    instances := all_instances
    signalGroups := [
      { name := "rs1_addr",   width := archWidth, wires := rs1_addr_0 },
      { name := "rs2_addr",   width := archWidth, wires := rs2_addr_0 },
      { name := "rs3_addr",   width := archWidth, wires := rs3_addr_0 },
      { name := "rd_addr",    width := archWidth, wires := rd_addr_0 },
      { name := "rs1_addr_1", width := archWidth, wires := rs1_addr_1 },
      { name := "rs2_addr_1", width := archWidth, wires := rs2_addr_1 },
      { name := "rs3_addr_1", width := archWidth, wires := rs3_addr_1 },
      { name := "rd_addr_1",  width := archWidth, wires := rd_addr_1 },
      { name := "commit_archRd",   width := archWidth, wires := commit_archRd_0 },
      { name := "commit_physRd",   width := tagWidth,  wires := commit_physRd_0 },
      { name := "commit_archRd_1", width := archWidth, wires := commit_archRd_1 },
      { name := "commit_physRd_1", width := tagWidth,  wires := commit_physRd_1 },
      { name := "cdb_tag_0",   width := tagWidth,  wires := cdb_tag_0 },
      { name := "cdb_data_0",  width := dataWidth, wires := cdb_data_0 },
      { name := "cdb_tag_1",   width := tagWidth,  wires := cdb_tag_1 },
      { name := "cdb_data_1",  width := dataWidth, wires := cdb_data_1 },
      { name := "retire_tag",       width := tagWidth, wires := retire_tag },
      { name := "rs1_phys_out",     width := tagWidth, wires := rs1_phys_out_0 },
      { name := "rs2_phys_out",     width := tagWidth, wires := rs2_phys_out_0 },
      { name := "rs3_phys_out",     width := tagWidth, wires := rs3_phys_out_0 },
      { name := "rd_phys_out",      width := tagWidth, wires := rd_phys_out_0 },
      { name := "old_rd_phys_out",  width := tagWidth, wires := old_rd_phys_0 },
      { name := "rs1_phys_out_1",   width := tagWidth, wires := rs1_phys_out_1 },
      { name := "rs2_phys_out_1",   width := tagWidth, wires := rs2_phys_out_1 },
      { name := "rs3_phys_out_1",   width := tagWidth, wires := rs3_phys_out_1 },
      { name := "rd_phys_out_1",    width := tagWidth, wires := rd_phys_out_1 },
      { name := "old_rd_phys_out_1", width := tagWidth, wires := old_rd_phys_1 }
    ]
  }

end Shoumei.RISCV.Renaming

