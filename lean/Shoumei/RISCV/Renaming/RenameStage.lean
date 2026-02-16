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
  let tagWidth := 6  -- log2(64) = 6 bits for physical register tag
  let archAddrWidth := 5  -- log2(32) = 5 bits for architectural register address
  let dataWidth := 32  -- 32-bit RISC-V word

  -- Input ports
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"
  let instr_valid := Wire.mk "instr_valid"
  let has_rd := Wire.mk "has_rd"
  -- Committed RAT recovery inputs
  let flush_en := Wire.mk "flush_en"
  let commit_valid := Wire.mk "commit_valid"
  let commit_archRd := (List.range 5).map (fun i => Wire.mk s!"commit_archRd_{i}")
  let commit_physRd := (List.range tagWidth).map (fun i => Wire.mk s!"commit_physRd_{i}")
  let commit_hasPhysRd := Wire.mk "commit_hasPhysRd"
  -- commit_hasAllocSlot: true if the committed instruction consumed a counter slot
  -- (i.e. hasPhysRd at allocation time, including branches with force_alloc)
  let commit_hasAllocSlot := Wire.mk "commit_hasAllocSlot"
  let rs1_addr := (List.range archAddrWidth).map (fun i => Wire.mk s!"rs1_addr_{i}")
  let rs2_addr := (List.range archAddrWidth).map (fun i => Wire.mk s!"rs2_addr_{i}")
  let rs3_addr := (List.range archAddrWidth).map (fun i => Wire.mk s!"rs3_addr_{i}")
  let rd_addr := (List.range archAddrWidth).map (fun i => Wire.mk s!"rd_addr_{i}")
  let cdb_valid := Wire.mk "cdb_valid"
  let cdb_tag := (List.range tagWidth).map (fun i => Wire.mk s!"cdb_tag_{i}")
  let cdb_data := (List.range dataWidth).map (fun i => Wire.mk s!"cdb_data_{i}")
  let retire_valid := Wire.mk "retire_valid"
  let retire_tag := (List.range tagWidth).map (fun i => Wire.mk s!"retire_tag_{i}")
  -- 3rd read port: rs3 data (PRF read via rs3_phys from RAT)
  let rd_data3 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data3_{i}")
  -- 4th read port: RVVI FP commit readback (rd_tag4 → rd_data4)
  let rd_tag4 := (List.range tagWidth).map (fun i => Wire.mk s!"rd_tag4_{i}")
  let rd_data4 := (List.range dataWidth).map (fun i => Wire.mk s!"rd_data4_{i}")

  -- Output ports
  let rename_valid := Wire.mk "rename_valid"
  let stall := Wire.mk "stall"
  let rs1_phys := (List.range tagWidth).map (fun i => Wire.mk s!"rs1_phys_{i}")
  let rs2_phys := (List.range tagWidth).map (fun i => Wire.mk s!"rs2_phys_{i}")
  let rs3_phys := (List.range tagWidth).map (fun i => Wire.mk s!"rs3_phys_{i}")
  let rd_phys := (List.range tagWidth).map (fun i => Wire.mk s!"rd_phys_{i}")
  let rs1_data := (List.range dataWidth).map (fun i => Wire.mk s!"rs1_data_{i}")
  let rs2_data := (List.range dataWidth).map (fun i => Wire.mk s!"rs2_data_{i}")
  -- Old physical register mapping output (for ROB oldPhysRd tracking)
  let old_rd_phys := (List.range tagWidth).map (fun i => Wire.mk s!"old_rd_phys_{i}")

  -- force_alloc: advance counter even for rd=x0 (branch tracking tags)
  let force_alloc := Wire.mk "force_alloc"

  -- Internal signals
  let x0_detect := Wire.mk "x0_detect"
  let needs_alloc := Wire.mk "needs_alloc"
  let allocate_fire := Wire.mk "allocate_fire"
  let counter_advance := Wire.mk "counter_advance"  -- counter increments on this
  let rat_we := Wire.mk "rat_we"

  -- Control logic gates

  -- x0 detection: x0_detect = NOR(rd_addr[4:0])
  let rd_or_tree := (List.range archAddrWidth).map (fun i => Wire.mk s!"rd_or_{i}")
  let x0_detect_gates :=
    (if archAddrWidth >= 2 then
      [Gate.mkOR (rd_addr[0]!) (rd_addr[1]!) (rd_or_tree[0]!)]
    else []) ++
    (List.range (archAddrWidth - 2)).map (fun i =>
      Gate.mkOR (rd_or_tree[i]!) (rd_addr[i + 2]!) (rd_or_tree[i + 1]!)
    ) ++
    [Gate.mkNOT (rd_or_tree[archAddrWidth - 2]!) x0_detect]

  -- needs_alloc = has_rd AND NOT x0_detect
  let not_x0 := Wire.mk "not_x0"
  let needs_alloc_gates := [
    Gate.mkNOT x0_detect not_x0,
    Gate.mkAND has_rd not_x0 needs_alloc
  ]

  -- === Free-List-Based Allocation ===
  -- FreeList wire declarations (needed before stall and fire logic)
  let freelist_enq_ready := Wire.mk "freelist_enq_ready"
  let alloc_avail := Wire.mk "alloc_avail"
  let freelist_deq_data := (List.range tagWidth).map (fun i => Wire.mk s!"freelist_deq_{i}")
  let freelist_deq_ready := Wire.mk "freelist_deq_ready"

  -- stall when allocation is needed but free list is empty
  let not_alloc_avail := Wire.mk "not_alloc_avail"
  let stall_raw := Wire.mk "stall_raw"
  let stall_gates := [
    Gate.mkNOT alloc_avail not_alloc_avail,
    Gate.mkAND needs_alloc not_alloc_avail stall_raw,
    Gate.mkBUF stall_raw stall
  ]

  -- rename_valid = instr_valid AND NOT stall
  let not_stall := Wire.mk "not_stall_ren"
  let rename_valid_gates := [
    Gate.mkNOT stall not_stall,
    Gate.mkAND instr_valid not_stall rename_valid
  ]

  -- allocate_fire = needs_alloc AND rename_valid (gated by stall to prevent
  -- RAT write and free list dequeue when free list is empty)
  let force_alloc_fire := Wire.mk "force_alloc_fire"
  let allocate_fire_gates := [
    Gate.mkAND needs_alloc rename_valid allocate_fire,
    -- force_alloc_fire = force_alloc AND rename_valid AND NOT(needs_alloc)
    -- (only when force_alloc is set AND rd=x0, dequeue without RAT write)
    Gate.mkAND force_alloc rename_valid force_alloc_fire,
    -- counter_advance = allocate_fire OR force_alloc_fire
    Gate.mkOR allocate_fire force_alloc_fire counter_advance
  ]

  -- rat_we = allocate_fire (only write RAT for real rd != x0)
  let rat_we_gate := Gate.mkBUF allocate_fire rat_we

  -- Dequeue when counter_advance fires (allocation or force_alloc)
  let freelist_ready_gate := Gate.mkBUF counter_advance freelist_deq_ready

  -- rd_phys = freelist dequeue data when actually allocating, else 0
  -- Must be 0 for x0/no-rd instructions to prevent CDB tag collisions
  -- (stale deq_data could match an in-flight preg and corrupt RS entries)
  let rd_phys_assign_gates := (List.range tagWidth).map (fun i =>
    Gate.mkAND (freelist_deq_data[i]!) counter_advance (rd_phys[i]!))

  -- === COMMITTED RAT ===
  -- Dump wires from committed RAT (32×6 = 192 wires)
  let crat_dump := (List.range 32).map (fun i =>
    (List.range tagWidth).map (fun j => Wire.mk s!"crat_dump_{i}_{j}"))

  -- Committed RAT write enable: commit_valid AND commit_hasPhysRd AND (archRd != 0)
  let crat_we := Wire.mk "crat_we"
  let commit_rd_or_tree := (List.range 5).map (fun i => Wire.mk s!"commit_rd_or_{i}")
  let commit_rd_is_x0 := Wire.mk "commit_rd_is_x0"
  let commit_not_x0 := Wire.mk "commit_not_x0"
  let commit_valid_hasRd := Wire.mk "commit_valid_hasRd"
  let crat_we_gates :=
    [Gate.mkOR commit_archRd[0]! commit_archRd[1]! commit_rd_or_tree[0]!] ++
    (List.range 3).map (fun i =>
      Gate.mkOR commit_rd_or_tree[i]! commit_archRd[i + 2]! commit_rd_or_tree[i + 1]!) ++
    [Gate.mkNOT commit_rd_or_tree[3]! commit_rd_is_x0,
     Gate.mkNOT commit_rd_is_x0 commit_not_x0,
     Gate.mkAND commit_valid commit_hasPhysRd commit_valid_hasRd,
     Gate.mkAND commit_valid_hasRd commit_not_x0 crat_we]

  let crat_inst : CircuitInstance := {
    moduleName := "RAT_32x6"
    instName := "u_crat"
    portMap :=
      [("clock", clock), ("reset", reset), ("write_en", crat_we)] ++
      (commit_archRd.enum.map (fun ⟨i, w⟩ => (s!"write_addr_{i}", w))) ++
      (commit_physRd.enum.map (fun ⟨i, w⟩ => (s!"write_data_{i}", w))) ++
      -- Read ports unused (tied to zero)
      ((List.range 5).map (fun i => (s!"rs1_addr_{i}", zero))) ++
      ((List.range 5).map (fun i => (s!"rs2_addr_{i}", zero))) ++
      ((List.range 5).map (fun i => (s!"rs3_addr_{i}", zero))) ++
      -- Read outputs unconnected (use unique wire names)
      ((List.range tagWidth).map (fun i => (s!"rs1_data_{i}", Wire.mk s!"crat_unused_rs1_{i}"))) ++
      ((List.range tagWidth).map (fun i => (s!"rs2_data_{i}", Wire.mk s!"crat_unused_rs2_{i}"))) ++
      ((List.range tagWidth).map (fun i => (s!"rs3_data_{i}", Wire.mk s!"crat_unused_rs3_{i}"))) ++
      ((List.range tagWidth).map (fun i => (s!"old_rd_data_{i}", Wire.mk s!"crat_unused_old_{i}"))) ++
      -- Committed RAT never restores (restore_en = zero)
      [("restore_en", zero)] ++
      ((List.range 32).map (fun i =>
        (List.range tagWidth).map (fun j =>
          (s!"restore_data_{i}_{j}", zero)))).flatten ++
      -- Dump outputs: committed RAT state
      ((List.range 32).map (fun i =>
        (List.range tagWidth).map (fun j =>
          (s!"dump_data_{i}_{j}", crat_dump[i]![j]!)))).flatten
  }

  -- RAT instance (now with old_rd_data output for previous mapping)
  let old_rd_raw := (List.range tagWidth).map (fun i => Wire.mk s!"old_rd_raw_{i}")
  -- Speculative RAT: restore from committed RAT on flush
  let rat_inst : CircuitInstance := {
    moduleName := "RAT_32x6"
    instName := "u_rat"
    portMap :=
      [("clock", clock), ("reset", reset), ("write_en", rat_we)] ++
      (rd_addr.enum.map (fun ⟨i, w⟩ => (s!"write_addr_{i}", w))) ++
      (rd_phys.enum.map (fun ⟨i, w⟩ => (s!"write_data_{i}", w))) ++
      (rs1_addr.enum.map (fun ⟨i, w⟩ => (s!"rs1_addr_{i}", w))) ++
      (rs2_addr.enum.map (fun ⟨i, w⟩ => (s!"rs2_addr_{i}", w))) ++
      (rs3_addr.enum.map (fun ⟨i, w⟩ => (s!"rs3_addr_{i}", w))) ++
      (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"rs1_data_{i}", w))) ++
      (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"rs2_data_{i}", w))) ++
      (rs3_phys.enum.map (fun ⟨i, w⟩ => (s!"rs3_data_{i}", w))) ++
      (old_rd_raw.enum.map (fun ⟨i, w⟩ => (s!"old_rd_data_{i}", w))) ++
      -- Restore from committed RAT on flush
      [("restore_en", flush_en)] ++
      ((List.range 32).map (fun i =>
        (List.range tagWidth).map (fun j =>
          (s!"restore_data_{i}_{j}", crat_dump[i]![j]!)))).flatten ++
      -- Dump outputs unused on speculative RAT
      ((List.range 32).map (fun i =>
        (List.range tagWidth).map (fun j =>
          (s!"dump_data_{i}_{j}", Wire.mk s!"srat_dump_{i}_{j}")))).flatten
  }

  -- === Commit-alloc enable: committed instruction consumed a free list slot ===
  let commit_alloc_advance := Wire.mk "commit_alloc_advance"
  let commit_alloc_advance_gate :=
    Gate.mkAND commit_valid commit_hasAllocSlot commit_alloc_advance

  -- old_rd_phys output = old_rd_raw (previous RAT mapping for rd)
  let old_rd_assign_gates := (List.range tagWidth).map (fun i =>
    Gate.mkBUF (old_rd_raw[i]!) (old_rd_phys[i]!))

  -- BitmapFreeList instance (replaces FIFO free list + cctr + committed_count)
  let freelist_inst : CircuitInstance := {
    moduleName := "BitmapFreeList_64"
    instName := "u_freelist"
    portMap :=
      [("clock", clock), ("reset", reset), ("zero", zero), ("one", one)] ++
      (retire_tag.enum.map (fun ⟨i, w⟩ => (s!"enq_data_{i}", w))) ++
      [("enq_valid", retire_valid)] ++
      [("deq_ready", freelist_deq_ready)] ++
      [("enq_ready", freelist_enq_ready)] ++
      (freelist_deq_data.enum.map (fun ⟨i, w⟩ => (s!"deq_data_{i}", w))) ++
      [("deq_valid", alloc_avail)] ++
      [("flush_en", flush_en)] ++
      [("commit_alloc_en", commit_alloc_advance)] ++
      (commit_physRd.enum.map (fun ⟨i, w⟩ => (s!"commit_alloc_tag_{i}", w)))
  }

  -- PhysRegFile instance
  let physregfile_inst : CircuitInstance := {
    moduleName := "PhysRegFile_64x32"
    instName := "u_prf"
    portMap :=
      [("clock", clock), ("reset", reset)] ++
      [("wr_en", cdb_valid)] ++
      (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"rd_tag1_{i}", w))) ++  -- Read port 1 uses renamed rs1
      (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"rd_tag2_{i}", w))) ++  -- Read port 2 uses renamed rs2
      (rs3_phys.enum.map (fun ⟨i, w⟩ => (s!"rd_tag3_{i}", w))) ++  -- Read port 3: rs3 via RAT lookup
      (rd_tag4.enum.map (fun ⟨i, w⟩ => (s!"rd_tag4_{i}", w))) ++   -- Read port 4: RVVI FP commit readback
      (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"wr_tag_{i}", w))) ++
      (cdb_data.enum.map (fun ⟨i, w⟩ => (s!"wr_data_{i}", w))) ++
      (rs1_data.enum.map (fun ⟨i, w⟩ => (s!"rd_data1_{i}", w))) ++
      (rs2_data.enum.map (fun ⟨i, w⟩ => (s!"rd_data2_{i}", w))) ++
      (rd_data3.enum.map (fun ⟨i, w⟩ => (s!"rd_data3_{i}", w))) ++
      (rd_data4.enum.map (fun ⟨i, w⟩ => (s!"rd_data4_{i}", w)))
  }

  -- Output wires (separate from internal to avoid Chisel IO conflicts)
  let rs1_phys_out := (List.range tagWidth).map (fun i => Wire.mk s!"rs1_phys_out_{i}")
  let rs2_phys_out := (List.range tagWidth).map (fun i => Wire.mk s!"rs2_phys_out_{i}")
  let rd_phys_out := (List.range tagWidth).map (fun i => Wire.mk s!"rd_phys_out_{i}")
  let old_rd_phys_out := (List.range tagWidth).map (fun i => Wire.mk s!"old_rd_phys_out_{i}")
  let rs3_phys_out := (List.range tagWidth).map (fun i => Wire.mk s!"rs3_phys_out_{i}")
  let phys_out_gates :=
    (List.range tagWidth).map (fun i => Gate.mkBUF (rs1_phys[i]!) (rs1_phys_out[i]!)) ++
    (List.range tagWidth).map (fun i => Gate.mkBUF (rs2_phys[i]!) (rs2_phys_out[i]!)) ++
    (List.range tagWidth).map (fun i => Gate.mkBUF (rd_phys[i]!) (rd_phys_out[i]!)) ++
    (List.range tagWidth).map (fun i => Gate.mkBUF (old_rd_phys[i]!) (old_rd_phys_out[i]!)) ++
    (List.range tagWidth).map (fun i => Gate.mkBUF (rs3_phys[i]!) (rs3_phys_out[i]!))

  { name := "RenameStage_32x64"
    inputs := [clock, reset, zero, one, instr_valid, has_rd] ++
              rs1_addr ++ rs2_addr ++ rs3_addr ++ rd_addr ++
              [cdb_valid] ++ cdb_tag ++ cdb_data ++
              [retire_valid] ++ retire_tag ++
              rd_tag4 ++
              [flush_en, commit_valid] ++ commit_archRd ++ commit_physRd ++ [commit_hasPhysRd] ++
              [force_alloc, commit_hasAllocSlot]
    outputs := [rename_valid, stall] ++
               rs1_phys_out ++ rs2_phys_out ++ rd_phys_out ++ old_rd_phys_out ++
               rs1_data ++ rs2_data ++ rd_data3 ++ rs3_phys_out ++ rd_data4
    gates := x0_detect_gates ++ needs_alloc_gates ++ [freelist_ready_gate] ++
             allocate_fire_gates ++ [rat_we_gate] ++ stall_gates ++ rename_valid_gates ++
             rd_phys_assign_gates ++
             old_rd_assign_gates ++ phys_out_gates ++
             crat_we_gates ++
             [commit_alloc_advance_gate]
    instances := [rat_inst, crat_inst, freelist_inst, physregfile_inst]
    -- V2 codegen annotations
    signalGroups := [
      { name := "rs1_addr", width := 5, wires := rs1_addr },
      { name := "rs2_addr", width := 5, wires := rs2_addr },
      { name := "rs3_addr", width := 5, wires := rs3_addr },
      { name := "rd_addr", width := 5, wires := rd_addr },
      { name := "cdb_tag", width := 6, wires := cdb_tag },
      { name := "cdb_data", width := 32, wires := cdb_data },
      { name := "retire_tag", width := 6, wires := retire_tag },
      { name := "rs1_phys_out", width := 6, wires := rs1_phys_out },
      { name := "rs2_phys_out", width := 6, wires := rs2_phys_out },
      { name := "rd_phys_out", width := 6, wires := rd_phys_out },
      { name := "old_rd_phys_out", width := 6, wires := old_rd_phys_out },
      { name := "rs1_data", width := 32, wires := rs1_data },
      { name := "rs2_data", width := 32, wires := rs2_data },
      { name := "rs1_phys", width := 6, wires := rs1_phys },
      { name := "rs2_phys", width := 6, wires := rs2_phys },
      { name := "rd_phys", width := 6, wires := rd_phys },
      { name := "old_rd_phys", width := 6, wires := old_rd_phys },
      { name := "freelist_deq", width := 6, wires := freelist_deq_data },
      { name := "rs3_phys", width := 6, wires := rs3_phys },
      { name := "rs3_phys_out", width := 6, wires := rs3_phys_out },
      { name := "rd_data3", width := 32, wires := rd_data3 },
      { name := "rd_tag4", width := 6, wires := rd_tag4 },
      { name := "rd_data4", width := 32, wires := rd_data4 },
      { name := "commit_archRd", width := 5, wires := commit_archRd },
      { name := "commit_physRd", width := 6, wires := commit_physRd }
    ]
  }

end Shoumei.RISCV.Renaming
