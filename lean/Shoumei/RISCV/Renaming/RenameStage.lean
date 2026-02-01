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
  /-- Immediate value - pass-through from DecodedInstruction -/
  imm : Option Int
  /-- Previous physical register mapped to rd (for ROB retirement/deallocation) -/
  oldPhysRd : Option (Fin 64)
  deriving Repr

/-- Default RenamedInstruction for Inhabited instance -/
instance : Inhabited RenamedInstruction where
  default := {
    opType := .ADD
    physRd := none
    physRs1 := none
    physRs2 := none
    imm := none
    oldPhysRd := none
  }

/-! ## Behavioral Model -/

/-- RenameStage state: composite of RAT, FreeList, and PhysRegFile -/
structure RenameStageState where
  /-- Register Alias Table: architectural register → physical register mapping -/
  rat : RATState 64
  /-- Free List: pool of available physical registers -/
  freeList : FreeListState 64
  /-- Physical Register File: storage for 64 physical registers -/
  physRegFile : PhysRegFileState 64

/-- Initialize RenameStage with identity RAT mapping, FreeList with regs 32-63 free,
    and PhysRegFile all zeros -/
def RenameStageState.init : RenameStageState :=
  { rat := RATState.init (by omega)           -- Identity mapping (0→0, 1→1, ..., 31→31)
    freeList := mkFreeList64Init              -- Registers 32-63 free
    physRegFile := PhysRegFileState.init 64   -- All zeros
  }

/-- Core rename operation: transform DecodedInstruction → RenamedInstruction.
    Returns updated state and optionally renamed instruction (None = stall). -/
def renameInstruction
    (state : RenameStageState)
    (instr : DecodedInstruction)
    : RenameStageState × Option RenamedInstruction :=
  -- 1. Lookup physical tags for source registers
  let physRs1 := instr.rs1.map state.rat.lookup
  let physRs2 := instr.rs2.map state.rat.lookup

  -- 2. Handle destination register (if exists and not x0)
  match instr.rd with
  | none =>
      -- No destination (branches, stores, etc.)
      (state, some {
        opType := instr.opType
        physRd := none
        physRs1 := physRs1
        physRs2 := physRs2
        imm := instr.imm
        oldPhysRd := none
      })
  | some rd =>
      if rd.val = 0 then
        -- x0 special case: never allocate, never update RAT
        (state, some {
          opType := instr.opType
          physRd := none  -- x0 is not a real physical register
          physRs1 := physRs1
          physRs2 := physRs2
          imm := instr.imm
          oldPhysRd := none
        })
      else
        -- Normal destination register: allocate new physical register
        let oldPhysRd := state.rat.lookup rd
        let (freeList', newPhysRd) := state.freeList.allocate
        match newPhysRd with
        | none =>
            -- Stall: no free physical registers available
            (state, none)
        | some physRd =>
            -- Success: update RAT and return renamed instruction
            let rat' := state.rat.allocate rd physRd
            ({ state with rat := rat', freeList := freeList' },
             some {
               opType := instr.opType
               physRd := some physRd
               physRs1 := physRs1
               physRs2 := physRs2
               imm := instr.imm
               oldPhysRd := some oldPhysRd
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
  let rs1_addr := (List.range archAddrWidth).map (fun i => Wire.mk s!"rs1_addr_{i}")
  let rs2_addr := (List.range archAddrWidth).map (fun i => Wire.mk s!"rs2_addr_{i}")
  let rd_addr := (List.range archAddrWidth).map (fun i => Wire.mk s!"rd_addr_{i}")
  let cdb_valid := Wire.mk "cdb_valid"
  let cdb_tag := (List.range tagWidth).map (fun i => Wire.mk s!"cdb_tag_{i}")
  let cdb_data := (List.range dataWidth).map (fun i => Wire.mk s!"cdb_data_{i}")
  let retire_valid := Wire.mk "retire_valid"
  let retire_tag := (List.range tagWidth).map (fun i => Wire.mk s!"retire_tag_{i}")

  -- Output ports
  let rename_valid := Wire.mk "rename_valid"
  let stall := Wire.mk "stall"
  let rs1_phys := (List.range tagWidth).map (fun i => Wire.mk s!"rs1_phys_{i}")
  let rs2_phys := (List.range tagWidth).map (fun i => Wire.mk s!"rs2_phys_{i}")
  let rd_phys := (List.range tagWidth).map (fun i => Wire.mk s!"rd_phys_{i}")
  let rs1_data := (List.range dataWidth).map (fun i => Wire.mk s!"rs1_data_{i}")
  let rs2_data := (List.range dataWidth).map (fun i => Wire.mk s!"rs2_data_{i}")

  -- Internal signals
  let x0_detect := Wire.mk "x0_detect"
  let needs_alloc := Wire.mk "needs_alloc"
  let alloc_avail := Wire.mk "alloc_avail"  -- deq_valid from FreeList
  let allocate_fire := Wire.mk "allocate_fire"
  let rat_we := Wire.mk "rat_we"
  let freelist_deq_ready := Wire.mk "freelist_deq_ready"

  -- Control logic gates

  -- x0 detection: x0_detect = NOR(rd_addr[4:0])
  -- If all rd_addr bits are 0, then rd = x0
  let rd_or_tree := (List.range archAddrWidth).map (fun i => Wire.mk s!"rd_or_{i}")
  let x0_detect_gates :=
    -- Build OR tree: or0 = rd_addr[0] OR rd_addr[1]
    --                or1 = or0 OR rd_addr[2]
    --                or2 = or1 OR rd_addr[3]
    --                or3 = or2 OR rd_addr[4]
    --                x0_detect = NOT or3
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

  -- freelist_deq_ready = needs_alloc (request allocation when needed)
  let freelist_ready_gate := Gate.mkBUF needs_alloc freelist_deq_ready

  -- allocate_fire = needs_alloc AND alloc_avail AND instr_valid
  let needs_and_avail := Wire.mk "needs_and_avail"
  let allocate_fire_gates := [
    Gate.mkAND needs_alloc alloc_avail needs_and_avail,
    Gate.mkAND needs_and_avail instr_valid allocate_fire
  ]

  -- rat_we = allocate_fire (update RAT on successful allocation)
  let rat_we_gate := Gate.mkBUF allocate_fire rat_we

  -- stall = needs_alloc AND NOT alloc_avail
  let not_alloc_avail := Wire.mk "not_alloc_avail"
  let stall_gates := [
    Gate.mkNOT alloc_avail not_alloc_avail,
    Gate.mkAND needs_alloc not_alloc_avail stall
  ]

  -- rename_valid = instr_valid AND NOT stall
  let not_stall := Wire.mk "not_stall"
  let rename_valid_gates := [
    Gate.mkNOT stall not_stall,
    Gate.mkAND instr_valid not_stall rename_valid
  ]

  -- RAT instance
  let rat_inst : CircuitInstance := {
    moduleName := "RAT_32x6"
    instName := "u_rat"
    portMap :=
      [("clock", clock), ("reset", reset), ("write_en", rat_we)] ++
      (rd_addr.enum.map (fun ⟨i, w⟩ => (s!"write_addr_{i}", w))) ++
      (rd_phys.enum.map (fun ⟨i, w⟩ => (s!"write_data_{i}", w))) ++  -- rd_phys comes from FreeList deq_data
      (rs1_addr.enum.map (fun ⟨i, w⟩ => (s!"rs1_addr_{i}", w))) ++
      (rs2_addr.enum.map (fun ⟨i, w⟩ => (s!"rs2_addr_{i}", w))) ++
      (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"rs1_data_{i}", w))) ++
      (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"rs2_data_{i}", w)))
  }

  -- FreeList instance
  let freelist_enq_ready := Wire.mk "freelist_enq_ready"  -- unused output
  let freelist_inst : CircuitInstance := {
    moduleName := "FreeList_64"
    instName := "u_freelist"
    portMap :=
      [("clock", clock), ("reset", reset), ("zero", zero), ("one", one)] ++
      (retire_tag.enum.map (fun ⟨i, w⟩ => (s!"enq_data_{i}", w))) ++
      [("enq_valid", retire_valid)] ++
      [("deq_ready", freelist_deq_ready)] ++
      [("enq_ready", freelist_enq_ready)] ++  -- unused
      (rd_phys.enum.map (fun ⟨i, w⟩ => (s!"deq_data_{i}", w))) ++  -- allocated tag
      [("deq_valid", alloc_avail)]
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
      (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"wr_tag_{i}", w))) ++
      (cdb_data.enum.map (fun ⟨i, w⟩ => (s!"wr_data_{i}", w))) ++
      (rs1_data.enum.map (fun ⟨i, w⟩ => (s!"rd_data1_{i}", w))) ++
      (rs2_data.enum.map (fun ⟨i, w⟩ => (s!"rd_data2_{i}", w)))
  }

  { name := "RenameStage_32x64"
    inputs := [clock, reset, zero, one, instr_valid, has_rd] ++
              rs1_addr ++ rs2_addr ++ rd_addr ++
              [cdb_valid] ++ cdb_tag ++ cdb_data ++
              [retire_valid] ++ retire_tag
    outputs := [rename_valid, stall] ++
               rs1_phys ++ rs2_phys ++ rd_phys ++
               rs1_data ++ rs2_data
    gates := x0_detect_gates ++ needs_alloc_gates ++ [freelist_ready_gate] ++
             allocate_fire_gates ++ [rat_we_gate] ++ stall_gates ++ rename_valid_gates
    instances := [rat_inst, freelist_inst, physregfile_inst]
  }

end Shoumei.RISCV.Renaming
