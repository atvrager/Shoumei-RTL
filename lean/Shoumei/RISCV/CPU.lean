/-
Top-Level CPU Integration - RV32I/RV32IM Tomasulo Processor

Integrates all 77 verified pipeline components into a complete, working CPU.
Supports configurable ISA extensions (M enable/disable via CPUConfig).

Pipeline Stages (7 stages + memory):
1. Fetch - PC management, instruction memory
2. Decode - Instruction decode (RV32I or RV32IM based on config)
3. Rename - RAT + FreeList + PhysRegFile
4. Issue - Dispatch to appropriate Reservation Station
5. Execute - Execution units + CDB broadcast
6. Writeback - CDB snooping by RS and ROB
7. Commit - ROB in-order retirement

RVVI Infrastructure (Phase 8):
- PC queue and instruction queue track retirement info alongside ROB
- Prepared for future lock-step cosimulation with Spike and SystemC
- See docs/cosimulation.md for details

Phase 8 scope: Behavioral model only. Structural circuit TBD.
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
import Shoumei.RISCV.Retirement.ROB
import Shoumei.RISCV.Memory.LSU
import Shoumei.RISCV.CPUControl
import Shoumei.DSL
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Sequential.Register

namespace Shoumei.RISCV.CPU

open Shoumei.RISCV
open Shoumei.RISCV.Control
open Shoumei.RISCV.Execution
open Shoumei.RISCV.Renaming
open Shoumei.RISCV.Retirement (ROBState CommittedRATState)
open Shoumei.RISCV.Memory (LSUState)

/-- Generate gates for 6-bit OpType dispatch code → 4-bit ALU opcode translation.

    Takes the RS dispatch opcode (6-bit OpType encoding from decoder) and produces
    the 4-bit ALU opcode expected by IntegerExecUnit / ALU32.

    Implemented as AND-OR logic: for each output bit, OR together product terms
    matching the input encodings that should set that bit.

    Parameters:
    - prefix: Wire name prefix (for unique naming in multi-instance circuits)
    - optype: 6-bit OpType dispatch code from RS
    - aluOp: 4-bit ALU opcode output
    - mapping: List of (optype_encoding, alu_opcode) pairs

    ALU opcode encoding:
      0=ADD, 1=SUB, 2=SLT, 3=SLTU, 4=AND, 5=OR, 6=XOR, 7=SLL, 8=SRL, 9=SRA
-/
def mkOpTypeToALU4 (pfx : String) (optype : List Wire) (aluOp : List Wire)
    (mapping : List (Nat × Nat)) : List Gate :=
  -- For each ALU output bit, collect optype values that set it
  let testBit (n : Nat) (b : Nat) : Bool := (n / (2 ^ b)) % 2 != 0
  let bit0_terms := mapping.filter (fun (_, alu) => testBit alu 0) |>.map Prod.fst
  let bit1_terms := mapping.filter (fun (_, alu) => testBit alu 1) |>.map Prod.fst
  let bit2_terms := mapping.filter (fun (_, alu) => testBit alu 2) |>.map Prod.fst
  let bit3_terms := mapping.filter (fun (_, alu) => testBit alu 3) |>.map Prod.fst
  -- Helper: build a 6-bit equality match for one encoding value
  let mkMatch (enc : Nat) (tag : String) : (List Gate × Wire) :=
    let matchWire := Wire.mk s!"{pfx}_{tag}"
    -- Select true/inverted bit for each position
    let bitWires := (List.range 6).map fun b =>
      if testBit enc b then optype[b]! else Wire.mk s!"{pfx}_n{b}"
    -- Chain 6-input AND: a0 & a1 → t01, t01 & a2 → t012, etc.
    let t01 := Wire.mk s!"{pfx}_{tag}_t01"
    let t012 := Wire.mk s!"{pfx}_{tag}_t012"
    let t0123 := Wire.mk s!"{pfx}_{tag}_t0123"
    let t01234 := Wire.mk s!"{pfx}_{tag}_t01234"
    let andGates := [
      Gate.mkAND bitWires[0]! bitWires[1]! t01,
      Gate.mkAND t01 bitWires[2]! t012,
      Gate.mkAND t012 bitWires[3]! t0123,
      Gate.mkAND t0123 bitWires[4]! t01234,
      Gate.mkAND t01234 bitWires[5]! matchWire
    ]
    (andGates, matchWire)
  -- Helper: OR-chain to combine match wires into one output
  let mkOrChain (wires : List Wire) (outWire : Wire) : List Gate :=
    match wires with
    | [] => [Gate.mkBUF (Wire.mk s!"{pfx}_gnd") outWire]  -- no terms → 0
    | [w] => [Gate.mkBUF w outWire]
    | w0 :: w1 :: rest =>
      let first := Wire.mk s!"{pfx}_{outWire.name}_or0"
      let firstGate := Gate.mkOR w0 w1 first
      let (gates, _) := rest.enum.foldl (fun (acc, prev) ⟨idx, w⟩ =>
        let isLast := idx == rest.length - 1
        let next := if isLast then outWire else Wire.mk s!"{pfx}_{outWire.name}_or{idx+1}"
        (acc ++ [Gate.mkOR prev w next], next)
      ) ([firstGate], first)
      gates
  -- Generate shared NOT wires for all 6 optype bits
  let notGates := (List.range 6).map fun b =>
    Gate.mkNOT optype[b]! (Wire.mk s!"{pfx}_n{b}")
  -- Generate match + OR logic for each output bit
  let mkBitLogic (terms : List Nat) (bitIdx : Nat) : List Gate :=
    let matchResults := terms.enum.map fun ⟨idx, enc⟩ =>
      mkMatch enc s!"b{bitIdx}_e{idx}"
    let matchGates := (matchResults.map Prod.fst).flatten
    let matchWires := matchResults.map Prod.snd
    let orGates := mkOrChain matchWires aluOp[bitIdx]!
    matchGates ++ orGates
  notGates ++
    mkBitLogic bit0_terms 0 ++
    mkBitLogic bit1_terms 1 ++
    mkBitLogic bit2_terms 2 ++
    mkBitLogic bit3_terms 3

/-- OpType → ALU4 mapping for RV32I decoder encoding.
    Encoding order (from generated RV32IDecoder.sv):
    0=XORI, 1=XOR, 2=SW, 3=SUB, 4=SRLI, 5=SRL, 6=SRAI, 7=SRA,
    8=SLTU, 9=SLTIU, 10=SLTI, 11=SLT, 12=SLLI, 13=SLL, 14=SH, 15=SB,
    16=ORI, 17=OR, 18=LW, 19=LUI, 20=LHU, 21=LH, 22=LBU, 23=LB,
    24=JALR, 25=JAL, 26=FENCE, 27=ECALL, 28=EBREAK, 29=BNE, 30=BLTU,
    31=BLT, 32=BGEU, 33=BGE, 34=BEQ, 35=AUIPC, 36=ANDI, 37=AND,
    38=ADDI, 39=ADD -/
def aluMapping_RV32I : List (Nat × Nat) :=
  [ (39, 0), (38, 0),   -- ADD, ADDI → 0
    (3, 1),             -- SUB → 1
    (11, 2), (10, 2),   -- SLT, SLTI → 2
    (8, 3), (9, 3),     -- SLTU, SLTIU → 3
    (37, 4), (36, 4),   -- AND, ANDI → 4
    (17, 5), (16, 5),   -- OR, ORI → 5
    (1, 6), (0, 6),     -- XOR, XORI → 6
    (13, 7), (12, 7),   -- SLL, SLLI → 7
    (5, 8), (4, 8),     -- SRL, SRLI → 8
    (7, 9), (6, 9) ]    -- SRA, SRAI → 9

/-- OpType → ALU4 mapping for RV32IM decoder encoding.
    Encoding order (from generated RV32IMDecoder.sv):
    0=XORI, 1=XOR, 2=SW, 3=SUB, 4=SRLI, 5=SRL, 6=SRAI, 7=SRA,
    8=SLTU, 9=SLTIU, 10=SLTI, 11=SLT, 12=SLLI, 13=SLL, 14=SH, 15=SB,
    16=REMU, 17=REM, 18=ORI, 19=OR, 20=MULHU, 21=MULHSU, 22=MULH, 23=MUL,
    24=LW, 25=LUI, 26=LHU, 27=LH, 28=LBU, 29=LB, 30=JALR, 31=JAL,
    32=FENCE, 33=ECALL, 34=EBREAK, 35=DIVU, 36=DIV, 37=BNE, 38=BLTU,
    39=BLT, 40=BGEU, 41=BGE, 42=BEQ, 43=AUIPC, 44=ANDI, 45=AND,
    46=ADDI, 47=ADD -/
def aluMapping_RV32IM : List (Nat × Nat) :=
  [ (47, 0), (46, 0),   -- ADD, ADDI → 0
    (3, 1),             -- SUB → 1
    (11, 2), (10, 2),   -- SLT, SLTI → 2
    (8, 3), (9, 3),     -- SLTU, SLTIU → 3
    (45, 4), (44, 4),   -- AND, ANDI → 4
    (19, 5), (18, 5),   -- OR, ORI → 5
    (1, 6), (0, 6),     -- XOR, XORI → 6
    (13, 7), (12, 7),   -- SLL, SLLI → 7
    (5, 8), (4, 8),     -- SRL, SRLI → 8
    (7, 9), (6, 9) ]    -- SRA, SRAI → 9

/-- Build a 64-bit busy-bit table for operand readiness tracking.

    The busy table tracks which physical registers have pending writes.
    - Set busy[rd_phys] when a new instruction is renamed (allocates rd_phys)
    - Clear busy[tag] when CDB broadcasts a result for that tag
    - Read busy[rs_phys] to determine if an operand is ready

    Returns: (gates, instances, src1_ready wire, src2_ready wire)

    Inputs:
    - clock, reset, zero, one: global signals
    - set_tag[5:0]: physical register to mark busy (rd_phys from rename)
    - set_en: enable set (rename_valid AND decode_has_rd)
    - clear_tag[5:0]: physical register to mark ready (cdb_tag)
    - clear_en: enable clear (cdb_valid)
    - read1_tag[5:0]: first read port (rs1_phys)
    - read2_tag[5:0]: second read port (rs2_phys)
    - use_imm: if true, src2 is always ready (I-type instruction)

    Hardware: 64 DFFs + 2 Decoder6 instances + 64 next-state MUXes + 2 64:1 read muxes
-/
def mkBusyBitTable
    (clock reset zero one : Wire)
    (set_tag : List Wire) (set_en : Wire)
    (clear_tag : List Wire) (clear_en : Wire)
    (read1_tag : List Wire) (read2_tag : List Wire)
    (use_imm : Wire)
    (src1_ready src2_ready src2_ready_reg : Wire)
    : (List Gate × List CircuitInstance) :=
  let mkW := fun (s : String) => Wire.mk s
  -- Decoder instances for set and clear paths
  let set_decode := (List.range 64).map fun i => mkW s!"busy_set_dec_{i}"
  let clear_decode := (List.range 64).map fun i => mkW s!"busy_clr_dec_{i}"

  let set_dec_inst : CircuitInstance := {
    moduleName := "Decoder6"
    instName := "u_busy_set_dec"
    portMap :=
      (set_tag.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (set_decode.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }
  let clear_dec_inst : CircuitInstance := {
    moduleName := "Decoder6"
    instName := "u_busy_clr_dec"
    portMap :=
      (clear_tag.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (clear_decode.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  -- 64 busy bits: DFF + next-state logic
  let busy_cur := (List.range 64).map fun i => mkW s!"busy_q_{i}"
  let busy_next := (List.range 64).map fun i => mkW s!"busy_d_{i}"

  -- Per-bit logic:
  --   set_i = set_en AND set_decode[i]
  --   clr_i = clear_en AND clear_decode[i]
  --   next[i] = clr_i ? 0 : (set_i ? 1 : cur[i])
  let perBitGates := (List.range 64).map fun i =>
    let set_i := mkW s!"busy_set_{i}"
    let clr_i := mkW s!"busy_clr_{i}"
    let mux1 := mkW s!"busy_mux1_{i}"
    [
      Gate.mkAND set_en set_decode[i]! set_i,
      Gate.mkAND clear_en clear_decode[i]! clr_i,
      Gate.mkMUX busy_cur[i]! one set_i mux1,     -- set: cur → 1
      Gate.mkMUX mux1 zero clr_i busy_next[i]!,    -- clear: → 0 (priority over set)
      Gate.mkDFF busy_next[i]! clock reset busy_cur[i]!  -- DFF (reset to 0 = not busy)
    ]

  -- Read port 1: 64:1 mux tree selecting busy_cur[read1_tag]
  -- Build 6-level binary mux tree: level 0 has 32 muxes, level 5 has 1 mux
  let mkMux64to1 (inputs : List Wire) (sel : List Wire) (portName : String) (output : Wire) : List Gate :=
    -- Level 0: sel[0] selects between pairs → 32 outputs
    let l0 := (List.range 32).map fun i =>
      let o := mkW s!"{portName}_l0_{i}"
      (Gate.mkMUX inputs[2*i]! inputs[2*i+1]! sel[0]! o, o)
    -- Level 1: sel[1] selects between pairs → 16 outputs
    let l0_outs := l0.map Prod.snd
    let l1 := (List.range 16).map fun i =>
      let o := mkW s!"{portName}_l1_{i}"
      (Gate.mkMUX l0_outs[2*i]! l0_outs[2*i+1]! sel[1]! o, o)
    let l1_outs := l1.map Prod.snd
    -- Level 2: → 8 outputs
    let l2 := (List.range 8).map fun i =>
      let o := mkW s!"{portName}_l2_{i}"
      (Gate.mkMUX l1_outs[2*i]! l1_outs[2*i+1]! sel[2]! o, o)
    let l2_outs := l2.map Prod.snd
    -- Level 3: → 4 outputs
    let l3 := (List.range 4).map fun i =>
      let o := mkW s!"{portName}_l3_{i}"
      (Gate.mkMUX l2_outs[2*i]! l2_outs[2*i+1]! sel[3]! o, o)
    let l3_outs := l3.map Prod.snd
    -- Level 4: → 2 outputs
    let l4 := (List.range 2).map fun i =>
      let o := mkW s!"{portName}_l4_{i}"
      (Gate.mkMUX l3_outs[2*i]! l3_outs[2*i+1]! sel[4]! o, o)
    let l4_outs := l4.map Prod.snd
    -- Level 5: → 1 output
    let l5 := Gate.mkMUX l4_outs[0]! l4_outs[1]! sel[5]! output
    (l0.map Prod.fst) ++ (l1.map Prod.fst) ++ (l2.map Prod.fst) ++
      (l3.map Prod.fst) ++ (l4.map Prod.fst) ++ [l5]

  let busy_rs1 := mkW "busy_rs1_raw"
  let busy_rs2 := mkW "busy_rs2_raw"
  let mux1_gates := mkMux64to1 busy_cur read1_tag "bmux1" busy_rs1
  let mux2_gates := mkMux64to1 busy_cur read2_tag "bmux2" busy_rs2

  -- src1_ready = NOT busy[rs1_phys]
  -- src2_ready = use_imm OR NOT busy[rs2_phys]
  let not_busy_rs2 := mkW "not_busy_rs2"
  let readyGates := [
    Gate.mkNOT busy_rs1 src1_ready,
    Gate.mkNOT busy_rs2 not_busy_rs2,
    Gate.mkOR use_imm not_busy_rs2 src2_ready,
    Gate.mkBUF not_busy_rs2 src2_ready_reg  -- src2 ready without use_imm masking (for stores)
  ]

  let allGates := perBitGates.flatten ++ mux1_gates ++ mux2_gates ++ readyGates
  let allInstances := [set_dec_inst, clear_dec_inst]
  (allGates, allInstances)

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

structure DecodeState where
  /-- Fetched instruction word (None if invalid/stalled) -/
  fetchedInstr : Option UInt32
  /-- Decoded instruction (None if decode failed) -/
  decodedInstr : Option DecodedInstruction
  /-- Program counter for the fetched instruction -/
  pc : UInt32
deriving Repr

def DecodeState.empty : DecodeState :=
  { fetchedInstr := none
    decodedInstr := none
    pc := 0 }

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
  { fetch := FetchState.init config.entryPoint
    decode := DecodeState.empty
    rename := RenameStageState.init
    rsInteger := RSState.init 4
    rsMemory := RSState.init 4
    rsBranch := RSState.init 4
    rsMulDiv := mulDivRS
    rob := ROBState.empty
    lsu := LSUState.empty
    committedRAT := CommittedRATState.init
    mulDivExecState := mulDivExec
    pcQueue := PCQueue.init
    insnQueue := InsnQueue.init
    globalStall := false
    flushing := false
    cycleCount := 0 }

/-
Helper Functions for CPU State Queries
-/

/-- Check if CPU is idle (no instructions in pipeline) -/
def CPUState.isIdle (cpu : CPUState config) : Bool :=
  ROBState.isEmpty cpu.rob &&
  cpu.decode.decodedInstr.isNone &&
  cpu.fetch.fetchedInstr.isNone

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
       rsBranch_postFlush, rsMulDiv_postFlush, decode_postFlush, globalStall_postFlush) :=
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
        let decodeEmpty := DecodeState.empty
        (robEmpty, renameRestored, rsIntEmpty, rsMemEmpty, rsBrEmpty, rsMulDivEmpty, decodeEmpty, false)
    | none =>
        (rob_afterCommit, rename_afterCommit, cpu.rsInteger, cpu.rsMemory,
         cpu.rsBranch, cpu.rsMulDiv, cpu.decode, cpu.globalStall)

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
          | some (opcode, src1, src2, destTag, _immediate, _pc) =>
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

  -- Select ready entries from each RS and execute
  -- Returns CDB broadcasts and optional branch redirect target
  let (cdbBroadcasts, branchRedirectTarget) : (List CDBBroadcast × Option UInt32) :=
    -- Integer RS execution (ALU operations)
    -- Uses verified IntegerExecUnit (executeInteger)
    let intBC : List CDBBroadcast := match rsInteger_postFlush.selectReady with
      | some idx =>
          let (_, dispatchResult) := rsInteger_postFlush.dispatch idx
          match dispatchResult with
          | some (opcode, src1, src2, destTag, _immediate, _pc) =>
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
          | some (opcode, src1, _src2, destTag, immediate, _pc) =>
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
          | some (opcode, src1, src2, destTag, immediate, pc) =>
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

    (intBC ++ memBC ++ branchBC ++ mulDivBC, branchRedirect)

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

  -- ========== CDB WRITEBACK TO PHYSREGFILE ==========
  -- Write execution results to physical register file
  let rename_postExecute := cdbBroadcasts.foldl (fun (ren : RenameStageState) (bc : CDBBroadcast) =>
    if bc.valid then
      { ren with physRegFile := ren.physRegFile.write bc.tag bc.data }
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

  -- ========== STAGE 4: DISPATCH TO RS ==========
  -- Route renamed instruction to appropriate RS based on OpType
  let (rsInteger_postDispatch, rsMemory_postDispatch, rsBranch_postDispatch,
       rsMulDiv_postDispatch, rename_postDispatch, rob_postDispatch) :=
    (rsInteger_postCDB, rsMemory_postCDB, rsBranch_postCDB, rsMulDiv_postCDB,
     rename_postExecute, rob_postCDB)
  -- TODO: Actually dispatch renamed instruction to RS and allocate ROB

  -- ========== STAGE 3: RENAME ==========
  -- Transform decoded instruction into renamed instruction (phys register tags)
  let (rename_postRename, renamedInstr) : (RenameStageState × Option RenamedInstruction) :=
    (rename_postDispatch, none)
  -- TODO: Call renameInstruction on decoded instruction

  -- ========== STAGE 2: DECODE ==========
  -- Decode instruction word into operation and fields
  let decode' : DecodeState :=
    match cpu.fetch.fetchedInstr with
    | none => DecodeState.empty
    | some instr =>
        -- Use provided decodedInstr parameter (for testing)
        -- TODO: Config-aware decoder call (decodeRV32I vs decodeRV32IM)
        -- PC of fetched instruction is the previous PC (before fetch incremented it)
        { fetchedInstr := some instr
          decodedInstr := decodedInstr
          pc := cpu.fetch.pc - 4 }  -- PC of instruction that was fetched last cycle

  -- ========== STAGE 1: FETCH ==========
  let stall := globalStall_postFlush
  -- Priority: branch redirect from execution > flush from commit
  let branchRedirect := match branchRedirectTarget with
    | some target => some target
    | none => flushPC
  let fetch' := fetchStep cpu.fetch imem stall branchRedirect

  -- ========== ASSEMBLE FINAL STATE ==========
  { cpu with
    fetch := fetch'
    decode := decode'
    rename := rename_postRename
    rsInteger := rsInteger_postDispatch
    rsMemory := rsMemory_postDispatch
    rsBranch := rsBranch_postDispatch
    rsMulDiv := rsMulDiv_postDispatch
    rob := rob_postDispatch
    mulDivExecState := mulDivExecState'
    globalStall := globalStall_postFlush
    flushing := flushPC.isSome
    cycleCount := cpu.cycleCount + 1 }

/-! ## Structural Circuit Implementation -/

/-
Note: The structural CPU circuits implement a simplified version of the behavioral model.
Decode stage is kept external (behavioral) due to the complexity of 48 instruction patterns.
The structural circuits focus on verified submodule composition.
-/

-- Import structural circuit modules
open Shoumei
open Shoumei.Circuits.Combinational
open Shoumei.Circuits.Sequential

/-- Helper: Create indexed wires -/
private def makeIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}_{i}")

/-- Helper: Create bundled I/O port map entries for modules with >200 ports -/
private def bundledPorts (portName : String) (wires : List Wire) : List (String × Wire) :=
  wires.enum.map (fun ⟨i, w⟩ => (s!"{portName}_{i}", w))

/--
RV32I CPU Structural Circuit (Base Integer ISA)

Same as RV32IM but without MulDiv RS and execution unit.

Instances (10 total):
1. FetchStage - PC management
2. RV32IDecoder - Instruction decoder
3. RenameStage_32x64 - RAT + FreeList + PhysRegFile
4-6. ReservationStation4 (×3) - Integer, Memory, Branch
7. IntegerExecUnit - ALU operations
8. MemoryExecUnit - Address calculation
9. ROB16 - Reorder buffer
10. LSU - Load-store unit
-/
def mkCPU_RV32I : Circuit :=
  -- Global signals
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- === EXTERNAL INTERFACES ===
  let imem_resp_data := makeIndexedWires "imem_resp_data" 32
  let dmem_req_ready := Wire.mk "dmem_req_ready"
  let dmem_resp_valid := Wire.mk "dmem_resp_valid"
  let dmem_resp_data := makeIndexedWires "dmem_resp_data" 32
  let branch_redirect_target := makeIndexedWires "branch_redirect_target" 32

  -- === DECODER OUTPUTS (internal, driven by RV32IDecoder instance) ===
  let decode_optype := makeIndexedWires "decode_optype" 6
  let decode_rd := makeIndexedWires "decode_rd" 5
  let decode_rs1 := makeIndexedWires "decode_rs1" 5
  let decode_rs2 := makeIndexedWires "decode_rs2" 5
  let decode_imm := makeIndexedWires "decode_imm" 32
  let decode_valid := Wire.mk "decode_valid"
  let decode_has_rd := Wire.mk "decode_has_rd"
  let dispatch_is_integer := Wire.mk "dispatch_is_integer"
  let dispatch_is_memory := Wire.mk "dispatch_is_memory"
  let dispatch_is_branch := Wire.mk "dispatch_is_branch"
  let dispatch_is_store := Wire.mk "dispatch_is_store"  -- Unused for now
  let decode_use_imm := Wire.mk "decode_use_imm"

  -- === FETCH STAGE ===
  let fetch_pc := makeIndexedWires "fetch_pc" 32
  let fetch_stalled := Wire.mk "fetch_stalled"
  let global_stall := Wire.mk "global_stall"

  let fetch_inst : CircuitInstance := {
    moduleName := "FetchStage"
    instName := "u_fetch"
    portMap :=
      [("clock", clock), ("reset", reset),
       ("stall", global_stall),
       ("branch_valid", zero),
       ("const_0", zero), ("const_1", one)] ++
      (branch_redirect_target.enum.map (fun ⟨i, w⟩ => (s!"branch_target_{i}", w))) ++
      (fetch_pc.enum.map (fun ⟨i, w⟩ => (s!"pc_{i}", w))) ++
      [("stalled_reg", fetch_stalled)]
  }

  -- === DECODER ===
  let decoder_inst : CircuitInstance := {
    moduleName := "RV32IDecoder"
    instName := "u_decoder"
    portMap :=
      (imem_resp_data.enum.map (fun ⟨i, w⟩ => (s!"io_instr_{i}", w))) ++
      (decode_optype.enum.map (fun ⟨i, w⟩ => (s!"io_optype_{i}", w))) ++
      (decode_rd.enum.map (fun ⟨i, w⟩ => (s!"io_rd_{i}", w))) ++
      (decode_rs1.enum.map (fun ⟨i, w⟩ => (s!"io_rs1_{i}", w))) ++
      (decode_rs2.enum.map (fun ⟨i, w⟩ => (s!"io_rs2_{i}", w))) ++
      (decode_imm.enum.map (fun ⟨i, w⟩ => (s!"io_imm_{i}", w))) ++
      [("io_valid", decode_valid),
       ("io_has_rd", decode_has_rd),
       ("io_is_integer", dispatch_is_integer),
       ("io_is_memory", dispatch_is_memory),
       ("io_is_branch", dispatch_is_branch),
       ("io_is_store", dispatch_is_store),
       ("io_use_imm", decode_use_imm)]
  }

  -- === RENAME STAGE ===
  let rename_valid := Wire.mk "rename_valid"
  let rename_stall := Wire.mk "rename_stall"
  let rs1_phys := makeIndexedWires "rs1_phys" 6
  let rs2_phys := makeIndexedWires "rs2_phys" 6
  let rd_phys := makeIndexedWires "rd_phys" 6
  let old_rd_phys := makeIndexedWires "old_rd_phys" 6
  let rs1_data := makeIndexedWires "rs1_data" 32
  let rs2_data := makeIndexedWires "rs2_data" 32
  let cdb_valid := Wire.mk "cdb_valid"
  let cdb_tag := makeIndexedWires "cdb_tag" 6
  let cdb_data := makeIndexedWires "cdb_data" 32

  -- Mask CDB valid for PhysRegFile writes: don't write to p0 (x0's home register)
  -- cdb_tag_nonzero = OR of all 6 tag bits; cdb_valid_prf = cdb_valid AND cdb_tag_nonzero
  let cdb_tag_nz_tmp := List.range 5 |>.map (fun i => Wire.mk s!"cdb_tag_nz_t{i}")
  let cdb_tag_nonzero := Wire.mk "cdb_tag_nonzero"
  let cdb_valid_prf := Wire.mk "cdb_valid_prf"
  let cdb_tag_nz_gates :=
    [Gate.mkOR cdb_tag[0]! cdb_tag[1]! cdb_tag_nz_tmp[0]!] ++
    (List.range 4).map (fun i =>
      Gate.mkOR cdb_tag_nz_tmp[i]! cdb_tag[i + 2]! (if i < 3 then cdb_tag_nz_tmp[i + 1]! else cdb_tag_nonzero)) ++
    [Gate.mkAND cdb_valid cdb_tag_nonzero cdb_valid_prf]

  let rob_commit_en := Wire.mk "rob_commit_en"
  let rob_head_physRd := makeIndexedWires "rob_head_physRd" 6
  let rob_head_oldPhysRd := makeIndexedWires "rob_head_oldPhysRd" 6
  let rob_head_hasOldPhysRd := Wire.mk "rob_head_hasOldPhysRd"
  -- Retire: recycle old physical register back to FreeList only when hasOldPhysRd
  let retire_recycle_valid := Wire.mk "retire_recycle_valid"

  let rename_inst : CircuitInstance := {
    moduleName := "RenameStage_32x64"
    instName := "u_rename"
    portMap :=
      [("clock", clock), ("reset", reset),
       ("zero", zero), ("one", one),
       ("instr_valid", decode_valid),
       ("has_rd", decode_has_rd)] ++
      (decode_rs1.enum.map (fun ⟨i, w⟩ => (s!"rs1_addr_{i}", w))) ++
      (decode_rs2.enum.map (fun ⟨i, w⟩ => (s!"rs2_addr_{i}", w))) ++
      (decode_rd.enum.map (fun ⟨i, w⟩ => (s!"rd_addr_{i}", w))) ++
      [("cdb_valid", cdb_valid_prf)] ++
      (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag_{i}", w))) ++
      (cdb_data.enum.map (fun ⟨i, w⟩ => (s!"cdb_data_{i}", w))) ++
      [("retire_valid", retire_recycle_valid)] ++
      (rob_head_oldPhysRd.enum.map (fun ⟨i, w⟩ => (s!"retire_tag_{i}", w))) ++
      [("rename_valid", rename_valid), ("stall", rename_stall)] ++
      (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"rs1_phys_out_{i}", w))) ++
      (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"rs2_phys_out_{i}", w))) ++
      (rd_phys.enum.map (fun ⟨i, w⟩ => (s!"rd_phys_out_{i}", w))) ++
      (rs1_data.enum.map (fun ⟨i, w⟩ => (s!"rs1_data_{i}", w))) ++
      (rs2_data.enum.map (fun ⟨i, w⟩ => (s!"rs2_data_{i}", w))) ++
      (old_rd_phys.enum.map (fun ⟨i, w⟩ => (s!"old_rd_phys_out_{i}", w)))
  }

  -- === DISPATCH QUALIFICATION ===
  let not_stall := Wire.mk "not_stall"
  let dispatch_base_valid := Wire.mk "dispatch_base_valid"
  let dispatch_int_valid := Wire.mk "dispatch_int_valid"
  let dispatch_mem_valid := Wire.mk "dispatch_mem_valid"
  let dispatch_branch_valid := Wire.mk "dispatch_branch_valid"

  -- Store buffer enqueue = memory RS dispatch valid (TODO: filter stores only)
  let sb_enq_en := Wire.mk "sb_enq_en"

  let dispatch_gates := [
    Gate.mkNOT global_stall not_stall,
    Gate.mkAND not_stall decode_valid dispatch_base_valid,
    Gate.mkAND dispatch_base_valid dispatch_is_integer dispatch_int_valid,
    Gate.mkAND dispatch_base_valid dispatch_is_memory dispatch_mem_valid,
    Gate.mkAND dispatch_base_valid dispatch_is_branch dispatch_branch_valid
  ]

  -- === BUSY-BIT TABLE (operand readiness tracking) ===
  let busy_set_en := Wire.mk "busy_set_en"
  let busy_set_gate := Gate.mkAND rename_valid decode_has_rd busy_set_en
  let busy_src1_ready := Wire.mk "busy_src1_ready"
  let busy_src2_ready := Wire.mk "busy_src2_ready"
  let busy_src2_ready_reg := Wire.mk "busy_src2_ready_reg"
  let (busy_gates, busy_instances) := mkBusyBitTable
    clock reset zero one
    rd_phys busy_set_en
    cdb_tag cdb_valid
    rs1_phys rs2_phys
    decode_use_imm
    busy_src1_ready busy_src2_ready busy_src2_ready_reg

  -- === CDB FORWARDING (same-cycle wakeup at RS entry) ===
  -- When CDB broadcasts a tag matching an instruction's source at the same cycle
  -- it enters the RS, the busy-bit table hasn't updated yet. We must forward
  -- the CDB data and readiness directly.
  let cdb_match_src1 := Wire.mk "cdb_match_src1"
  let cdb_match_src2 := Wire.mk "cdb_match_src2"
  let cdb_fwd_src1 := Wire.mk "cdb_fwd_src1"
  let cdb_fwd_src2 := Wire.mk "cdb_fwd_src2"
  let issue_src1_ready := Wire.mk "issue_src1_ready"
  let issue_src2_ready := Wire.mk "issue_src2_ready"
  let issue_src2_ready_reg := Wire.mk "issue_src2_ready_reg"

  let cdb_fwd_cmp_src1_inst : CircuitInstance := {
    moduleName := "Comparator6"
    instName := "u_cdb_fwd_cmp_src1"
    portMap := [("one", one), ("eq", cdb_match_src1),
                ("lt", Wire.mk "cdb_fwd_cmp_src1_lt"), ("ltu", Wire.mk "cdb_fwd_cmp_src1_ltu"),
                ("gt", Wire.mk "cdb_fwd_cmp_src1_gt"), ("gtu", Wire.mk "cdb_fwd_cmp_src1_gtu")] ++
               (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  }
  let cdb_fwd_cmp_src2_inst : CircuitInstance := {
    moduleName := "Comparator6"
    instName := "u_cdb_fwd_cmp_src2"
    portMap := [("one", one), ("eq", cdb_match_src2),
                ("lt", Wire.mk "cdb_fwd_cmp_src2_lt"), ("ltu", Wire.mk "cdb_fwd_cmp_src2_ltu"),
                ("gt", Wire.mk "cdb_fwd_cmp_src2_gt"), ("gtu", Wire.mk "cdb_fwd_cmp_src2_gtu")] ++
               (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  }

  let cdb_fwd_gates := [
    Gate.mkAND cdb_valid cdb_match_src1 cdb_fwd_src1,
    Gate.mkAND cdb_valid cdb_match_src2 cdb_fwd_src2,
    Gate.mkOR busy_src1_ready cdb_fwd_src1 issue_src1_ready,
    Gate.mkOR busy_src2_ready cdb_fwd_src2 issue_src2_ready,
    Gate.mkOR busy_src2_ready_reg cdb_fwd_src2 issue_src2_ready_reg
  ]

  -- Forwarded data: use CDB data when forwarding, else PRF data
  let fwd_src1_data := makeIndexedWires "fwd_src1_data" 32
  let fwd_src2_data := makeIndexedWires "fwd_src2_data" 32
  let fwd_src1_data_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (rs1_data[i]!) (cdb_data[i]!) cdb_fwd_src1 (fwd_src1_data[i]!))
  let fwd_src2_data_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (rs2_data[i]!) (cdb_data[i]!) cdb_fwd_src2 (fwd_src2_data[i]!))

  let cdb_fwd_instances := [cdb_fwd_cmp_src1_inst, cdb_fwd_cmp_src2_inst]

  -- === SRC2 MUX: select immediate for I-type, forwarded register value for R-type ===
  let issue_src2_muxed := makeIndexedWires "issue_src2_muxed" 32
  let src2_mux_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (fwd_src2_data[i]!) (decode_imm[i]!) decode_use_imm (issue_src2_muxed[i]!))

  -- === RESERVATION STATIONS (3 instances) ===
  let rs_int_alloc_ptr_unused := makeIndexedWires "rs_int_alloc_ptr_unused" 2
  let rs_int_grant_unused := makeIndexedWires "rs_int_grant_unused" 4
  let rs_int_issue_full := Wire.mk "rs_int_issue_full"
  let rs_int_dispatch_valid := Wire.mk "rs_int_dispatch_valid"
  let rs_int_dispatch_opcode := makeIndexedWires "rs_int_dispatch_opcode" 6
  let rs_int_dispatch_src1 := makeIndexedWires "rs_int_dispatch_src1" 32
  let rs_int_dispatch_src2 := makeIndexedWires "rs_int_dispatch_src2" 32
  let rs_int_dispatch_tag := makeIndexedWires "rs_int_dispatch_tag" 6

  let rs_int_inst : CircuitInstance := {
    moduleName := "ReservationStation4"
    instName := "u_rs_integer"
    portMap := [("clock", clock), ("reset", reset),
                ("zero", zero), ("one", one), ("issue_en", dispatch_int_valid),
                ("issue_src1_ready", issue_src1_ready), ("issue_src2_ready", issue_src2_ready),
                ("cdb_valid", cdb_valid), ("dispatch_en", one),
                ("issue_full", rs_int_issue_full), ("dispatch_valid", rs_int_dispatch_valid)] ++
               (decode_optype.enum.map (fun ⟨i, w⟩ => (s!"issue_opcode_{i}", w))) ++
               (rd_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_dest_tag_{i}", w))) ++
               (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_tag_{i}", w))) ++
               (fwd_src1_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_data_{i}", w))) ++
               (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_tag_{i}", w))) ++
               (issue_src2_muxed.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_data_{i}", w))) ++
               (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag_{i}", w))) ++
               (cdb_data.enum.map (fun ⟨i, w⟩ => (s!"cdb_data_{i}", w))) ++
               (rs_int_dispatch_opcode.enum.map (fun ⟨i, w⟩ => (s!"dispatch_opcode_{i}", w))) ++
               (rs_int_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src1_data_{i}", w))) ++
               (rs_int_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src2_data_{i}", w))) ++
               (rs_int_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dispatch_dest_tag_{i}", w))) ++
               (rs_int_alloc_ptr_unused.enum.map (fun ⟨i, w⟩ => (s!"alloc_ptr_{i}", w))) ++
               (rs_int_grant_unused.enum.map (fun ⟨i, w⟩ => (s!"dispatch_grant_{i}", w)))
  }

  let rs_mem_issue_full := Wire.mk "rs_mem_issue_full"
  let rs_mem_dispatch_valid := Wire.mk "rs_mem_dispatch_valid"
  let rs_mem_dispatch_opcode := makeIndexedWires "rs_mem_dispatch_opcode" 6
  let rs_mem_dispatch_src1 := makeIndexedWires "rs_mem_dispatch_src1" 32
  let rs_mem_dispatch_src2 := makeIndexedWires "rs_mem_dispatch_src2" 32
  let rs_mem_dispatch_tag := makeIndexedWires "rs_mem_dispatch_tag" 6
  let rs_mem_alloc_ptr := makeIndexedWires "rs_mem_alloc_ptr" 2
  let rs_mem_grant := makeIndexedWires "rs_mem_grant" 4

  let rs_mem_inst : CircuitInstance := {
    moduleName := "ReservationStation4"
    instName := "u_rs_memory"
    portMap := [("clock", clock), ("reset", reset),
                ("zero", zero), ("one", one), ("issue_en", dispatch_mem_valid),
                ("issue_src1_ready", issue_src1_ready), ("issue_src2_ready", issue_src2_ready_reg),
                ("cdb_valid", cdb_valid), ("dispatch_en", one),
                ("issue_full", rs_mem_issue_full), ("dispatch_valid", rs_mem_dispatch_valid)] ++
               (decode_optype.enum.map (fun ⟨i, w⟩ => (s!"issue_opcode_{i}", w))) ++
               (rd_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_dest_tag_{i}", w))) ++
               (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_tag_{i}", w))) ++
               (fwd_src1_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_data_{i}", w))) ++
               (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_tag_{i}", w))) ++
               -- Memory RS: src2 = forwarded register value (store data), NOT immediate
               (fwd_src2_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_data_{i}", w))) ++
               (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag_{i}", w))) ++
               (cdb_data.enum.map (fun ⟨i, w⟩ => (s!"cdb_data_{i}", w))) ++
               (rs_mem_dispatch_opcode.enum.map (fun ⟨i, w⟩ => (s!"dispatch_opcode_{i}", w))) ++
               (rs_mem_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src1_data_{i}", w))) ++
               (rs_mem_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src2_data_{i}", w))) ++
               (rs_mem_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dispatch_dest_tag_{i}", w))) ++
               (rs_mem_alloc_ptr.enum.map (fun ⟨i, w⟩ => (s!"alloc_ptr_{i}", w))) ++
               (rs_mem_grant.enum.map (fun ⟨i, w⟩ => (s!"dispatch_grant_{i}", w)))
  }

  -- === IMMEDIATE REGISTER FILE (RV32I) ===
  -- Captures decode_imm at mem RS dispatch time, indexed by RS alloc_ptr.
  -- Read at issue time using dispatch_grant. Fixes OoO immediate desync.
  let imm_rf_decoded := makeIndexedWires "imm_rf_decoded" 4
  let imm_rf_we := makeIndexedWires "imm_rf_we" 4

  let imm_rf_decoder_inst : CircuitInstance := {
    moduleName := "Decoder2"
    instName := "u_imm_rf_dec"
    portMap := [
      ("in_0", rs_mem_alloc_ptr[0]!), ("in_1", rs_mem_alloc_ptr[1]!),
      ("out_0", imm_rf_decoded[0]!), ("out_1", imm_rf_decoded[1]!),
      ("out_2", imm_rf_decoded[2]!), ("out_3", imm_rf_decoded[3]!)
    ]
  }

  let imm_rf_we_gates := (List.range 4).map (fun e =>
    Gate.mkAND imm_rf_decoded[e]! dispatch_mem_valid imm_rf_we[e]!)

  let imm_rf_entries := (List.range 4).map (fun e =>
    makeIndexedWires s!"imm_rf_e{e}" 32)
  let imm_rf_gates := (List.range 4).map (fun e =>
    let entry := imm_rf_entries[e]!
    (List.range 32).map (fun b =>
      let next := Wire.mk s!"imm_rf_next_e{e}_{b}"
      [ Gate.mkMUX entry[b]! decode_imm[b]! imm_rf_we[e]! next,
        Gate.mkDFF next clock reset entry[b]! ]
    ) |>.flatten
  ) |>.flatten

  let captured_imm := makeIndexedWires "captured_imm" 32
  let imm_rf_sel := makeIndexedWires "imm_rf_sel" 2
  let imm_rf_sel_gates := [
    Gate.mkOR rs_mem_grant[1]! rs_mem_grant[3]! imm_rf_sel[0]!,
    Gate.mkOR rs_mem_grant[2]! rs_mem_grant[3]! imm_rf_sel[1]!
  ]

  let imm_rf_mux_inst : CircuitInstance := {
    moduleName := "Mux4x32"
    instName := "u_imm_rf_mux"
    portMap :=
      (((List.range 4).map (fun e =>
          (List.range 32).map (fun b =>
            (s!"in{e}[{b}]", imm_rf_entries[e]![b]!)
          )
        )).flatten) ++
      (imm_rf_sel.enum.map (fun ⟨i, w⟩ => (s!"sel[{i}]", w))) ++
      (captured_imm.enum.map (fun ⟨i, w⟩ => (s!"out[{i}]", w)))
  }

  let rs_branch_alloc_ptr_unused := makeIndexedWires "rs_branch_alloc_ptr_unused" 2
  let rs_branch_grant_unused := makeIndexedWires "rs_branch_grant_unused" 4
  let rs_branch_issue_full := Wire.mk "rs_branch_issue_full"
  let rs_branch_dispatch_valid := Wire.mk "rs_branch_dispatch_valid"
  let rs_branch_dispatch_opcode := makeIndexedWires "rs_branch_dispatch_opcode" 6
  let rs_branch_dispatch_src1 := makeIndexedWires "rs_branch_dispatch_src1" 32
  let rs_branch_dispatch_src2 := makeIndexedWires "rs_branch_dispatch_src2" 32
  let rs_branch_dispatch_tag := makeIndexedWires "rs_branch_dispatch_tag" 6

  let rs_branch_inst : CircuitInstance := {
    moduleName := "ReservationStation4"
    instName := "u_rs_branch"
    portMap := [("clock", clock), ("reset", reset),
                ("zero", zero), ("one", one), ("issue_en", dispatch_branch_valid),
                ("issue_src1_ready", issue_src1_ready), ("issue_src2_ready", issue_src2_ready),
                ("cdb_valid", cdb_valid), ("dispatch_en", one),
                ("issue_full", rs_branch_issue_full), ("dispatch_valid", rs_branch_dispatch_valid)] ++
               (decode_optype.enum.map (fun ⟨i, w⟩ => (s!"issue_opcode_{i}", w))) ++
               (rd_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_dest_tag_{i}", w))) ++
               (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_tag_{i}", w))) ++
               (fwd_src1_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_data_{i}", w))) ++
               (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_tag_{i}", w))) ++
               -- Branch RS: src2 = forwarded register value, NOT immediate
               (fwd_src2_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_data_{i}", w))) ++
               (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag_{i}", w))) ++
               (cdb_data.enum.map (fun ⟨i, w⟩ => (s!"cdb_data_{i}", w))) ++
               (rs_branch_dispatch_opcode.enum.map (fun ⟨i, w⟩ => (s!"dispatch_opcode_{i}", w))) ++
               (rs_branch_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src1_data_{i}", w))) ++
               (rs_branch_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src2_data_{i}", w))) ++
               (rs_branch_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dispatch_dest_tag_{i}", w))) ++
               (rs_branch_alloc_ptr_unused.enum.map (fun ⟨i, w⟩ => (s!"alloc_ptr_{i}", w))) ++
               (rs_branch_grant_unused.enum.map (fun ⟨i, w⟩ => (s!"dispatch_grant_{i}", w)))
  }

  -- === EXECUTION UNITS ===
  let int_result := makeIndexedWires "int_result" 32
  let int_tag_out := makeIndexedWires "int_tag_out" 6

  -- ALU opcode LUT: translate 6-bit dispatch optype → 4-bit ALU op
  -- Driven from RS dispatch opcode (not imem_resp_data) so the ALU executes
  -- the correct operation for the dispatched instruction, not the current fetch.
  let alu_op := makeIndexedWires "alu_op" 4
  let alu_lut_gates := mkOpTypeToALU4 "alulut" rs_int_dispatch_opcode alu_op aluMapping_RV32I

  let int_exec_inst : CircuitInstance := {
    moduleName := "IntegerExecUnit"
    instName := "u_exec_integer"
    portMap :=
      (rs_int_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (rs_int_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      (alu_op.enum.map (fun ⟨i, w⟩ => (s!"opcode_{i}", w))) ++
      (rs_int_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dest_tag_{i}", w))) ++
      [("zero", zero), ("one", one)] ++
      (int_result.enum.map (fun ⟨i, w⟩ => (s!"result_{i}", w))) ++
      (int_tag_out.enum.map (fun ⟨i, w⟩ => (s!"tag_out_{i}", w)))
  }

  -- Branch execution unit
  let branch_result := makeIndexedWires "branch_result" 32
  let branch_tag_out := makeIndexedWires "branch_tag_out" 6

  let branch_exec_inst : CircuitInstance := {
    moduleName := "BranchExecUnit"
    instName := "u_exec_branch"
    portMap :=
      (rs_branch_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"src1_{i}", w))) ++
      (rs_branch_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"src2_{i}", w))) ++
      (rs_branch_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dest_tag_{i}", w))) ++
      [("zero", zero)] ++
      (branch_result.enum.map (fun ⟨i, w⟩ => (s!"result_{i}", w))) ++
      (branch_tag_out.enum.map (fun ⟨i, w⟩ => (s!"tag_out_{i}", w)))
  }

  let mem_address := makeIndexedWires "mem_address" 32
  let mem_tag_out := makeIndexedWires "mem_tag_out" 6

  let mem_exec_inst : CircuitInstance := {
    moduleName := "MemoryExecUnit"
    instName := "u_exec_memory"
    portMap :=
      (rs_mem_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"base_{i}", w))) ++
      (captured_imm.enum.map (fun ⟨i, w⟩ => (s!"offset_{i}", w))) ++
      (rs_mem_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dest_tag_{i}", w))) ++
      [("zero", zero)] ++
      (mem_address.enum.map (fun ⟨i, w⟩ => (s!"address_{i}", w))) ++
      (mem_tag_out.enum.map (fun ⟨i, w⟩ => (s!"tag_out_{i}", w)))
  }

  -- === LSU ===
  let lsu_agu_address := makeIndexedWires "lsu_agu_address" 32
  let lsu_agu_tag := makeIndexedWires "lsu_agu_tag" 6
  let lsu_sb_full := Wire.mk "lsu_sb_full"
  let lsu_sb_empty := Wire.mk "lsu_sb_empty"
  let lsu_sb_fwd_hit := Wire.mk "lsu_sb_fwd_hit"
  let lsu_sb_fwd_data := makeIndexedWires "lsu_sb_fwd_data" 32
  let lsu_sb_deq_valid := Wire.mk "lsu_sb_deq_valid"
  let lsu_sb_deq_bits := makeIndexedWires "lsu_sb_deq_bits" 66
  let lsu_sb_enq_idx := makeIndexedWires "lsu_sb_enq_idx" 3

  let lsu_inst : CircuitInstance := {
    moduleName := "LSU"
    instName := "u_lsu"
    portMap := [("clock", clock), ("reset", reset),
                ("zero", zero), ("one", one),
                ("commit_store_en", rob_commit_en),
                ("deq_ready", dmem_req_ready),
                ("flush_en", zero),
                ("sb_enq_en", sb_enq_en),
                ("sb_full", lsu_sb_full), ("sb_empty", lsu_sb_empty), ("sb_fwd_hit", lsu_sb_fwd_hit),
                ("sb_deq_valid", lsu_sb_deq_valid)] ++
               (rs_mem_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"dispatch_base_{i}", w))) ++
               (captured_imm.enum.map (fun ⟨i, w⟩ => (s!"dispatch_offset_{i}", w))) ++
               (rs_mem_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dispatch_dest_tag_{i}", w))) ++
               (rs_mem_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"store_data_{i}", w))) ++
               ((makeIndexedWires "lsu_commit_idx" 3).enum.map (fun ⟨i, w⟩ => (s!"commit_store_idx_{i}", w))) ++
               (mem_address.enum.map (fun ⟨i, w⟩ => (s!"fwd_address_{i}", w))) ++
               ((makeIndexedWires "lsu_sb_enq_size" 2).enum.map (fun ⟨i, w⟩ => (s!"sb_enq_size_{i}", w))) ++
               (lsu_agu_address.enum.map (fun ⟨i, w⟩ => (s!"agu_address_{i}", w))) ++
               (lsu_agu_tag.enum.map (fun ⟨i, w⟩ => (s!"agu_tag_out_{i}", w))) ++
               (lsu_sb_fwd_data.enum.map (fun ⟨i, w⟩ => (s!"sb_fwd_data_{i}", w))) ++
               (lsu_sb_deq_bits.enum.map (fun ⟨i, w⟩ => (s!"sb_deq_bits_{i}", w))) ++
               (lsu_sb_enq_idx.enum.map (fun ⟨i, w⟩ => (s!"sb_enq_idx_{i}", w)))
  }

  -- === ROB ===
  let rob_full := Wire.mk "rob_full"
  let rob_empty := Wire.mk "rob_empty"
  let rob_alloc_idx := makeIndexedWires "rob_alloc_idx" 4
  let rob_head_valid := Wire.mk "rob_head_valid"
  let rob_head_complete := Wire.mk "rob_head_complete"
  let rob_head_hasPhysRd := Wire.mk "rob_head_hasPhysRd"
  let rob_head_archRd := makeIndexedWires "rob_head_archRd" 5
  let rob_head_exception := Wire.mk "rob_head_exception"
  let rob_head_isBranch := Wire.mk "rob_head_isBranch"
  let rob_head_mispredicted := Wire.mk "rob_head_mispredicted"

  let rob_inst : CircuitInstance := {
    moduleName := "ROB16"
    instName := "u_rob"
    portMap :=
      [("clock", clock), ("reset", reset),
       ("zero", zero), ("one", one),
       ("alloc_en", rename_valid)] ++
      (rd_phys.enum.map (fun ⟨i, w⟩ => (s!"alloc_physRd[{i}]", w))) ++
      [("alloc_hasPhysRd", decode_has_rd)] ++
      (old_rd_phys.enum.map (fun ⟨i, w⟩ => (s!"alloc_oldPhysRd[{i}]", w))) ++
      [("alloc_hasOldPhysRd", decode_has_rd)] ++
      (decode_rd.enum.map (fun ⟨i, w⟩ => (s!"alloc_archRd[{i}]", w))) ++
      [("alloc_isBranch", dispatch_is_branch),
       ("cdb_valid", cdb_valid)] ++
      (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag[{i}]", w))) ++
      [("cdb_exception", zero),
       ("cdb_mispredicted", zero),
       ("commit_en", rob_commit_en),
       ("flush_en", zero),
       ("full", rob_full),
       ("empty", rob_empty)] ++
      (rob_alloc_idx.enum.map (fun ⟨i, w⟩ => (s!"alloc_idx[{i}]", w))) ++
      [("head_valid", rob_head_valid),
       ("head_complete", rob_head_complete)] ++
      (rob_head_physRd.enum.map (fun ⟨i, w⟩ => (s!"head_physRd[{i}]", w))) ++
      [("head_hasPhysRd", rob_head_hasPhysRd)] ++
      (rob_head_oldPhysRd.enum.map (fun ⟨i, w⟩ => (s!"head_oldPhysRd[{i}]", w))) ++
      [("head_hasOldPhysRd", rob_head_hasOldPhysRd)] ++
      (rob_head_archRd.enum.map (fun ⟨i, w⟩ => (s!"head_archRd[{i}]", w))) ++
      [("head_exception", rob_head_exception),
       ("head_isBranch", rob_head_isBranch),
       ("head_mispredicted", rob_head_mispredicted)]
  }

  -- === CDB REPLAY BUFFER (saves integer result when LSU wins arbitration) ===
  let replay_valid := Wire.mk "replay_valid"
  let replay_valid_next := Wire.mk "replay_valid_next"
  let replay_tag := makeIndexedWires "replay_tag" 6
  let replay_tag_next := makeIndexedWires "replay_tag_next" 6
  let replay_data := makeIndexedWires "replay_data" 32
  let replay_data_next := makeIndexedWires "replay_data_next" 32

  -- === CDB ARBITRATION (Priority: Replay > LSU > Integer > Branch) ===

  -- Level 0: Merge Branch into Integer (Integer has priority)
  -- Branch exec unit outputs result=0 and tag passthrough
  let int_branch_valid := Wire.mk "int_branch_valid"
  let int_branch_tag := makeIndexedWires "int_branch_tag" 6
  let int_branch_data := makeIndexedWires "int_branch_data" 32

  let arb_level0_gates :=
    [Gate.mkOR rs_int_dispatch_valid rs_branch_dispatch_valid int_branch_valid] ++
    (List.range 6).map (fun i =>
      Gate.mkMUX branch_tag_out[i]! int_tag_out[i]! rs_int_dispatch_valid int_branch_tag[i]!) ++
    (List.range 32).map (fun i =>
      Gate.mkMUX branch_result[i]! int_result[i]! rs_int_dispatch_valid int_branch_data[i]!)

  -- Save condition: int/branch has result AND LSU wins AND no replay pending
  let int_dropped := Wire.mk "int_dropped"
  let int_dropped_tmp := Wire.mk "int_dropped_tmp"
  let not_replay_valid := Wire.mk "not_replay_valid"
  -- Replay wins CDB this cycle (clears replay)
  let replay_wins := Wire.mk "replay_wins"

  let replay_save_gates := [
    Gate.mkNOT replay_valid not_replay_valid,
    Gate.mkAND int_branch_valid lsu_sb_deq_valid int_dropped_tmp,
    Gate.mkAND int_dropped_tmp not_replay_valid int_dropped,
    Gate.mkMUX replay_valid one int_dropped (Wire.mk "replay_v_tmp1"),
    Gate.mkMUX (Wire.mk "replay_v_tmp1") zero replay_wins replay_valid_next,
    Gate.mkDFF replay_valid_next clock reset replay_valid
  ]

  -- Save tag and data when int_dropped
  let replay_tag_gates := (List.range 6).map (fun i =>
    [Gate.mkMUX replay_tag[i]! int_branch_tag[i]! int_dropped replay_tag_next[i]!,
     Gate.mkDFF replay_tag_next[i]! clock reset replay_tag[i]!]) |>.flatten

  let replay_data_gates := (List.range 32).map (fun i =>
    [Gate.mkMUX replay_data[i]! int_branch_data[i]! int_dropped replay_data_next[i]!,
     Gate.mkDFF replay_data_next[i]! clock reset replay_data[i]!]) |>.flatten

  -- replay_wins = replay_valid (highest priority)
  let replay_wins_gate := [Gate.mkBUF replay_valid replay_wins]

  -- lsu_wins = lsu_valid AND NOT replay_valid
  let lsu_wins := Wire.mk "lsu_wins"
  let lsu_wins_gate := [Gate.mkAND lsu_sb_deq_valid not_replay_valid lsu_wins]

  -- int_wins = int_branch_valid AND NOT lsu_valid AND NOT replay_valid
  let int_wins := Wire.mk "int_wins"
  let int_wins_tmp := Wire.mk "int_wins_tmp"
  let not_lsu_valid := Wire.mk "not_lsu_valid"
  let int_wins_gates := [
    Gate.mkNOT lsu_sb_deq_valid not_lsu_valid,
    Gate.mkAND int_branch_valid not_lsu_valid int_wins_tmp,
    Gate.mkAND int_wins_tmp not_replay_valid int_wins
  ]

  -- cdb_valid = replay_wins OR lsu_wins OR int_wins
  let cdb_valid_tmp := Wire.mk "cdb_valid_tmp"
  let cdb_valid_gates := [
    Gate.mkOR replay_wins lsu_wins cdb_valid_tmp,
    Gate.mkOR cdb_valid_tmp int_wins cdb_valid
  ]

  -- cdb_tag/cdb_data: MUX chain (int/branch -> lsu -> replay, last wins)
  let cdb_tag_mux_gates := (List.range 6).map (fun i =>
    let m1 := Wire.mk s!"cdb_tag_m1_{i}"
    [Gate.mkMUX int_branch_tag[i]! lsu_agu_tag[i]! lsu_wins m1,
     Gate.mkMUX m1 replay_tag[i]! replay_wins cdb_tag[i]!])
  let cdb_data_mux_gates := (List.range 32).map (fun i =>
    let m1 := Wire.mk s!"cdb_data_m1_{i}"
    [Gate.mkMUX int_branch_data[i]! lsu_sb_fwd_data[i]! lsu_wins m1,
     Gate.mkMUX m1 replay_data[i]! replay_wins cdb_data[i]!])
  let cdb_mux_gates := cdb_tag_mux_gates.flatten ++ cdb_data_mux_gates.flatten

  let cdb_arb_gates := arb_level0_gates ++ replay_save_gates ++ replay_tag_gates ++ replay_data_gates ++
    replay_wins_gate ++ lsu_wins_gate ++ int_wins_gates ++ cdb_valid_gates ++ cdb_mux_gates

  -- === COMMIT CONTROL ===
  let commit_gates := [
    Gate.mkAND rob_head_valid rob_head_complete rob_commit_en,
    -- Recycle old physical register to FreeList only when commit has oldPhysRd
    Gate.mkAND rob_commit_en rob_head_hasOldPhysRd retire_recycle_valid
  ]

  -- === STALL GENERATION ===
  let stall_tmp1 := Wire.mk "stall_tmp1"
  let stall_tmp2 := Wire.mk "stall_tmp2"
  let stall_tmp3 := Wire.mk "stall_tmp3"
  let stall_tmp4 := Wire.mk "stall_tmp4"

  let stall_gates := [
    Gate.mkOR rename_stall rob_full stall_tmp1,
    Gate.mkOR stall_tmp1 rs_int_issue_full stall_tmp2,
    Gate.mkOR stall_tmp2 rs_mem_issue_full stall_tmp3,
    Gate.mkOR stall_tmp3 rs_branch_issue_full stall_tmp4,
    Gate.mkOR stall_tmp4 lsu_sb_full global_stall
  ]

  -- === MEMORY INTERFACE ===
  let dmem_req_valid := Wire.mk "dmem_req_valid"
  let dmem_req_we := Wire.mk "dmem_req_we"
  let dmem_req_addr := makeIndexedWires "dmem_req_addr" 32
  let dmem_req_data := makeIndexedWires "dmem_req_data" 32

  -- sb_enq_en = rs_mem_dispatch_valid (TODO: filter stores only via RS opcode)
  let sb_enq_gate := Gate.mkBUF rs_mem_dispatch_valid sb_enq_en

  -- dmem interface: loads + store buffer dequeues
  let dmem_valid_tmp := Wire.mk "dmem_valid_tmp"
  let dmem_gates := [sb_enq_gate,
    Gate.mkOR rs_mem_dispatch_valid lsu_sb_deq_valid dmem_valid_tmp,
    Gate.mkBUF dmem_valid_tmp dmem_req_valid,
    Gate.mkBUF lsu_sb_deq_valid dmem_req_we] ++
    (List.range 32).map (fun i =>
      Gate.mkMUX mem_address[i]! lsu_sb_deq_bits[i]! lsu_sb_deq_valid dmem_req_addr[i]!) ++
    (List.range 32).map (fun i =>
      Gate.mkBUF lsu_sb_deq_bits[32+i]! dmem_req_data[i]!)

  -- === OUTPUT BUFFERS ===
  let global_stall_out := Wire.mk "global_stall_out"
  let output_gates := [Gate.mkBUF global_stall global_stall_out]

  { name := "CPU_RV32I"
    inputs := [clock, reset, zero, one] ++
              imem_resp_data ++
              [dmem_req_ready, dmem_resp_valid] ++ dmem_resp_data ++
              branch_redirect_target
    outputs := fetch_pc ++ [fetch_stalled, global_stall_out] ++
               [dmem_req_valid, dmem_req_we] ++ dmem_req_addr ++ dmem_req_data ++
               [rob_empty]
    gates := dispatch_gates ++ src2_mux_gates ++ [busy_set_gate] ++ busy_gates ++
             cdb_fwd_gates ++ fwd_src1_data_gates ++ fwd_src2_data_gates ++
             alu_lut_gates ++ cdb_tag_nz_gates ++ cdb_arb_gates ++
             imm_rf_we_gates ++ imm_rf_gates ++ imm_rf_sel_gates ++
             commit_gates ++ stall_gates ++ dmem_gates ++ output_gates
    instances := [fetch_inst, decoder_inst, rename_inst] ++ busy_instances ++
                  cdb_fwd_instances ++
                  [rs_int_inst, rs_mem_inst, rs_branch_inst,
                  int_exec_inst, branch_exec_inst, mem_exec_inst,
                  rob_inst, lsu_inst,
                  imm_rf_decoder_inst, imm_rf_mux_inst]
    -- V2 codegen annotations
    signalGroups := [
      { name := "imem_resp_data", width := 32, wires := imem_resp_data },
      { name := "dmem_resp_data", width := 32, wires := dmem_resp_data },
      { name := "decode_optype", width := 6, wires := decode_optype },
      { name := "decode_rd", width := 5, wires := decode_rd },
      { name := "decode_rs1", width := 5, wires := decode_rs1 },
      { name := "decode_rs2", width := 5, wires := decode_rs2 },
      { name := "decode_imm", width := 32, wires := decode_imm },
      { name := "branch_redirect_target", width := 32, wires := branch_redirect_target },
      { name := "fetch_pc", width := 32, wires := fetch_pc },
      { name := "rs1_phys", width := 6, wires := rs1_phys },
      { name := "rs2_phys", width := 6, wires := rs2_phys },
      { name := "rd_phys", width := 6, wires := rd_phys },
      { name := "old_rd_phys", width := 6, wires := old_rd_phys },
      { name := "rs1_data", width := 32, wires := rs1_data },
      { name := "rs2_data", width := 32, wires := rs2_data },
      { name := "issue_src2_muxed", width := 32, wires := issue_src2_muxed },
      { name := "cdb_tag", width := 6, wires := cdb_tag },
      { name := "cdb_data", width := 32, wires := cdb_data },
      { name := "rob_head_physRd", width := 6, wires := rob_head_physRd },
      { name := "rob_alloc_idx", width := 4, wires := rob_alloc_idx },
      { name := "rob_head_oldPhysRd", width := 6, wires := rob_head_oldPhysRd },
      { name := "rob_head_archRd", width := 5, wires := rob_head_archRd },
      { name := "int_result", width := 32, wires := int_result },
      { name := "int_tag_out", width := 6, wires := int_tag_out },
      { name := "mem_address", width := 32, wires := mem_address },
      { name := "mem_tag_out", width := 6, wires := mem_tag_out },
      { name := "lsu_agu_address", width := 32, wires := lsu_agu_address },
      { name := "lsu_agu_tag", width := 6, wires := lsu_agu_tag },
      { name := "lsu_sb_fwd_data", width := 32, wires := lsu_sb_fwd_data },
      { name := "lsu_sb_deq_bits", width := 66, wires := lsu_sb_deq_bits },
      { name := "lsu_sb_enq_idx", width := 3, wires := lsu_sb_enq_idx },
      { name := "dmem_req_addr", width := 32, wires := dmem_req_addr },
      { name := "dmem_req_data", width := 32, wires := dmem_req_data },
      { name := "rs_int_dispatch_opcode", width := 6, wires := rs_int_dispatch_opcode },
      { name := "rs_int_dispatch_src1", width := 32, wires := rs_int_dispatch_src1 },
      { name := "rs_int_dispatch_src2", width := 32, wires := rs_int_dispatch_src2 },
      { name := "rs_int_dispatch_tag", width := 6, wires := rs_int_dispatch_tag },
      { name := "rs_mem_dispatch_opcode", width := 6, wires := rs_mem_dispatch_opcode },
      { name := "rs_mem_dispatch_src1", width := 32, wires := rs_mem_dispatch_src1 },
      { name := "rs_mem_dispatch_src2", width := 32, wires := rs_mem_dispatch_src2 },
      { name := "rs_mem_dispatch_tag", width := 6, wires := rs_mem_dispatch_tag },
      { name := "rs_branch_dispatch_opcode", width := 6, wires := rs_branch_dispatch_opcode },
      { name := "rs_branch_dispatch_src1", width := 32, wires := rs_branch_dispatch_src1 },
      { name := "rs_branch_dispatch_src2", width := 32, wires := rs_branch_dispatch_src2 },
      { name := "rs_branch_dispatch_tag", width := 6, wires := rs_branch_dispatch_tag }
    ]
  }

/--
RV32IM CPU Structural Circuit (With M-Extension)

Complete synthesizable CPU with all 12 verified submodules:
1. FetchStage - PC management
2. RV32IMDecoder - Instruction decoder (with M-extension)
3. RenameStage_32x64 - RAT + FreeList + PhysRegFile
4-7. ReservationStation4 (×4) - Integer, Memory, Branch, MulDiv
8. IntegerExecUnit - ALU operations
9. MemoryExecUnit - Address calculation
10. MulDivExecUnit - Multiply/divide
11. ROB16 - Reorder buffer
12. LSU - Load-store unit with store buffer

Design notes:
- Source ready bits tied high (always ready)
- Branch redirect tied low (no redirects for now)
- CDB arbitration: priority MUX (LSU > MulDiv > Integer)
-/
def mkCPU_RV32IM : Circuit :=
  -- Global signals
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- === EXTERNAL INTERFACES ===
  -- Memory interfaces
  let imem_resp_data := makeIndexedWires "imem_resp_data" 32
  let dmem_req_ready := Wire.mk "dmem_req_ready"
  let dmem_resp_valid := Wire.mk "dmem_resp_valid"
  let dmem_resp_data := makeIndexedWires "dmem_resp_data" 32

  -- Branch redirect (tied to zero for now - no branch prediction)
  let branch_redirect_target := makeIndexedWires "branch_redirect_target" 32

  -- === DECODER OUTPUTS (internal, driven by RV32IMDecoder instance) ===
  let decode_optype := makeIndexedWires "decode_optype" 6
  let decode_rd := makeIndexedWires "decode_rd" 5
  let decode_rs1 := makeIndexedWires "decode_rs1" 5
  let decode_rs2 := makeIndexedWires "decode_rs2" 5
  let decode_imm := makeIndexedWires "decode_imm" 32
  let decode_valid := Wire.mk "decode_valid"
  let decode_has_rd := Wire.mk "decode_has_rd"
  let dispatch_is_integer := Wire.mk "dispatch_is_integer"
  let dispatch_is_memory := Wire.mk "dispatch_is_memory"
  let dispatch_is_branch := Wire.mk "dispatch_is_branch"
  let dispatch_is_muldiv := Wire.mk "dispatch_is_muldiv"
  let dispatch_is_store := Wire.mk "dispatch_is_store"  -- Unused for now
  let decode_use_imm := Wire.mk "decode_use_imm"

  -- === FETCH STAGE ===
  let fetch_pc := makeIndexedWires "fetch_pc" 32
  let fetch_stalled := Wire.mk "fetch_stalled"
  let global_stall := Wire.mk "global_stall"

  let fetch_inst : CircuitInstance := {
    moduleName := "FetchStage"
    instName := "u_fetch"
    portMap :=
      [("clock", clock), ("reset", reset),
       ("stall", global_stall),
       ("branch_valid", zero),  -- No branch redirect for now
       ("const_0", zero), ("const_1", one)] ++
      (branch_redirect_target.enum.map (fun ⟨i, w⟩ => (s!"branch_target_{i}", w))) ++
      (fetch_pc.enum.map (fun ⟨i, w⟩ => (s!"pc_{i}", w))) ++
      [("stalled_reg", fetch_stalled)]
  }

  -- === DECODER ===
  let decoder_inst : CircuitInstance := {
    moduleName := "RV32IMDecoder"
    instName := "u_decoder"
    portMap :=
      (imem_resp_data.enum.map (fun ⟨i, w⟩ => (s!"io_instr_{i}", w))) ++
      (decode_optype.enum.map (fun ⟨i, w⟩ => (s!"io_optype_{i}", w))) ++
      (decode_rd.enum.map (fun ⟨i, w⟩ => (s!"io_rd_{i}", w))) ++
      (decode_rs1.enum.map (fun ⟨i, w⟩ => (s!"io_rs1_{i}", w))) ++
      (decode_rs2.enum.map (fun ⟨i, w⟩ => (s!"io_rs2_{i}", w))) ++
      (decode_imm.enum.map (fun ⟨i, w⟩ => (s!"io_imm_{i}", w))) ++
      [("io_valid", decode_valid),
       ("io_has_rd", decode_has_rd),
       ("io_is_integer", dispatch_is_integer),
       ("io_is_memory", dispatch_is_memory),
       ("io_is_branch", dispatch_is_branch),
       ("io_is_muldiv", dispatch_is_muldiv),
       ("io_is_store", dispatch_is_store),
       ("io_use_imm", decode_use_imm)]
  }

  -- === RENAME STAGE ===
  let rename_valid := Wire.mk "rename_valid"
  let rename_stall := Wire.mk "rename_stall"
  let rs1_phys := makeIndexedWires "rs1_phys" 6
  let rs2_phys := makeIndexedWires "rs2_phys" 6
  let rd_phys := makeIndexedWires "rd_phys" 6
  let old_rd_phys := makeIndexedWires "old_rd_phys" 6
  let rs1_data := makeIndexedWires "rs1_data" 32
  let rs2_data := makeIndexedWires "rs2_data" 32

  -- CDB signals (driven by arbitration)
  let cdb_valid := Wire.mk "cdb_valid"
  let cdb_tag := makeIndexedWires "cdb_tag" 6
  let cdb_data := makeIndexedWires "cdb_data" 32

  -- Mask CDB valid for PhysRegFile writes: don't write to p0 (x0's home register)
  let cdb_tag_nz_tmp := List.range 5 |>.map (fun i => Wire.mk s!"cdb_tag_nz_t{i}")
  let cdb_tag_nonzero := Wire.mk "cdb_tag_nonzero"
  let cdb_valid_prf := Wire.mk "cdb_valid_prf"
  let cdb_tag_nz_gates :=
    [Gate.mkOR cdb_tag[0]! cdb_tag[1]! cdb_tag_nz_tmp[0]!] ++
    (List.range 4).map (fun i =>
      Gate.mkOR cdb_tag_nz_tmp[i]! cdb_tag[i + 2]! (if i < 3 then cdb_tag_nz_tmp[i + 1]! else cdb_tag_nonzero)) ++
    [Gate.mkAND cdb_valid cdb_tag_nonzero cdb_valid_prf]

  -- ROB commit signals
  let rob_commit_en := Wire.mk "rob_commit_en"
  let rob_head_physRd := makeIndexedWires "rob_head_physRd" 6
  let rob_head_oldPhysRd := makeIndexedWires "rob_head_oldPhysRd" 6
  let rob_head_hasOldPhysRd := Wire.mk "rob_head_hasOldPhysRd"
  -- Retire: recycle old physical register back to FreeList only when hasOldPhysRd
  let retire_recycle_valid := Wire.mk "retire_recycle_valid"

  let rename_inst : CircuitInstance := {
    moduleName := "RenameStage_32x64"
    instName := "u_rename"
    portMap :=
      [("clock", clock), ("reset", reset),
       ("zero", zero), ("one", one),
       ("instr_valid", decode_valid),
       ("has_rd", decode_has_rd)] ++
      (decode_rs1.enum.map (fun ⟨i, w⟩ => (s!"rs1_addr_{i}", w))) ++
      (decode_rs2.enum.map (fun ⟨i, w⟩ => (s!"rs2_addr_{i}", w))) ++
      (decode_rd.enum.map (fun ⟨i, w⟩ => (s!"rd_addr_{i}", w))) ++
      [("cdb_valid", cdb_valid_prf)] ++
      (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag_{i}", w))) ++
      (cdb_data.enum.map (fun ⟨i, w⟩ => (s!"cdb_data_{i}", w))) ++
      [("retire_valid", retire_recycle_valid)] ++
      (rob_head_oldPhysRd.enum.map (fun ⟨i, w⟩ => (s!"retire_tag_{i}", w))) ++
      [("rename_valid", rename_valid), ("stall", rename_stall)] ++
      (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"rs1_phys_out_{i}", w))) ++
      (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"rs2_phys_out_{i}", w))) ++
      (rd_phys.enum.map (fun ⟨i, w⟩ => (s!"rd_phys_out_{i}", w))) ++
      (rs1_data.enum.map (fun ⟨i, w⟩ => (s!"rs1_data_{i}", w))) ++
      (rs2_data.enum.map (fun ⟨i, w⟩ => (s!"rs2_data_{i}", w))) ++
      (old_rd_phys.enum.map (fun ⟨i, w⟩ => (s!"old_rd_phys_out_{i}", w)))
  }

  -- === DISPATCH QUALIFICATION GATES ===
  -- Dispatch valid = NOT(stall) AND decode_valid AND dispatch_is_X
  let not_stall := Wire.mk "not_stall"
  let dispatch_base_valid := Wire.mk "dispatch_base_valid"
  let dispatch_int_valid := Wire.mk "dispatch_int_valid"
  let dispatch_mem_valid := Wire.mk "dispatch_mem_valid"
  let dispatch_branch_valid := Wire.mk "dispatch_branch_valid"
  let dispatch_muldiv_valid := Wire.mk "dispatch_muldiv_valid"

  -- Store buffer enqueue = memory RS dispatch valid (TODO: filter stores only)
  let sb_enq_en := Wire.mk "sb_enq_en"

  let dispatch_gates := [
    Gate.mkNOT global_stall not_stall,
    Gate.mkAND not_stall decode_valid dispatch_base_valid,
    Gate.mkAND dispatch_base_valid dispatch_is_integer dispatch_int_valid,
    Gate.mkAND dispatch_base_valid dispatch_is_memory dispatch_mem_valid,
    Gate.mkAND dispatch_base_valid dispatch_is_branch dispatch_branch_valid,
    Gate.mkAND dispatch_base_valid dispatch_is_muldiv dispatch_muldiv_valid
  ]

  -- === BUSY-BIT TABLE (operand readiness tracking) ===
  let busy_set_en := Wire.mk "busy_set_en"
  let busy_set_gate := Gate.mkAND rename_valid decode_has_rd busy_set_en
  let busy_src1_ready := Wire.mk "busy_src1_ready"
  let busy_src2_ready := Wire.mk "busy_src2_ready"
  let busy_src2_ready_reg := Wire.mk "busy_src2_ready_reg"
  let (busy_gates, busy_instances) := mkBusyBitTable
    clock reset zero one
    rd_phys busy_set_en
    cdb_tag cdb_valid
    rs1_phys rs2_phys
    decode_use_imm
    busy_src1_ready busy_src2_ready busy_src2_ready_reg

  -- === CDB FORWARDING (same-cycle wakeup at RS entry) ===
  let cdb_match_src1 := Wire.mk "cdb_match_src1"
  let cdb_match_src2 := Wire.mk "cdb_match_src2"
  let cdb_fwd_src1 := Wire.mk "cdb_fwd_src1"
  let cdb_fwd_src2 := Wire.mk "cdb_fwd_src2"
  let issue_src1_ready := Wire.mk "issue_src1_ready"
  let issue_src2_ready := Wire.mk "issue_src2_ready"
  let issue_src2_ready_reg := Wire.mk "issue_src2_ready_reg"

  let cdb_fwd_cmp_src1_inst : CircuitInstance := {
    moduleName := "Comparator6"
    instName := "u_cdb_fwd_cmp_src1"
    portMap := [("one", one), ("eq", cdb_match_src1),
                ("lt", Wire.mk "cdb_fwd_cmp_src1_lt"), ("ltu", Wire.mk "cdb_fwd_cmp_src1_ltu"),
                ("gt", Wire.mk "cdb_fwd_cmp_src1_gt"), ("gtu", Wire.mk "cdb_fwd_cmp_src1_gtu")] ++
               (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  }
  let cdb_fwd_cmp_src2_inst : CircuitInstance := {
    moduleName := "Comparator6"
    instName := "u_cdb_fwd_cmp_src2"
    portMap := [("one", one), ("eq", cdb_match_src2),
                ("lt", Wire.mk "cdb_fwd_cmp_src2_lt"), ("ltu", Wire.mk "cdb_fwd_cmp_src2_ltu"),
                ("gt", Wire.mk "cdb_fwd_cmp_src2_gt"), ("gtu", Wire.mk "cdb_fwd_cmp_src2_gtu")] ++
               (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  }

  let cdb_fwd_gates := [
    Gate.mkAND cdb_valid cdb_match_src1 cdb_fwd_src1,
    Gate.mkAND cdb_valid cdb_match_src2 cdb_fwd_src2,
    Gate.mkOR busy_src1_ready cdb_fwd_src1 issue_src1_ready,
    Gate.mkOR busy_src2_ready cdb_fwd_src2 issue_src2_ready,
    Gate.mkOR busy_src2_ready_reg cdb_fwd_src2 issue_src2_ready_reg
  ]

  let fwd_src1_data := makeIndexedWires "fwd_src1_data" 32
  let fwd_src2_data := makeIndexedWires "fwd_src2_data" 32
  let fwd_src1_data_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (rs1_data[i]!) (cdb_data[i]!) cdb_fwd_src1 (fwd_src1_data[i]!))
  let fwd_src2_data_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (rs2_data[i]!) (cdb_data[i]!) cdb_fwd_src2 (fwd_src2_data[i]!))

  let cdb_fwd_instances := [cdb_fwd_cmp_src1_inst, cdb_fwd_cmp_src2_inst]

  -- === SRC2 MUX: select immediate for I-type, forwarded register value for R-type ===
  let issue_src2_muxed := makeIndexedWires "issue_src2_muxed" 32
  let src2_mux_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (fwd_src2_data[i]!) (decode_imm[i]!) decode_use_imm (issue_src2_muxed[i]!))

  -- === RESERVATION STATIONS (4 instances, bundled I/O) ===
  -- RS Integer
  let rs_int_alloc_ptr_unused := makeIndexedWires "rs_int_alloc_ptr_unused" 2
  let rs_int_grant_unused := makeIndexedWires "rs_int_grant_unused" 4
  let rs_int_issue_full := Wire.mk "rs_int_issue_full"
  let rs_int_dispatch_valid := Wire.mk "rs_int_dispatch_valid"
  let rs_int_dispatch_opcode := makeIndexedWires "rs_int_dispatch_opcode" 6
  let rs_int_dispatch_src1 := makeIndexedWires "rs_int_dispatch_src1" 32
  let rs_int_dispatch_src2 := makeIndexedWires "rs_int_dispatch_src2" 32
  let rs_int_dispatch_tag := makeIndexedWires "rs_int_dispatch_tag" 6

  let rs_int_inst : CircuitInstance := {
    moduleName := "ReservationStation4"
    instName := "u_rs_integer"
    portMap := [("clock", clock), ("reset", reset),
                ("zero", zero), ("one", one), ("issue_en", dispatch_int_valid),
                ("issue_src1_ready", issue_src1_ready), ("issue_src2_ready", issue_src2_ready),
                ("cdb_valid", cdb_valid), ("dispatch_en", one),
                ("issue_full", rs_int_issue_full), ("dispatch_valid", rs_int_dispatch_valid)] ++
               (decode_optype.enum.map (fun ⟨i, w⟩ => (s!"issue_opcode_{i}", w))) ++
               (rd_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_dest_tag_{i}", w))) ++
               (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_tag_{i}", w))) ++
               (fwd_src1_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_data_{i}", w))) ++
               (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_tag_{i}", w))) ++
               (issue_src2_muxed.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_data_{i}", w))) ++
               (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag_{i}", w))) ++
               (cdb_data.enum.map (fun ⟨i, w⟩ => (s!"cdb_data_{i}", w))) ++
               (rs_int_dispatch_opcode.enum.map (fun ⟨i, w⟩ => (s!"dispatch_opcode_{i}", w))) ++
               (rs_int_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src1_data_{i}", w))) ++
               (rs_int_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src2_data_{i}", w))) ++
               (rs_int_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dispatch_dest_tag_{i}", w))) ++
               (rs_int_alloc_ptr_unused.enum.map (fun ⟨i, w⟩ => (s!"alloc_ptr_{i}", w))) ++
               (rs_int_grant_unused.enum.map (fun ⟨i, w⟩ => (s!"dispatch_grant_{i}", w)))
  }

  -- RS Memory
  let rs_mem_issue_full := Wire.mk "rs_mem_issue_full"
  let rs_mem_dispatch_valid := Wire.mk "rs_mem_dispatch_valid"
  let rs_mem_dispatch_opcode := makeIndexedWires "rs_mem_dispatch_opcode" 6
  let rs_mem_dispatch_src1 := makeIndexedWires "rs_mem_dispatch_src1" 32
  let rs_mem_dispatch_src2 := makeIndexedWires "rs_mem_dispatch_src2" 32
  let rs_mem_dispatch_tag := makeIndexedWires "rs_mem_dispatch_tag" 6
  let rs_mem_alloc_ptr := makeIndexedWires "rs_mem_alloc_ptr" 2
  let rs_mem_grant := makeIndexedWires "rs_mem_grant" 4

  let rs_mem_inst : CircuitInstance := {
    moduleName := "ReservationStation4"
    instName := "u_rs_memory"
    portMap := [("clock", clock), ("reset", reset),
                ("zero", zero), ("one", one), ("issue_en", dispatch_mem_valid),
                ("issue_src1_ready", issue_src1_ready), ("issue_src2_ready", issue_src2_ready_reg),
                ("cdb_valid", cdb_valid), ("dispatch_en", one),
                ("issue_full", rs_mem_issue_full), ("dispatch_valid", rs_mem_dispatch_valid)] ++
               (decode_optype.enum.map (fun ⟨i, w⟩ => (s!"issue_opcode_{i}", w))) ++
               (rd_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_dest_tag_{i}", w))) ++
               (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_tag_{i}", w))) ++
               (fwd_src1_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_data_{i}", w))) ++
               (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_tag_{i}", w))) ++
               -- Memory RS: src2 = forwarded register value (store data), NOT immediate
               (fwd_src2_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_data_{i}", w))) ++
               (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag_{i}", w))) ++
               (cdb_data.enum.map (fun ⟨i, w⟩ => (s!"cdb_data_{i}", w))) ++
               (rs_mem_dispatch_opcode.enum.map (fun ⟨i, w⟩ => (s!"dispatch_opcode_{i}", w))) ++
               (rs_mem_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src1_data_{i}", w))) ++
               (rs_mem_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src2_data_{i}", w))) ++
               (rs_mem_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dispatch_dest_tag_{i}", w))) ++
               (rs_mem_alloc_ptr.enum.map (fun ⟨i, w⟩ => (s!"alloc_ptr_{i}", w))) ++
               (rs_mem_grant.enum.map (fun ⟨i, w⟩ => (s!"dispatch_grant_{i}", w)))
  }

  -- === IMMEDIATE REGISTER FILE ===
  -- Captures decode_imm at mem RS dispatch time, indexed by RS alloc_ptr.
  -- Read at issue time using dispatch_grant. Fixes OoO immediate desync.
  let imm_rf_decoded := makeIndexedWires "imm_rf_decoded" 4
  let imm_rf_we := makeIndexedWires "imm_rf_we" 4

  let imm_rf_decoder_inst : CircuitInstance := {
    moduleName := "Decoder2"
    instName := "u_imm_rf_dec"
    portMap := [
      ("in_0", rs_mem_alloc_ptr[0]!), ("in_1", rs_mem_alloc_ptr[1]!),
      ("out_0", imm_rf_decoded[0]!), ("out_1", imm_rf_decoded[1]!),
      ("out_2", imm_rf_decoded[2]!), ("out_3", imm_rf_decoded[3]!)
    ]
  }

  -- Gate each decoded output with dispatch_mem_valid
  let imm_rf_we_gates := (List.range 4).map (fun e =>
    Gate.mkAND imm_rf_decoded[e]! dispatch_mem_valid imm_rf_we[e]!)

  -- 4 entries × 32 bits: MUX + DFF per bit
  let imm_rf_entries := (List.range 4).map (fun e =>
    makeIndexedWires s!"imm_rf_e{e}" 32)
  let imm_rf_gates := (List.range 4).map (fun e =>
    let entry := imm_rf_entries[e]!
    (List.range 32).map (fun b =>
      let next := Wire.mk s!"imm_rf_next_e{e}_{b}"
      [ Gate.mkMUX entry[b]! decode_imm[b]! imm_rf_we[e]! next,
        Gate.mkDFF next clock reset entry[b]! ]
    ) |>.flatten
  ) |>.flatten

  -- Read mux: convert dispatch_grant (one-hot) → binary sel, then Mux4x32
  let captured_imm := makeIndexedWires "captured_imm" 32
  let imm_rf_sel := makeIndexedWires "imm_rf_sel" 2
  let imm_rf_sel_gates := [
    Gate.mkOR rs_mem_grant[1]! rs_mem_grant[3]! imm_rf_sel[0]!,
    Gate.mkOR rs_mem_grant[2]! rs_mem_grant[3]! imm_rf_sel[1]!
  ]

  let imm_rf_mux_inst : CircuitInstance := {
    moduleName := "Mux4x32"
    instName := "u_imm_rf_mux"
    portMap :=
      (((List.range 4).map (fun e =>
          (List.range 32).map (fun b =>
            (s!"in{e}[{b}]", imm_rf_entries[e]![b]!)
          )
        )).flatten) ++
      (imm_rf_sel.enum.map (fun ⟨i, w⟩ => (s!"sel[{i}]", w))) ++
      (captured_imm.enum.map (fun ⟨i, w⟩ => (s!"out[{i}]", w)))
  }

  -- RS Branch
  let rs_branch_alloc_ptr_unused := makeIndexedWires "rs_branch_alloc_ptr_unused" 2
  let rs_branch_grant_unused := makeIndexedWires "rs_branch_grant_unused" 4
  let rs_branch_issue_full := Wire.mk "rs_branch_issue_full"
  let rs_branch_dispatch_valid := Wire.mk "rs_branch_dispatch_valid"
  let rs_branch_dispatch_opcode := makeIndexedWires "rs_branch_dispatch_opcode" 6
  let rs_branch_dispatch_src1 := makeIndexedWires "rs_branch_dispatch_src1" 32
  let rs_branch_dispatch_src2 := makeIndexedWires "rs_branch_dispatch_src2" 32
  let rs_branch_dispatch_tag := makeIndexedWires "rs_branch_dispatch_tag" 6

  let rs_branch_inst : CircuitInstance := {
    moduleName := "ReservationStation4"
    instName := "u_rs_branch"
    portMap := [("clock", clock), ("reset", reset),
                ("zero", zero), ("one", one), ("issue_en", dispatch_branch_valid),
                ("issue_src1_ready", issue_src1_ready), ("issue_src2_ready", issue_src2_ready),
                ("cdb_valid", cdb_valid), ("dispatch_en", one),
                ("issue_full", rs_branch_issue_full), ("dispatch_valid", rs_branch_dispatch_valid)] ++
               (decode_optype.enum.map (fun ⟨i, w⟩ => (s!"issue_opcode_{i}", w))) ++
               (rd_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_dest_tag_{i}", w))) ++
               (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_tag_{i}", w))) ++
               (fwd_src1_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_data_{i}", w))) ++
               (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_tag_{i}", w))) ++
               -- Branch RS: src2 = forwarded register value, NOT immediate
               (fwd_src2_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_data_{i}", w))) ++
               (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag_{i}", w))) ++
               (cdb_data.enum.map (fun ⟨i, w⟩ => (s!"cdb_data_{i}", w))) ++
               (rs_branch_dispatch_opcode.enum.map (fun ⟨i, w⟩ => (s!"dispatch_opcode_{i}", w))) ++
               (rs_branch_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src1_data_{i}", w))) ++
               (rs_branch_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src2_data_{i}", w))) ++
               (rs_branch_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dispatch_dest_tag_{i}", w))) ++
               (rs_branch_alloc_ptr_unused.enum.map (fun ⟨i, w⟩ => (s!"alloc_ptr_{i}", w))) ++
               (rs_branch_grant_unused.enum.map (fun ⟨i, w⟩ => (s!"dispatch_grant_{i}", w)))
  }

  -- RS MulDiv
  let rs_muldiv_alloc_ptr_unused := makeIndexedWires "rs_muldiv_alloc_ptr_unused" 2
  let rs_muldiv_grant_unused := makeIndexedWires "rs_muldiv_grant_unused" 4
  let rs_muldiv_issue_full := Wire.mk "rs_muldiv_issue_full"
  let rs_muldiv_dispatch_valid := Wire.mk "rs_muldiv_dispatch_valid"
  let rs_muldiv_dispatch_opcode := makeIndexedWires "rs_muldiv_dispatch_opcode" 6
  let rs_muldiv_dispatch_src1 := makeIndexedWires "rs_muldiv_dispatch_src1" 32
  let rs_muldiv_dispatch_src2 := makeIndexedWires "rs_muldiv_dispatch_src2" 32
  let rs_muldiv_dispatch_tag := makeIndexedWires "rs_muldiv_dispatch_tag" 6

  let rs_muldiv_inst : CircuitInstance := {
    moduleName := "ReservationStation4"
    instName := "u_rs_muldiv"
    portMap := [("clock", clock), ("reset", reset),
                ("zero", zero), ("one", one), ("issue_en", dispatch_muldiv_valid),
                ("issue_src1_ready", issue_src1_ready), ("issue_src2_ready", issue_src2_ready),
                ("cdb_valid", cdb_valid), ("dispatch_en", one),
                ("issue_full", rs_muldiv_issue_full), ("dispatch_valid", rs_muldiv_dispatch_valid)] ++
               (decode_optype.enum.map (fun ⟨i, w⟩ => (s!"issue_opcode_{i}", w))) ++
               (rd_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_dest_tag_{i}", w))) ++
               (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_tag_{i}", w))) ++
               (fwd_src1_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_data_{i}", w))) ++
               (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_tag_{i}", w))) ++
               (issue_src2_muxed.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_data_{i}", w))) ++
               (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag_{i}", w))) ++
               (cdb_data.enum.map (fun ⟨i, w⟩ => (s!"cdb_data_{i}", w))) ++
               (rs_muldiv_dispatch_opcode.enum.map (fun ⟨i, w⟩ => (s!"dispatch_opcode_{i}", w))) ++
               (rs_muldiv_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src1_data_{i}", w))) ++
               (rs_muldiv_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src2_data_{i}", w))) ++
               (rs_muldiv_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dispatch_dest_tag_{i}", w))) ++
               (rs_muldiv_alloc_ptr_unused.enum.map (fun ⟨i, w⟩ => (s!"alloc_ptr_{i}", w))) ++
               (rs_muldiv_grant_unused.enum.map (fun ⟨i, w⟩ => (s!"dispatch_grant_{i}", w)))
  }

  -- === EXECUTION UNITS ===
  -- Integer ALU (combinational, named ports, 4-bit opcode)
  let int_result := makeIndexedWires "int_result" 32
  let int_tag_out := makeIndexedWires "int_tag_out" 6

  -- ALU opcode LUT: translate 6-bit dispatch optype → 4-bit ALU op
  -- Driven from RS dispatch opcode (not imem_resp_data) so the ALU executes
  -- the correct operation for the dispatched instruction, not the current fetch.
  let alu_op := makeIndexedWires "alu_op" 4
  let alu_lut_gates := mkOpTypeToALU4 "alulut" rs_int_dispatch_opcode alu_op aluMapping_RV32IM

  let int_exec_inst : CircuitInstance := {
    moduleName := "IntegerExecUnit"
    instName := "u_exec_integer"
    portMap :=
      (rs_int_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (rs_int_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      (alu_op.enum.map (fun ⟨i, w⟩ => (s!"opcode_{i}", w))) ++
      (rs_int_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dest_tag_{i}", w))) ++
      [("zero", zero), ("one", one)] ++
      (int_result.enum.map (fun ⟨i, w⟩ => (s!"result_{i}", w))) ++
      (int_tag_out.enum.map (fun ⟨i, w⟩ => (s!"tag_out_{i}", w)))
  }

  -- Branch execution unit
  let branch_result := makeIndexedWires "branch_result" 32
  let branch_tag_out := makeIndexedWires "branch_tag_out" 6

  let branch_exec_inst : CircuitInstance := {
    moduleName := "BranchExecUnit"
    instName := "u_exec_branch"
    portMap :=
      (rs_branch_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"src1_{i}", w))) ++
      (rs_branch_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"src2_{i}", w))) ++
      (rs_branch_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dest_tag_{i}", w))) ++
      [("zero", zero)] ++
      (branch_result.enum.map (fun ⟨i, w⟩ => (s!"result_{i}", w))) ++
      (branch_tag_out.enum.map (fun ⟨i, w⟩ => (s!"tag_out_{i}", w)))
  }

  -- Memory AGU (combinational, named ports)
  let mem_address := makeIndexedWires "mem_address" 32
  let mem_tag_out := makeIndexedWires "mem_tag_out" 6

  let mem_exec_inst : CircuitInstance := {
    moduleName := "MemoryExecUnit"
    instName := "u_exec_memory"
    portMap :=
      (rs_mem_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"base_{i}", w))) ++
      (captured_imm.enum.map (fun ⟨i, w⟩ => (s!"offset_{i}", w))) ++  -- Use captured immediate as offset
      (rs_mem_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dest_tag_{i}", w))) ++
      [("zero", zero)] ++
      (mem_address.enum.map (fun ⟨i, w⟩ => (s!"address_{i}", w))) ++
      (mem_tag_out.enum.map (fun ⟨i, w⟩ => (s!"tag_out_{i}", w)))
  }

  -- MulDiv (sequential, named ports, 3-bit opcode)
  let muldiv_result := makeIndexedWires "muldiv_result" 32
  let muldiv_tag_out := makeIndexedWires "muldiv_tag_out" 6
  let muldiv_valid_out := Wire.mk "muldiv_valid_out"
  let muldiv_busy := Wire.mk "muldiv_busy"

  let muldiv_exec_inst : CircuitInstance := {
    moduleName := "MulDivExecUnit"
    instName := "u_exec_muldiv"
    portMap :=
      (rs_muldiv_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (rs_muldiv_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      -- Width mismatch: RS has 6-bit opcode, MulDiv takes 3-bit. Connect lower 3 bits.
      [(s!"op_0", rs_muldiv_dispatch_opcode[0]!),
       (s!"op_1", rs_muldiv_dispatch_opcode[1]!),
       (s!"op_2", rs_muldiv_dispatch_opcode[2]!)] ++
      (rs_muldiv_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dest_tag_{i}", w))) ++
      [("valid_in", rs_muldiv_dispatch_valid),
       ("clock", clock), ("reset", reset),
       ("zero", zero), ("one", one)] ++
      (muldiv_result.enum.map (fun ⟨i, w⟩ => (s!"result_{i}", w))) ++
      (muldiv_tag_out.enum.map (fun ⟨i, w⟩ => (s!"tag_out_{i}", w))) ++
      [("valid_out", muldiv_valid_out), ("busy", muldiv_busy)]
  }

  -- === LSU (bundled I/O) ===
  let lsu_agu_address := makeIndexedWires "lsu_agu_address" 32
  let lsu_agu_tag := makeIndexedWires "lsu_agu_tag" 6
  let lsu_sb_full := Wire.mk "lsu_sb_full"
  let lsu_sb_empty := Wire.mk "lsu_sb_empty"
  let lsu_sb_fwd_hit := Wire.mk "lsu_sb_fwd_hit"
  let lsu_sb_fwd_data := makeIndexedWires "lsu_sb_fwd_data" 32
  let lsu_sb_deq_valid := Wire.mk "lsu_sb_deq_valid"
  let lsu_sb_deq_bits := makeIndexedWires "lsu_sb_deq_bits" 66
  let lsu_sb_enq_idx := makeIndexedWires "lsu_sb_enq_idx" 3

  let lsu_inst : CircuitInstance := {
    moduleName := "LSU"
    instName := "u_lsu"
    portMap := [("clock", clock), ("reset", reset),
                ("zero", zero), ("one", one),
                ("commit_store_en", rob_commit_en),
                ("deq_ready", dmem_req_ready),
                ("flush_en", zero),
                ("sb_enq_en", sb_enq_en),
                ("sb_full", lsu_sb_full), ("sb_empty", lsu_sb_empty), ("sb_fwd_hit", lsu_sb_fwd_hit),
                ("sb_deq_valid", lsu_sb_deq_valid)] ++
               (rs_mem_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"dispatch_base_{i}", w))) ++
               (captured_imm.enum.map (fun ⟨i, w⟩ => (s!"dispatch_offset_{i}", w))) ++
               (rs_mem_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dispatch_dest_tag_{i}", w))) ++
               (rs_mem_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"store_data_{i}", w))) ++
               ((makeIndexedWires "lsu_commit_idx" 3).enum.map (fun ⟨i, w⟩ => (s!"commit_store_idx_{i}", w))) ++
               (mem_address.enum.map (fun ⟨i, w⟩ => (s!"fwd_address_{i}", w))) ++
               ((makeIndexedWires "lsu_sb_enq_size" 2).enum.map (fun ⟨i, w⟩ => (s!"sb_enq_size_{i}", w))) ++
               (lsu_agu_address.enum.map (fun ⟨i, w⟩ => (s!"agu_address_{i}", w))) ++
               (lsu_agu_tag.enum.map (fun ⟨i, w⟩ => (s!"agu_tag_out_{i}", w))) ++
               (lsu_sb_fwd_data.enum.map (fun ⟨i, w⟩ => (s!"sb_fwd_data_{i}", w))) ++
               (lsu_sb_deq_bits.enum.map (fun ⟨i, w⟩ => (s!"sb_deq_bits_{i}", w))) ++
               (lsu_sb_enq_idx.enum.map (fun ⟨i, w⟩ => (s!"sb_enq_idx_{i}", w)))
  }

  -- === ROB (named ports) ===
  let rob_full := Wire.mk "rob_full"
  let rob_empty := Wire.mk "rob_empty"
  let rob_alloc_idx := makeIndexedWires "rob_alloc_idx" 4
  let rob_head_valid := Wire.mk "rob_head_valid"
  let rob_head_complete := Wire.mk "rob_head_complete"
  let rob_head_hasPhysRd := Wire.mk "rob_head_hasPhysRd"
  let rob_head_archRd := makeIndexedWires "rob_head_archRd" 5
  let rob_head_exception := Wire.mk "rob_head_exception"
  let rob_head_isBranch := Wire.mk "rob_head_isBranch"
  let rob_head_mispredicted := Wire.mk "rob_head_mispredicted"

  let rob_inst : CircuitInstance := {
    moduleName := "ROB16"
    instName := "u_rob"
    portMap :=
      [("clock", clock), ("reset", reset),
       ("zero", zero), ("one", one),
       ("alloc_en", rename_valid)] ++
      (rd_phys.enum.map (fun ⟨i, w⟩ => (s!"alloc_physRd[{i}]", w))) ++
      [("alloc_hasPhysRd", decode_has_rd)] ++
      (old_rd_phys.enum.map (fun ⟨i, w⟩ => (s!"alloc_oldPhysRd[{i}]", w))) ++
      [("alloc_hasOldPhysRd", decode_has_rd)] ++
      (decode_rd.enum.map (fun ⟨i, w⟩ => (s!"alloc_archRd[{i}]", w))) ++
      [("alloc_isBranch", dispatch_is_branch),
       ("cdb_valid", cdb_valid)] ++
      (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag[{i}]", w))) ++
      [("cdb_exception", zero),
       ("cdb_mispredicted", zero),
       ("commit_en", rob_commit_en),
       ("flush_en", zero),
       ("full", rob_full),
       ("empty", rob_empty)] ++
      (rob_alloc_idx.enum.map (fun ⟨i, w⟩ => (s!"alloc_idx[{i}]", w))) ++
      [("head_valid", rob_head_valid),
       ("head_complete", rob_head_complete)] ++
      (rob_head_physRd.enum.map (fun ⟨i, w⟩ => (s!"head_physRd[{i}]", w))) ++
      [("head_hasPhysRd", rob_head_hasPhysRd)] ++
      (rob_head_oldPhysRd.enum.map (fun ⟨i, w⟩ => (s!"head_oldPhysRd[{i}]", w))) ++
      [("head_hasOldPhysRd", rob_head_hasOldPhysRd)] ++
      (rob_head_archRd.enum.map (fun ⟨i, w⟩ => (s!"head_archRd[{i}]", w))) ++
      [("head_exception", rob_head_exception),
       ("head_isBranch", rob_head_isBranch),
       ("head_mispredicted", rob_head_mispredicted)]
  }

  -- === CDB ARBITRATION (Priority: LSU > MulDiv > Integer > Branch) ===
  -- 3-level MUX tree

  -- Level 0: Arbitrate between Branch and Integer (Integer has priority)
  -- Branch exec unit outputs result=0 and tag passthrough
  let int_branch_valid := Wire.mk "int_branch_valid"
  let int_branch_tag := makeIndexedWires "int_branch_tag" 6
  let int_branch_data := makeIndexedWires "int_branch_data" 32

  let arb_level0_gates :=
    [Gate.mkOR rs_int_dispatch_valid rs_branch_dispatch_valid int_branch_valid,
     Gate.mkMUX rs_branch_dispatch_valid rs_int_dispatch_valid rs_int_dispatch_valid (Wire.mk "ib_valid_unused")] ++
    (List.range 6).map (fun i =>
      Gate.mkMUX branch_tag_out[i]! int_tag_out[i]! rs_int_dispatch_valid int_branch_tag[i]!) ++
    (List.range 32).map (fun i =>
      Gate.mkMUX branch_result[i]! int_result[i]! rs_int_dispatch_valid int_branch_data[i]!)

  -- Level 1: Arbitrate between Int/Branch and MulDiv (MulDiv has priority)
  let int_muldiv_valid := Wire.mk "int_muldiv_valid"
  let int_muldiv_tag := makeIndexedWires "int_muldiv_tag" 6
  let int_muldiv_data := makeIndexedWires "int_muldiv_data" 32

  let arb_level1_gates := [Gate.mkMUX int_branch_valid muldiv_valid_out muldiv_valid_out int_muldiv_valid] ++
    (List.range 6).map (fun i =>
      Gate.mkMUX int_branch_tag[i]! muldiv_tag_out[i]! muldiv_valid_out int_muldiv_tag[i]!) ++
    (List.range 32).map (fun i =>
      Gate.mkMUX int_branch_data[i]! muldiv_result[i]! muldiv_valid_out int_muldiv_data[i]!)

  -- === CDB REPLAY BUFFER (saves int/muldiv result when LSU wins arbitration) ===
  let replay_valid := Wire.mk "replay_valid"
  let replay_valid_next := Wire.mk "replay_valid_next"
  let replay_tag := makeIndexedWires "replay_tag" 6
  let replay_tag_next := makeIndexedWires "replay_tag_next" 6
  let replay_data := makeIndexedWires "replay_data" 32
  let replay_data_next := makeIndexedWires "replay_data_next" 32

  let int_dropped := Wire.mk "int_dropped"
  let int_dropped_tmp := Wire.mk "int_dropped_tmp"
  let not_replay_valid := Wire.mk "not_replay_valid"
  let replay_wins := Wire.mk "replay_wins"

  let replay_save_gates := [
    Gate.mkNOT replay_valid not_replay_valid,
    Gate.mkAND int_muldiv_valid lsu_sb_deq_valid int_dropped_tmp,
    Gate.mkAND int_dropped_tmp not_replay_valid int_dropped,
    Gate.mkMUX replay_valid one int_dropped (Wire.mk "replay_v_tmp1"),
    Gate.mkMUX (Wire.mk "replay_v_tmp1") zero replay_wins replay_valid_next,
    Gate.mkDFF replay_valid_next clock reset replay_valid
  ]

  let replay_tag_gates := (List.range 6).map (fun i =>
    [Gate.mkMUX replay_tag[i]! int_muldiv_tag[i]! int_dropped replay_tag_next[i]!,
     Gate.mkDFF replay_tag_next[i]! clock reset replay_tag[i]!]) |>.flatten

  let replay_data_gates := (List.range 32).map (fun i =>
    [Gate.mkMUX replay_data[i]! int_muldiv_data[i]! int_dropped replay_data_next[i]!,
     Gate.mkDFF replay_data_next[i]! clock reset replay_data[i]!]) |>.flatten

  -- Level 2: CDB Arbitration (Priority: Replay > LSU > Int/MulDiv)
  let replay_wins_gate := [Gate.mkBUF replay_valid replay_wins]

  let lsu_wins := Wire.mk "lsu_wins"
  let lsu_wins_gate := [Gate.mkAND lsu_sb_deq_valid not_replay_valid lsu_wins]

  let int_wins := Wire.mk "int_wins"
  let int_wins_tmp := Wire.mk "int_wins_tmp"
  let not_lsu_valid := Wire.mk "not_lsu_valid"
  let int_wins_gates := [
    Gate.mkNOT lsu_sb_deq_valid not_lsu_valid,
    Gate.mkAND int_muldiv_valid not_lsu_valid int_wins_tmp,
    Gate.mkAND int_wins_tmp not_replay_valid int_wins
  ]

  let cdb_valid_tmp := Wire.mk "cdb_valid_tmp"
  let cdb_valid_gates := [
    Gate.mkOR replay_wins lsu_wins cdb_valid_tmp,
    Gate.mkOR cdb_valid_tmp int_wins cdb_valid
  ]

  let cdb_tag_mux_gates := (List.range 6).map (fun i =>
    let m1 := Wire.mk s!"cdb_tag_m1_{i}"
    [Gate.mkMUX int_muldiv_tag[i]! lsu_agu_tag[i]! lsu_wins m1,
     Gate.mkMUX m1 replay_tag[i]! replay_wins cdb_tag[i]!])
  let cdb_data_mux_gates := (List.range 32).map (fun i =>
    let m1 := Wire.mk s!"cdb_data_m1_{i}"
    [Gate.mkMUX int_muldiv_data[i]! lsu_sb_fwd_data[i]! lsu_wins m1,
     Gate.mkMUX m1 replay_data[i]! replay_wins cdb_data[i]!])
  let cdb_mux_gates := cdb_tag_mux_gates.flatten ++ cdb_data_mux_gates.flatten

  let cdb_arb_gates := arb_level0_gates ++ arb_level1_gates ++ replay_save_gates ++ replay_tag_gates ++
    replay_data_gates ++ replay_wins_gate ++ lsu_wins_gate ++ int_wins_gates ++
    cdb_valid_gates ++ cdb_mux_gates

  -- === COMMIT CONTROL ===
  -- Commit enable = head_valid AND head_complete
  let commit_gates := [
    Gate.mkAND rob_head_valid rob_head_complete rob_commit_en
  ]

  -- === STALL GENERATION (OR tree) ===
  let stall_tmp1 := Wire.mk "stall_tmp1"
  let stall_tmp2 := Wire.mk "stall_tmp2"
  let stall_tmp3 := Wire.mk "stall_tmp3"
  let stall_tmp4 := Wire.mk "stall_tmp4"
  let stall_tmp5 := Wire.mk "stall_tmp5"

  let stall_gates := [
    Gate.mkOR rename_stall rob_full stall_tmp1,
    Gate.mkOR stall_tmp1 rs_int_issue_full stall_tmp2,
    Gate.mkOR stall_tmp2 rs_mem_issue_full stall_tmp3,
    Gate.mkOR stall_tmp3 rs_branch_issue_full stall_tmp4,
    Gate.mkOR stall_tmp4 rs_muldiv_issue_full stall_tmp5,
    Gate.mkOR stall_tmp5 lsu_sb_full global_stall
  ]

  -- === MEMORY INTERFACE OUTPUTS ===
  let dmem_req_valid := Wire.mk "dmem_req_valid"
  let dmem_req_we := Wire.mk "dmem_req_we"
  let dmem_req_addr := makeIndexedWires "dmem_req_addr" 32
  let dmem_req_data := makeIndexedWires "dmem_req_data" 32

  -- dmem interface:
  --   req_valid = load dispatch OR store buffer dequeue
  --   req_we    = store buffer dequeue (only stores write)
  --   req_addr  = MUX(load_addr, store_addr, is_store)
  --   req_data  = store buffer dequeue data (sb_deq_bits[32:63])
  -- sb_enq_en = rs_mem_dispatch_valid (TODO: filter stores only via RS opcode)
  let sb_enq_gate := Gate.mkBUF rs_mem_dispatch_valid sb_enq_en

  let dmem_valid_tmp := Wire.mk "dmem_valid_tmp"
  let dmem_gates := [sb_enq_gate,
    Gate.mkOR rs_mem_dispatch_valid lsu_sb_deq_valid dmem_valid_tmp,
    Gate.mkBUF dmem_valid_tmp dmem_req_valid,
    Gate.mkBUF lsu_sb_deq_valid dmem_req_we] ++
    -- Address: MUX between load address (mem_address) and store address (sb_deq_bits[0:31])
    (List.range 32).map (fun i =>
      Gate.mkMUX mem_address[i]! lsu_sb_deq_bits[i]! lsu_sb_deq_valid dmem_req_addr[i]!) ++
    -- Data: store buffer dequeue data (sb_deq_bits[32:63])
    (List.range 32).map (fun i =>
      Gate.mkBUF lsu_sb_deq_bits[32+i]! dmem_req_data[i]!)

  -- === OUTPUT BUFFERS ===
  let global_stall_out := Wire.mk "global_stall_out"
  let output_gates := [Gate.mkBUF global_stall global_stall_out]

  { name := "CPU_RV32IM"
    inputs := [clock, reset, zero, one] ++
              imem_resp_data ++
              [dmem_req_ready, dmem_resp_valid] ++ dmem_resp_data ++
              branch_redirect_target
    outputs := fetch_pc ++ [fetch_stalled, global_stall_out] ++
               [dmem_req_valid, dmem_req_we] ++ dmem_req_addr ++ dmem_req_data ++
               [rob_empty]
    gates := dispatch_gates ++ src2_mux_gates ++ [busy_set_gate] ++ busy_gates ++
             cdb_fwd_gates ++ fwd_src1_data_gates ++ fwd_src2_data_gates ++
             alu_lut_gates ++ cdb_tag_nz_gates ++ cdb_arb_gates ++
             imm_rf_we_gates ++ imm_rf_gates ++ imm_rf_sel_gates ++
             commit_gates ++ stall_gates ++ dmem_gates ++ output_gates
    instances := [fetch_inst, decoder_inst, rename_inst] ++ busy_instances ++
                  cdb_fwd_instances ++
                  [rs_int_inst, rs_mem_inst, rs_branch_inst, rs_muldiv_inst,
                  int_exec_inst, branch_exec_inst, mem_exec_inst, muldiv_exec_inst,
                  rob_inst, lsu_inst,
                  imm_rf_decoder_inst, imm_rf_mux_inst]
    -- V2 codegen annotations
    signalGroups := [
      { name := "imem_resp_data", width := 32, wires := imem_resp_data },
      { name := "dmem_resp_data", width := 32, wires := dmem_resp_data },
      { name := "decode_optype", width := 6, wires := decode_optype },
      { name := "decode_rd", width := 5, wires := decode_rd },
      { name := "decode_rs1", width := 5, wires := decode_rs1 },
      { name := "decode_rs2", width := 5, wires := decode_rs2 },
      { name := "decode_imm", width := 32, wires := decode_imm },
      { name := "branch_redirect_target", width := 32, wires := branch_redirect_target },
      { name := "fetch_pc", width := 32, wires := fetch_pc },
      { name := "rs1_phys", width := 6, wires := rs1_phys },
      { name := "rs2_phys", width := 6, wires := rs2_phys },
      { name := "rd_phys", width := 6, wires := rd_phys },
      { name := "old_rd_phys", width := 6, wires := old_rd_phys },
      { name := "rs1_data", width := 32, wires := rs1_data },
      { name := "rs2_data", width := 32, wires := rs2_data },
      { name := "issue_src2_muxed", width := 32, wires := issue_src2_muxed },
      { name := "cdb_tag", width := 6, wires := cdb_tag },
      { name := "cdb_data", width := 32, wires := cdb_data },
      { name := "rob_head_physRd", width := 6, wires := rob_head_physRd },
      { name := "rob_alloc_idx", width := 4, wires := rob_alloc_idx },
      { name := "rob_head_oldPhysRd", width := 6, wires := rob_head_oldPhysRd },
      { name := "rob_head_archRd", width := 5, wires := rob_head_archRd },
      { name := "int_result", width := 32, wires := int_result },
      { name := "int_tag_out", width := 6, wires := int_tag_out },
      { name := "mem_address", width := 32, wires := mem_address },
      { name := "mem_tag_out", width := 6, wires := mem_tag_out },
      { name := "muldiv_result", width := 32, wires := muldiv_result },
      { name := "muldiv_tag_out", width := 6, wires := muldiv_tag_out },
      { name := "lsu_agu_address", width := 32, wires := lsu_agu_address },
      { name := "lsu_agu_tag", width := 6, wires := lsu_agu_tag },
      { name := "lsu_sb_fwd_data", width := 32, wires := lsu_sb_fwd_data },
      { name := "lsu_sb_deq_bits", width := 66, wires := lsu_sb_deq_bits },
      { name := "lsu_sb_enq_idx", width := 3, wires := lsu_sb_enq_idx },
      { name := "dmem_req_addr", width := 32, wires := dmem_req_addr },
      { name := "dmem_req_data", width := 32, wires := dmem_req_data },
      { name := "rs_int_dispatch_opcode", width := 6, wires := rs_int_dispatch_opcode },
      { name := "rs_int_dispatch_src1", width := 32, wires := rs_int_dispatch_src1 },
      { name := "rs_int_dispatch_src2", width := 32, wires := rs_int_dispatch_src2 },
      { name := "rs_int_dispatch_tag", width := 6, wires := rs_int_dispatch_tag },
      { name := "rs_mem_dispatch_opcode", width := 6, wires := rs_mem_dispatch_opcode },
      { name := "rs_mem_dispatch_src1", width := 32, wires := rs_mem_dispatch_src1 },
      { name := "rs_mem_dispatch_src2", width := 32, wires := rs_mem_dispatch_src2 },
      { name := "rs_mem_dispatch_tag", width := 6, wires := rs_mem_dispatch_tag },
      { name := "rs_branch_dispatch_opcode", width := 6, wires := rs_branch_dispatch_opcode },
      { name := "rs_branch_dispatch_src1", width := 32, wires := rs_branch_dispatch_src1 },
      { name := "rs_branch_dispatch_src2", width := 32, wires := rs_branch_dispatch_src2 },
      { name := "rs_branch_dispatch_tag", width := 6, wires := rs_branch_dispatch_tag },
      { name := "rs_muldiv_dispatch_opcode", width := 6, wires := rs_muldiv_dispatch_opcode },
      { name := "rs_muldiv_dispatch_src1", width := 32, wires := rs_muldiv_dispatch_src1 },
      { name := "rs_muldiv_dispatch_src2", width := 32, wires := rs_muldiv_dispatch_src2 },
      { name := "rs_muldiv_dispatch_tag", width := 6, wires := rs_muldiv_dispatch_tag },
      { name := "int_muldiv_tag", width := 6, wires := int_muldiv_tag },
      { name := "int_muldiv_data", width := 32, wires := int_muldiv_data }
    ]
  }

end Shoumei.RISCV.CPU
