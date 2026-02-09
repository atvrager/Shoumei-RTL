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
import Shoumei.RISCV.Retirement.Queue16x32
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
Parameterized CPU Structural Circuit

Supports RV32I (base) and RV32IM (with M-extension multiply/divide).
Controlled by `CPUConfig.enableM`:
- When false: 3 RS (int, mem, branch), 3 exec units, 2-level CDB arb
- When true:  4 RS (+muldiv), 4 exec units (+MulDivExecUnit), 3-level CDB arb

Instances: 10 (RV32I) or 12 (RV32IM) verified submodules.
-/
def mkCPU (config : CPUConfig) : Circuit :=
  let enableM := config.enableM
  let sbFwdPipelined := config.sbFwdPipelineStages > 0
  let enc := config.opcodeEncodings
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

  -- === DECODER OUTPUTS (internal, driven by decoder instance) ===
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
  let dispatch_is_store := Wire.mk "dispatch_is_store"
  let decode_use_imm := Wire.mk "decode_use_imm"

  -- === FETCH STAGE ===
  let fetch_pc := makeIndexedWires "fetch_pc" 32
  let fetch_stalled := Wire.mk "fetch_stalled"
  let global_stall := Wire.mk "global_stall"
  let branch_redirect_valid := Wire.mk "branch_redirect_valid"
  let branch_redirect_target := makeIndexedWires "branch_redirect_target" 32

  let branch_redirect_valid_reg := Wire.mk "branch_redirect_valid_reg"
  let pipeline_flush_comb := Wire.mk "pipeline_flush_comb"
  let pipeline_flush := Wire.mk "pipeline_flush"
  -- Per-subsystem flush registers
  let flush_rs_int := Wire.mk "flush_rs_int"
  let flush_rs_mem := Wire.mk "flush_rs_mem"
  let flush_rs_br := Wire.mk "flush_rs_br"
  let flush_rs_muldiv := Wire.mk "flush_rs_muldiv"
  let flush_rob := Wire.mk "flush_rob"
  let flush_busy := Wire.mk "flush_busy"
  let flush_misc := Wire.mk "flush_misc"
  let pipeline_reset_rs_int := Wire.mk "pipeline_reset_rs_int"
  let pipeline_reset_rs_mem := Wire.mk "pipeline_reset_rs_mem"
  let pipeline_reset_rs_br := Wire.mk "pipeline_reset_rs_br"
  let pipeline_reset_rs_muldiv := Wire.mk "pipeline_reset_rs_muldiv"
  let pipeline_reset_rob := Wire.mk "pipeline_reset_rob"
  let pipeline_reset_busy := Wire.mk "pipeline_reset_busy"
  let pipeline_reset_misc := Wire.mk "pipeline_reset_misc"
  let fetch_stall := Wire.mk "fetch_stall"
  let branch_redirect_target_reg := makeIndexedWires "branch_redirect_target_reg" 32
  let redirect_valid_dff_inst : CircuitInstance := {
    moduleName := "DFlipFlop"
    instName := "u_redirect_valid_dff"
    portMap := [("d", branch_redirect_valid), ("q", branch_redirect_valid_reg),
                ("clock", clock), ("reset", reset)]
  }
  let redirect_target_dff_insts : List CircuitInstance := (List.range 32).map (fun i => {
    moduleName := "DFlipFlop"
    instName := s!"u_redirect_target_dff_{i}"
    portMap := [("d", branch_redirect_target[i]!), ("q", branch_redirect_target_reg[i]!),
                ("clock", clock), ("reset", reset)]
  })

  -- Per-subsystem flush DFFs
  let flush_dff_dispatch : CircuitInstance := {
    moduleName := "DFlipFlop"
    instName := "u_flush_dff_dispatch"
    portMap := [("d", pipeline_flush_comb), ("q", pipeline_flush),
                ("clock", clock), ("reset", reset)]
  }
  let flush_tags := if enableM then
    ["rs_int", "rs_mem", "rs_br", "rs_muldiv", "rob", "busy", "misc"]
  else
    ["rs_int", "rs_mem", "rs_br", "rob", "busy", "misc"]
  let flush_dff_insts : List CircuitInstance := flush_tags.map (fun tag => {
    moduleName := "DFlipFlop"
    instName := s!"u_flush_dff_{tag}"
    portMap := [("d", pipeline_flush_comb), ("q", Wire.mk s!"flush_{tag}"),
                ("clock", clock), ("reset", reset)]
  })

  let fetch_inst : CircuitInstance := {
    moduleName := "FetchStage"
    instName := "u_fetch"
    portMap :=
      [("clock", clock), ("reset", reset),
       ("stall", fetch_stall),
       ("branch_valid", branch_redirect_valid_reg),
       ("const_0", zero), ("const_1", one)] ++
      (branch_redirect_target_reg.enum.map (fun ⟨i, w⟩ => (s!"branch_target_{i}", w))) ++
      (fetch_pc.enum.map (fun ⟨i, w⟩ => (s!"pc_{i}", w))) ++
      [("stalled_reg", fetch_stalled)]
  }

  -- === DECODER ===
  let decoder_inst : CircuitInstance := {
    moduleName := if enableM then "RV32IMDecoder" else "RV32IDecoder"
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
       ("io_is_branch", dispatch_is_branch)] ++
      (if enableM then [("io_is_muldiv", dispatch_is_muldiv)] else []) ++
      [("io_is_store", dispatch_is_store),
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
  -- Pre-register CDB signals (before pipeline register)
  let cdb_pre_valid := Wire.mk "cdb_pre_valid"
  let cdb_pre_tag := makeIndexedWires "cdb_pre_tag" 6
  let cdb_pre_data := makeIndexedWires "cdb_pre_data" 32
  -- Mask CDB valid for PhysRegFile writes: don't write to p0 (x0's home register)
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
  let retire_recycle_valid := Wire.mk "retire_recycle_valid"
  let rvvi_rd_data := makeIndexedWires "rvvi_rd_data" 32

  -- Gate rename's instr_valid during redirect/flush
  let decode_valid_rename := Wire.mk "decode_valid_rename"

  let rename_inst : CircuitInstance := {
    moduleName := "RenameStage_32x64"
    instName := "u_rename"
    portMap :=
      [("clock", clock), ("reset", reset),
       ("zero", zero), ("one", one),
       ("instr_valid", decode_valid_rename),
       ("has_rd", decode_has_rd)] ++
      (decode_rs1.enum.map (fun ⟨i, w⟩ => (s!"rs1_addr_{i}", w))) ++
      (decode_rs2.enum.map (fun ⟨i, w⟩ => (s!"rs2_addr_{i}", w))) ++
      (decode_rd.enum.map (fun ⟨i, w⟩ => (s!"rd_addr_{i}", w))) ++
      [("cdb_valid", cdb_valid_prf)] ++
      (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag_{i}", w))) ++
      (cdb_data.enum.map (fun ⟨i, w⟩ => (s!"cdb_data_{i}", w))) ++
      [("retire_valid", retire_recycle_valid)] ++
      (rob_head_oldPhysRd.enum.map (fun ⟨i, w⟩ => (s!"retire_tag_{i}", w))) ++
      (rob_head_physRd.enum.map (fun ⟨i, w⟩ => (s!"rd_tag3_{i}", w))) ++  -- 3rd read port: RVVI commit readback
      [("rename_valid", rename_valid), ("stall", rename_stall)] ++
      (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"rs1_phys_out_{i}", w))) ++
      (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"rs2_phys_out_{i}", w))) ++
      (rd_phys.enum.map (fun ⟨i, w⟩ => (s!"rd_phys_out_{i}", w))) ++
      (rs1_data.enum.map (fun ⟨i, w⟩ => (s!"rs1_data_{i}", w))) ++
      (rs2_data.enum.map (fun ⟨i, w⟩ => (s!"rs2_data_{i}", w))) ++
      (old_rd_phys.enum.map (fun ⟨i, w⟩ => (s!"old_rd_phys_out_{i}", w))) ++
      (rvvi_rd_data.enum.map (fun ⟨i, w⟩ => (s!"rd_data3_{i}", w)))
  }

  -- === DISPATCH QUALIFICATION ===
  let not_stall := Wire.mk "not_stall"
  let dispatch_base_valid := Wire.mk "dispatch_base_valid"
  let dispatch_int_valid := Wire.mk "dispatch_int_valid"
  let dispatch_mem_valid := Wire.mk "dispatch_mem_valid"
  let dispatch_branch_valid := Wire.mk "dispatch_branch_valid"
  let dispatch_muldiv_valid := Wire.mk "dispatch_muldiv_valid"

  let sb_enq_en := Wire.mk "sb_enq_en"

  let not_redirecting := Wire.mk "not_redirecting"
  let redirect_or := Wire.mk "redirect_or"
  let redirect_or_flush := Wire.mk "redirect_or_flush"
  let decode_valid_no_redirect := Wire.mk "decode_valid_no_redirect"

  -- pipeline_flush_comb = reset OR redirect_valid_reg (feeds flush DFFs)
  let flush_gate :=
    [Gate.mkOR reset branch_redirect_valid_reg pipeline_flush_comb,
     Gate.mkOR global_stall pipeline_flush fetch_stall,
     -- Per-subsystem reset OR gates
     Gate.mkOR reset flush_rs_int pipeline_reset_rs_int,
     Gate.mkOR reset flush_rs_mem pipeline_reset_rs_mem,
     Gate.mkOR reset flush_rs_br pipeline_reset_rs_br] ++
    (if enableM then [Gate.mkOR reset flush_rs_muldiv pipeline_reset_rs_muldiv] else []) ++
    [Gate.mkOR reset flush_rob pipeline_reset_rob,
     Gate.mkOR reset flush_busy pipeline_reset_busy,
     Gate.mkOR reset flush_misc pipeline_reset_misc]

  let dispatch_gates :=
    [Gate.mkNOT global_stall not_stall,
     Gate.mkOR branch_redirect_valid branch_redirect_valid_reg redirect_or,
     Gate.mkOR redirect_or pipeline_flush redirect_or_flush,
     Gate.mkNOT redirect_or_flush not_redirecting,
     Gate.mkAND decode_valid not_redirecting decode_valid_no_redirect,
     Gate.mkAND decode_valid_no_redirect not_stall decode_valid_rename,
     Gate.mkBUF decode_valid_rename dispatch_base_valid,
     Gate.mkAND dispatch_base_valid dispatch_is_integer dispatch_int_valid,
     Gate.mkAND dispatch_base_valid dispatch_is_memory dispatch_mem_valid,
     Gate.mkAND dispatch_base_valid dispatch_is_branch dispatch_branch_valid] ++
    (if enableM then [Gate.mkAND dispatch_base_valid dispatch_is_muldiv dispatch_muldiv_valid] else [])

  -- === BUSY-BIT TABLE ===
  let busy_set_en := Wire.mk "busy_set_en"
  let busy_set_gate := Gate.mkAND rename_valid decode_has_rd busy_set_en
  let busy_src1_ready := Wire.mk "busy_src1_ready"
  let busy_src2_ready := Wire.mk "busy_src2_ready"
  let busy_src2_ready_reg := Wire.mk "busy_src2_ready_reg"
  let (busy_gates, busy_instances) := mkBusyBitTable
    clock pipeline_reset_busy zero one
    rd_phys busy_set_en
    cdb_tag cdb_valid
    rs1_phys rs2_phys
    decode_use_imm
    busy_src1_ready busy_src2_ready busy_src2_ready_reg

  -- === CDB FORWARDING ===
  -- Two forwarding paths: registered CDB (cdb_*) and pre-register CDB (cdb_pre_*).
  -- Pre-register has priority (newest result). Both set issue_src_ready.
  let cdb_match_src1 := Wire.mk "cdb_match_src1"
  let cdb_match_src2 := Wire.mk "cdb_match_src2"
  let cdb_fwd_src1 := Wire.mk "cdb_fwd_src1"
  let cdb_fwd_src2 := Wire.mk "cdb_fwd_src2"
  let cdb_pre_match_src1 := Wire.mk "cdb_pre_match_src1"
  let cdb_pre_match_src2 := Wire.mk "cdb_pre_match_src2"
  let cdb_pre_fwd_src1 := Wire.mk "cdb_pre_fwd_src1"
  let cdb_pre_fwd_src2 := Wire.mk "cdb_pre_fwd_src2"
  let any_fwd_src1 := Wire.mk "any_fwd_src1"
  let any_fwd_src2 := Wire.mk "any_fwd_src2"
  let issue_src1_ready := Wire.mk "issue_src1_ready"
  let issue_src2_ready := Wire.mk "issue_src2_ready"
  let issue_src2_ready_reg := Wire.mk "issue_src2_ready_reg"

  -- Registered CDB comparators (equality-only, faster than full Comparator6)
  let cdb_fwd_cmp_src1_inst : CircuitInstance := {
    moduleName := "EqualityComparator6"
    instName := "u_cdb_fwd_cmp_src1"
    portMap := [("eq", cdb_match_src1)] ++
               (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  }
  let cdb_fwd_cmp_src2_inst : CircuitInstance := {
    moduleName := "EqualityComparator6"
    instName := "u_cdb_fwd_cmp_src2"
    portMap := [("eq", cdb_match_src2)] ++
               (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  }
  -- Pre-register CDB comparators (same-cycle forwarding bypass)
  let cdb_pre_fwd_cmp_src1_inst : CircuitInstance := {
    moduleName := "EqualityComparator6"
    instName := "u_cdb_pre_fwd_cmp_src1"
    portMap := [("eq", cdb_pre_match_src1)] ++
               (cdb_pre_tag.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  }
  let cdb_pre_fwd_cmp_src2_inst : CircuitInstance := {
    moduleName := "EqualityComparator6"
    instName := "u_cdb_pre_fwd_cmp_src2"
    portMap := [("eq", cdb_pre_match_src2)] ++
               (cdb_pre_tag.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  }

  let cdb_fwd_gates := [
    Gate.mkAND cdb_valid cdb_match_src1 cdb_fwd_src1,
    Gate.mkAND cdb_valid cdb_match_src2 cdb_fwd_src2,
    Gate.mkAND cdb_pre_valid cdb_pre_match_src1 cdb_pre_fwd_src1,
    Gate.mkAND cdb_pre_valid cdb_pre_match_src2 cdb_pre_fwd_src2,
    Gate.mkOR cdb_fwd_src1 cdb_pre_fwd_src1 any_fwd_src1,
    Gate.mkOR cdb_fwd_src2 cdb_pre_fwd_src2 any_fwd_src2,
    Gate.mkOR busy_src1_ready any_fwd_src1 issue_src1_ready,
    Gate.mkOR busy_src2_ready any_fwd_src2 issue_src2_ready,
    Gate.mkOR busy_src2_ready_reg any_fwd_src2 issue_src2_ready_reg
  ]

  -- Forwarded data: pre-register CDB has priority over registered CDB over PRF
  let fwd_src1_data := makeIndexedWires "fwd_src1_data" 32
  let fwd_src2_data := makeIndexedWires "fwd_src2_data" 32
  let fwd_src1_data_tmp := makeIndexedWires "fwd_src1_data_tmp" 32
  let fwd_src2_data_tmp := makeIndexedWires "fwd_src2_data_tmp" 32
  let fwd_src1_data_gates := (List.range 32).map (fun i =>
    [Gate.mkMUX (rs1_data[i]!) (cdb_data[i]!) cdb_fwd_src1 (fwd_src1_data_tmp[i]!),
     Gate.mkMUX (fwd_src1_data_tmp[i]!) (cdb_pre_data[i]!) cdb_pre_fwd_src1 (fwd_src1_data[i]!)]) |>.flatten
  let fwd_src2_data_gates := (List.range 32).map (fun i =>
    [Gate.mkMUX (rs2_data[i]!) (cdb_data[i]!) cdb_fwd_src2 (fwd_src2_data_tmp[i]!),
     Gate.mkMUX (fwd_src2_data_tmp[i]!) (cdb_pre_data[i]!) cdb_pre_fwd_src2 (fwd_src2_data[i]!)]) |>.flatten

  let cdb_fwd_instances := [cdb_fwd_cmp_src1_inst, cdb_fwd_cmp_src2_inst,
                             cdb_pre_fwd_cmp_src1_inst, cdb_pre_fwd_cmp_src2_inst]

  -- === SRC2 MUX ===
  let issue_src2_muxed := makeIndexedWires "issue_src2_muxed" 32
  let src2_mux_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (fwd_src2_data[i]!) (decode_imm[i]!) decode_use_imm (issue_src2_muxed[i]!))

  -- === RESERVATION STATIONS ===
  -- RS Integer
  let rs_int_alloc_ptr := makeIndexedWires "rs_int_alloc_ptr" 2
  let rs_int_grant := makeIndexedWires "rs_int_grant" 4
  let rs_int_issue_full := Wire.mk "rs_int_issue_full"
  let rs_int_dispatch_valid := Wire.mk "rs_int_dispatch_valid"
  let rs_int_dispatch_opcode := makeIndexedWires "rs_int_dispatch_opcode" 6
  let rs_int_dispatch_src1 := makeIndexedWires "rs_int_dispatch_src1" 32
  let rs_int_dispatch_src2 := makeIndexedWires "rs_int_dispatch_src2" 32
  let rs_int_dispatch_tag := makeIndexedWires "rs_int_dispatch_tag" 6

  let rs_int_inst : CircuitInstance := {
    moduleName := "ReservationStation4"
    instName := "u_rs_integer"
    portMap := [("clock", clock), ("reset", pipeline_reset_rs_int),
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
               (rs_int_alloc_ptr.enum.map (fun ⟨i, w⟩ => (s!"alloc_ptr_{i}", w))) ++
               (rs_int_grant.enum.map (fun ⟨i, w⟩ => (s!"dispatch_grant_{i}", w)))
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
    portMap := [("clock", clock), ("reset", pipeline_reset_rs_mem),
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

  -- === INTEGER IMMEDIATE REGISTER FILE ===
  let int_imm_rf_decoded := makeIndexedWires "int_imm_rf_decoded" 4
  let int_imm_rf_we := makeIndexedWires "int_imm_rf_we" 4

  let int_imm_rf_decoder_inst : CircuitInstance := {
    moduleName := "Decoder2"
    instName := "u_int_imm_rf_dec"
    portMap := [
      ("in_0", rs_int_alloc_ptr[0]!), ("in_1", rs_int_alloc_ptr[1]!),
      ("out_0", int_imm_rf_decoded[0]!), ("out_1", int_imm_rf_decoded[1]!),
      ("out_2", int_imm_rf_decoded[2]!), ("out_3", int_imm_rf_decoded[3]!)
    ]
  }

  let int_imm_rf_we_gates := (List.range 4).map (fun e =>
    Gate.mkAND int_imm_rf_decoded[e]! dispatch_int_valid int_imm_rf_we[e]!)

  let int_imm_rf_entries := (List.range 4).map (fun e =>
    makeIndexedWires s!"int_imm_rf_e{e}" 32)
  let int_imm_rf_gates := (List.range 4).map (fun e =>
    let entry := int_imm_rf_entries[e]!
    (List.range 32).map (fun b =>
      let next := Wire.mk s!"int_imm_rf_next_e{e}_{b}"
      [ Gate.mkMUX entry[b]! decode_imm[b]! int_imm_rf_we[e]! next,
        Gate.mkDFF next clock reset entry[b]! ]
    ) |>.flatten
  ) |>.flatten

  let int_captured_imm := makeIndexedWires "int_captured_imm" 32
  let int_imm_rf_sel := makeIndexedWires "int_imm_rf_sel" 2
  let int_imm_rf_sel_gates := [
    Gate.mkOR rs_int_grant[1]! rs_int_grant[3]! int_imm_rf_sel[0]!,
    Gate.mkOR rs_int_grant[2]! rs_int_grant[3]! int_imm_rf_sel[1]!
  ]

  let int_imm_rf_mux_inst : CircuitInstance := {
    moduleName := "Mux4x32"
    instName := "u_int_imm_rf_mux"
    portMap :=
      (((List.range 4).map (fun e =>
          (List.range 32).map (fun b =>
            (s!"in{e}[{b}]", int_imm_rf_entries[e]![b]!)
          )
        )).flatten) ++
      (int_imm_rf_sel.enum.map (fun ⟨i, w⟩ => (s!"sel[{i}]", w))) ++
      (int_captured_imm.enum.map (fun ⟨i, w⟩ => (s!"out[{i}]", w)))
  }

  -- === INTEGER PC REGISTER FILE ===
  let int_pc_rf_entries := (List.range 4).map (fun e =>
    makeIndexedWires s!"int_pc_rf_e{e}" 32)
  let int_pc_rf_gates := (List.range 4).map (fun e =>
    let entry := int_pc_rf_entries[e]!
    (List.range 32).map (fun b =>
      let next := Wire.mk s!"int_pc_rf_next_e{e}_{b}"
      [ Gate.mkMUX entry[b]! fetch_pc[b]! int_imm_rf_we[e]! next,
        Gate.mkDFF next clock reset entry[b]! ]
    ) |>.flatten
  ) |>.flatten

  let int_captured_pc := makeIndexedWires "int_captured_pc" 32
  let int_pc_rf_mux_inst : CircuitInstance := {
    moduleName := "Mux4x32"
    instName := "u_int_pc_rf_mux"
    portMap :=
      (((List.range 4).map (fun e =>
          (List.range 32).map (fun b =>
            (s!"in{e}[{b}]", int_pc_rf_entries[e]![b]!)
          )
        )).flatten) ++
      (int_imm_rf_sel.enum.map (fun ⟨i, w⟩ => (s!"sel[{i}]", w))) ++
      (int_captured_pc.enum.map (fun ⟨i, w⟩ => (s!"out[{i}]", w)))
  }

  -- === BRANCH RS + PC/IMM REGISTER FILES ===
  let rs_branch_alloc_ptr := makeIndexedWires "rs_branch_alloc_ptr" 2
  let rs_branch_grant := makeIndexedWires "rs_branch_grant" 4
  let rs_branch_issue_full := Wire.mk "rs_branch_issue_full"
  let rs_branch_dispatch_valid := Wire.mk "rs_branch_dispatch_valid"
  let rs_branch_dispatch_opcode := makeIndexedWires "rs_branch_dispatch_opcode" 6
  let rs_branch_dispatch_src1 := makeIndexedWires "rs_branch_dispatch_src1" 32
  let rs_branch_dispatch_src2 := makeIndexedWires "rs_branch_dispatch_src2" 32
  let rs_branch_dispatch_tag := makeIndexedWires "rs_branch_dispatch_tag" 6

  let rs_branch_inst : CircuitInstance := {
    moduleName := "ReservationStation4"
    instName := "u_rs_branch"
    portMap := [("clock", clock), ("reset", pipeline_reset_rs_br),
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
               (rs_branch_alloc_ptr.enum.map (fun ⟨i, w⟩ => (s!"alloc_ptr_{i}", w))) ++
               (rs_branch_grant.enum.map (fun ⟨i, w⟩ => (s!"dispatch_grant_{i}", w)))
  }

  -- === BRANCH PC REGISTER FILE ===
  let br_pc_rf_decoded := makeIndexedWires "br_pc_rf_decoded" 4
  let br_pc_rf_we := makeIndexedWires "br_pc_rf_we" 4

  let br_pc_rf_decoder_inst : CircuitInstance := {
    moduleName := "Decoder2"
    instName := "u_br_pc_rf_dec"
    portMap := [
      ("in_0", rs_branch_alloc_ptr[0]!), ("in_1", rs_branch_alloc_ptr[1]!),
      ("out_0", br_pc_rf_decoded[0]!), ("out_1", br_pc_rf_decoded[1]!),
      ("out_2", br_pc_rf_decoded[2]!), ("out_3", br_pc_rf_decoded[3]!)
    ]
  }

  let br_pc_rf_we_gates := (List.range 4).map (fun e =>
    Gate.mkAND br_pc_rf_decoded[e]! dispatch_branch_valid br_pc_rf_we[e]!)

  let br_pc_rf_entries := (List.range 4).map (fun e =>
    makeIndexedWires s!"br_pc_rf_e{e}" 32)
  let br_pc_rf_gates := (List.range 4).map (fun e =>
    let entry := br_pc_rf_entries[e]!
    (List.range 32).map (fun b =>
      let next := Wire.mk s!"br_pc_rf_next_e{e}_{b}"
      [ Gate.mkMUX entry[b]! fetch_pc[b]! br_pc_rf_we[e]! next,
        Gate.mkDFF next clock reset entry[b]! ]
    ) |>.flatten
  ) |>.flatten

  let br_captured_pc := makeIndexedWires "br_captured_pc" 32
  let br_pc_rf_sel := makeIndexedWires "br_pc_rf_sel" 2
  let br_pc_rf_sel_gates := [
    Gate.mkOR rs_branch_grant[1]! rs_branch_grant[3]! br_pc_rf_sel[0]!,
    Gate.mkOR rs_branch_grant[2]! rs_branch_grant[3]! br_pc_rf_sel[1]!
  ]

  let br_pc_rf_mux_inst : CircuitInstance := {
    moduleName := "Mux4x32"
    instName := "u_br_pc_rf_mux"
    portMap :=
      (((List.range 4).map (fun e =>
          (List.range 32).map (fun b =>
            (s!"in{e}[{b}]", br_pc_rf_entries[e]![b]!)
          )
        )).flatten) ++
      (br_pc_rf_sel.enum.map (fun ⟨i, w⟩ => (s!"sel[{i}]", w))) ++
      (br_captured_pc.enum.map (fun ⟨i, w⟩ => (s!"out[{i}]", w)))
  }

  -- === BRANCH IMMEDIATE REGISTER FILE ===
  let br_imm_rf_entries := (List.range 4).map (fun e =>
    makeIndexedWires s!"br_imm_rf_e{e}" 32)
  let br_imm_rf_gates := (List.range 4).map (fun e =>
    let entry := br_imm_rf_entries[e]!
    (List.range 32).map (fun b =>
      let next := Wire.mk s!"br_imm_rf_next_e{e}_{b}"
      [ Gate.mkMUX entry[b]! decode_imm[b]! br_pc_rf_we[e]! next,
        Gate.mkDFF next clock reset entry[b]! ]
    ) |>.flatten
  ) |>.flatten

  let br_captured_imm := makeIndexedWires "br_captured_imm" 32
  let br_imm_rf_mux_inst : CircuitInstance := {
    moduleName := "Mux4x32"
    instName := "u_br_imm_rf_mux"
    portMap :=
      (((List.range 4).map (fun e =>
          (List.range 32).map (fun b =>
            (s!"in{e}[{b}]", br_imm_rf_entries[e]![b]!)
          )
        )).flatten) ++
      (br_pc_rf_sel.enum.map (fun ⟨i, w⟩ => (s!"sel[{i}]", w))) ++
      (br_captured_imm.enum.map (fun ⟨i, w⟩ => (s!"out[{i}]", w)))
  }

  -- === MULDIV RS (conditional) ===
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
    portMap := [("clock", clock), ("reset", pipeline_reset_rs_muldiv),
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
  let int_result := makeIndexedWires "int_result" 32
  let int_tag_out := makeIndexedWires "int_tag_out" 6

  -- ALU opcode LUT: translate 6-bit dispatch optype → 4-bit ALU op
  let alu_op := makeIndexedWires "alu_op" 4
  let alu_lut_gates := mkOpTypeToALU4 "alulut" rs_int_dispatch_opcode alu_op
    (if enableM then aluMapping_RV32IM else aluMapping_RV32I)

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

  -- MulDiv exec unit (conditional)
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
      [(s!"op_0", rs_muldiv_dispatch_opcode[0]!),
       (s!"op_1", rs_muldiv_dispatch_opcode[1]!),
       (s!"op_2", rs_muldiv_dispatch_opcode[2]!)] ++
      (rs_muldiv_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dest_tag_{i}", w))) ++
      [("valid_in", rs_muldiv_dispatch_valid),
       ("clock", clock), ("reset", pipeline_reset_rs_muldiv),
       ("zero", zero), ("one", one)] ++
      (muldiv_result.enum.map (fun ⟨i, w⟩ => (s!"result_{i}", w))) ++
      (muldiv_tag_out.enum.map (fun ⟨i, w⟩ => (s!"tag_out_{i}", w))) ++
      [("valid_out", muldiv_valid_out), ("busy", muldiv_busy)]
  }

  -- === LUI/AUIPC POST-ALU MUX ===
  let auipc_result := makeIndexedWires "auipc_result" 32
  let auipc_adder_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32"
    instName := "u_auipc_adder"
    portMap :=
      (int_captured_pc.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (int_captured_imm.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("cin", zero)] ++
      (auipc_result.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w))) ++
      []
  }

  -- Opcode match: LUI and AUIPC encodings from config
  let is_lui := Wire.mk "is_lui"
  let is_auipc := Wire.mk "is_auipc"
  let testBit (n : Nat) (b : Nat) : Bool := (n / (2 ^ b)) % 2 != 0

  let mkOpcodeMatch6 (pfx : String) (enc : Nat) (opcode : List Wire) (result : Wire) : List Gate :=
    let bitWires := (List.range 6).map fun b =>
      if testBit enc b then opcode[b]! else Wire.mk s!"{pfx}_n{b}"
    let notGates := (List.range 6).filterMap fun b =>
      if !testBit enc b then some (Gate.mkNOT opcode[b]! (Wire.mk s!"{pfx}_n{b}")) else none
    let t01 := Wire.mk s!"{pfx}_t01"
    let t012 := Wire.mk s!"{pfx}_t012"
    let t0123 := Wire.mk s!"{pfx}_t0123"
    let t01234 := Wire.mk s!"{pfx}_t01234"
    notGates ++ [
      Gate.mkAND bitWires[0]! bitWires[1]! t01,
      Gate.mkAND t01 bitWires[2]! t012,
      Gate.mkAND t012 bitWires[3]! t0123,
      Gate.mkAND t0123 bitWires[4]! t01234,
      Gate.mkAND t01234 bitWires[5]! result
    ]

  let lui_match_gates := mkOpcodeMatch6 "lui_match" enc.lui rs_int_dispatch_opcode is_lui
  let auipc_match_gates := mkOpcodeMatch6 "auipc_match" enc.auipc rs_int_dispatch_opcode is_auipc

  -- Post-ALU MUX: int_result_final = MUX(MUX(int_result, auipc_result, is_auipc), int_captured_imm, is_lui)
  let int_result_final := makeIndexedWires "int_result_final" 32
  let int_auipc_muxed := makeIndexedWires "int_auipc_muxed" 32
  let lui_auipc_gates := (List.range 32).map (fun i =>
    [ Gate.mkMUX int_result[i]! auipc_result[i]! is_auipc int_auipc_muxed[i]!,
      Gate.mkMUX int_auipc_muxed[i]! int_captured_imm[i]! is_lui int_result_final[i]! ]
  ) |>.flatten

  -- === JAL/JALR LINK REGISTER (PC+4) ===
  let br_pc_plus_4 := makeIndexedWires "br_pc_plus_4" 32
  let br_pc_plus_4_b := makeIndexedWires "br_pc_plus_4_b" 32
  let br_pc_plus_4_b_gates := (List.range 32).map (fun i =>
    if i == 2 then Gate.mkBUF one br_pc_plus_4_b[i]!
    else Gate.mkBUF zero br_pc_plus_4_b[i]!)

  let br_pc_plus_4_adder_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32"
    instName := "u_br_pc_plus_4"
    portMap :=
      (br_captured_pc.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (br_pc_plus_4_b.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("cin", zero)] ++
      (br_pc_plus_4.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w))) ++
      []
  }

  -- Opcode match: JAL/JALR from config
  let is_jal := Wire.mk "is_jal"
  let is_jalr := Wire.mk "is_jalr"
  let is_jal_or_jalr := Wire.mk "is_jal_or_jalr"
  let jal_match_gates := mkOpcodeMatch6 "jal_match" enc.jal rs_branch_dispatch_opcode is_jal
  let jalr_match_gates := mkOpcodeMatch6 "jalr_match" enc.jalr rs_branch_dispatch_opcode is_jalr
  let jal_jalr_or_gate := [Gate.mkOR is_jal is_jalr is_jal_or_jalr]

  let branch_result_final := makeIndexedWires "branch_result_final" 32
  let branch_result_mux_gates := (List.range 32).map (fun i =>
    Gate.mkMUX branch_result[i]! br_pc_plus_4[i]! is_jal_or_jalr branch_result_final[i]!)

  -- === BRANCH TARGET + PC REDIRECT ===
  let branch_target := makeIndexedWires "branch_target" 32
  let branch_target_adder_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32"
    instName := "u_branch_target"
    portMap :=
      (br_captured_pc.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (br_captured_imm.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("cin", zero)] ++
      (branch_target.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w))) ++
      []
  }

  -- JALR target = src1 + br_captured_imm, bit 0 cleared
  let jalr_target_raw := makeIndexedWires "jalr_target_raw" 32
  let jalr_target := makeIndexedWires "jalr_target" 32
  let jalr_target_adder_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32"
    instName := "u_jalr_target"
    portMap :=
      (rs_branch_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (br_captured_imm.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("cin", zero)] ++
      (jalr_target_raw.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w))) ++
      []
  }
  let jalr_target_gates := (List.range 32).map (fun i =>
    if i == 0 then Gate.mkBUF zero jalr_target[i]!
    else Gate.mkBUF jalr_target_raw[i]! jalr_target[i]!)

  let final_branch_target := makeIndexedWires "final_branch_target" 32
  let target_sel_gates := (List.range 32).map (fun i =>
    Gate.mkMUX branch_target[i]! jalr_target[i]! is_jalr final_branch_target[i]!)

  -- Branch condition evaluation
  let br_eq := Wire.mk "br_eq"
  let br_lt := Wire.mk "br_lt"
  let br_ltu := Wire.mk "br_ltu"

  let br_cmp_inst : CircuitInstance := {
    moduleName := "Comparator32"
    instName := "u_br_cmp"
    portMap :=
      (rs_branch_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (rs_branch_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("one", one), ("eq", br_eq), ("lt", br_lt), ("ltu", br_ltu),
       ("gt", Wire.mk "br_gt"), ("gtu", Wire.mk "br_gtu")]
  }

  -- Decode branch condition from opcode (encodings from config)
  let is_beq := Wire.mk "is_beq"
  let is_bne := Wire.mk "is_bne"
  let is_blt := Wire.mk "is_blt"
  let is_bge := Wire.mk "is_bge"
  let is_bltu := Wire.mk "is_bltu"
  let is_bgeu := Wire.mk "is_bgeu"

  let beq_match_gates := mkOpcodeMatch6 "beq_match" enc.beq rs_branch_dispatch_opcode is_beq
  let bne_match_gates := mkOpcodeMatch6 "bne_match" enc.bne rs_branch_dispatch_opcode is_bne
  let blt_match_gates := mkOpcodeMatch6 "blt_match" enc.blt rs_branch_dispatch_opcode is_blt
  let bge_match_gates := mkOpcodeMatch6 "bge_match" enc.bge rs_branch_dispatch_opcode is_bge
  let bltu_match_gates := mkOpcodeMatch6 "bltu_match" enc.bltu rs_branch_dispatch_opcode is_bltu
  let bgeu_match_gates := mkOpcodeMatch6 "bgeu_match" enc.bgeu rs_branch_dispatch_opcode is_bgeu

  -- Condition evaluation
  let not_eq := Wire.mk "br_not_eq"
  let not_lt := Wire.mk "not_lt"
  let not_ltu := Wire.mk "not_ltu"
  let beq_taken := Wire.mk "beq_taken"
  let bne_taken := Wire.mk "bne_taken"
  let blt_taken := Wire.mk "blt_taken"
  let bge_taken := Wire.mk "bge_taken"
  let bltu_taken := Wire.mk "bltu_taken"
  let bgeu_taken := Wire.mk "bgeu_taken"
  let cond_taken_tmp1 := Wire.mk "cond_taken_tmp1"
  let cond_taken_tmp2 := Wire.mk "cond_taken_tmp2"
  let cond_taken_tmp3 := Wire.mk "cond_taken_tmp3"
  let cond_taken_tmp4 := Wire.mk "cond_taken_tmp4"
  let cond_taken := Wire.mk "cond_taken"
  let branch_taken := Wire.mk "branch_taken"

  let branch_cond_gates := [
    Gate.mkNOT br_eq not_eq,
    Gate.mkNOT br_lt not_lt,
    Gate.mkNOT br_ltu not_ltu,
    Gate.mkAND is_beq br_eq beq_taken,
    Gate.mkAND is_bne not_eq bne_taken,
    Gate.mkAND is_blt br_lt blt_taken,
    Gate.mkAND is_bge not_lt bge_taken,
    Gate.mkAND is_bltu br_ltu bltu_taken,
    Gate.mkAND is_bgeu not_ltu bgeu_taken,
    Gate.mkOR beq_taken bne_taken cond_taken_tmp1,
    Gate.mkOR cond_taken_tmp1 blt_taken cond_taken_tmp2,
    Gate.mkOR cond_taken_tmp2 bge_taken cond_taken_tmp3,
    Gate.mkOR cond_taken_tmp3 bltu_taken cond_taken_tmp4,
    Gate.mkOR cond_taken_tmp4 bgeu_taken cond_taken,
    Gate.mkOR cond_taken is_jal_or_jalr branch_taken
  ]

  let branch_redirect_valid := Wire.mk "branch_redirect_valid"
  let branch_redirect_gate := [Gate.mkAND branch_taken rs_branch_dispatch_valid branch_redirect_valid]

  let branch_target_wire_gates := (List.range 32).map (fun i =>
    Gate.mkBUF final_branch_target[i]! branch_redirect_target[i]!)

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
  let rob_head_idx := makeIndexedWires "rob_head_idx" 4

  let rob_inst : CircuitInstance := {
    moduleName := "ROB16"
    instName := "u_rob"
    portMap :=
      [("clock", clock), ("reset", pipeline_reset_rob),
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
      (rob_head_idx.enum.map (fun ⟨i, w⟩ => (s!"head_idx[{i}]", w))) ++
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

  -- === RVVI INFRASTRUCTURE ===
  -- PC queue and instruction queue for RVVI-TRACE output
  let rvvi_valid := Wire.mk "rvvi_valid"
  let rvvi_trap := Wire.mk "rvvi_trap"
  let rvvi_pc_rdata := makeIndexedWires "rvvi_pc_rdata" 32
  let rvvi_insn := makeIndexedWires "rvvi_insn" 32
  let rvvi_rd := makeIndexedWires "rvvi_rd" 5
  let rvvi_rd_valid := Wire.mk "rvvi_rd_valid"

  let pc_queue_inst : CircuitInstance := {
    moduleName := "Queue16x32"
    instName := "u_pc_queue"
    portMap :=
      [("clock", clock), ("reset", reset),
       ("wr_en", rename_valid)] ++
      (rob_alloc_idx.enum.map (fun ⟨i, w⟩ => (s!"wr_idx_{i}", w))) ++
      (fetch_pc.enum.map (fun ⟨i, w⟩ => (s!"wr_data_{i}", w))) ++
      (rob_head_idx.enum.map (fun ⟨i, w⟩ => (s!"rd_idx_{i}", w))) ++
      (rvvi_pc_rdata.enum.map (fun ⟨i, w⟩ => (s!"rd_data_{i}", w)))
  }

  let insn_queue_inst : CircuitInstance := {
    moduleName := "Queue16x32"
    instName := "u_insn_queue"
    portMap :=
      [("clock", clock), ("reset", reset),
       ("wr_en", rename_valid)] ++
      (rob_alloc_idx.enum.map (fun ⟨i, w⟩ => (s!"wr_idx_{i}", w))) ++
      (imem_resp_data.enum.map (fun ⟨i, w⟩ => (s!"wr_data_{i}", w))) ++
      (rob_head_idx.enum.map (fun ⟨i, w⟩ => (s!"rd_idx_{i}", w))) ++
      (rvvi_insn.enum.map (fun ⟨i, w⟩ => (s!"rd_data_{i}", w)))
  }

  -- RVVI output logic
  -- rvvi_valid = rob_commit_en (head_valid AND head_complete)
  -- rvvi_trap = rob_head_exception AND rob_commit_en
  -- rvvi_rd[4:0] = rob_head_archRd
  -- rvvi_rd_valid = rob_head_hasPhysRd AND rob_commit_en
  -- rvvi_rd_data = prf rd_data3 (via rename stage 3rd read port, already wired)
  let rvvi_gates :=
    [Gate.mkBUF rob_commit_en rvvi_valid,
     Gate.mkAND rob_head_exception rob_commit_en rvvi_trap,
     Gate.mkAND rob_head_hasPhysRd rob_commit_en rvvi_rd_valid] ++
    (List.range 5).map (fun i =>
      Gate.mkBUF rob_head_archRd[i]! rvvi_rd[i]!)

  -- === CDB REPLAY BUFFER ===
  let replay_valid := Wire.mk "replay_valid"
  let replay_valid_next := Wire.mk "replay_valid_next"
  let replay_tag := makeIndexedWires "replay_tag" 6
  let replay_tag_next := makeIndexedWires "replay_tag_next" 6
  let replay_data := makeIndexedWires "replay_data" 32
  let replay_data_next := makeIndexedWires "replay_data_next" 32

  -- === CDB ARBITRATION ===
  -- Level 0: Merge Branch into Integer (Integer has priority)
  let int_branch_valid := Wire.mk "int_branch_valid"
  let int_branch_tag := makeIndexedWires "int_branch_tag" 6
  let int_branch_data := makeIndexedWires "int_branch_data" 32

  let arb_level0_gates :=
    [Gate.mkOR rs_int_dispatch_valid rs_branch_dispatch_valid int_branch_valid] ++
    (List.range 6).map (fun i =>
      Gate.mkMUX branch_tag_out[i]! int_tag_out[i]! rs_int_dispatch_valid int_branch_tag[i]!) ++
    (List.range 32).map (fun i =>
      Gate.mkMUX branch_result_final[i]! int_result_final[i]! rs_int_dispatch_valid int_branch_data[i]!)

  -- Level 1 (M-extension only): Merge Int/Branch with MulDiv (MulDiv has priority)
  let int_muldiv_valid := Wire.mk "int_muldiv_valid"
  let int_muldiv_tag := makeIndexedWires "int_muldiv_tag" 6
  let int_muldiv_data := makeIndexedWires "int_muldiv_data" 32

  let arb_level1_gates :=
    if enableM then
      [Gate.mkMUX int_branch_valid muldiv_valid_out muldiv_valid_out int_muldiv_valid] ++
      (List.range 6).map (fun i =>
        Gate.mkMUX int_branch_tag[i]! muldiv_tag_out[i]! muldiv_valid_out int_muldiv_tag[i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkMUX int_branch_data[i]! muldiv_result[i]! muldiv_valid_out int_muldiv_data[i]!)
    else []

  -- Wire names for the merged signal that feeds CDB arb level 2
  -- RV32I: int_branch_*; RV32IM: int_muldiv_*
  let merged_valid := if enableM then int_muldiv_valid else int_branch_valid
  let merged_tag := if enableM then int_muldiv_tag else int_branch_tag
  let merged_data := if enableM then int_muldiv_data else int_branch_data

  -- Save condition: merged has result AND LSU wins AND no replay pending
  let int_dropped := Wire.mk "int_dropped"
  let int_dropped_tmp := Wire.mk "int_dropped_tmp"
  let not_replay_valid := Wire.mk "not_replay_valid"
  let replay_wins := Wire.mk "replay_wins"
  -- Forward-declare lsu_valid for replay save logic
  let lsu_valid := Wire.mk "lsu_valid"

  let int_higher_priority := Wire.mk "int_higher_priority"
  let replay_save_gates := [
    Gate.mkNOT replay_valid not_replay_valid,
    Gate.mkOR lsu_valid dmem_resp_valid int_higher_priority,
    Gate.mkAND merged_valid int_higher_priority int_dropped_tmp,
    Gate.mkAND int_dropped_tmp not_replay_valid int_dropped,
    Gate.mkMUX replay_valid one int_dropped (Wire.mk "replay_v_tmp1"),
    Gate.mkMUX (Wire.mk "replay_v_tmp1") zero replay_wins replay_valid_next,
    Gate.mkDFF replay_valid_next clock reset replay_valid
  ]

  let replay_tag_gates := (List.range 6).map (fun i =>
    [Gate.mkMUX replay_tag[i]! merged_tag[i]! int_dropped replay_tag_next[i]!,
     Gate.mkDFF replay_tag_next[i]! clock reset replay_tag[i]!]) |>.flatten

  let replay_data_gates := (List.range 32).map (fun i =>
    [Gate.mkMUX replay_data[i]! merged_data[i]! int_dropped replay_data_next[i]!,
     Gate.mkDFF replay_data_next[i]! clock reset replay_data[i]!]) |>.flatten

  -- === LSU STORE-TO-LOAD FORWARDING ===
  let is_lw := Wire.mk "is_lw"
  let is_lh := Wire.mk "is_lh"
  let is_lhu := Wire.mk "is_lhu"
  let is_lb := Wire.mk "is_lb"
  let is_lbu := Wire.mk "is_lbu"
  let is_load := Wire.mk "is_load"
  let is_load_tmp1 := Wire.mk "is_load_tmp1"
  let is_load_tmp2 := Wire.mk "is_load_tmp2"
  let is_load_tmp3 := Wire.mk "is_load_tmp3"

  let lw_match_gates := mkOpcodeMatch6 "lw_match" enc.lw rs_mem_dispatch_opcode is_lw
  let lh_match_gates := mkOpcodeMatch6 "lh_match" enc.lh rs_mem_dispatch_opcode is_lh
  let lhu_match_gates := mkOpcodeMatch6 "lhu_match" enc.lhu rs_mem_dispatch_opcode is_lhu
  let lb_match_gates := mkOpcodeMatch6 "lb_match" enc.lb rs_mem_dispatch_opcode is_lb
  let lbu_match_gates := mkOpcodeMatch6 "lbu_match" enc.lbu rs_mem_dispatch_opcode is_lbu
  let is_load_gates := [
    Gate.mkOR is_lw is_lh is_load_tmp1,
    Gate.mkOR is_load_tmp1 is_lhu is_load_tmp2,
    Gate.mkOR is_load_tmp2 is_lb is_load_tmp3,
    Gate.mkOR is_load_tmp3 is_lbu is_load
  ]

  let load_fwd_valid := Wire.mk "load_fwd_valid"
  let load_fwd_tmp := Wire.mk "load_fwd_tmp"
  let load_fwd_gates := [
    Gate.mkAND lsu_sb_fwd_hit rs_mem_dispatch_valid load_fwd_tmp,
    Gate.mkAND load_fwd_tmp is_load load_fwd_valid
  ]

  let lsu_valid := Wire.mk "lsu_valid"
  let lsu_tag := makeIndexedWires "lsu_tag" 6
  let lsu_data := makeIndexedWires "lsu_data" 32

  -- When sbFwdPipelineStages > 0, register the SB forwarding result through DFFs.
  -- This breaks the timing-critical path: mem_address → SB compare → CDB arbiter.
  -- The registered result enters the CDB arbiter one cycle later.
  -- When sbFwdPipelineStages = 0, use combinational BUF (current behavior).
  let lsu_valid_gate :=
    if sbFwdPipelined then
      [Gate.mkDFF load_fwd_valid clock reset lsu_valid]
    else
      [Gate.mkBUF load_fwd_valid lsu_valid]

  let lsu_tag_data_mux_gates :=
    if sbFwdPipelined then
      (List.range 6).map (fun i =>
        Gate.mkDFF rs_mem_dispatch_tag[i]! clock reset lsu_tag[i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkDFF lsu_sb_fwd_data[i]! clock reset lsu_data[i]!)
    else
      (List.range 6).map (fun i =>
        Gate.mkBUF rs_mem_dispatch_tag[i]! lsu_tag[i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkBUF lsu_sb_fwd_data[i]! lsu_data[i]!)

  let lsu_pipeline_insts : List CircuitInstance := []

  -- === DMEM RESPONSE PATH ===
  let load_no_fwd := Wire.mk "load_no_fwd"
  let load_no_fwd_tmp := Wire.mk "load_no_fwd_tmp"
  let not_sb_fwd_hit := Wire.mk "not_sb_fwd_hit"
  let dmem_load_tag_reg := makeIndexedWires "dmem_load_tag_reg" 6
  let dmem_load_tag_next := makeIndexedWires "dmem_load_tag_next" 6

  let load_no_fwd_gates := [
    Gate.mkNOT lsu_sb_fwd_hit not_sb_fwd_hit,
    Gate.mkAND rs_mem_dispatch_valid is_load load_no_fwd_tmp,
    Gate.mkAND load_no_fwd_tmp not_sb_fwd_hit load_no_fwd
  ]

  let dmem_tag_capture_gates := (List.range 6).map (fun i =>
    [Gate.mkMUX dmem_load_tag_reg[i]! rs_mem_dispatch_tag[i]! load_no_fwd dmem_load_tag_next[i]!,
     Gate.mkDFF dmem_load_tag_next[i]! clock pipeline_reset_misc dmem_load_tag_reg[i]!]) |>.flatten

  -- CDB level 2: Priority: Replay > dmem_resp > LSU > merged
  let replay_wins_gate := [Gate.mkBUF replay_valid replay_wins]

  let dmem_wins := Wire.mk "dmem_wins"
  let dmem_wins_gate := [Gate.mkAND dmem_resp_valid not_replay_valid dmem_wins]

  let lsu_wins := Wire.mk "lsu_wins"
  let lsu_wins_tmp := Wire.mk "lsu_wins_tmp"
  let not_dmem_resp := Wire.mk "not_dmem_resp"
  let lsu_wins_gate := [
    Gate.mkNOT dmem_resp_valid not_dmem_resp,
    Gate.mkAND lsu_valid not_replay_valid lsu_wins_tmp,
    Gate.mkAND lsu_wins_tmp not_dmem_resp lsu_wins
  ]

  let int_wins := Wire.mk "int_wins"
  let int_wins_tmp := Wire.mk "int_wins_tmp"
  let int_wins_tmp2 := Wire.mk "int_wins_tmp2"
  let not_lsu_valid := Wire.mk "not_lsu_valid"
  let int_wins_gates := [
    Gate.mkNOT lsu_valid not_lsu_valid,
    Gate.mkAND merged_valid not_lsu_valid int_wins_tmp,
    Gate.mkAND int_wins_tmp not_replay_valid int_wins_tmp2,
    Gate.mkAND int_wins_tmp2 not_dmem_resp int_wins
  ]

  let cdb_valid_tmp := Wire.mk "cdb_valid_tmp"
  let cdb_valid_tmp2 := Wire.mk "cdb_valid_tmp2"
  let cdb_valid_gates := [
    Gate.mkOR replay_wins dmem_wins cdb_valid_tmp,
    Gate.mkOR cdb_valid_tmp lsu_wins cdb_valid_tmp2,
    Gate.mkOR cdb_valid_tmp2 int_wins cdb_pre_valid
  ]

  let cdb_tag_mux_gates := (List.range 6).map (fun i =>
    let m1 := Wire.mk s!"cdb_tag_m1_{i}"
    let m2 := Wire.mk s!"cdb_tag_m2_{i}"
    [Gate.mkMUX merged_tag[i]! lsu_tag[i]! lsu_wins m1,
     Gate.mkMUX m1 dmem_load_tag_reg[i]! dmem_wins m2,
     Gate.mkMUX m2 replay_tag[i]! replay_wins cdb_pre_tag[i]!])
  let cdb_data_mux_gates := (List.range 32).map (fun i =>
    let m1 := Wire.mk s!"cdb_data_m1_{i}"
    let m2 := Wire.mk s!"cdb_data_m2_{i}"
    [Gate.mkMUX merged_data[i]! lsu_data[i]! lsu_wins m1,
     Gate.mkMUX m1 dmem_resp_data[i]! dmem_wins m2,
     Gate.mkMUX m2 replay_data[i]! replay_wins cdb_pre_data[i]!])
  let cdb_mux_gates := cdb_tag_mux_gates.flatten ++ cdb_data_mux_gates.flatten

  -- CDB pipeline register: breaks critical path between execution and broadcast
  -- Uses DFlipFlop sub-module instances (not flat DFF gates) so they get their own
  -- always_ff block with plain `reset`, avoiding the pipeline_reset_busy domain.
  -- CDB pipeline register: breaks critical path between execution and broadcast
  -- Uses DFlipFlop sub-module instances (not flat DFF gates) so they get their own
  -- always_ff block with plain `reset`, avoiding the pipeline_reset_busy domain.
  let cdb_reg_insts : List CircuitInstance :=
    [{ moduleName := "DFlipFlop", instName := "u_cdb_valid_reg",
       portMap := [("d", cdb_pre_valid), ("q", cdb_valid),
                   ("clock", clock), ("reset", reset)] }] ++
    (List.range 6).map (fun i => {
       moduleName := "DFlipFlop", instName := s!"u_cdb_tag_reg_{i}",
       portMap := [("d", cdb_pre_tag[i]!), ("q", cdb_tag[i]!),
                   ("clock", clock), ("reset", reset)] }) ++
    (List.range 32).map (fun i => {
       moduleName := "DFlipFlop", instName := s!"u_cdb_data_reg_{i}",
       portMap := [("d", cdb_pre_data[i]!), ("q", cdb_data[i]!),
                   ("clock", clock), ("reset", reset)] })

  let cdb_arb_gates := arb_level0_gates ++ arb_level1_gates ++ replay_save_gates ++
    replay_tag_gates ++ replay_data_gates ++
    load_no_fwd_gates ++ dmem_tag_capture_gates ++
    replay_wins_gate ++ dmem_wins_gate ++ lsu_wins_gate ++ int_wins_gates ++
    cdb_valid_gates ++ cdb_mux_gates

  -- === COMMIT CONTROL ===
  let commit_gates := [
    Gate.mkAND rob_head_valid rob_head_complete rob_commit_en,
    Gate.mkAND rob_commit_en rob_head_hasOldPhysRd retire_recycle_valid
  ]

  -- === STALL GENERATION ===
  let stall_tmp1 := Wire.mk "stall_tmp1"
  let stall_tmp2 := Wire.mk "stall_tmp2"
  let stall_tmp3 := Wire.mk "stall_tmp3"
  let stall_tmp4 := Wire.mk "stall_tmp4"
  let stall_tmp5 := Wire.mk "stall_tmp5"

  let stall_gates :=
    [Gate.mkOR rename_stall rob_full stall_tmp1,
     Gate.mkOR stall_tmp1 rs_int_issue_full stall_tmp2,
     Gate.mkOR stall_tmp2 rs_mem_issue_full stall_tmp3,
     Gate.mkOR stall_tmp3 rs_branch_issue_full stall_tmp4] ++
    (if enableM then
      [Gate.mkOR stall_tmp4 rs_muldiv_issue_full stall_tmp5,
       Gate.mkOR stall_tmp5 lsu_sb_full global_stall]
    else
      [Gate.mkOR stall_tmp4 lsu_sb_full global_stall])

  -- === MEMORY INTERFACE ===
  let dmem_req_valid := Wire.mk "dmem_req_valid"
  let dmem_req_we := Wire.mk "dmem_req_we"
  let dmem_req_addr := makeIndexedWires "dmem_req_addr" 32
  let dmem_req_data := makeIndexedWires "dmem_req_data" 32

  let not_is_load := Wire.mk "not_is_load"
  let sb_enq_gate_gates := [
    Gate.mkNOT is_load not_is_load,
    Gate.mkAND rs_mem_dispatch_valid not_is_load sb_enq_en
  ]

  let dmem_valid_tmp := Wire.mk "dmem_valid_tmp"
  let dmem_gates := sb_enq_gate_gates ++ [
    Gate.mkOR load_no_fwd lsu_sb_deq_valid dmem_valid_tmp,
    Gate.mkBUF dmem_valid_tmp dmem_req_valid,
    Gate.mkBUF lsu_sb_deq_valid dmem_req_we] ++
    (List.range 32).map (fun i =>
      Gate.mkMUX mem_address[i]! lsu_sb_deq_bits[i]! lsu_sb_deq_valid dmem_req_addr[i]!) ++
    (List.range 32).map (fun i =>
      Gate.mkBUF lsu_sb_deq_bits[32+i]! dmem_req_data[i]!)

  -- === OUTPUT BUFFERS ===
  let global_stall_out := Wire.mk "global_stall_out"
  let output_gates := [Gate.mkBUF global_stall global_stall_out]

  { name := if enableM then "CPU_RV32IM" else "CPU_RV32I"
    inputs := [clock, reset, zero, one] ++
              imem_resp_data ++
              [dmem_req_ready, dmem_resp_valid] ++ dmem_resp_data
    outputs := fetch_pc ++ [fetch_stalled, global_stall_out] ++
               [dmem_req_valid, dmem_req_we] ++ dmem_req_addr ++ dmem_req_data ++
               [rob_empty] ++
               -- RVVI-TRACE outputs
               [rvvi_valid, rvvi_trap] ++ rvvi_pc_rdata ++ rvvi_insn ++
               rvvi_rd ++ [rvvi_rd_valid] ++ rvvi_rd_data
    gates := flush_gate ++ dispatch_gates ++ src2_mux_gates ++ [busy_set_gate] ++ busy_gates ++
             cdb_fwd_gates ++ fwd_src1_data_gates ++ fwd_src2_data_gates ++
             alu_lut_gates ++ cdb_tag_nz_gates ++ cdb_arb_gates ++
             imm_rf_we_gates ++ imm_rf_gates ++ imm_rf_sel_gates ++
             int_imm_rf_we_gates ++ int_imm_rf_gates ++ int_imm_rf_sel_gates ++
             int_pc_rf_gates ++
             lui_match_gates ++ auipc_match_gates ++ lui_auipc_gates ++
             br_pc_rf_we_gates ++ br_pc_rf_gates ++ br_pc_rf_sel_gates ++
             br_imm_rf_gates ++
             br_pc_plus_4_b_gates ++ branch_result_mux_gates ++
             jal_match_gates ++ jalr_match_gates ++ jal_jalr_or_gate ++
             beq_match_gates ++ bne_match_gates ++ blt_match_gates ++
             bge_match_gates ++ bltu_match_gates ++ bgeu_match_gates ++
             branch_cond_gates ++ branch_redirect_gate ++ branch_target_wire_gates ++
             jalr_target_gates ++ target_sel_gates ++
             lw_match_gates ++ lh_match_gates ++ lhu_match_gates ++
             lb_match_gates ++ lbu_match_gates ++ is_load_gates ++
             load_fwd_gates ++ lsu_valid_gate ++ lsu_tag_data_mux_gates ++
             commit_gates ++ stall_gates ++ dmem_gates ++ output_gates ++ rvvi_gates
    instances := [fetch_inst, decoder_inst, rename_inst,
                  redirect_valid_dff_inst, flush_dff_dispatch] ++ flush_dff_insts ++
                  redirect_target_dff_insts ++
                  busy_instances ++
                  cdb_fwd_instances ++
                  [rs_int_inst, rs_mem_inst, rs_branch_inst] ++
                  (if enableM then [rs_muldiv_inst] else []) ++
                  [int_exec_inst, branch_exec_inst, mem_exec_inst] ++
                  (if enableM then [muldiv_exec_inst] else []) ++
                  [rob_inst, lsu_inst,
                  imm_rf_decoder_inst, imm_rf_mux_inst,
                  int_imm_rf_decoder_inst, int_imm_rf_mux_inst, int_pc_rf_mux_inst,
                  br_pc_rf_decoder_inst, br_pc_rf_mux_inst, br_imm_rf_mux_inst,
                  auipc_adder_inst, br_pc_plus_4_adder_inst,
                  branch_target_adder_inst, jalr_target_adder_inst,
                  br_cmp_inst] ++
                  cdb_reg_insts ++
                  lsu_pipeline_insts ++
                  [pc_queue_inst, insn_queue_inst]
    signalGroups :=
      [{ name := "imem_resp_data", width := 32, wires := imem_resp_data },
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
       { name := "int_result_final", width := 32, wires := int_result_final },
       { name := "int_captured_imm", width := 32, wires := int_captured_imm },
       { name := "int_captured_pc", width := 32, wires := int_captured_pc },
       { name := "auipc_result", width := 32, wires := auipc_result },
       { name := "int_tag_out", width := 6, wires := int_tag_out },
       { name := "branch_result_final", width := 32, wires := branch_result_final },
       { name := "br_captured_pc", width := 32, wires := br_captured_pc },
       { name := "br_captured_imm", width := 32, wires := br_captured_imm },
       { name := "br_pc_plus_4", width := 32, wires := br_pc_plus_4 },
       { name := "branch_target", width := 32, wires := branch_target },
       { name := "final_branch_target", width := 32, wires := final_branch_target },
       { name := "mem_address", width := 32, wires := mem_address },
       { name := "mem_tag_out", width := 6, wires := mem_tag_out }] ++
      (if enableM then [
       { name := "muldiv_result", width := 32, wires := muldiv_result },
       { name := "muldiv_tag_out", width := 6, wires := muldiv_tag_out }] else []) ++
      [{ name := "lsu_agu_address", width := 32, wires := lsu_agu_address },
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
       { name := "rs_branch_dispatch_tag", width := 6, wires := rs_branch_dispatch_tag }] ++
      (if enableM then [
       { name := "rs_muldiv_dispatch_opcode", width := 6, wires := rs_muldiv_dispatch_opcode },
       { name := "rs_muldiv_dispatch_src1", width := 32, wires := rs_muldiv_dispatch_src1 },
       { name := "rs_muldiv_dispatch_src2", width := 32, wires := rs_muldiv_dispatch_src2 },
       { name := "rs_muldiv_dispatch_tag", width := 6, wires := rs_muldiv_dispatch_tag },
       { name := "int_muldiv_tag", width := 6, wires := int_muldiv_tag },
       { name := "int_muldiv_data", width := 32, wires := int_muldiv_data }] else []) ++
      [{ name := "rvvi_pc_rdata", width := 32, wires := rvvi_pc_rdata },
       { name := "rvvi_insn", width := 32, wires := rvvi_insn },
       { name := "rvvi_rd", width := 5, wires := rvvi_rd },
       { name := "rvvi_rd_data", width := 32, wires := rvvi_rd_data },
       { name := "rob_head_idx", width := 4, wires := rob_head_idx }]
  }

/-- RV32I CPU (backward-compatible alias) -/
def mkCPU_RV32I : Circuit := mkCPU rv32iConfig

/-- RV32IM CPU (backward-compatible alias) -/
def mkCPU_RV32IM : Circuit := mkCPU rv32imConfig

end Shoumei.RISCV.CPU
