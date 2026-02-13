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
import Shoumei.RISCV.Execution.FPExecUnit
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
    (13, 8), (12, 8),   -- SLL, SLLI → 8  (1000: dir=0=left, arith=0)
    (5, 9), (4, 9),     -- SRL, SRLI → 9  (1001: dir=1=right, arith=0)
    (7, 11), (6, 11) ]  -- SRA, SRAI → 11 (1011: dir=1=right, arith=1)

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
    (13, 8), (12, 8),   -- SLL, SLLI → 8  (1000: dir=0=left, arith=0)
    (5, 9), (4, 9),     -- SRL, SRLI → 9  (1001: dir=1=right, arith=0)
    (7, 11), (6, 11) ]  -- SRA, SRAI → 11 (1011: dir=1=right, arith=1)

/-- OpType → MulDiv 3-bit opcode mapping for RV32IM/RV32IMF decoder encoding.
    MUL=0, MULH=1, MULHSU=2, MULHU=3, DIV=4, DIVU=5, REM=6, REMU=7
    Decoder enum positions (same for IM and IMF):
    16=REMU, 17=REM, 20=MULHU, 21=MULHSU, 22=MULH, 23=MUL, 35=DIVU, 36=DIV -/
def mulDivMapping : List (Nat × Nat) :=
  [ (23, 0),   -- MUL → 0
    (22, 1),   -- MULH → 1
    (21, 2),   -- MULHSU → 2
    (20, 3),   -- MULHU → 3
    (36, 4),   -- DIV → 4
    (35, 5),   -- DIVU → 5
    (17, 6),   -- REM → 6
    (16, 7) ]  -- REMU → 7

/-- Generic optype→opcode LUT for N-bit input → M-bit output.
    Same algorithm as mkOpTypeToALU4 but parameterized on widths. -/
def mkOpTypeLUT (pfx : String) (optype : List Wire) (outOp : List Wire)
    (mapping : List (Nat × Nat)) : List Gate :=
  let inWidth := optype.length
  let outWidth := outOp.length
  let testBit (n : Nat) (b : Nat) : Bool := (n / (2 ^ b)) % 2 != 0
  let bitTerms := (List.range outWidth).map fun b =>
    mapping.filter (fun (_, code) => testBit code b) |>.map Prod.fst
  let mkMatch (enc : Nat) (tag : String) : (List Gate × Wire) :=
    let matchWire := Wire.mk s!"{pfx}_{tag}"
    let bitWires := (List.range inWidth).map fun b =>
      if testBit enc b then optype[b]! else Wire.mk s!"{pfx}_n{b}"
    -- Chain AND gates
    let pairs := bitWires.enum.toArray
    if pairs.size <= 1 then
      ([Gate.mkBUF (bitWires.head!) matchWire], matchWire)
    else
      let first := Wire.mk s!"{pfx}_{tag}_t01"
      let firstGate := Gate.mkAND pairs[0]!.2 pairs[1]!.2 first
      let (gates, final) := (List.range (pairs.size - 2)).foldl (fun (acc, prev) idx =>
        let isLast := idx == pairs.size - 3
        let next := if isLast then matchWire else Wire.mk s!"{pfx}_{tag}_t{idx+2}"
        (acc ++ [Gate.mkAND prev pairs[idx + 2]!.2 next], next)
      ) ([firstGate], first)
      (gates, final)
  let mkOrChain (wires : List Wire) (outWire : Wire) : List Gate :=
    match wires with
    | [] => [Gate.mkBUF (Wire.mk s!"{pfx}_gnd") outWire]
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
  let notGates := (List.range inWidth).map fun b =>
    Gate.mkNOT optype[b]! (Wire.mk s!"{pfx}_n{b}")
  let mkBitLogic (terms : List Nat) (bitIdx : Nat) : List Gate :=
    let matchResults := terms.enum.map fun ⟨idx, enc⟩ =>
      mkMatch enc s!"b{bitIdx}_e{idx}"
    let matchGates := (matchResults.map Prod.fst).flatten
    let matchWires := matchResults.map Prod.snd
    let orGates := mkOrChain matchWires outOp[bitIdx]!
    matchGates ++ orGates
  notGates ++ (bitTerms.enum.map fun ⟨i, terms⟩ => mkBitLogic terms i).flatten

/-- OpType → FPU5 opcode mapping for RV32IMF decoder.
    Maps 7-bit decoder optype to 5-bit FPU operation code. -/
def fpuMapping_RV32IMF : List (Nat × Nat) :=
  [ (73, 0),   -- FADD_S → 0
    (49, 1),   -- FSUB_S → 1
    (58, 2),   -- FMUL_S → 2
    (67, 3),   -- FDIV_S → 3
    (50, 4),   -- FSQRT_S → 4
    (62, 5),   -- FMADD_S → 5
    (59, 6),   -- FMSUB_S → 6
    (55, 7),   -- FNMADD_S → 7
    (54, 8),   -- FNMSUB_S → 8
    (66, 9),   -- FEQ_S → 9
    (64, 10),  -- FLT_S → 10
    (65, 11),  -- FLE_S → 11
    (69, 12),  -- FCVT_W_S → 12
    (68, 13),  -- FCVT_WU_S → 13
    (71, 14),  -- FCVT_S_W → 14
    (70, 15),  -- FCVT_S_WU → 15
    (56, 16),  -- FMV_X_W → 16
    (57, 17),  -- FMV_W_X → 17
    (72, 18),  -- FCLASS_S → 18
    (60, 19),  -- FMIN_S → 19
    (61, 20),  -- FMAX_S → 20
    (53, 21),  -- FSGNJ_S → 21
    (52, 22),  -- FSGNJN_S → 22
    (51, 23) ] -- FSGNJX_S → 23

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
    (pfx : String := "busy")
    : (List Gate × List CircuitInstance) :=
  let mkW := fun (s : String) => Wire.mk s
  -- Decoder instances for set and clear paths
  let set_decode := (List.range 64).map fun i => mkW s!"{pfx}_set_dec_{i}"
  let clear_decode := (List.range 64).map fun i => mkW s!"{pfx}_clr_dec_{i}"

  let set_dec_inst : CircuitInstance := {
    moduleName := "Decoder6"
    instName := s!"u_{pfx}_set_dec"
    portMap :=
      (set_tag.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (set_decode.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }
  let clear_dec_inst : CircuitInstance := {
    moduleName := "Decoder6"
    instName := s!"u_{pfx}_clr_dec"
    portMap :=
      (clear_tag.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (clear_decode.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  -- 64 busy bits: DFF + next-state logic
  let busy_cur := (List.range 64).map fun i => mkW s!"{pfx}_q_{i}"
  let busy_next := (List.range 64).map fun i => mkW s!"{pfx}_d_{i}"

  -- Per-bit logic:
  --   set_i = set_en AND set_decode[i]
  --   clr_i = clear_en AND clear_decode[i]
  --   next[i] = clr_i ? 0 : (set_i ? 1 : cur[i])
  let perBitGates := (List.range 64).map fun i =>
    let set_i := mkW s!"{pfx}_set_{i}"
    let clr_i := mkW s!"{pfx}_clr_{i}"
    let mux1 := mkW s!"{pfx}_mux1_{i}"
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

  let busy_rs1 := mkW s!"{pfx}_rs1_raw"
  let busy_rs2 := mkW s!"{pfx}_rs2_raw"
  let mux1_gates := mkMux64to1 busy_cur read1_tag s!"{pfx}mux1" busy_rs1
  let mux2_gates := mkMux64to1 busy_cur read2_tag s!"{pfx}mux2" busy_rs2

  -- src1_ready = NOT busy[rs1_phys]
  -- src2_ready = use_imm OR NOT busy[rs2_phys]
  let not_busy_rs2 := mkW s!"not_{pfx}_rs2"
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

  -- ========== STAGE 4: DISPATCH TO RS ==========
  -- Route renamed instruction to appropriate RS based on OpType
  let (rsInteger_postDispatch, rsMemory_postDispatch, rsBranch_postDispatch,
       rsMulDiv_postDispatch, rsFPExec_postDispatch, rename_postDispatch, rob_postDispatch) :=
    (rsInteger_postCDB, rsMemory_postCDB, rsBranch_postCDB, rsMulDiv_postCDB,
     rsFPExec_postCDB, rename_postExecute, rob_postCDB)
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
    rsFPExec := rsFPExec_postDispatch
    rob := rob_postDispatch
    mulDivExecState := mulDivExecState'
    fpExecState := fpExecState'
    fflags := fflags'
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

section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

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
  let enableF := config.enableF
  let sbFwdPipelined := config.sbFwdPipelineStages > 0
  let enc := config.opcodeEncodings
  -- Opcode width: 7 bits when F extension (>64 instructions), 6 bits otherwise
  let opcodeWidth := if enableF then 7 else 6
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
  let decode_optype := makeIndexedWires "decode_optype" opcodeWidth
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

  -- FP decoder outputs (only used when enableF)
  let decode_rs3 := makeIndexedWires "decode_rs3" 5
  let decode_rm := makeIndexedWires "decode_rm" 3
  let dispatch_is_fp := Wire.mk "dispatch_is_fp"
  let decode_has_fp_rd := Wire.mk "decode_has_fp_rd"
  let decode_fp_rs1_read := Wire.mk "decode_fp_rs1_read"
  let decode_fp_rs2_read := Wire.mk "decode_fp_rs2_read"
  let decode_fp_rs3_used := Wire.mk "decode_fp_rs3_used"
  let dispatch_is_fp_load := Wire.mk "dispatch_is_fp_load"
  let dispatch_is_fp_store := Wire.mk "dispatch_is_fp_store"
  let decode_has_any_rd := Wire.mk "decode_has_any_rd"
  let decode_rd_nonzero := Wire.mk "decode_rd_nonzero"
  let decode_has_rd_nox0 := Wire.mk "decode_has_rd_nox0"
  let decode_has_any_rd_nox0 := Wire.mk "decode_has_any_rd_nox0"

  -- Forward-declare FP wires needed by INT rename and cross-domain logic
  let cdb_is_fp_rd := Wire.mk "cdb_is_fp_rd"
  let cdb_valid_int_prf := Wire.mk "cdb_valid_int_prf"
  let cdb_valid_fp_prf := Wire.mk "cdb_valid_fp_prf"
  let not_cdb_is_fp := Wire.mk "not_cdb_is_fp"
  let int_retire_valid := Wire.mk "int_retire_valid"
  let fp_retire_recycle_valid := Wire.mk "fp_retire_recycle_valid"
  let rob_old_phys_muxed := makeIndexedWires "rob_old_phys_muxed" 6

  -- === FETCH STAGE ===
  let fetch_pc := makeIndexedWires "fetch_pc" 32
  let fetch_stalled := Wire.mk "fetch_stalled"
  let global_stall := Wire.mk "global_stall"
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
  let flush_rs_fp := Wire.mk "flush_rs_fp"
  let pipeline_reset_rs_int := Wire.mk "pipeline_reset_rs_int"
  let pipeline_reset_rs_mem := Wire.mk "pipeline_reset_rs_mem"
  let pipeline_reset_rs_br := Wire.mk "pipeline_reset_rs_br"
  let pipeline_reset_rs_muldiv := Wire.mk "pipeline_reset_rs_muldiv"
  let pipeline_reset_rs_fp := Wire.mk "pipeline_reset_rs_fp"
  let pipeline_reset_rob := Wire.mk "pipeline_reset_rob"
  let pipeline_reset_busy := Wire.mk "pipeline_reset_busy"
  let pipeline_reset_misc := Wire.mk "pipeline_reset_misc"
  let fetch_stall := Wire.mk "fetch_stall"
  let rob_redirect_valid := Wire.mk "rob_redirect_valid"
  let rob_head_isBranch := Wire.mk "rob_head_isBranch"
  let rob_head_mispredicted := Wire.mk "rob_head_mispredicted"
  let rob_head_redirect_target := makeIndexedWires "rob_head_redirect_target" 32
  let retire_tag_muxed := makeIndexedWires "retire_tag_muxed" 6
  let branch_redirect_target_reg := makeIndexedWires "branch_redirect_target_reg" 32
  let redirect_valid_dff_inst : CircuitInstance := {
    moduleName := "DFlipFlop"
    instName := "u_redirect_valid_dff"
    portMap := [("d", rob_redirect_valid), ("q", branch_redirect_valid_reg),
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
  let flush_tags :=
    ["rs_int", "rs_mem", "rs_br"] ++
    (if enableM then ["rs_muldiv"] else []) ++
    (if enableF then ["rs_fp"] else []) ++
    ["rob", "busy", "misc"]
  let flush_dff_insts : List CircuitInstance := flush_tags.map (fun tag => {
    moduleName := "DFlipFlop"
    instName := s!"u_flush_dff_{tag}"
    portMap := [("d", pipeline_flush_comb), ("q", Wire.mk s!"flush_{tag}"),
                ("clock", clock), ("reset", reset)]
  })

  let fetch_predicted_taken := Wire.mk "fetch_predicted_taken"

  let fetch_inst : CircuitInstance := {
    moduleName := "FetchStage"
    instName := "u_fetch"
    portMap :=
      [("clock", clock), ("reset", reset),
       ("stall", fetch_stall),
       ("branch_valid", branch_redirect_valid_reg),
       ("const_0", zero), ("const_1", one)] ++
      (branch_redirect_target_reg.enum.map (fun ⟨i, w⟩ => (s!"branch_target_{i}", w))) ++
      (imem_resp_data.enum.map (fun ⟨i, w⟩ => (s!"instr_{i}", w))) ++
      (fetch_pc.enum.map (fun ⟨i, w⟩ => (s!"pc_{i}", w))) ++
      [("stalled_reg", fetch_stalled),
       ("predicted_taken", fetch_predicted_taken)]
  }

  -- === DECODER ===
  let decoderModuleName :=
    if enableF && enableM then "RV32IMFDecoder"
    else if enableF then "RV32IFDecoder"
    else if enableM then "RV32IMDecoder"
    else "RV32IDecoder"
  let decoder_inst : CircuitInstance := {
    moduleName := decoderModuleName
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
       ("io_use_imm", decode_use_imm)] ++
      (if enableF then
        (decode_rs3.enum.map (fun ⟨i, w⟩ => (s!"io_rs3_{i}", w))) ++
        (decode_rm.enum.map (fun ⟨i, w⟩ => (s!"io_rm_{i}", w))) ++
        [("io_is_fp", dispatch_is_fp),
         ("io_has_fp_rd", decode_has_fp_rd),
         ("io_fp_rs1_read", decode_fp_rs1_read),
         ("io_fp_rs2_read", decode_fp_rs2_read),
         ("io_fp_rs3_used", decode_fp_rs3_used),
         ("io_is_fp_load", dispatch_is_fp_load),
         ("io_is_fp_store", dispatch_is_fp_store)]
      else [])
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
  -- Domain-gated CDB valid: prevent tag collisions between INT/FP phys reg pools
  let cdb_valid_int_domain := if enableF then Wire.mk "cdb_valid_for_int" else Wire.mk "cdb_valid_nz"
  let cdb_valid_fp_domain := if enableF then Wire.mk "cdb_valid_for_fp" else cdb_valid
  -- Pre-register CDB signals (before pipeline register)
  let cdb_pre_valid := Wire.mk "cdb_pre_valid"
  -- Domain-gated pre-register CDB (wires created in cdb_domain_gates)
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
  let commit_store_en := Wire.mk "commit_store_en"
  let sb_commit_ptr := makeIndexedWires "sb_commit_ptr" 3
  let rob_head_isStore := Wire.mk "rob_head_isStore"
  let rob_head_physRd := makeIndexedWires "rob_head_physRd" 6
  let rob_head_oldPhysRd := makeIndexedWires "rob_head_oldPhysRd" 6
  let rob_head_hasOldPhysRd := Wire.mk "rob_head_hasOldPhysRd"
  let retire_recycle_valid := Wire.mk "retire_recycle_valid"
  let rvvi_rd_data := makeIndexedWires "rvvi_rd_data" 32
  let int_rename_rd_data3 := makeIndexedWires "int_rename_rd_data3" 32  -- unused rs3 data (INT has no FMA)

  -- Gate rename's instr_valid during redirect/flush
  let decode_valid_rename := Wire.mk "decode_valid_rename"

  let rename_inst : CircuitInstance := {
    moduleName := "RenameStage_32x64"
    instName := "u_rename"
    portMap :=
      [("clock", clock), ("reset", reset),
       ("zero", zero), ("one", one),
       ("instr_valid", decode_valid_rename),
       ("has_rd", if enableF then Wire.mk "decode_has_rd_int" else decode_has_rd)] ++
      (decode_rs1.enum.map (fun ⟨i, w⟩ => (s!"rs1_addr_{i}", w))) ++
      (decode_rs2.enum.map (fun ⟨i, w⟩ => (s!"rs2_addr_{i}", w))) ++
      ((List.range 5).map (fun i => (s!"rs3_addr_{i}", zero))) ++  -- rs3_addr: unused on INT rename
      (decode_rd.enum.map (fun ⟨i, w⟩ => (s!"rd_addr_{i}", w))) ++
      [("cdb_valid", if enableF then cdb_valid_int_prf else cdb_valid_prf)] ++
      (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag_{i}", w))) ++
      (cdb_data.enum.map (fun ⟨i, w⟩ => (s!"cdb_data_{i}", w))) ++
      [("retire_valid", if enableF then int_retire_valid else retire_recycle_valid)] ++
      (retire_tag_muxed.enum.map (fun ⟨i, w⟩ => (s!"retire_tag_{i}", w))) ++
      (rob_head_physRd.enum.map (fun ⟨i, w⟩ => (s!"rd_tag4_{i}", w))) ++  -- 4th read port: RVVI commit readback
      [("rename_valid", rename_valid), ("stall", rename_stall)] ++
      (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"rs1_phys_out_{i}", w))) ++
      (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"rs2_phys_out_{i}", w))) ++
      (rd_phys.enum.map (fun ⟨i, w⟩ => (s!"rd_phys_out_{i}", w))) ++
      (rs1_data.enum.map (fun ⟨i, w⟩ => (s!"rs1_data_{i}", w))) ++
      (rs2_data.enum.map (fun ⟨i, w⟩ => (s!"rs2_data_{i}", w))) ++
      (old_rd_phys.enum.map (fun ⟨i, w⟩ => (s!"old_rd_phys_out_{i}", w))) ++
      (int_rename_rd_data3.enum.map (fun ⟨i, w⟩ => (s!"rd_data3_{i}", w))) ++
      (rvvi_rd_data.enum.map (fun ⟨i, w⟩ => (s!"rd_data4_{i}", w))) ++
      -- Committed RAT recovery
      [("flush_en", branch_redirect_valid_reg),  -- Committed RAT restore on misprediction
       ("commit_valid", rob_commit_en),
       ("commit_hasPhysRd",
        if enableF then Wire.mk "int_commit_hasPhysRd" else rob_head_hasOldPhysRd)] ++
      ((List.range 5).map (fun i => (s!"commit_archRd_{i}", Wire.mk s!"rob_head_archRd_{i}"))) ++
      (rob_head_physRd.enum.map (fun ⟨i, w⟩ => (s!"commit_physRd_{i}", w))) ++
      [("force_alloc", dispatch_is_branch)]
  }

  -- === DISPATCH QUALIFICATION ===
  let not_stall := Wire.mk "not_stall"
  let dispatch_base_valid := Wire.mk "dispatch_base_valid"
  let dispatch_int_valid := Wire.mk "dispatch_int_valid"
  let dispatch_mem_valid := Wire.mk "dispatch_mem_valid"
  let dispatch_branch_valid := Wire.mk "dispatch_branch_valid"
  let dispatch_muldiv_valid := Wire.mk "dispatch_muldiv_valid"
  let dispatch_fp_valid := Wire.mk "dispatch_fp_valid"

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
    (if enableF then [Gate.mkOR reset flush_rs_fp pipeline_reset_rs_fp] else []) ++
    [Gate.mkOR reset flush_rob pipeline_reset_rob,
     Gate.mkOR reset flush_busy pipeline_reset_busy,
     Gate.mkOR reset flush_misc pipeline_reset_misc]

  let dispatch_gates :=
    [Gate.mkNOT global_stall not_stall,
     Gate.mkOR rob_redirect_valid branch_redirect_valid_reg redirect_or,
     Gate.mkOR redirect_or pipeline_flush redirect_or_flush,
     Gate.mkNOT redirect_or_flush not_redirecting,
     Gate.mkAND decode_valid not_redirecting decode_valid_no_redirect,
     Gate.mkAND decode_valid_no_redirect not_stall decode_valid_rename,
     Gate.mkBUF decode_valid_rename dispatch_base_valid,
     Gate.mkAND dispatch_base_valid dispatch_is_integer dispatch_int_valid,
     Gate.mkAND dispatch_base_valid dispatch_is_memory dispatch_mem_valid,
     Gate.mkAND dispatch_base_valid dispatch_is_branch dispatch_branch_valid] ++
    (if enableM then [Gate.mkAND dispatch_base_valid dispatch_is_muldiv dispatch_muldiv_valid] else []) ++
    (if enableF then
      let not_has_fp_rd := Wire.mk "not_has_fp_rd"
      let decode_has_rd_int := Wire.mk "decode_has_rd_int"
      [Gate.mkAND dispatch_base_valid dispatch_is_fp dispatch_fp_valid,
       Gate.mkOR decode_has_rd decode_has_fp_rd decode_has_any_rd,
       -- Mask has_rd for INT rename: exclude FP-only-write instructions
       -- FP ops that write INT rd (FMV.X.W, FCMP, etc.) have has_fp_rd=0, so they keep has_rd=1
       Gate.mkNOT decode_has_fp_rd not_has_fp_rd,
       Gate.mkAND decode_has_rd not_has_fp_rd decode_has_rd_int]
    else [])

  -- INT rename has_rd: use masked version when F enabled (exclude FP-only-write ops)
  let decode_has_rd_for_int := if enableF then Wire.mk "decode_has_rd_int" else decode_has_rd

  -- Compute decode_rd_nonzero = OR of all 5 bits of decode_rd (for x0 exclusion)
  -- Used to gate alloc_hasPhysRd/alloc_hasOldPhysRd in the ROB:
  -- if rd=x0, the rename stage doesn't allocate a physRd, so the ROB shouldn't
  -- record hasPhysRd=1 (otherwise it frees oldPhysRd=p0 at commit, putting p0
  -- back in the free list where CDB writes to tag=0 are blocked by cdb_tag_nonzero).
  let rd_nz_or1 := Wire.mk "rd_nz_or1"
  let rd_nz_or2 := Wire.mk "rd_nz_or2"
  let rd_nz_or3 := Wire.mk "rd_nz_or3"
  let rd_nonzero_gates := [
    Gate.mkOR decode_rd[0]! decode_rd[1]! rd_nz_or1,
    Gate.mkOR rd_nz_or1 decode_rd[2]! rd_nz_or2,
    Gate.mkOR rd_nz_or2 decode_rd[3]! rd_nz_or3,
    Gate.mkOR rd_nz_or3 decode_rd[4]! decode_rd_nonzero,
    Gate.mkAND decode_has_rd decode_rd_nonzero decode_has_rd_nox0
  ] ++ (if enableF then [
    -- For FP path: FP rd is always valid (f0 is a real register), so only gate INT rd on x0
    Gate.mkOR decode_has_rd_nox0 decode_has_fp_rd decode_has_any_rd_nox0
  ] else [])

  -- === BUSY-BIT TABLE ===
  let busy_set_en := Wire.mk "busy_set_en"
  let busy_set_gate := Gate.mkAND rename_valid decode_has_rd_for_int busy_set_en
  let busy_src1_ready := Wire.mk "busy_src1_ready"
  let busy_src2_ready := Wire.mk "busy_src2_ready"
  let busy_src2_ready_reg := Wire.mk "busy_src2_ready_reg"
  let (busy_gates, busy_instances) := mkBusyBitTable
    clock pipeline_reset_busy zero one
    rd_phys busy_set_en
    cdb_tag cdb_valid_int_domain
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

  let cdb_pre_valid_int_dom := if enableF then Wire.mk "cdb_pre_valid_for_int" else Wire.mk "cdb_pre_valid_nz"
  let cdb_fwd_gates := [
    Gate.mkAND cdb_valid_int_domain cdb_match_src1 cdb_fwd_src1,
    Gate.mkAND cdb_valid_int_domain cdb_match_src2 cdb_fwd_src2,
    Gate.mkAND cdb_pre_valid_int_dom cdb_pre_match_src1 cdb_pre_fwd_src1,
    Gate.mkAND cdb_pre_valid_int_dom cdb_pre_match_src2 cdb_pre_fwd_src2,
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

  -- === FP RENAME STAGE (conditional) ===
  let fp_rs1_phys := makeIndexedWires "fp_rs1_phys" 6
  let fp_rs2_phys := makeIndexedWires "fp_rs2_phys" 6
  let fp_rd_phys := makeIndexedWires "fp_rd_phys" 6
  let fp_old_rd_phys := makeIndexedWires "fp_old_rd_phys" 6
  let fp_rs1_data := makeIndexedWires "fp_rs1_data" 32
  let fp_rs2_data := makeIndexedWires "fp_rs2_data" 32
  let fp_rename_valid := Wire.mk "fp_rename_valid"
  let fp_rename_stall := Wire.mk "fp_rename_stall"
  let fp_rs3_data := makeIndexedWires "fp_rs3_data" 32
  let fp_rvvi_rd_data := makeIndexedWires "fp_rvvi_rd_data" 32  -- FP PRF 4th read port for RVVI

  -- CDB routing: split CDB writes between INT and FP PRFs
  let cdb_prf_route_gates :=
    if enableF then
      [Gate.mkNOT cdb_is_fp_rd not_cdb_is_fp,
       Gate.mkAND cdb_valid_prf not_cdb_is_fp cdb_valid_int_prf,
       Gate.mkAND cdb_valid_prf cdb_is_fp_rd cdb_valid_fp_prf]
    else []

  let fp_rename_inst : CircuitInstance := {
    moduleName := "RenameStage_32x64"
    instName := "u_fp_rename"
    portMap :=
      [("clock", clock), ("reset", reset),
       ("zero", zero), ("one", one),
       ("instr_valid", decode_valid_rename),
       ("has_rd", decode_has_fp_rd)] ++
      (decode_rs1.enum.map (fun ⟨i, w⟩ => (s!"rs1_addr_{i}", w))) ++
      (decode_rs2.enum.map (fun ⟨i, w⟩ => (s!"rs2_addr_{i}", w))) ++
      (decode_rs3.enum.map (fun ⟨i, w⟩ => (s!"rs3_addr_{i}", w))) ++  -- rs3 lookup via FP RAT
      (decode_rd.enum.map (fun ⟨i, w⟩ => (s!"rd_addr_{i}", w))) ++
      [("cdb_valid", cdb_valid_fp_prf)] ++
      (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag_{i}", w))) ++
      (cdb_data.enum.map (fun ⟨i, w⟩ => (s!"cdb_data_{i}", w))) ++
      [("retire_valid", fp_retire_recycle_valid)] ++
      (fp_old_rd_phys.enum.map (fun ⟨i, w⟩ => (s!"retire_tag_{i}", w))) ++
      (rob_head_physRd.enum.map (fun ⟨i, w⟩ => (s!"rd_tag4_{i}", w))) ++  -- 4th read port: RVVI FP commit readback
      [("rename_valid", fp_rename_valid), ("stall", fp_rename_stall)] ++
      (fp_rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"rs1_phys_out_{i}", w))) ++
      (fp_rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"rs2_phys_out_{i}", w))) ++
      (fp_rd_phys.enum.map (fun ⟨i, w⟩ => (s!"rd_phys_out_{i}", w))) ++
      (fp_rs1_data.enum.map (fun ⟨i, w⟩ => (s!"rs1_data_{i}", w))) ++
      (fp_rs2_data.enum.map (fun ⟨i, w⟩ => (s!"rs2_data_{i}", w))) ++
      (fp_old_rd_phys.enum.map (fun ⟨i, w⟩ => (s!"old_rd_phys_out_{i}", w))) ++
      (fp_rs3_data.enum.map (fun ⟨i, w⟩ => (s!"rd_data3_{i}", w))) ++
      (fp_rvvi_rd_data.enum.map (fun ⟨i, w⟩ => (s!"rd_data4_{i}", w))) ++
      -- Committed RAT recovery (FP uses same commit signals, filtered by is_fp)
      [("flush_en", branch_redirect_valid_reg),  -- Committed RAT restore on misprediction
       ("commit_valid", rob_commit_en),
       ("commit_hasPhysRd", Wire.mk "rob_head_is_fp")] ++
      ((List.range 5).map (fun i => (s!"commit_archRd_{i}", Wire.mk s!"rob_head_archRd_{i}"))) ++
      (rob_head_physRd.enum.map (fun ⟨i, w⟩ => (s!"commit_physRd_{i}", w))) ++
      [("force_alloc", zero)]  -- FP rename doesn't need branch tracking
  }

  -- Mask dest_tag to 0 when no INT rd writeback (has_rd=0, rd=x0, or FP-only rd).
  -- This prevents stale tags from matching in RS entries via CDB forwarding.
  let int_has_rd_nox0 := Wire.mk "int_has_rd_nox0"
  let int_has_rd_nox0_gate :=
    if enableF then
      -- decode_has_rd_nox0 already excludes x0 and no-rd; just also exclude FP-only
      Gate.mkAND decode_has_rd_nox0 (Wire.mk "not_has_fp_rd") int_has_rd_nox0
    else
      Gate.mkBUF decode_has_rd_nox0 int_has_rd_nox0
  let int_dest_tag_masked := makeIndexedWires "int_dest_tag_masked" 6
  let int_dest_tag_mask_gates := [int_has_rd_nox0_gate] ++
    (List.range 6).map (fun i =>
      Gate.mkAND rd_phys[i]! int_has_rd_nox0 int_dest_tag_masked[i]!)

  -- === BRANCH UNIQUE TAG ALLOCATION ===
  -- Branches need unique CDB tags for misprediction tracking in ROB, even for rd=x0.
  -- Use the unmasked rename counter tag (rd_phys) for branches.
  let branch_alloc_physRd := makeIndexedWires "branch_alloc_physRd" 6
  let branch_alloc_hasPhysRd := Wire.mk "branch_alloc_hasPhysRd"
  let rob_alloc_physRd_fp := makeIndexedWires "rob_alloc_physRd_fp" 6
  let rob_alloc_hasPhysRd_fp := Wire.mk "rob_alloc_hasPhysRd_fp"
  let fp_issue_dest_tag := makeIndexedWires "fp_issue_dest_tag" 6
  let branch_alloc_physRd_gates :=
    -- branch_alloc_hasPhysRd = dispatch_is_branch OR decode_has_rd_nox0
    [Gate.mkOR dispatch_is_branch decode_has_rd_nox0 branch_alloc_hasPhysRd] ++
    -- branch_alloc_physRd = MUX(int_dest_tag_masked, rd_phys, dispatch_is_branch)
    -- When branch: use unmasked tag (unique); otherwise: use masked tag
    (List.range 6).map (fun i =>
      Gate.mkMUX int_dest_tag_masked[i]! rd_phys[i]! dispatch_is_branch branch_alloc_physRd[i]!) ++
    -- FP-aware: rob_alloc_physRd_fp = MUX(fp_issue_dest_tag, rd_phys, dispatch_is_branch)
    (if enableF then
      [Gate.mkOR dispatch_is_branch decode_has_any_rd_nox0 rob_alloc_hasPhysRd_fp] ++
      (List.range 6).map (fun i =>
        Gate.mkMUX fp_issue_dest_tag[i]! rd_phys[i]! dispatch_is_branch rob_alloc_physRd_fp[i]!)
    else
      [Gate.mkBUF branch_alloc_hasPhysRd rob_alloc_hasPhysRd_fp] ++
      (List.range 6).map (fun i =>
        Gate.mkBUF branch_alloc_physRd[i]! rob_alloc_physRd_fp[i]!))
  -- For retire: branches with rd=x0 need to free their tracking tag at commit
  let branch_tracking := Wire.mk "branch_tracking"
  let not_hasOldPhysRd := Wire.mk "not_hasOldPhysRd"
  let branch_tracking_tmp := Wire.mk "branch_tracking_tmp"
  let retire_any_old := Wire.mk "retire_any_old"

  -- === CROSS-DOMAIN SOURCE ROUTING ===
  let fp_issue_src1_tag := makeIndexedWires "fp_issue_src1_tag" 6
  let fp_issue_src2_tag := makeIndexedWires "fp_issue_src2_tag" 6
  let fp_issue_src1_data := makeIndexedWires "fp_issue_src1_data" 32
  let fp_issue_src2_data := makeIndexedWires "fp_issue_src2_data" 32

  let fp_crossdomain_gates :=
    if enableF then
      (List.range 6).map (fun i =>
        Gate.mkMUX rs1_phys[i]! fp_rs1_phys[i]! decode_fp_rs1_read fp_issue_src1_tag[i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkMUX (fwd_src1_data[i]!) fp_rs1_data[i]! decode_fp_rs1_read fp_issue_src1_data[i]!) ++
      (List.range 6).map (fun i =>
        Gate.mkMUX rs2_phys[i]! fp_rs2_phys[i]! decode_fp_rs2_read fp_issue_src2_tag[i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkMUX (fwd_src2_data[i]!) fp_rs2_data[i]! decode_fp_rs2_read fp_issue_src2_data[i]!) ++
      (List.range 6).map (fun i =>
        Gate.mkMUX int_dest_tag_masked[i]! fp_rd_phys[i]! decode_has_fp_rd fp_issue_dest_tag[i]!)
    else []

  -- === FP BUSY-BIT TABLE (conditional) ===
  let fp_busy_src1_ready_raw := Wire.mk "fp_busy_src1_ready_raw"
  let fp_busy_src2_ready_raw := Wire.mk "fp_busy_src2_ready_raw"
  let fp_busy_src2_ready_reg_raw := Wire.mk "fp_busy_src2_ready_reg_raw"
  let fp_busy_set_en := Wire.mk "fp_busy_set_en"

  let fp_busy_set_gate :=
    if enableF then Gate.mkAND rename_valid decode_has_fp_rd fp_busy_set_en
    else Gate.mkBUF zero fp_busy_set_en

  let (fp_busy_gates, fp_busy_instances) :=
    if enableF then mkBusyBitTable
      clock pipeline_reset_busy zero one
      fp_rd_phys fp_busy_set_en
      cdb_tag cdb_valid_fp_domain
      fp_rs1_phys fp_rs2_phys
      zero
      fp_busy_src1_ready_raw fp_busy_src2_ready_raw fp_busy_src2_ready_reg_raw
      "fp_busy"
    else ([], [])

  -- === FP CDB FORWARDING ===
  let fp_cdb_match_src1 := Wire.mk "fp_cdb_match_src1"
  let fp_cdb_match_src2 := Wire.mk "fp_cdb_match_src2"
  let fp_cdb_fwd_src1 := Wire.mk "fp_cdb_fwd_src1"
  let fp_cdb_fwd_src2 := Wire.mk "fp_cdb_fwd_src2"
  let fp_cdb_pre_match_src1 := Wire.mk "fp_cdb_pre_match_src1"
  let fp_cdb_pre_match_src2 := Wire.mk "fp_cdb_pre_match_src2"
  let fp_cdb_pre_fwd_src1 := Wire.mk "fp_cdb_pre_fwd_src1"
  let fp_cdb_pre_fwd_src2 := Wire.mk "fp_cdb_pre_fwd_src2"
  let fp_any_fwd_src1 := Wire.mk "fp_any_fwd_src1"
  let fp_any_fwd_src2 := Wire.mk "fp_any_fwd_src2"
  let fp_issue_src1_ready := Wire.mk "fp_issue_src1_ready"
  let fp_issue_src2_ready := Wire.mk "fp_issue_src2_ready"
  let fp_busy_src1_ready := Wire.mk "fp_busy_src1_ready"
  let fp_busy_src2_ready := Wire.mk "fp_busy_src2_ready"

  let fp_cdb_fwd_cmp_src1_inst : CircuitInstance := {
    moduleName := "EqualityComparator6"
    instName := "u_fp_cdb_fwd_cmp_src1"
    portMap := [("eq", fp_cdb_match_src1)] ++
               (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (fp_issue_src1_tag.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  }
  let fp_cdb_fwd_cmp_src2_inst : CircuitInstance := {
    moduleName := "EqualityComparator6"
    instName := "u_fp_cdb_fwd_cmp_src2"
    portMap := [("eq", fp_cdb_match_src2)] ++
               (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (fp_issue_src2_tag.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  }
  let fp_cdb_pre_fwd_cmp_src1_inst : CircuitInstance := {
    moduleName := "EqualityComparator6"
    instName := "u_fp_cdb_pre_fwd_cmp_src1"
    portMap := [("eq", fp_cdb_pre_match_src1)] ++
               (cdb_pre_tag.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (fp_issue_src1_tag.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  }
  let fp_cdb_pre_fwd_cmp_src2_inst : CircuitInstance := {
    moduleName := "EqualityComparator6"
    instName := "u_fp_cdb_pre_fwd_cmp_src2"
    portMap := [("eq", fp_cdb_pre_match_src2)] ++
               (cdb_pre_tag.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (fp_issue_src2_tag.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  }

  -- FP CDB forwarding: domain-aware (XNOR match to prevent tag collision)
  -- domain_match_src1 = (cdb_is_fp_rd XNOR decode_fp_rs1_read)
  --   = (both FP) OR (both INT) — only forward when CDB domain matches source domain
  let fp_domain_xor_src1 := Wire.mk "fp_domain_xor_src1"
  let fp_domain_match_src1 := Wire.mk "fp_domain_match_src1"
  let fp_domain_xor_src2 := Wire.mk "fp_domain_xor_src2"
  let fp_domain_match_src2 := Wire.mk "fp_domain_match_src2"
  let fp_cdb_fwd_src1_tmp := Wire.mk "fp_cdb_fwd_src1_tmp"
  let fp_cdb_fwd_src2_tmp := Wire.mk "fp_cdb_fwd_src2_tmp"
  -- Same for pre-register CDB
  let fp_pre_domain_xor_src1 := Wire.mk "fp_pre_domain_xor_src1"
  let fp_pre_domain_match_src1 := Wire.mk "fp_pre_domain_match_src1"
  let fp_pre_domain_xor_src2 := Wire.mk "fp_pre_domain_xor_src2"
  let fp_pre_domain_match_src2 := Wire.mk "fp_pre_domain_match_src2"
  let fp_cdb_pre_fwd_src1_tmp := Wire.mk "fp_cdb_pre_fwd_src1_tmp"
  let fp_cdb_pre_fwd_src2_tmp := Wire.mk "fp_cdb_pre_fwd_src2_tmp"

  let fp_cdb_fwd_gates :=
    if enableF then [
      -- Registered CDB domain matching
      Gate.mkXOR cdb_is_fp_rd decode_fp_rs1_read fp_domain_xor_src1,
      Gate.mkNOT fp_domain_xor_src1 fp_domain_match_src1,
      Gate.mkXOR cdb_is_fp_rd decode_fp_rs2_read fp_domain_xor_src2,
      Gate.mkNOT fp_domain_xor_src2 fp_domain_match_src2,
      Gate.mkAND cdb_valid fp_cdb_match_src1 fp_cdb_fwd_src1_tmp,
      Gate.mkAND fp_cdb_fwd_src1_tmp fp_domain_match_src1 fp_cdb_fwd_src1,
      Gate.mkAND cdb_valid fp_cdb_match_src2 fp_cdb_fwd_src2_tmp,
      Gate.mkAND fp_cdb_fwd_src2_tmp fp_domain_match_src2 fp_cdb_fwd_src2,
      -- Pre-register CDB domain matching
      Gate.mkXOR (Wire.mk "cdb_pre_is_fp") decode_fp_rs1_read fp_pre_domain_xor_src1,
      Gate.mkNOT fp_pre_domain_xor_src1 fp_pre_domain_match_src1,
      Gate.mkXOR (Wire.mk "cdb_pre_is_fp") decode_fp_rs2_read fp_pre_domain_xor_src2,
      Gate.mkNOT fp_pre_domain_xor_src2 fp_pre_domain_match_src2,
      Gate.mkAND cdb_pre_valid fp_cdb_pre_match_src1 fp_cdb_pre_fwd_src1_tmp,
      Gate.mkAND fp_cdb_pre_fwd_src1_tmp fp_pre_domain_match_src1 fp_cdb_pre_fwd_src1,
      Gate.mkAND cdb_pre_valid fp_cdb_pre_match_src2 fp_cdb_pre_fwd_src2_tmp,
      Gate.mkAND fp_cdb_pre_fwd_src2_tmp fp_pre_domain_match_src2 fp_cdb_pre_fwd_src2,
      -- Combine forwarding results
      Gate.mkOR fp_cdb_fwd_src1 fp_cdb_pre_fwd_src1 fp_any_fwd_src1,
      Gate.mkOR fp_cdb_fwd_src2 fp_cdb_pre_fwd_src2 fp_any_fwd_src2,
      Gate.mkMUX busy_src1_ready fp_busy_src1_ready_raw decode_fp_rs1_read fp_busy_src1_ready,
      Gate.mkMUX busy_src2_ready fp_busy_src2_ready_raw decode_fp_rs2_read fp_busy_src2_ready,
      Gate.mkOR fp_busy_src1_ready fp_any_fwd_src1 fp_issue_src1_ready,
      Gate.mkOR fp_busy_src2_ready fp_any_fwd_src2 fp_issue_src2_ready
    ] else []

  let fp_fwd_src1_data := makeIndexedWires "fp_fwd_src1_data" 32
  let fp_fwd_src2_data := makeIndexedWires "fp_fwd_src2_data" 32
  let fp_fwd_src1_tmp := makeIndexedWires "fp_fwd_src1_tmp" 32
  let fp_fwd_src2_tmp := makeIndexedWires "fp_fwd_src2_tmp" 32

  let fp_fwd_data_gates :=
    if enableF then
      ((List.range 32).map (fun i =>
        [Gate.mkMUX fp_issue_src1_data[i]! cdb_data[i]! fp_cdb_fwd_src1 fp_fwd_src1_tmp[i]!,
         Gate.mkMUX fp_fwd_src1_tmp[i]! cdb_pre_data[i]! fp_cdb_pre_fwd_src1 fp_fwd_src1_data[i]!]) |>.flatten) ++
      ((List.range 32).map (fun i =>
        [Gate.mkMUX fp_issue_src2_data[i]! cdb_data[i]! fp_cdb_fwd_src2 fp_fwd_src2_tmp[i]!,
         Gate.mkMUX fp_fwd_src2_tmp[i]! cdb_pre_data[i]! fp_cdb_pre_fwd_src2 fp_fwd_src2_data[i]!]) |>.flatten)
    else []

  let fp_cdb_fwd_instances :=
    if enableF then
      [fp_cdb_fwd_cmp_src1_inst, fp_cdb_fwd_cmp_src2_inst,
       fp_cdb_pre_fwd_cmp_src1_inst, fp_cdb_pre_fwd_cmp_src2_inst]
    else []

  -- === SRC2 MUX ===
  let issue_src2_muxed := makeIndexedWires "issue_src2_muxed" 32
  let src2_mux_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (fwd_src2_data[i]!) (decode_imm[i]!) decode_use_imm (issue_src2_muxed[i]!))

  -- === RESERVATION STATIONS ===
  -- RS Integer
  let rs_int_alloc_ptr := makeIndexedWires "rs_int_alloc_ptr" 2
  let rs_int_grant := makeIndexedWires "rs_int_grant" 4
  let ib_fifo_enq_ready := Wire.mk "ib_fifo_enq_ready"
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
                ("cdb_valid", cdb_valid_int_domain), ("dispatch_en", ib_fifo_enq_ready),
                ("issue_full", rs_int_issue_full), ("dispatch_valid", rs_int_dispatch_valid)] ++
               -- Only connect lower 6 bits of optype; bit 6 is FP flag, unused by integer RS
               ((decode_optype.take 6).enum.map (fun ⟨i, w⟩ => (s!"issue_opcode_{i}", w))) ++
               (int_dest_tag_masked.enum.map (fun ⟨i, w⟩ => (s!"issue_dest_tag_{i}", w))) ++
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

  -- FP memory path: MUX dest_tag and src2 for FLW/FSW
  let mem_dest_tag := if enableF then makeIndexedWires "mem_dest_tag" 6 else int_dest_tag_masked
  let mem_src2_tag := if enableF then makeIndexedWires "mem_src2_tag" 6 else rs2_phys
  let mem_src2_data := if enableF then makeIndexedWires "mem_src2_data" 32 else fwd_src2_data
  let mem_src2_ready := if enableF then Wire.mk "mem_src2_ready" else issue_src2_ready_reg
  let fp_mem_mux_gates :=
    if enableF then
      -- FLW: dest_tag from FP rename, not INT rename
      (List.range 6).map (fun i =>
        Gate.mkMUX int_dest_tag_masked[i]! fp_issue_dest_tag[i]! dispatch_is_fp_load mem_dest_tag[i]!) ++
      -- FSW: src2 tag/data from FP rename (store data from FP reg)
      (List.range 6).map (fun i =>
        Gate.mkMUX rs2_phys[i]! fp_rs2_phys[i]! dispatch_is_fp_store mem_src2_tag[i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkMUX fwd_src2_data[i]! fp_fwd_src2_data[i]! dispatch_is_fp_store mem_src2_data[i]!) ++
      -- FSW: src2 ready from FP busy table
      [Gate.mkMUX issue_src2_ready_reg fp_issue_src2_ready dispatch_is_fp_store mem_src2_ready]
    else []

  -- Forward-declare cross-size stall wires (driven later by load forwarding logic)
  let mem_dispatch_en := Wire.mk "mem_dispatch_en"
  let cross_size_stall := Wire.mk "cross_size_stall"
  let not_cross_size_stall := Wire.mk "not_cross_size_stall"
  let branch_dispatch_en := Wire.mk "branch_dispatch_en"
  let not_int_dispatching := Wire.mk "not_int_dispatching"

  let rs_mem_inst : CircuitInstance := {
    moduleName := "MemoryRS4"
    instName := "u_rs_memory"
    portMap := [("clock", clock), ("reset", pipeline_reset_rs_mem),
                ("zero", zero), ("one", one), ("issue_en", dispatch_mem_valid),
                ("issue_is_store", dispatch_is_store),
                ("issue_src1_ready", issue_src1_ready), ("issue_src2_ready", mem_src2_ready),
                ("cdb_valid", cdb_valid_int_domain), ("dispatch_en", mem_dispatch_en),
                ("issue_full", rs_mem_issue_full), ("dispatch_valid", rs_mem_dispatch_valid)] ++
               -- Only connect lower 6 bits of optype; bit 6 is FP flag, unused by memory RS
               ((decode_optype.take 6).enum.map (fun ⟨i, w⟩ => (s!"issue_opcode_{i}", w))) ++
               (mem_dest_tag.enum.map (fun ⟨i, w⟩ => (s!"issue_dest_tag_{i}", w))) ++
               (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_tag_{i}", w))) ++
               (fwd_src1_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_data_{i}", w))) ++
               (mem_src2_tag.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_tag_{i}", w))) ++
               -- Memory RS: src2 = forwarded register value (store data), NOT immediate
               (mem_src2_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_data_{i}", w))) ++
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
                ("cdb_valid", cdb_valid_int_domain), ("dispatch_en", branch_dispatch_en),
                ("issue_full", rs_branch_issue_full), ("dispatch_valid", rs_branch_dispatch_valid)] ++
               -- Only connect lower 6 bits of optype; bit 6 is FP flag, unused by branch RS
               ((decode_optype.take 6).enum.map (fun ⟨i, w⟩ => (s!"issue_opcode_{i}", w))) ++
               -- Branch RS uses unmasked physRd (rd_phys) for unique CDB tag matching
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

  -- === BRANCH PREDICTED_TAKEN SHADOW DFFs (4 entries, indexed by RS alloc_ptr) ===
  -- Store predicted_taken from fetch stage alongside each branch RS entry.
  -- Write: gated by dispatch_branch_valid + decoded alloc_ptr
  -- Read: MUX4 selected by dispatch grant → branch_predicted_taken
  -- NOTE: Use distinct wire names (br_pred_e{N}) to prevent codegen from grouping
  -- them into a single bus (which would break multi-DFF assignment).
  let br_pred_e := (List.range 4).map (fun e => Wire.mk s!"br_pred_e{e}")
  let br_pred_taken_gates := (List.range 4).map (fun e =>
    let next := Wire.mk s!"br_pred_next_e{e}"
    [ Gate.mkMUX br_pred_e[e]! fetch_predicted_taken br_pc_rf_we[e]! next,
      Gate.mkDFF next clock reset br_pred_e[e]! ]
  ) |>.flatten

  -- Read predicted_taken for dispatching branch using grant one-hot
  -- MUX4: grant[0]→e0, grant[1]→e1, grant[2]→e2, grant[3]→e3
  let br_pred_sel0 := Wire.mk "br_pred_sel0"
  let br_pred_sel1 := Wire.mk "br_pred_sel1"
  let branch_predicted_taken := Wire.mk "branch_predicted_taken"
  let br_pred_mux_01 := Wire.mk "br_pred_mux_01"
  let br_pred_mux_23 := Wire.mk "br_pred_mux_23"
  let br_pred_read_gates := [
    -- sel = {grant[2]|grant[3], grant[1]|grant[3]}
    Gate.mkOR rs_branch_grant[1]! rs_branch_grant[3]! br_pred_sel0,
    Gate.mkOR rs_branch_grant[2]! rs_branch_grant[3]! br_pred_sel1,
    -- 4:1 mux using 2-level tree
    Gate.mkMUX br_pred_e[0]! br_pred_e[1]! br_pred_sel0 br_pred_mux_01,
    Gate.mkMUX br_pred_e[2]! br_pred_e[3]! br_pred_sel0 br_pred_mux_23,
    Gate.mkMUX br_pred_mux_01 br_pred_mux_23 br_pred_sel1 branch_predicted_taken
  ]

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
                ("cdb_valid", cdb_valid_int_domain), ("dispatch_en", one),
                ("issue_full", rs_muldiv_issue_full), ("dispatch_valid", rs_muldiv_dispatch_valid)] ++
               -- Only connect lower 6 bits of optype; bit 6 is FP flag, unused by muldiv RS
               ((decode_optype.take 6).enum.map (fun ⟨i, w⟩ => (s!"issue_opcode_{i}", w))) ++
               (int_dest_tag_masked.enum.map (fun ⟨i, w⟩ => (s!"issue_dest_tag_{i}", w))) ++
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

  -- MulDiv opcode LUT: translate 6-bit dispatch optype → 3-bit MulDiv op
  let muldiv_op := makeIndexedWires "muldiv_op" 3
  let muldiv_lut_gates :=
    if enableM then mkOpTypeLUT "mdlut" rs_muldiv_dispatch_opcode muldiv_op mulDivMapping
    else []

  let muldiv_exec_inst : CircuitInstance := {
    moduleName := "MulDivExecUnit"
    instName := "u_exec_muldiv"
    portMap :=
      (rs_muldiv_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (rs_muldiv_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      (muldiv_op.enum.map (fun ⟨i, w⟩ => (s!"op_{i}", w))) ++
      (rs_muldiv_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dest_tag_{i}", w))) ++
      [("valid_in", rs_muldiv_dispatch_valid),
       ("clock", clock), ("reset", pipeline_reset_rs_muldiv),
       ("zero", zero), ("one", one)] ++
      (muldiv_result.enum.map (fun ⟨i, w⟩ => (s!"result_{i}", w))) ++
      (muldiv_tag_out.enum.map (fun ⟨i, w⟩ => (s!"tag_out_{i}", w))) ++
      [("valid_out", muldiv_valid_out), ("busy", muldiv_busy)]
  }

  -- === FP OPCODE LUT: 7-bit decoder optype → 5-bit FPU opcode ===
  let fpu_opcode := makeIndexedWires "fpu_opcode" 5
  let fpu_opcode_padded := fpu_opcode ++ [zero]  -- zero-pad to 6 bits for RS

  let fpu_lut_gates :=
    if enableF then mkOpTypeLUT "fpulut" decode_optype fpu_opcode fpuMapping_RV32IMF
    else []

  -- === FP RESERVATION STATION (conditional) ===
  let rs_fp_alloc_ptr := makeIndexedWires "rs_fp_alloc_ptr" 2
  let rs_fp_grant := makeIndexedWires "rs_fp_grant" 4
  let rs_fp_issue_full := Wire.mk "rs_fp_issue_full"
  let rs_fp_dispatch_valid := Wire.mk "rs_fp_dispatch_valid"
  let rs_fp_dispatch_opcode := makeIndexedWires "rs_fp_dispatch_opcode" 6
  let rs_fp_dispatch_src1 := makeIndexedWires "rs_fp_dispatch_src1" 32
  let rs_fp_dispatch_src2 := makeIndexedWires "rs_fp_dispatch_src2" 32
  let rs_fp_dispatch_tag := makeIndexedWires "rs_fp_dispatch_tag" 6

  -- Gate FP RS dispatch when FP EU is busy (multi-cycle FP operations)
  let fp_rs_dispatch_en := Wire.mk "fp_rs_dispatch_en"
  let fp_rs_dispatch_gate :=
    if enableF then
      let not_fp_eu_busy := Wire.mk "not_fp_eu_busy"
      [Gate.mkNOT (Wire.mk "fp_busy") not_fp_eu_busy,
       Gate.mkBUF not_fp_eu_busy fp_rs_dispatch_en]
    else [Gate.mkBUF one fp_rs_dispatch_en]

  let rs_fp_inst : CircuitInstance := {
    moduleName := "ReservationStation4"
    instName := "u_rs_fp"
    portMap := [("clock", clock), ("reset", pipeline_reset_rs_fp),
                ("zero", zero), ("one", one), ("issue_en", dispatch_fp_valid),
                ("issue_src1_ready", fp_issue_src1_ready), ("issue_src2_ready", fp_issue_src2_ready),
                ("cdb_valid", cdb_valid_fp_domain), ("dispatch_en", fp_rs_dispatch_en),
                ("issue_full", rs_fp_issue_full), ("dispatch_valid", rs_fp_dispatch_valid)] ++
               -- Use FPU LUT output (5-bit FPU opcode, zero-padded to 6 bits)
               (fpu_opcode_padded.enum.map (fun ⟨i, w⟩ => (s!"issue_opcode_{i}", w))) ++
               (fp_issue_dest_tag.enum.map (fun ⟨i, w⟩ => (s!"issue_dest_tag_{i}", w))) ++
               (fp_issue_src1_tag.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_tag_{i}", w))) ++
               (fp_fwd_src1_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_data_{i}", w))) ++
               (fp_issue_src2_tag.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_tag_{i}", w))) ++
               (fp_fwd_src2_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_data_{i}", w))) ++
               (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag_{i}", w))) ++
               (cdb_data.enum.map (fun ⟨i, w⟩ => (s!"cdb_data_{i}", w))) ++
               (rs_fp_dispatch_opcode.enum.map (fun ⟨i, w⟩ => (s!"dispatch_opcode_{i}", w))) ++
               (rs_fp_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src1_data_{i}", w))) ++
               (rs_fp_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src2_data_{i}", w))) ++
               (rs_fp_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dispatch_dest_tag_{i}", w))) ++
               (rs_fp_alloc_ptr.enum.map (fun ⟨i, w⟩ => (s!"alloc_ptr_{i}", w))) ++
               (rs_fp_grant.enum.map (fun ⟨i, w⟩ => (s!"dispatch_grant_{i}", w)))
  }

  -- === FP SRC3 SIDECAR: 4-entry × 32-bit storage for FMA rs3 data ===
  -- Written at issue time (alloc_ptr selects slot), read at dispatch (grant one-hot mux)
  let fp_src3_dispatch := makeIndexedWires "fp_src3_dispatch" 32

  -- Decode alloc_ptr to one-hot write-enable
  let fp_src3_we := (List.range 4).map (fun slot => Wire.mk s!"fp_src3_we_{slot}")
  let fp_src3_alloc_decode :=
    if enableF then
      let ap0 := rs_fp_alloc_ptr[0]!
      let ap1 := rs_fp_alloc_ptr[1]!
      let not_ap0 := Wire.mk "fp_src3_not_ap0"
      let not_ap1 := Wire.mk "fp_src3_not_ap1"
      [Gate.mkNOT ap0 not_ap0, Gate.mkNOT ap1 not_ap1] ++
      -- slot 0: !ap1 & !ap0 & issue_en
      [Gate.mkAND not_ap1 not_ap0 (Wire.mk "fp_src3_sel0"),
       Gate.mkAND (Wire.mk "fp_src3_sel0") dispatch_fp_valid fp_src3_we[0]!] ++
      -- slot 1: !ap1 & ap0 & issue_en
      [Gate.mkAND not_ap1 ap0 (Wire.mk "fp_src3_sel1"),
       Gate.mkAND (Wire.mk "fp_src3_sel1") dispatch_fp_valid fp_src3_we[1]!] ++
      -- slot 2: ap1 & !ap0 & issue_en
      [Gate.mkAND ap1 not_ap0 (Wire.mk "fp_src3_sel2"),
       Gate.mkAND (Wire.mk "fp_src3_sel2") dispatch_fp_valid fp_src3_we[2]!] ++
      -- slot 3: ap1 & ap0 & issue_en
      [Gate.mkAND ap1 ap0 (Wire.mk "fp_src3_sel3"),
       Gate.mkAND (Wire.mk "fp_src3_sel3") dispatch_fp_valid fp_src3_we[3]!]
    else []

  -- 4 slots × 32 DFFs each, with write-enable MUX
  let fp_src3_slots := (List.range 4).map (fun slot =>
    makeIndexedWires s!"fp_src3_slot{slot}" 32)
  let fp_src3_dff_gates :=
    if enableF then
      (List.range 4).flatMap (fun slot =>
        (List.range 32).flatMap (fun bit =>
          let d_mux := Wire.mk s!"fp_src3_slot{slot}_d_{bit}"
          [Gate.mkMUX fp_src3_slots[slot]![bit]! fp_rs3_data[bit]! fp_src3_we[slot]! d_mux,
           Gate.mkDFF d_mux clock reset fp_src3_slots[slot]![bit]!]))
    else []

  -- Read mux: one-hot grant selects which slot's data to output
  let fp_src3_read_gates :=
    if enableF then
      (List.range 32).flatMap (fun bit =>
        let and0 := Wire.mk s!"fp_src3_rd0_{bit}"
        let and1 := Wire.mk s!"fp_src3_rd1_{bit}"
        let and2 := Wire.mk s!"fp_src3_rd2_{bit}"
        let and3 := Wire.mk s!"fp_src3_rd3_{bit}"
        let or01 := Wire.mk s!"fp_src3_or01_{bit}"
        let or23 := Wire.mk s!"fp_src3_or23_{bit}"
        [Gate.mkAND fp_src3_slots[0]![bit]! rs_fp_grant[0]! and0,
         Gate.mkAND fp_src3_slots[1]![bit]! rs_fp_grant[1]! and1,
         Gate.mkAND fp_src3_slots[2]![bit]! rs_fp_grant[2]! and2,
         Gate.mkAND fp_src3_slots[3]![bit]! rs_fp_grant[3]! and3,
         Gate.mkOR and0 and1 or01,
         Gate.mkOR and2 and3 or23,
         Gate.mkOR or01 or23 fp_src3_dispatch[bit]!])
    else []

  -- === FP EXECUTION UNIT (conditional) ===
  let fp_result := makeIndexedWires "fp_result" 32
  let fp_tag_out := makeIndexedWires "fp_tag_out" 6
  let fp_exceptions := makeIndexedWires "fp_exceptions" 5
  let fp_valid_out := Wire.mk "fp_valid_out"
  let fp_busy := Wire.mk "fp_busy"
  let fp_result_is_int := Wire.mk "fp_result_is_int"

  -- FP opcode LUT: translate 6-bit RS dispatch optype → 5-bit FPU op
  let fp_op := makeIndexedWires "fp_op" 5
  let fp_rm := makeIndexedWires "fp_rm" 3

  -- For now, pass the lower 5 bits of opcode directly as FPU op
  -- (FP instructions start at position 48, so bits [4:0] give offsets 0-25)
  -- The FPExecUnit expects opTypeToFPUOpcode encoding
  let fp_op_gates :=
    if enableF then
      -- Gate EU valid_in with dispatch_en to prevent processing when stalled
      [Gate.mkAND rs_fp_dispatch_valid fp_rs_dispatch_en (Wire.mk "fp_eu_valid_in")] ++
      (List.range 5).map (fun i =>
        Gate.mkBUF rs_fp_dispatch_opcode[i]! fp_op[i]!) ++
      -- rm: use bits from dispatch opcode or default to 0 (RNE)
      -- For now tie rm to zero (round to nearest even)
      (List.range 3).map (fun i =>
        Gate.mkBUF zero fp_rm[i]!)
    else []

  let fp_exec_inst : CircuitInstance := {
    moduleName := "FPExecUnit"
    instName := "u_exec_fp"
    portMap :=
      (rs_fp_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"src1_{i}", w))) ++
      (rs_fp_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"src2_{i}", w))) ++
      -- src3: from sidecar storage (rs3 data captured at issue time)
      (fp_src3_dispatch.enum.map (fun ⟨i, w⟩ => (s!"src3_{i}", w))) ++
      (fp_op.enum.map (fun ⟨i, w⟩ => (s!"op_{i}", w))) ++
      (fp_rm.enum.map (fun ⟨i, w⟩ => (s!"rm_{i}", w))) ++
      (rs_fp_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dest_tag_{i}", w))) ++
      [("valid_in", Wire.mk "fp_eu_valid_in"),
       ("clock", clock), ("reset", reset),
       ("zero", zero), ("one", one)] ++
      (fp_result.enum.map (fun ⟨i, w⟩ => (s!"result_{i}", w))) ++
      (fp_tag_out.enum.map (fun ⟨i, w⟩ => (s!"tag_out_{i}", w))) ++
      (fp_exceptions.enum.map (fun ⟨i, w⟩ => (s!"exceptions_{i}", w))) ++
      [("valid_out", fp_valid_out), ("busy", fp_busy),
       ("result_is_int", fp_result_is_int)]
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

  -- Misprediction = XOR(predicted_taken, actual_taken)
  -- predicted_taken comes from shadow DFFs, actual_taken = branch_taken
  let branch_mispredicted := Wire.mk "branch_mispredicted"
  let branch_mispredicted_gate := [Gate.mkXOR branch_predicted_taken branch_taken branch_mispredicted]

  -- Redirect now comes from ROB commit, not branch RS dispatch.
  -- branch_redirect_valid = rob_commit_en AND rob_head_isBranch AND rob_head_mispredicted
  let rob_redirect_tmp := Wire.mk "rob_redirect_tmp"
  let branch_redirect_gate := [
    Gate.mkAND rob_commit_en rob_head_isBranch rob_redirect_tmp,
    Gate.mkAND rob_redirect_tmp rob_head_mispredicted rob_redirect_valid
  ]

  -- Redirect target comes from shadow registers, not execute-stage target
  let branch_target_wire_gates := (List.range 32).map (fun i =>
    Gate.mkBUF rob_head_redirect_target[i]! branch_redirect_target[i]!)

  -- === LSU ===
  let lsu_agu_address := makeIndexedWires "lsu_agu_address" 32
  let lsu_agu_tag := makeIndexedWires "lsu_agu_tag" 6
  let lsu_sb_full := Wire.mk "lsu_sb_full"
  let lsu_sb_empty := Wire.mk "lsu_sb_empty"
  let lsu_sb_fwd_hit := Wire.mk "lsu_sb_fwd_hit"
  let lsu_sb_fwd_committed_hit := Wire.mk "lsu_sb_fwd_committed_hit"
  let lsu_sb_fwd_data := makeIndexedWires "lsu_sb_fwd_data" 32
  let lsu_sb_fwd_size := makeIndexedWires "lsu_sb_fwd_size" 2
  let lsu_sb_deq_valid := Wire.mk "lsu_sb_deq_valid"
  let lsu_sb_deq_bits := makeIndexedWires "lsu_sb_deq_bits" 66
  let lsu_sb_enq_idx := makeIndexedWires "lsu_sb_enq_idx" 3
  let lsu_sb_committed_tail := makeIndexedWires "lsu_sb_committed_tail" 3

  let lsu_inst : CircuitInstance := {
    moduleName := "LSU"
    instName := "u_lsu"
    portMap := [("clock", clock), ("reset", reset),
                ("zero", zero), ("one", one),
                ("commit_store_en", commit_store_en),
                ("deq_ready", dmem_req_ready),
                ("flush_en", pipeline_flush_comb),
                ("sb_enq_en", sb_enq_en),
                ("sb_full", lsu_sb_full), ("sb_empty", lsu_sb_empty), ("sb_fwd_hit", lsu_sb_fwd_hit),
                ("sb_fwd_committed_hit", lsu_sb_fwd_committed_hit),
                ("sb_deq_valid", lsu_sb_deq_valid)] ++
               (rs_mem_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"dispatch_base_{i}", w))) ++
               (captured_imm.enum.map (fun ⟨i, w⟩ => (s!"dispatch_offset_{i}", w))) ++
               (rs_mem_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dispatch_dest_tag_{i}", w))) ++
               ((makeIndexedWires "store_data_masked" 32).enum.map (fun ⟨i, w⟩ => (s!"store_data_{i}", w))) ++
               (sb_commit_ptr.enum.map (fun ⟨i, w⟩ => (s!"commit_store_idx_{i}", w))) ++
               (mem_address.enum.map (fun ⟨i, w⟩ => (s!"fwd_address_{i}", w))) ++
               ((makeIndexedWires "lsu_sb_enq_size" 2).enum.map (fun ⟨i, w⟩ => (s!"sb_enq_size_{i}", w))) ++
               (lsu_agu_address.enum.map (fun ⟨i, w⟩ => (s!"agu_address_{i}", w))) ++
               (lsu_agu_tag.enum.map (fun ⟨i, w⟩ => (s!"agu_tag_out_{i}", w))) ++
               (lsu_sb_fwd_data.enum.map (fun ⟨i, w⟩ => (s!"sb_fwd_data_{i}", w))) ++
               (lsu_sb_fwd_size.enum.map (fun ⟨i, w⟩ => (s!"sb_fwd_size_{i}", w))) ++
               (lsu_sb_deq_bits.enum.map (fun ⟨i, w⟩ => (s!"sb_deq_bits_{i}", w))) ++
               (lsu_sb_enq_idx.enum.map (fun ⟨i, w⟩ => (s!"sb_enq_idx_{i}", w))) ++
               (lsu_sb_committed_tail.enum.map (fun ⟨i, w⟩ => (s!"sb_committed_tail_{i}", w)))
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
  let rob_head_idx := makeIndexedWires "rob_head_idx" 4

  let rob_inst : CircuitInstance := {
    moduleName := "ROB16"
    instName := "u_rob"
    portMap :=
      [("clock", clock), ("reset", pipeline_reset_rob),
       ("zero", zero), ("one", one),
       ("alloc_en", rename_valid)] ++
      -- Branches get unmasked unique tag for CDB misprediction tracking.
      -- rob_alloc_physRd = branch ? rd_phys : (enableF ? fp_issue_dest_tag : int_dest_tag_masked)
      ((if enableF then rob_alloc_physRd_fp else branch_alloc_physRd).enum.map (fun ⟨i, w⟩ => (s!"alloc_physRd[{i}]", w))) ++
      [("alloc_hasPhysRd", if enableF then rob_alloc_hasPhysRd_fp else branch_alloc_hasPhysRd)] ++
      ((if enableF then rob_old_phys_muxed else old_rd_phys).enum.map (fun ⟨i, w⟩ => (s!"alloc_oldPhysRd[{i}]", w))) ++
      [("alloc_hasOldPhysRd", if enableF then decode_has_any_rd_nox0 else decode_has_rd_nox0)] ++
      (decode_rd.enum.map (fun ⟨i, w⟩ => (s!"alloc_archRd[{i}]", w))) ++
      [("alloc_isBranch", dispatch_is_branch),
       ("cdb_valid", cdb_valid)] ++
      (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag[{i}]", w))) ++
      [("cdb_exception", zero),
       ("cdb_mispredicted", Wire.mk "cdb_mispredicted"),
       ("cdb_is_fp", if enableF then cdb_is_fp_rd else zero)] ++
      ((List.range 16).map (fun i =>
        (s!"is_fp_shadow_{i}", if enableF then Wire.mk s!"rob_is_fp_e{i}" else zero))) ++
      [("commit_en", rob_commit_en),
       ("flush_en", branch_redirect_valid_reg),
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
  -- FP RVVI signals (F extension)
  let rvvi_frd := makeIndexedWires "rvvi_frd" 5
  let rvvi_frd_valid := Wire.mk "rvvi_frd_valid"
  let rvvi_frd_data := makeIndexedWires "rvvi_frd_data" 32

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
  -- rvvi_rd_data = prf rd_data4 (via rename stage 4th read port, already wired)
  let rvvi_gates :=
    [Gate.mkBUF rob_commit_en rvvi_valid,
     Gate.mkAND rob_head_exception rob_commit_en rvvi_trap,
     Gate.mkAND rob_head_hasPhysRd rob_commit_en rvvi_rd_valid] ++
    (List.range 5).map (fun i =>
      Gate.mkBUF rob_head_archRd[i]! rvvi_rd[i]!)

  -- FP RVVI gates: rvvi_frd_valid = rob_head_is_fp AND rob_commit_en
  -- rvvi_frd = rob_head_archRd (same arch rd field, FP regs share encoding)
  -- rvvi_frd_data = FP PRF rd_data4 (via fp_rename 4th read port)
  let rvvi_fp_gates :=
    if enableF then
      [Gate.mkAND (Wire.mk "rob_head_is_fp") rob_commit_en rvvi_frd_valid] ++
      (List.range 5).map (fun i => Gate.mkBUF rob_head_archRd[i]! rvvi_frd[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF fp_rvvi_rd_data[i]! rvvi_frd_data[i]!)
    else
      [Gate.mkBUF zero rvvi_frd_valid] ++
      (List.range 5).map (fun i => Gate.mkBUF zero rvvi_frd[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF zero rvvi_frd_data[i]!)

  -- === FFLAGS ACCUMULATOR ===
  -- Accumulate FP exception flags: fflags_new[i] = fflags_reg[i] | (fp_valid_out & exceptions[i])
  let fflags_acc := makeIndexedWires "fflags_acc" 5
  let fflags_reg := makeIndexedWires "fflags_reg" 5
  let fflags_new := makeIndexedWires "fflags_new" 5
  let fflags_masked := makeIndexedWires "fflags_masked" 5

  let fflags_gates :=
    if enableF then
      (List.range 5).map (fun i =>
        Gate.mkAND fp_valid_out fp_exceptions[i]! fflags_masked[i]!) ++
      (List.range 5).map (fun i =>
        Gate.mkOR fflags_reg[i]! fflags_masked[i]! fflags_new[i]!) ++
      (List.range 5).map (fun i =>
        Gate.mkBUF fflags_reg[i]! fflags_acc[i]!)
    else
      (List.range 5).map (fun i => Gate.mkBUF zero fflags_acc[i]!)

  let fflags_dff_instances :=
    if enableF then
      (List.range 5).map (fun i =>
        { moduleName := "DFlipFlop"
          instName := s!"u_fflags_dff_{i}"
          portMap := [("d", fflags_new[i]!), ("q", fflags_reg[i]!),
                      ("clock", clock), ("reset", reset)] : CircuitInstance })
    else []

  -- === CDB FIFO-BASED ARBITRATION ===
  -- Each execution unit output enters a Queue1_39 FIFO (6 tag + 32 data + 1 is_fp_rd).
  -- The CDB arbiter is a priority drain over FIFO deq_valid signals.
  -- Backpressure (enq_ready) stalls the RS when the FIFO is occupied.

  -- Level 0: Merge Branch into Integer (mutually exclusive — same dispatch slot)
  let int_branch_valid := Wire.mk "int_branch_valid"
  let int_branch_tag := makeIndexedWires "int_branch_tag" 6
  let int_branch_data := makeIndexedWires "int_branch_data" 32

  let branch_dispatch_gated := Wire.mk "branch_dispatch_gated"
  let branch_dispatch_gated_pre := Wire.mk "branch_dispatch_gated_pre"
  let arb_level0_gates :=
    [Gate.mkAND rs_branch_dispatch_valid not_cross_size_stall branch_dispatch_gated_pre,
     Gate.mkAND branch_dispatch_gated_pre not_int_dispatching branch_dispatch_gated,
     Gate.mkOR rs_int_dispatch_valid branch_dispatch_gated int_branch_valid] ++
    (List.range 6).map (fun i =>
      Gate.mkMUX branch_tag_out[i]! int_tag_out[i]! rs_int_dispatch_valid int_branch_tag[i]!) ++
    (List.range 32).map (fun i =>
      Gate.mkMUX branch_result_final[i]! int_result_final[i]! rs_int_dispatch_valid int_branch_data[i]!)

  -- FP is_fp_rd computation: NOT fp_result_is_int (FMV.X.W etc. target INT PRF)
  let fp_enq_is_fp := Wire.mk "fp_enq_is_fp"
  let fp_enq_is_fp_gate :=
    if enableF then [Gate.mkNOT fp_result_is_int fp_enq_is_fp]
    else [Gate.mkBUF zero fp_enq_is_fp]

  -- Misprediction redirect target mux:
  -- If predicted taken → redirect is PC+4 (fall-through, since prediction was wrong)
  -- If predicted not-taken → redirect is branch target (taken path)
  let mispredict_redirect_target := makeIndexedWires "mispredict_redirect_target" 32
  let mispredict_redirect_gates := (List.range 32).map (fun i =>
    Gate.mkMUX final_branch_target[i]! br_pc_plus_4[i]! branch_predicted_taken mispredict_redirect_target[i]!)

  -- FIFO enqueue data buses
  -- IB FIFO: 72 bits: tag[5:0] ++ data[37:6] ++ is_fp_rd[38] ++ redirect_target[70:39] ++ mispredicted[71]
  -- Assembled via BUF gates so Chisel codegen sees them as coherent signal groups.
  let ib_fifo_enq_data := makeIndexedWires "ib_fifo_enq_data" 72
  let muldiv_fifo_enq_data := makeIndexedWires "muldiv_fifo_enq_data" 39
  let fp_fifo_enq_data := makeIndexedWires "fp_fifo_enq_data" 39
  let lsu_fifo_enq_data := makeIndexedWires "lsu_fifo_enq_data" 39

  let ib_fifo_enq_assemble :=
    (List.range 6).map (fun i => Gate.mkBUF int_branch_tag[i]! ib_fifo_enq_data[i]!) ++
    (List.range 32).map (fun i => Gate.mkBUF int_branch_data[i]! ib_fifo_enq_data[6+i]!) ++
    [Gate.mkBUF zero ib_fifo_enq_data[38]!] ++  -- is_fp_rd = 0
    -- bits [70:39]: redirect_target (gated by branch dispatch; zero for integer)
    (List.range 32).map (fun i =>
      Gate.mkAND mispredict_redirect_target[i]! branch_dispatch_gated ib_fifo_enq_data[39+i]!) ++
    -- bit [71]: mispredicted flag (gated by branch dispatch; zero for integer)
    [Gate.mkAND branch_mispredicted branch_dispatch_gated ib_fifo_enq_data[71]!]

  let muldiv_fifo_enq_assemble :=
    if enableM then
      (List.range 6).map (fun i => Gate.mkBUF muldiv_tag_out[i]! muldiv_fifo_enq_data[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF muldiv_result[i]! muldiv_fifo_enq_data[6+i]!) ++
      [Gate.mkBUF zero muldiv_fifo_enq_data[38]!]  -- is_fp_rd = 0
    else
      (List.range 39).map (fun i => Gate.mkBUF zero muldiv_fifo_enq_data[i]!)

  let fp_fifo_enq_assemble :=
    if enableF then
      (List.range 6).map (fun i => Gate.mkBUF fp_tag_out[i]! fp_fifo_enq_data[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF fp_result[i]! fp_fifo_enq_data[6+i]!) ++
      [Gate.mkBUF fp_enq_is_fp fp_fifo_enq_data[38]!]  -- is_fp_rd = NOT is_int
    else
      (List.range 39).map (fun i => Gate.mkBUF zero fp_fifo_enq_data[i]!)

  -- FIFO output wires (ib_fifo_enq_ready declared earlier near RS instances)
  let ib_fifo_deq_valid := Wire.mk "ib_fifo_deq_valid"
  let ib_fifo_deq := makeIndexedWires "ib_fifo_deq" 72
  let ib_fifo_drain := Wire.mk "ib_fifo_drain"

  let muldiv_fifo_enq_ready := Wire.mk "muldiv_fifo_enq_ready"
  let muldiv_fifo_deq_valid := Wire.mk "muldiv_fifo_deq_valid"
  let muldiv_fifo_deq := makeIndexedWires "muldiv_fifo_deq" 39
  let muldiv_fifo_drain := Wire.mk "muldiv_fifo_drain"

  let fp_fifo_enq_ready := Wire.mk "fp_fifo_enq_ready"
  let fp_fifo_deq_valid := Wire.mk "fp_fifo_deq_valid"
  let fp_fifo_deq := makeIndexedWires "fp_fifo_deq" 39
  let fp_fifo_drain := Wire.mk "fp_fifo_drain"

  let lsu_fifo_enq_ready := Wire.mk "lsu_fifo_enq_ready"
  let lsu_fifo_deq_valid := Wire.mk "lsu_fifo_deq_valid"
  let lsu_fifo_deq := makeIndexedWires "lsu_fifo_deq" 39
  let lsu_fifo_drain := Wire.mk "lsu_fifo_drain"

  -- INT/Branch FIFO instance (72 bits: tag+data+is_fp+redirect_target+mispredicted)
  let ib_fifo_inst : CircuitInstance := {
    moduleName := "Queue1Flow_72", instName := "u_cdb_fifo_ib",
    portMap := [("clock", clock), ("reset", pipeline_reset_busy),
                ("enq_valid", int_branch_valid),
                ("deq_ready", ib_fifo_drain),
                ("enq_ready", ib_fifo_enq_ready),
                ("deq_valid", ib_fifo_deq_valid)] ++
      (List.range 72).map (fun i => (s!"enq_data_{i}", ib_fifo_enq_data[i]!)) ++
      (List.range 72).map (fun i => (s!"deq_data_{i}", ib_fifo_deq[i]!))
  }

  -- MulDiv FIFO instance (conditional on M-extension)
  let muldiv_fifo_inst : CircuitInstance := {
    moduleName := "Queue1Flow_39", instName := "u_cdb_fifo_muldiv",
    portMap := [("clock", clock), ("reset", pipeline_reset_rs_muldiv),
                ("enq_valid", muldiv_valid_out),
                ("deq_ready", muldiv_fifo_drain),
                ("enq_ready", muldiv_fifo_enq_ready),
                ("deq_valid", muldiv_fifo_deq_valid)] ++
      (List.range 39).map (fun i => (s!"enq_data_{i}", muldiv_fifo_enq_data[i]!)) ++
      (List.range 39).map (fun i => (s!"deq_data_{i}", muldiv_fifo_deq[i]!))
  }

  -- FP FIFO instance (conditional on F-extension)
  let fp_fifo_inst : CircuitInstance := {
    moduleName := "Queue1Flow_39", instName := "u_cdb_fifo_fp",
    portMap := [("clock", clock), ("reset", pipeline_reset_rs_fp),
                ("enq_valid", fp_valid_out),
                ("deq_ready", fp_fifo_drain),
                ("enq_ready", fp_fifo_enq_ready),
                ("deq_valid", fp_fifo_deq_valid)] ++
      (List.range 39).map (fun i => (s!"enq_data_{i}", fp_fifo_enq_data[i]!)) ++
      (List.range 39).map (fun i => (s!"deq_data_{i}", fp_fifo_deq[i]!))
  }

  -- Dummy gates to tie off unused FIFO wires when extensions disabled
  let muldiv_fifo_dummy_gates :=
    if enableM then []
    else [Gate.mkBUF one muldiv_fifo_enq_ready,
          Gate.mkBUF zero muldiv_fifo_deq_valid] ++
         (List.range 39).map (fun i => Gate.mkBUF zero muldiv_fifo_deq[i]!)

  let fp_fifo_dummy_gates :=
    if enableF then []
    else [Gate.mkBUF one fp_fifo_enq_ready,
          Gate.mkBUF zero fp_fifo_deq_valid] ++
         (List.range 39).map (fun i => Gate.mkBUF zero fp_fifo_deq[i]!)

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
  -- FLW detection (conditional on F extension)
  let is_flw := Wire.mk "is_flw"
  let flw_match_gates :=
    if enableF then mkOpcodeMatch6 "flw_match" enc.flw rs_mem_dispatch_opcode is_flw
    else [Gate.mkBUF zero is_flw]

  let is_load_gates := [
    Gate.mkOR is_lw is_lh is_load_tmp1,
    Gate.mkOR is_load_tmp1 is_lhu is_load_tmp2,
    Gate.mkOR is_load_tmp2 is_lb is_load_tmp3,
    Gate.mkOR is_load_tmp3 is_lbu (Wire.mk "is_load_int"),
    Gate.mkOR (Wire.mk "is_load_int") is_flw is_load
  ]

  -- === STORE TYPE DECODE ===
  let is_sw := Wire.mk "is_sw"
  let is_sh := Wire.mk "is_sh"
  let is_sb := Wire.mk "is_sb"
  let is_fsw := Wire.mk "is_fsw"
  let sw_match_gates := mkOpcodeMatch6 "sw_match" enc.sw rs_mem_dispatch_opcode is_sw
  let sh_match_gates := mkOpcodeMatch6 "sh_match" enc.sh rs_mem_dispatch_opcode is_sh
  let sb_match_gates := mkOpcodeMatch6 "sb_match" enc.sb rs_mem_dispatch_opcode is_sb
  let fsw_match_gates :=
    if enableF then mkOpcodeMatch6 "fsw_match" enc.fsw rs_mem_dispatch_opcode is_fsw
    else [Gate.mkBUF zero is_fsw]

  -- Derive mem_size[1:0]: 00=byte, 01=half, 10=word
  -- For loads: is_lb|is_lbu → 00, is_lh|is_lhu → 01, is_lw|is_flw → 10
  -- For stores: is_sb → 00, is_sh → 01, is_sw|is_fsw → 10
  -- mem_size_0 = is_lh | is_lhu | is_sh
  -- mem_size_1 = is_lw | is_flw | is_sw | is_fsw
  let mem_size := makeIndexedWires "mem_size" 2
  let mem_size_0_tmp1 := Wire.mk "mem_size_0_tmp1"
  let mem_size_0_tmp2 := Wire.mk "mem_size_0_tmp2"
  let mem_size_1_tmp1 := Wire.mk "mem_size_1_tmp1"
  let mem_size_1_tmp2 := Wire.mk "mem_size_1_tmp2"
  let mem_size_gates := [
    Gate.mkOR is_lh is_lhu mem_size_0_tmp1,
    Gate.mkOR mem_size_0_tmp1 is_sh mem_size_0_tmp2,
    Gate.mkBUF mem_size_0_tmp2 mem_size[0]!,
    Gate.mkOR is_lw is_sw mem_size_1_tmp1,
    Gate.mkOR mem_size_1_tmp1 is_flw mem_size_1_tmp2,
    Gate.mkOR mem_size_1_tmp2 is_fsw mem_size[1]!
  ]

  -- sign_extend: 1 for LB/LH, 0 for LBU/LHU/LW/FLW and all stores
  let sign_extend := Wire.mk "sign_extend"
  let sign_extend_gates := [
    Gate.mkOR is_lb is_lh sign_extend
  ]

  -- Drive lsu_sb_enq_size[1:0] from store type
  -- sb_enq_size = mem_size (00=byte, 01=half, 10=word)
  let lsu_sb_enq_size := makeIndexedWires "lsu_sb_enq_size" 2
  let sb_enq_size_gates :=
    (List.range 2).map (fun i => Gate.mkBUF mem_size[i]! lsu_sb_enq_size[i]!)

  -- Mask store data: SB keeps [7:0], SH keeps [15:0], SW keeps all 32
  -- For SB: zero bits [31:8]; for SH: zero bits [31:16]
  -- is_sw means keep all bits. is_sh means keep [15:0]. is_sb means keep [7:0].
  -- mask_bit[i] = is_sw | (is_sh & i<16) | (is_sb & i<8)
  -- Equivalently: keep bit i if mem_size_1 | (mem_size_0 & i<16) | (!mem_size_0 & !mem_size_1 & i<8)
  -- Simpler: keep_hi16 = mem_size[1] (word), keep_lo16_hi8 = mem_size[1] | mem_size[0] (word or half)
  let store_data_masked := makeIndexedWires "store_data_masked" 32
  let keep_hi16 := Wire.mk "keep_hi16"
  let keep_lo16_hi8 := Wire.mk "keep_lo16_hi8"
  let store_mask_gates :=
    [Gate.mkBUF mem_size[1]! keep_hi16,
     Gate.mkOR mem_size[1]! mem_size[0]! keep_lo16_hi8] ++
    -- Bits [7:0]: always kept (AND with one = passthrough)
    (List.range 8).map (fun i =>
      Gate.mkBUF rs_mem_dispatch_src2[i]! store_data_masked[i]!) ++
    -- Bits [15:8]: kept for half or word
    (List.range 8).map (fun i =>
      Gate.mkAND rs_mem_dispatch_src2[8+i]! keep_lo16_hi8 store_data_masked[8+i]!) ++
    -- Bits [31:16]: kept for word only
    (List.range 16).map (fun i =>
      Gate.mkAND rs_mem_dispatch_src2[16+i]! keep_hi16 store_data_masked[16+i]!)

  -- SB fwd size check: only forward when store covers the full load
  -- size_ok = store[1] | (!load[1] & (store[0] | !load[0]))
  let fwd_size_ok := Wire.mk "fwd_size_ok"
  let not_load_size1 := Wire.mk "not_load_size1"
  let not_load_size0 := Wire.mk "not_load_size0"
  let fwd_sz_tmp1 := Wire.mk "fwd_sz_tmp1"
  let fwd_sz_tmp2 := Wire.mk "fwd_sz_tmp2"
  let fwd_size_check_gates := [
    Gate.mkNOT mem_size[1]! not_load_size1,
    Gate.mkNOT mem_size[0]! not_load_size0,
    Gate.mkOR lsu_sb_fwd_size[0]! not_load_size0 fwd_sz_tmp1,
    Gate.mkAND not_load_size1 fwd_sz_tmp1 fwd_sz_tmp2,
    Gate.mkOR lsu_sb_fwd_size[1]! fwd_sz_tmp2 fwd_size_ok
  ]

  let load_fwd_valid := Wire.mk "load_fwd_valid"
  let load_fwd_tmp := Wire.mk "load_fwd_tmp"
  let load_fwd_tmp2 := Wire.mk "load_fwd_tmp2"
  -- Cross-size stall: load has SB address hit but store size < load size.
  -- Stall the RS dispatch (don't clear entry) so the load retries next cycle.
  -- Eventually the store drains from SB and the load goes to DMEM with committed data.
  let not_fwd_size_ok := Wire.mk "not_fwd_size_ok"
  let cross_size_any := Wire.mk "cross_size_any"
  let cross_size_uncommitted := Wire.mk "cross_size_uncommitted"
  let not_fwd_committed_hit := Wire.mk "not_fwd_committed_hit"
  -- With FIFO redesign, valid bits are properly cleared on dequeue.
  -- No stale-entry gating needed — fwd_hit from SB is trustworthy.
  let load_fwd_gates := [
    Gate.mkAND lsu_sb_fwd_hit rs_mem_dispatch_valid load_fwd_tmp,
    Gate.mkAND load_fwd_tmp is_load load_fwd_tmp2,
    Gate.mkAND load_fwd_tmp2 fwd_size_ok load_fwd_valid,
    -- Cross-size detection: SB hit but size insufficient
    Gate.mkNOT fwd_size_ok not_fwd_size_ok,
    Gate.mkAND load_fwd_tmp2 not_fwd_size_ok cross_size_any,
    Gate.mkBUF cross_size_any cross_size_stall,
    Gate.mkNOT cross_size_stall not_cross_size_stall,
    -- Branch RS dispatch is suppressed when INT RS also dispatches (shared IB FIFO slot)
    -- Also gated by IB FIFO enq_ready to prevent result loss when FIFO is full
    Gate.mkNOT rs_int_dispatch_valid not_int_dispatching,
    Gate.mkAND not_cross_size_stall not_int_dispatching (Wire.mk "branch_dispatch_en_tmp"),
    Gate.mkAND (Wire.mk "branch_dispatch_en_tmp") ib_fifo_enq_ready branch_dispatch_en,
    -- cross_size_uncommitted: SB hit, size mismatch, but not committed
    Gate.mkNOT lsu_sb_fwd_committed_hit not_fwd_committed_hit,
    Gate.mkAND cross_size_any not_fwd_committed_hit cross_size_uncommitted
  ]

  -- === LOAD BYTE/HALF FORMATTING (SB forwarding path) ===
  -- SB fwd data is already low-aligned (store data was masked before SB entry):
  --   SB stores: data[7:0]; SH stores: data[15:0]; SW stores: data[31:0]
  -- NO barrel shift needed — just sign/zero extend directly.
  -- (Barrel shift is only needed on the DMEM path where data is word-positioned.)
  let lsu_sb_fwd_formatted := makeIndexedWires "lsu_sb_fwd_fmt" 32

  -- Sign/zero extension for SB fwd path
  -- For byte (mem_size=00): sign bit = data[7], extend bits [31:8]
  -- For half (mem_size=01): sign bit = data[15], extend bits [31:16]
  -- For word (mem_size=10): no extension needed
  let sb_fwd_sign_bit := Wire.mk "sb_fwd_sign_bit"
  let sb_fwd_sign_bit_raw := Wire.mk "sb_fwd_sign_bit_raw"
  let sb_fwd_sign_gates := [
    Gate.mkMUX lsu_sb_fwd_data[7]! lsu_sb_fwd_data[15]! mem_size[0]! sb_fwd_sign_bit_raw,
    Gate.mkAND sb_fwd_sign_bit_raw sign_extend sb_fwd_sign_bit
  ]
  let sb_fwd_ext_lo := Wire.mk "sb_fwd_ext_lo"  -- keep bits [15:8]?
  let sb_fwd_ext_hi := Wire.mk "sb_fwd_ext_hi"  -- keep bits [31:16]?
  let sb_fwd_format_gates :=
    [Gate.mkOR mem_size[0]! mem_size[1]! sb_fwd_ext_lo,
     Gate.mkBUF mem_size[1]! sb_fwd_ext_hi] ++
    -- Bits [7:0]: passthrough
    (List.range 8).map (fun i =>
      Gate.mkBUF lsu_sb_fwd_data[i]! lsu_sb_fwd_formatted[i]!) ++
    -- Bits [15:8]: MUX(sign_bit, data[i], ext_lo)
    (List.range 8).map (fun i =>
      Gate.mkMUX sb_fwd_sign_bit lsu_sb_fwd_data[8+i]! sb_fwd_ext_lo lsu_sb_fwd_formatted[8+i]!) ++
    -- Bits [31:16]: MUX(sign_bit, data[i], ext_hi)
    (List.range 16).map (fun i =>
      Gate.mkMUX sb_fwd_sign_bit lsu_sb_fwd_data[16+i]! sb_fwd_ext_hi lsu_sb_fwd_formatted[16+i]!)

  let lsu_sb_fwd_format_all := sb_fwd_sign_gates ++ sb_fwd_format_gates

  let lsu_valid := Wire.mk "lsu_valid"
  let lsu_tag := makeIndexedWires "lsu_tag" 6
  let lsu_data := makeIndexedWires "lsu_data" 32

  -- When sbFwdPipelineStages > 0, register the SB forwarding result through DFFs.
  -- This breaks the timing-critical path: mem_address → SB compare → CDB arbiter.
  -- The registered result enters the CDB arbiter one cycle later.
  -- When sbFwdPipelineStages = 0, use combinational BUF (current behavior).
  let lsu_valid_gate :=
    if sbFwdPipelined then
      [Gate.mkDFF load_fwd_valid clock pipeline_reset_misc lsu_valid]
    else
      [Gate.mkBUF load_fwd_valid lsu_valid]

  let lsu_tag_data_mux_gates :=
    if sbFwdPipelined then
      (List.range 6).map (fun i =>
        Gate.mkDFF rs_mem_dispatch_tag[i]! clock pipeline_reset_misc lsu_tag[i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkDFF lsu_sb_fwd_formatted[i]! clock pipeline_reset_misc lsu_data[i]!)
    else
      (List.range 6).map (fun i =>
        Gate.mkBUF rs_mem_dispatch_tag[i]! lsu_tag[i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkBUF lsu_sb_fwd_formatted[i]! lsu_data[i]!)

  let lsu_pipeline_insts : List CircuitInstance := []

  -- Track is_fp_load through LSU path for FIFO is_fp_rd bit
  let lsu_is_fp := Wire.mk "lsu_is_fp"
  let lsu_is_fp_gates :=
    if enableF then
      if sbFwdPipelined then
        [Gate.mkDFF is_flw clock pipeline_reset_misc lsu_is_fp]
      else
        [Gate.mkBUF is_flw lsu_is_fp]
    else [Gate.mkBUF zero lsu_is_fp]

  -- Assemble LSU FIFO enqueue data bus
  let lsu_fifo_enq_assemble :=
    (List.range 6).map (fun i => Gate.mkBUF lsu_tag[i]! lsu_fifo_enq_data[i]!) ++
    (List.range 32).map (fun i => Gate.mkBUF lsu_data[i]! lsu_fifo_enq_data[6+i]!) ++
    [Gate.mkBUF lsu_is_fp lsu_fifo_enq_data[38]!]

  -- LSU FIFO instance: SB-forwarded load results enter here
  let lsu_fifo_inst : CircuitInstance := {
    moduleName := "Queue1Flow_39", instName := "u_cdb_fifo_lsu",
    portMap := [("clock", clock), ("reset", pipeline_reset_misc),
                ("enq_valid", lsu_valid),
                ("deq_ready", lsu_fifo_drain),
                ("enq_ready", lsu_fifo_enq_ready),
                ("deq_valid", lsu_fifo_deq_valid)] ++
      (List.range 39).map (fun i => (s!"enq_data_{i}", lsu_fifo_enq_data[i]!)) ++
      (List.range 39).map (fun i => (s!"deq_data_{i}", lsu_fifo_deq[i]!))
  }

  -- === DMEM RESPONSE PATH ===
  let load_no_fwd := Wire.mk "load_no_fwd"
  let load_no_fwd_tmp := Wire.mk "load_no_fwd_tmp"
  let not_sb_fwd_hit := Wire.mk "not_sb_fwd_hit"
  let dmem_load_tag_reg := makeIndexedWires "dmem_load_tag_reg" 6
  let dmem_load_tag_next := makeIndexedWires "dmem_load_tag_next" 6

  -- DMEM load pending: 1-cycle busy flag to prevent back-to-back DMEM loads.
  -- The DMEM path has a single tag register, so a second load_no_fwd before
  -- dmem_resp_valid would overwrite the first load's tag.
  let dmem_load_pending := Wire.mk "dmem_load_pending"
  let dmem_load_pending_next := Wire.mk "dmem_load_pending_next"
  let not_dmem_load_pending := Wire.mk "not_dmem_load_pending"

  let load_no_fwd_base := Wire.mk "load_no_fwd_base"
  let load_no_fwd_gates := [
    Gate.mkNOT lsu_sb_fwd_hit not_sb_fwd_hit,
    Gate.mkAND rs_mem_dispatch_valid is_load load_no_fwd_tmp,
    -- Normal DMEM path: no SB hit
    Gate.mkAND load_no_fwd_tmp not_sb_fwd_hit load_no_fwd_base,
    -- Gate by not_dmem_load_pending: only one DMEM load in flight at a time
    -- (DMEM path has single tag register, back-to-back would overwrite first tag)
    Gate.mkAND load_no_fwd_base not_dmem_load_pending load_no_fwd
  ]

  let dmem_pending_gates := [
    -- Set on load_no_fwd, clear on dmem_resp_valid (or reset)
    -- pending_next = load_no_fwd OR (pending AND NOT dmem_resp_valid)
    Gate.mkNOT dmem_resp_valid (Wire.mk "not_dmem_resp_valid"),
    Gate.mkAND dmem_load_pending (Wire.mk "not_dmem_resp_valid") (Wire.mk "dmem_pending_hold"),
    Gate.mkOR load_no_fwd (Wire.mk "dmem_pending_hold") dmem_load_pending_next,
    Gate.mkNOT dmem_load_pending not_dmem_load_pending
  ]
  let dmem_pending_inst : CircuitInstance :=
    { moduleName := "DFlipFlop", instName := "u_dmem_load_pending",
      portMap := [("d", dmem_load_pending_next), ("q", dmem_load_pending),
                  ("clock", clock), ("reset", reset)] }

  -- mem_dispatch_en: gate by both cross_size_stall and dmem_load_pending
  let mem_dispatch_en_tmp := Wire.mk "mem_dispatch_en_tmp"
  let mem_dispatch_en_gates := [
    Gate.mkNOT cross_size_stall mem_dispatch_en_tmp,
    Gate.mkAND mem_dispatch_en_tmp not_dmem_load_pending mem_dispatch_en
  ]

  -- DMEM metadata DFFs use CircuitInstance DFlipFlop with external `reset`
  -- (NOT pipeline_reset_misc) because the DMEM response arrives 1 cycle after
  -- the request, and the pipeline flush happens in between. The metadata must
  -- survive the flush. Flat Gate.mkDFF gets grouped into pipeline_reset_busy
  -- by the codegen, so we must use instances.
  let dmem_tag_capture_gates := (List.range 6).map (fun i =>
    Gate.mkMUX dmem_load_tag_reg[i]! rs_mem_dispatch_tag[i]! load_no_fwd dmem_load_tag_next[i]!)
  let dmem_tag_capture_insts := (List.range 6).map (fun i =>
    ({ moduleName := "DFlipFlop", instName := s!"u_dmem_tag_{i}",
       portMap := [("d", dmem_load_tag_next[i]!), ("q", dmem_load_tag_reg[i]!),
                   ("clock", clock), ("reset", reset)] } : CircuitInstance))

  -- Track is_fp_load through dmem response path (1-cycle load latency)
  let dmem_is_fp_reg := Wire.mk "dmem_is_fp_reg"
  let dmem_is_fp_next := Wire.mk "dmem_is_fp_next"
  let dmem_is_fp_gates :=
    if enableF then
      [Gate.mkMUX dmem_is_fp_reg is_flw load_no_fwd dmem_is_fp_next]
    else []
  let dmem_is_fp_insts :=
    if enableF then
      [({ moduleName := "DFlipFlop", instName := "u_dmem_is_fp",
          portMap := [("d", dmem_is_fp_next), ("q", dmem_is_fp_reg),
                      ("clock", clock), ("reset", reset)] } : CircuitInstance)]
    else []

  -- === DMEM LOAD METADATA CAPTURE (for sub-word load formatting) ===
  -- Capture addr[1:0], mem_size[1:0], sign_extend alongside dmem_load_tag
  let dmem_addr_lo_reg := makeIndexedWires "dmem_addr_lo_reg" 2
  let dmem_addr_lo_next := makeIndexedWires "dmem_addr_lo_next" 2
  let dmem_mem_size_reg := makeIndexedWires "dmem_mem_size_reg" 2
  let dmem_mem_size_next := makeIndexedWires "dmem_mem_size_next" 2
  let dmem_sign_ext_reg := Wire.mk "dmem_sign_ext_reg"
  let dmem_sign_ext_next := Wire.mk "dmem_sign_ext_next"

  let dmem_addr_lo_capture_gates := (List.range 2).map (fun i =>
      Gate.mkMUX dmem_addr_lo_reg[i]! mem_address[i]! load_no_fwd dmem_addr_lo_next[i]!)
  let dmem_addr_lo_capture_insts := (List.range 2).map (fun i =>
    ({ moduleName := "DFlipFlop", instName := s!"u_dmem_addr_lo_{i}",
       portMap := [("d", dmem_addr_lo_next[i]!), ("q", dmem_addr_lo_reg[i]!),
                   ("clock", clock), ("reset", reset)] } : CircuitInstance))
  let dmem_mem_size_capture_gates := (List.range 2).map (fun i =>
      Gate.mkMUX dmem_mem_size_reg[i]! mem_size[i]! load_no_fwd dmem_mem_size_next[i]!)
  let dmem_mem_size_capture_insts := (List.range 2).map (fun i =>
    ({ moduleName := "DFlipFlop", instName := s!"u_dmem_mem_size_{i}",
       portMap := [("d", dmem_mem_size_next[i]!), ("q", dmem_mem_size_reg[i]!),
                   ("clock", clock), ("reset", reset)] } : CircuitInstance))
  let dmem_meta_capture_gates :=
    dmem_addr_lo_capture_gates ++ dmem_mem_size_capture_gates ++
    [Gate.mkMUX dmem_sign_ext_reg sign_extend load_no_fwd dmem_sign_ext_next]
  let dmem_sign_ext_inst : CircuitInstance :=
    { moduleName := "DFlipFlop", instName := "u_dmem_sign_ext",
      portMap := [("d", dmem_sign_ext_next), ("q", dmem_sign_ext_reg),
                  ("clock", clock), ("reset", reset)] }
  let dmem_meta_capture_insts :=
    dmem_addr_lo_capture_insts ++ dmem_mem_size_capture_insts ++ [dmem_sign_ext_inst]

  -- === DMEM RESPONSE LOAD FORMATTING ===
  -- Same barrel-shift + sign/zero-extend as SB fwd path, using registered metadata
  let dmem_resp_formatted := makeIndexedWires "dmem_resp_fmt" 32
  let dmem_resp_shifted := makeIndexedWires "dmem_resp_shifted" 32
  let dmem_sh8 := makeIndexedWires "dmem_sh8" 32
  let dmem_sh8_gates :=
    (List.range 24).map (fun i =>
      Gate.mkMUX dmem_resp_data[i]! dmem_resp_data[i+8]! dmem_addr_lo_reg[0]! dmem_sh8[i]!) ++
    (List.range 8).map (fun i =>
      Gate.mkMUX dmem_resp_data[24+i]! zero dmem_addr_lo_reg[0]! dmem_sh8[24+i]!)
  let dmem_sh16_gates :=
    (List.range 16).map (fun i =>
      Gate.mkMUX dmem_sh8[i]! dmem_sh8[i+16]! dmem_addr_lo_reg[1]! dmem_resp_shifted[i]!) ++
    (List.range 16).map (fun i =>
      Gate.mkMUX dmem_sh8[16+i]! zero dmem_addr_lo_reg[1]! dmem_resp_shifted[16+i]!)

  let dmem_sign_bit := Wire.mk "dmem_sign_bit"
  let dmem_sign_bit_raw := Wire.mk "dmem_sign_bit_raw"
  let dmem_sign_gates := [
    Gate.mkMUX dmem_resp_shifted[7]! dmem_resp_shifted[15]! dmem_mem_size_reg[0]! dmem_sign_bit_raw,
    Gate.mkAND dmem_sign_bit_raw dmem_sign_ext_reg dmem_sign_bit
  ]
  let dmem_ext_lo := Wire.mk "dmem_ext_lo"
  let dmem_ext_hi := Wire.mk "dmem_ext_hi"
  let dmem_format_gates :=
    [Gate.mkOR dmem_mem_size_reg[0]! dmem_mem_size_reg[1]! dmem_ext_lo,
     Gate.mkBUF dmem_mem_size_reg[1]! dmem_ext_hi] ++
    (List.range 8).map (fun i =>
      Gate.mkBUF dmem_resp_shifted[i]! dmem_resp_formatted[i]!) ++
    (List.range 8).map (fun i =>
      Gate.mkMUX dmem_sign_bit dmem_resp_shifted[8+i]! dmem_ext_lo dmem_resp_formatted[8+i]!) ++
    (List.range 16).map (fun i =>
      Gate.mkMUX dmem_sign_bit dmem_resp_shifted[16+i]! dmem_ext_hi dmem_resp_formatted[16+i]!)

  let dmem_resp_format_all := dmem_sh8_gates ++ dmem_sh16_gates ++
    dmem_sign_gates ++ dmem_format_gates

  -- === CDB PRIORITY DRAIN MUX ===
  -- Priority: DMEM (no FIFO) > LSU FIFO > MulDiv FIFO > FP FIFO > INT/Branch FIFO
  -- DMEM has highest priority because it has no buffering.

  let dmem_wins := Wire.mk "dmem_wins"
  let not_dmem := Wire.mk "not_dmem_resp_drain"

  let lsu_wins := Wire.mk "lsu_wins"
  let not_lsu := Wire.mk "not_lsu_fifo_drain"

  let muldiv_wins := Wire.mk "muldiv_wins"
  let not_muldiv := Wire.mk "not_muldiv_fifo_drain"
  let muldiv_wins_tmp := Wire.mk "muldiv_wins_tmp"

  let fp_wins := Wire.mk "fp_wins"
  let not_fp := Wire.mk "not_fp_fifo_drain"
  let fp_wins_tmp := Wire.mk "fp_wins_tmp"
  let fp_wins_tmp2 := Wire.mk "fp_wins_tmp2"

  let ib_wins := Wire.mk "ib_wins"
  let ib_wins_tmp := Wire.mk "ib_wins_tmp"
  let ib_wins_tmp2 := Wire.mk "ib_wins_tmp2"
  let ib_wins_tmp3 := Wire.mk "ib_wins_tmp3"

  let drain_priority_gates := [
    -- DMEM wins if valid (highest priority)
    Gate.mkBUF dmem_resp_valid dmem_wins,
    Gate.mkNOT dmem_resp_valid not_dmem,

    -- LSU FIFO wins if valid and no DMEM
    Gate.mkAND lsu_fifo_deq_valid not_dmem lsu_wins,
    Gate.mkNOT lsu_wins not_lsu,

    -- MulDiv FIFO wins if valid and no DMEM/LSU
    Gate.mkAND muldiv_fifo_deq_valid not_dmem muldiv_wins_tmp,
    Gate.mkAND muldiv_wins_tmp not_lsu muldiv_wins,
    Gate.mkNOT muldiv_wins not_muldiv,

    -- FP FIFO wins if valid and no DMEM/LSU/MulDiv
    Gate.mkAND fp_fifo_deq_valid not_dmem fp_wins_tmp,
    Gate.mkAND fp_wins_tmp not_lsu fp_wins_tmp2,
    Gate.mkAND fp_wins_tmp2 not_muldiv fp_wins,
    Gate.mkNOT fp_wins not_fp,

    -- INT/Branch FIFO wins if valid and no higher-priority source
    Gate.mkAND ib_fifo_deq_valid not_dmem ib_wins_tmp,
    Gate.mkAND ib_wins_tmp not_lsu ib_wins_tmp2,
    Gate.mkAND ib_wins_tmp2 not_muldiv ib_wins_tmp3,
    Gate.mkAND ib_wins_tmp3 not_fp ib_wins,

    -- Connect drain signals to FIFOs (deq_ready = this source wins)
    Gate.mkBUF lsu_wins lsu_fifo_drain,
    Gate.mkBUF muldiv_wins muldiv_fifo_drain,
    Gate.mkBUF fp_wins fp_fifo_drain,
    Gate.mkBUF ib_wins ib_fifo_drain
  ]

  -- CDB valid: any source won
  let cdb_valid_tmp := Wire.mk "cdb_valid_tmp"
  let cdb_valid_tmp2 := Wire.mk "cdb_valid_tmp2"
  let cdb_valid_tmp3 := Wire.mk "cdb_valid_tmp3"
  let cdb_valid_gates := [
    Gate.mkOR dmem_wins lsu_wins cdb_valid_tmp,
    Gate.mkOR cdb_valid_tmp muldiv_wins cdb_valid_tmp2,
    Gate.mkOR cdb_valid_tmp2 fp_wins cdb_valid_tmp3,
    Gate.mkOR cdb_valid_tmp3 ib_wins cdb_pre_valid
  ]

  -- CDB tag MUX: 4-level priority select from FIFO outputs + DMEM
  -- FIFO deq bits: [5:0]=tag, [37:6]=data, [38]=is_fp_rd
  let cdb_tag_mux_gates := (List.range 6).map (fun i =>
    let m1 := Wire.mk s!"cdb_tag_m1_{i}"
    let m2 := Wire.mk s!"cdb_tag_m2_{i}"
    let m3 := Wire.mk s!"cdb_tag_m3_{i}"
    [Gate.mkMUX ib_fifo_deq[i]! fp_fifo_deq[i]! fp_wins m1,
     Gate.mkMUX m1 muldiv_fifo_deq[i]! muldiv_wins m2,
     Gate.mkMUX m2 lsu_fifo_deq[i]! lsu_wins m3,
     Gate.mkMUX m3 dmem_load_tag_reg[i]! dmem_wins cdb_pre_tag[i]!])

  let cdb_data_mux_gates := (List.range 32).map (fun i =>
    let m1 := Wire.mk s!"cdb_data_m1_{i}"
    let m2 := Wire.mk s!"cdb_data_m2_{i}"
    let m3 := Wire.mk s!"cdb_data_m3_{i}"
    [Gate.mkMUX ib_fifo_deq[6+i]! fp_fifo_deq[6+i]! fp_wins m1,
     Gate.mkMUX m1 muldiv_fifo_deq[6+i]! muldiv_wins m2,
     Gate.mkMUX m2 lsu_fifo_deq[6+i]! lsu_wins m3,
     Gate.mkMUX m3 dmem_resp_formatted[i]! dmem_wins cdb_pre_data[i]!])

  let cdb_mux_gates := cdb_tag_mux_gates.flatten ++ cdb_data_mux_gates.flatten

  -- cdb_is_fp_rd tracking: bit 38 of winning FIFO + DMEM is_fp_reg
  let cdb_pre_is_fp := Wire.mk "cdb_pre_is_fp"
  let cdb_is_fp_rd_gates :=
    if enableF then
      -- Bit 38 carries is_fp_rd for all FIFO sources
      let fp_from_fifo := Wire.mk "cdb_fp_from_fifo"
      let fp_mux1 := Wire.mk "cdb_fp_mux1"
      let fp_mux2 := Wire.mk "cdb_fp_mux2"
      let fp_mux3 := Wire.mk "cdb_fp_mux3"
      [-- MUX tree on bit 38 of each FIFO output
       Gate.mkMUX ib_fifo_deq[38]! fp_fifo_deq[38]! fp_wins fp_mux1,
       Gate.mkMUX fp_mux1 muldiv_fifo_deq[38]! muldiv_wins fp_mux2,
       Gate.mkMUX fp_mux2 lsu_fifo_deq[38]! lsu_wins fp_mux3,
       -- DMEM is_fp_rd from registered flag
       Gate.mkMUX fp_mux3 dmem_is_fp_reg dmem_wins fp_from_fifo,
       Gate.mkBUF fp_from_fifo cdb_pre_is_fp]
    else
      [Gate.mkBUF zero cdb_pre_is_fp]

  -- CDB redirect target: extract from IB FIFO bits [70:39] when ib_wins, else zero
  let cdb_redirect_target_pre := makeIndexedWires "cdb_redirect_target_pre" 32
  let cdb_pre_mispredicted := Wire.mk "cdb_pre_mispredicted"
  let cdb_redirect_target := makeIndexedWires "cdb_redirect_target" 32
  let cdb_mispredicted := Wire.mk "cdb_mispredicted"
  let cdb_redirect_extract_gates :=
    (List.range 32).map (fun i =>
      Gate.mkAND ib_fifo_deq[39+i]! ib_wins cdb_redirect_target_pre[i]!) ++
    [Gate.mkAND ib_fifo_deq[71]! ib_wins cdb_pre_mispredicted]

  -- CDB pipeline register
  -- Use custom reset that preserves DMEM responses through flush:
  -- cdb_reset = pipeline_reset_misc AND NOT(dmem_resp_valid)
  -- This ensures a DMEM response arriving during flush is still broadcast.
  let not_dmem_resp := Wire.mk "not_dmem_resp_for_cdb"
  let cdb_reset := Wire.mk "cdb_reset"
  let cdb_reset_gates := [
    Gate.mkNOT dmem_resp_valid not_dmem_resp,
    Gate.mkAND pipeline_reset_misc not_dmem_resp cdb_reset
  ]

  let cdb_reg_insts : List CircuitInstance :=
    [{ moduleName := "DFlipFlop", instName := "u_cdb_valid_reg",
       portMap := [("d", cdb_pre_valid), ("q", cdb_valid),
                   ("clock", clock), ("reset", cdb_reset)] }] ++
    (List.range 6).map (fun i => {
       moduleName := "DFlipFlop", instName := s!"u_cdb_tag_reg_{i}",
       portMap := [("d", cdb_pre_tag[i]!), ("q", cdb_tag[i]!),
                   ("clock", clock), ("reset", cdb_reset)] }) ++
    (List.range 32).map (fun i => {
       moduleName := "DFlipFlop", instName := s!"u_cdb_data_reg_{i}",
       portMap := [("d", cdb_pre_data[i]!), ("q", cdb_data[i]!),
                   ("clock", clock), ("reset", cdb_reset)] }) ++
    (if enableF then
      [{ moduleName := "DFlipFlop", instName := "u_cdb_is_fp_rd_reg",
         portMap := [("d", cdb_pre_is_fp), ("q", cdb_is_fp_rd),
                     ("clock", clock), ("reset", cdb_reset)] }]
    else []) ++
    -- CDB redirect target pipeline registers (32 DFFs)
    (List.range 32).map (fun i => {
       moduleName := "DFlipFlop", instName := s!"u_cdb_redirect_target_reg_{i}",
       portMap := [("d", cdb_redirect_target_pre[i]!), ("q", cdb_redirect_target[i]!),
                   ("clock", clock), ("reset", cdb_reset)] }) ++
    -- CDB mispredicted pipeline register (1 DFF)
    [{ moduleName := "DFlipFlop", instName := "u_cdb_mispredicted_reg",
       portMap := [("d", cdb_pre_mispredicted), ("q", cdb_mispredicted),
                   ("clock", clock), ("reset", cdb_reset)] }]

  -- CDB domain gating: prevent tag collisions between INT/FP phys reg pools
  -- Also gate with cdb_tag_nonzero to suppress tag=0 broadcasts (x0 writeback)
  -- which would otherwise corrupt CDB forwarding in RS for src tags matching p0.
  let not_cdb_pre_is_fp := Wire.mk "not_cdb_pre_is_fp"
  let cdb_valid_nz := Wire.mk "cdb_valid_nz"
  -- Pre-register tag nonzero check
  let cdb_pre_tag_nz_tmp := List.range 5 |>.map (fun i => Wire.mk s!"cdb_pre_tag_nz_t{i}")
  let cdb_pre_tag_nonzero := Wire.mk "cdb_pre_tag_nonzero"
  let cdb_pre_valid_nz := Wire.mk "cdb_pre_valid_nz"
  let cdb_pre_tag_nz_gates :=
    [Gate.mkOR cdb_pre_tag[0]! cdb_pre_tag[1]! cdb_pre_tag_nz_tmp[0]!] ++
    (List.range 4).map (fun i =>
      Gate.mkOR cdb_pre_tag_nz_tmp[i]! cdb_pre_tag[i + 2]! (if i < 3 then cdb_pre_tag_nz_tmp[i + 1]! else cdb_pre_tag_nonzero)) ++
    [Gate.mkAND cdb_valid cdb_tag_nonzero cdb_valid_nz,
     Gate.mkAND cdb_pre_valid cdb_pre_tag_nonzero cdb_pre_valid_nz]
  let cdb_domain_gates :=
    cdb_pre_tag_nz_gates ++
    if enableF then
      [Gate.mkAND cdb_valid_nz not_cdb_is_fp (Wire.mk "cdb_valid_for_int"),
       Gate.mkAND cdb_valid_nz cdb_is_fp_rd (Wire.mk "cdb_valid_for_fp"),
       Gate.mkNOT cdb_pre_is_fp not_cdb_pre_is_fp,
       Gate.mkAND cdb_pre_valid_nz not_cdb_pre_is_fp (Wire.mk "cdb_pre_valid_for_int"),
       Gate.mkAND cdb_pre_valid_nz cdb_pre_is_fp (Wire.mk "cdb_pre_valid_for_fp")]
    else []

  let cdb_arb_gates := arb_level0_gates ++ fp_enq_is_fp_gate ++
    ib_fifo_enq_assemble ++ muldiv_fifo_enq_assemble ++ fp_fifo_enq_assemble ++
    lsu_fifo_enq_assemble ++
    muldiv_fifo_dummy_gates ++ fp_fifo_dummy_gates ++
    load_no_fwd_gates ++ dmem_pending_gates ++ mem_dispatch_en_gates ++
    dmem_tag_capture_gates ++
    drain_priority_gates ++
    cdb_valid_gates ++ cdb_mux_gates ++ cdb_is_fp_rd_gates ++ cdb_reset_gates ++ cdb_domain_gates

  -- === ROB is_fp_rd SHADOW REGISTER (conditional) ===
  -- 16-entry DFF array parallel to ROB, tracking whether each entry's rd is FP
  -- Written at ROB allocation with decode_has_fp_rd
  -- Read at ROB commit to route retire to correct free list
  let rob_is_fp_shadow := (List.range 16).map (fun e =>
    Wire.mk s!"rob_is_fp_e{e}")
  let rob_head_is_fp := Wire.mk "rob_head_is_fp"
  let not_rob_head_is_fp := Wire.mk "not_rob_head_is_fp"

  -- Shadow register write: decode rob_alloc_idx to select entry, write decode_has_fp_rd
  let rob_fp_shadow_decoded := makeIndexedWires "rob_fp_shadow_decoded" 16
  let rob_fp_shadow_we := makeIndexedWires "rob_fp_shadow_we" 16

  -- Shadow register write gates
  let rob_fp_shadow_write_gates :=
    if enableF then
      (List.range 16).map (fun e =>
        let match_bits := (List.range 4).map (fun b =>
          if (e / (2 ^ b)) % 2 != 0 then rob_alloc_idx[b]!
          else Wire.mk s!"rob_fp_sd_n{e}_{b}")
        let not_gates := (List.range 4).filterMap (fun b =>
          if (e / (2 ^ b)) % 2 == 0 then
            some (Gate.mkNOT rob_alloc_idx[b]! (Wire.mk s!"rob_fp_sd_n{e}_{b}"))
          else none)
        let t01 := Wire.mk s!"rob_fp_sd_t01_{e}"
        let t012 := Wire.mk s!"rob_fp_sd_t012_{e}"
        let next := Wire.mk s!"rob_fp_sdnx_e{e}"
        not_gates ++ [
          Gate.mkAND match_bits[0]! match_bits[1]! t01,
          Gate.mkAND t01 match_bits[2]! t012,
          Gate.mkAND t012 match_bits[3]! rob_fp_shadow_decoded[e]!,
          Gate.mkAND rob_fp_shadow_decoded[e]! rename_valid rob_fp_shadow_we[e]!,
          Gate.mkMUX rob_is_fp_shadow[e]! decode_has_fp_rd rob_fp_shadow_we[e]! next,
          Gate.mkDFF next clock reset rob_is_fp_shadow[e]!
        ]) |>.flatten
    else []

  -- Shadow register read mux tree (16:1)
  let rob_fp_shadow_read_gates :=
    if enableF then
      -- 16:1 mux tree on rob_is_fp_shadow, selected by rob_head_idx
      let mux_l0_w := (List.range 8).map (fun i => Wire.mk s!"rob_fp_rd_m0_{i}")
      let mux_l0_g := (List.range 8).map (fun i =>
        Gate.mkMUX rob_is_fp_shadow[2*i]! rob_is_fp_shadow[2*i+1]! rob_head_idx[0]! mux_l0_w[i]!)
      let mux_l1_w := (List.range 4).map (fun i => Wire.mk s!"rob_fp_rd_m1_{i}")
      let mux_l1_g := (List.range 4).map (fun i =>
        Gate.mkMUX mux_l0_w[2*i]! mux_l0_w[2*i+1]! rob_head_idx[1]! mux_l1_w[i]!)
      let mux_l2_w := (List.range 2).map (fun i => Wire.mk s!"rob_fp_rd_m2_{i}")
      let mux_l2_g := (List.range 2).map (fun i =>
        Gate.mkMUX mux_l1_w[2*i]! mux_l1_w[2*i+1]! rob_head_idx[2]! mux_l2_w[i]!)
      mux_l0_g ++ mux_l1_g ++ mux_l2_g ++
      [Gate.mkMUX mux_l2_w[0]! mux_l2_w[1]! rob_head_idx[3]! rob_head_is_fp,
       Gate.mkNOT rob_head_is_fp not_rob_head_is_fp]
    else []

  let rob_fp_shadow_gates := rob_fp_shadow_write_gates ++ rob_fp_shadow_read_gates

  -- === isStore SHADOW REGISTER ===
  -- 16-entry DFF array parallel to ROB, tracking whether each entry is a store instruction
  -- Written at ROB allocation with dispatch_is_store
  -- Read at ROB commit to route commit_store_en to SB
  let rob_isStore_shadow := (List.range 16).map (fun e =>
    Wire.mk s!"rob_isStore_e{e}")

  -- Shadow register write gates + DFF instances (4-bit equality match on rob_alloc_idx per entry)
  -- Uses CircuitInstance DFlipFlop to avoid pipeline_reset_busy grouping (must survive flush)
  let rob_isStore_shadow_results := (List.range 16).map (fun e =>
      let match_bits := (List.range 4).map (fun b =>
        if (e / (2 ^ b)) % 2 != 0 then rob_alloc_idx[b]!
        else Wire.mk s!"rob_st_sd_n{e}_{b}")
      let not_gates := (List.range 4).filterMap (fun b =>
        if (e / (2 ^ b)) % 2 == 0 then
          some (Gate.mkNOT rob_alloc_idx[b]! (Wire.mk s!"rob_st_sd_n{e}_{b}"))
        else none)
      let t01 := Wire.mk s!"rob_st_sd_t01_{e}"
      let t012 := Wire.mk s!"rob_st_sd_t012_{e}"
      let decoded := Wire.mk s!"rob_st_sd_dec_{e}"
      let we := Wire.mk s!"rob_st_sd_we_{e}"
      let next := Wire.mk s!"rob_st_sdnx_e{e}"
      let gates := not_gates ++ [
        Gate.mkAND match_bits[0]! match_bits[1]! t01,
        Gate.mkAND t01 match_bits[2]! t012,
        Gate.mkAND t012 match_bits[3]! decoded,
        Gate.mkAND decoded rename_valid we,
        Gate.mkMUX rob_isStore_shadow[e]! dispatch_is_store we next
      ]
      let inst : CircuitInstance := {
        moduleName := "DFlipFlop", instName := s!"u_rob_isStore_dff_{e}",
        portMap := [("d", next), ("q", rob_isStore_shadow[e]!),
                    ("clock", clock), ("reset", reset)]
      }
      (gates, inst))
  let rob_isStore_shadow_write_gates := (rob_isStore_shadow_results.map Prod.fst).flatten
  let rob_isStore_shadow_insts := rob_isStore_shadow_results.map Prod.snd

  -- Shadow register read: 16:1 mux tree using rob_head_idx
  let rob_isStore_shadow_read_gates :=
    let mux_l0_w := (List.range 8).map (fun i => Wire.mk s!"rob_st_rd_m0_{i}")
    let mux_l0_g := (List.range 8).map (fun i =>
      Gate.mkMUX rob_isStore_shadow[2*i]! rob_isStore_shadow[2*i+1]! rob_head_idx[0]! mux_l0_w[i]!)
    let mux_l1_w := (List.range 4).map (fun i => Wire.mk s!"rob_st_rd_m1_{i}")
    let mux_l1_g := (List.range 4).map (fun i =>
      Gate.mkMUX mux_l0_w[2*i]! mux_l0_w[2*i+1]! rob_head_idx[1]! mux_l1_w[i]!)
    let mux_l2_w := (List.range 2).map (fun i => Wire.mk s!"rob_st_rd_m2_{i}")
    let mux_l2_g := (List.range 2).map (fun i =>
      Gate.mkMUX mux_l1_w[2*i]! mux_l1_w[2*i+1]! rob_head_idx[2]! mux_l2_w[i]!)
    mux_l0_g ++ mux_l1_g ++ mux_l2_g ++
    [Gate.mkMUX mux_l2_w[0]! mux_l2_w[1]! rob_head_idx[3]! rob_head_isStore]

  let rob_isStore_shadow_gates := rob_isStore_shadow_write_gates ++ rob_isStore_shadow_read_gates

  -- === REDIRECT TARGET SHADOW REGISTERS ===
  -- 16-entry × 6-bit tag shadow (written at alloc) + 16 × 6-bit comparators
  -- + 16-entry × 32-bit target shadow (written on CDB tag match) + 16:1 × 32-bit read MUX
  -- This stores the redirect target per ROB entry for redirect-from-commit.

  -- Phase 1: Tag shadow (physRd tag per ROB entry, written at allocation)
  let redir_tag_shadow := (List.range 16).map (fun e =>
    makeIndexedWires s!"redir_tag_e{e}" 6)

  -- The physRd tag written at allocation is: branch_alloc_physRd (or rob_alloc_physRd_fp for F)
  let alloc_physRd_for_shadow := if enableF then rob_alloc_physRd_fp else branch_alloc_physRd

  let redir_tag_shadow_results := (List.range 16).map (fun e =>
    -- Decode rob_alloc_idx to match entry e
    let match_bits := (List.range 4).map (fun b =>
      if (e / (2 ^ b)) % 2 != 0 then rob_alloc_idx[b]!
      else Wire.mk s!"redir_ts_n{e}_{b}")
    let not_gates := (List.range 4).filter (fun b => (e / (2 ^ b)) % 2 == 0) |>.map (fun b =>
      Gate.mkNOT rob_alloc_idx[b]! (Wire.mk s!"redir_ts_n{e}_{b}"))
    let decoded := Wire.mk s!"redir_ts_dec{e}"
    let we := Wire.mk s!"redir_ts_we{e}"
    let t01 := Wire.mk s!"redir_ts_t01_{e}"
    let t012 := Wire.mk s!"redir_ts_t012_{e}"
    let gates := not_gates ++ [
      Gate.mkAND match_bits[0]! match_bits[1]! t01,
      Gate.mkAND t01 match_bits[2]! t012,
      Gate.mkAND t012 match_bits[3]! decoded,
      Gate.mkAND decoded rename_valid we
    ]
    -- Per-bit MUX + DFF for tag shadow
    let bit_gates := (List.range 6).map (fun b =>
      let next := Wire.mk s!"redir_ts_next{e}_{b}"
      [Gate.mkMUX redir_tag_shadow[e]![b]! alloc_physRd_for_shadow[b]! we next,
       Gate.mkDFF next clock reset redir_tag_shadow[e]![b]!]) |>.flatten
    (gates ++ bit_gates))

  let redir_tag_shadow_gates := redir_tag_shadow_results.flatten

  -- Phase 2: Tag comparators (compare cdb_tag vs each entry's stored tag)
  let redir_tag_match := (List.range 16).map (fun e => Wire.mk s!"redir_tm{e}")
  let redir_tag_cmp_insts : List CircuitInstance := (List.range 16).map (fun e => {
    moduleName := "EqualityComparator6"
    instName := s!"u_redir_tag_cmp_{e}"
    portMap := [("eq", redir_tag_match[e]!)] ++
               (cdb_tag.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (redir_tag_shadow[e]!.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  })

  -- Phase 3: Target shadow (32-bit redirect target per entry, written on CDB match)
  let redir_target_shadow := (List.range 16).map (fun e =>
    makeIndexedWires s!"redir_tgt_e{e}" 32)

  let redir_target_shadow_results := (List.range 16).map (fun e =>
    let we := Wire.mk s!"redir_tgt_we{e}"
    -- Write enable = cdb_valid AND tag_match AND cdb_mispredicted
    -- (only store target for mispredicted branches to avoid overwriting with stale data)
    let we_tmp := Wire.mk s!"redir_tgt_we_tmp{e}"
    let gates := [
      Gate.mkAND cdb_valid redir_tag_match[e]! we_tmp,
      Gate.mkAND we_tmp cdb_mispredicted we
    ]
    -- Per-bit MUX + DFF (CircuitInstance to control reset domain)
    let insts : List (List Gate × CircuitInstance) := (List.range 32).map (fun b =>
      let next := Wire.mk s!"redir_tgt_next{e}_{b}"
      ([Gate.mkMUX redir_target_shadow[e]![b]! cdb_redirect_target[b]! we next],
       { moduleName := "DFlipFlop"
         instName := s!"u_redir_tgt_dff_{e}_{b}"
         portMap := [("d", next), ("q", redir_target_shadow[e]![b]!),
                     ("clock", clock), ("reset", reset)]
       }))
    (gates ++ (insts.map Prod.fst).flatten, insts.map Prod.snd))

  let redir_target_shadow_gates := (redir_target_shadow_results.map Prod.fst).flatten
  let redir_target_shadow_insts := (redir_target_shadow_results.map Prod.snd).flatten

  -- Phase 4: Target read MUX tree (16:1 × 32 bits, indexed by rob_head_idx)
  let redir_target_read_gates := (List.range 32).map (fun b =>
    let mux_l0 := (List.range 8).map (fun i => Wire.mk s!"redir_rd_m0_{b}_{i}")
    let mux_l0_g := (List.range 8).map (fun i =>
      Gate.mkMUX redir_target_shadow[2*i]![b]! redir_target_shadow[2*i+1]![b]! rob_head_idx[0]! mux_l0[i]!)
    let mux_l1 := (List.range 4).map (fun i => Wire.mk s!"redir_rd_m1_{b}_{i}")
    let mux_l1_g := (List.range 4).map (fun i =>
      Gate.mkMUX mux_l0[2*i]! mux_l0[2*i+1]! rob_head_idx[1]! mux_l1[i]!)
    let mux_l2 := (List.range 2).map (fun i => Wire.mk s!"redir_rd_m2_{b}_{i}")
    let mux_l2_g := (List.range 2).map (fun i =>
      Gate.mkMUX mux_l1[2*i]! mux_l1[2*i+1]! rob_head_idx[2]! mux_l2[i]!)
    mux_l0_g ++ mux_l1_g ++ mux_l2_g ++
    [Gate.mkMUX mux_l2[0]! mux_l2[1]! rob_head_idx[3]! rob_head_redirect_target[b]!]
  ) |>.flatten

  let redir_shadow_all_gates := redir_tag_shadow_gates ++ redir_target_shadow_gates ++ redir_target_read_gates

  -- ROB old_rd_phys MUX: at dispatch, select FP or INT old_rd_phys for ROB storage
  -- When has_fp_rd, use fp_old_rd_phys; else use int old_rd_phys
  let rob_old_phys_mux_gates :=
    if enableF then
      (List.range 6).map (fun i =>
        Gate.mkMUX old_rd_phys[i]! fp_old_rd_phys[i]! decode_has_fp_rd rob_old_phys_muxed[i]!)
    else []

  -- === COMMIT CONTROL ===
  -- Branch tracking: branches with rd=x0 allocate a tracking physical register.
  -- At commit, free the tracking register (physRd) instead of the old register (oldPhysRd).
  -- branch_tracking = isBranch AND NOT(hasOldPhysRd) AND hasPhysRd
  --   (hasPhysRd=1 for all branches since we give them unique tags)
  let not_flushing := Wire.mk "not_flushing"
  let rob_commit_en_pre := Wire.mk "rob_commit_en_pre"
  let commit_gates := [
    Gate.mkNOT branch_redirect_valid_reg not_flushing,
    Gate.mkAND rob_head_valid rob_head_complete rob_commit_en_pre,
    Gate.mkAND rob_commit_en_pre not_flushing rob_commit_en,
    -- Determine if this is a branch-tracking-only commit (no real rd writeback)
    Gate.mkNOT rob_head_hasOldPhysRd not_hasOldPhysRd,
    Gate.mkAND rob_head_isBranch not_hasOldPhysRd branch_tracking_tmp,
    Gate.mkAND branch_tracking_tmp (Wire.mk "rob_head_hasPhysRd") branch_tracking,
    -- retire_any_old = hasOldPhysRd OR branch_tracking
    Gate.mkOR rob_head_hasOldPhysRd branch_tracking retire_any_old,
    Gate.mkAND rob_commit_en retire_any_old retire_recycle_valid,
    -- Store commit: only commit SB entry when retiring a store instruction
    Gate.mkAND rob_commit_en rob_head_isStore commit_store_en
  ] ++
  -- retire_tag_muxed = MUX(oldPhysRd, physRd, branch_tracking)
  (List.range 6).map (fun i =>
    Gate.mkMUX rob_head_oldPhysRd[i]! rob_head_physRd[i]! branch_tracking retire_tag_muxed[i]!)

  -- SB commit pointer: 3-bit counter, increments when a store retires from ROB
  let sb_commit_ptr_inc := makeIndexedWires "sb_commit_ptr_inc" 3
  let sb_commit_ptr_next := makeIndexedWires "sb_commit_ptr_next" 3
  let sb_commit_carry_0 := Wire.mk "sb_commit_carry_0"
  let sb_commit_ptr_normal := makeIndexedWires "sb_commit_ptr_normal" 3
  let sb_commit_ptr_gates := [
    -- 3-bit incrementer: ptr + 1
    Gate.mkNOT sb_commit_ptr[0]! sb_commit_ptr_inc[0]!,
    Gate.mkXOR sb_commit_ptr[1]! sb_commit_ptr[0]! sb_commit_ptr_inc[1]!,
    Gate.mkAND sb_commit_ptr[0]! sb_commit_ptr[1]! sb_commit_carry_0,
    Gate.mkXOR sb_commit_ptr[2]! sb_commit_carry_0 sb_commit_ptr_inc[2]!
  ] ++ (List.range 3).map (fun i =>
    -- Normal: increment on commit_store_en, else hold
    Gate.mkMUX sb_commit_ptr[i]! sb_commit_ptr_inc[i]! commit_store_en sb_commit_ptr_normal[i]!)
  ++ (List.range 3).map (fun i =>
    -- Flush override: reset to committed tail (= head + popcount(committed), computed by SB)
    Gate.mkMUX sb_commit_ptr_normal[i]! lsu_sb_committed_tail[i]! pipeline_flush_comb sb_commit_ptr_next[i]!)

  let sb_commit_ptr_insts := (List.range 3).map (fun i =>
    { moduleName := "DFlipFlop", instName := s!"u_sb_commit_ptr_{i}",
      portMap := [("d", sb_commit_ptr_next[i]!), ("q", sb_commit_ptr[i]!),
                  ("clock", clock), ("reset", reset)] : CircuitInstance })

  -- FP retire routing: split retire_valid between INT and FP free lists
  -- Also: committed RAT routing — INT commit when hasPhysRd AND NOT is_fp
  let fp_retire_gates :=
    if enableF then [
      Gate.mkAND retire_recycle_valid not_rob_head_is_fp int_retire_valid,
      Gate.mkAND retire_recycle_valid rob_head_is_fp fp_retire_recycle_valid,
      Gate.mkAND rob_head_hasOldPhysRd not_rob_head_is_fp (Wire.mk "int_commit_hasPhysRd")
    ] else []

  -- === CROSS-DOMAIN DISPATCH STALLS ===
  -- Stall FP instruction dispatch when INT source is not ready (prevents INT tags in FP RS)
  let fp_crossdomain_stall := Wire.mk "fp_crossdomain_stall"
  -- Stall FSW dispatch when FP source is not ready (prevents FP tags in Memory RS)
  let mem_fp_src_stall := Wire.mk "mem_fp_src_stall"
  let crossdomain_stall_gates :=
    if enableF then
      let not_fp_rs1_read := Wire.mk "not_fp_rs1_read_for_stall"
      let not_fp_src1_rdy := Wire.mk "not_fp_src1_rdy_for_stall"
      let fp_has_int_src := Wire.mk "fp_has_int_src"
      let not_mem_src2_rdy := Wire.mk "not_mem_src2_rdy_for_stall"
      [Gate.mkNOT decode_fp_rs1_read not_fp_rs1_read,
       Gate.mkNOT fp_issue_src1_ready not_fp_src1_rdy,
       Gate.mkAND dispatch_is_fp not_fp_rs1_read fp_has_int_src,
       Gate.mkAND fp_has_int_src not_fp_src1_rdy fp_crossdomain_stall,
       Gate.mkNOT mem_src2_ready not_mem_src2_rdy,
       Gate.mkAND dispatch_is_fp_store not_mem_src2_rdy mem_fp_src_stall]
    else
      [Gate.mkBUF zero fp_crossdomain_stall,
       Gate.mkBUF zero mem_fp_src_stall]

  -- === STALL GENERATION ===
  let stall_tmp1 := Wire.mk "stall_tmp1"
  let stall_tmp2 := Wire.mk "stall_tmp2"
  let stall_tmp3 := Wire.mk "stall_tmp3"
  let stall_tmp4 := Wire.mk "stall_tmp4"
  let stall_tmp5 := Wire.mk "stall_tmp5"

  let stall_tmp6 := Wire.mk "stall_tmp6"
  let stall_tmp7 := Wire.mk "stall_tmp7"
  let stall_tmp8 := Wire.mk "stall_tmp8"
  let stall_tmp9 := Wire.mk "stall_tmp9"

  let stall_gates :=
    [Gate.mkOR rename_stall rob_full stall_tmp1,
     Gate.mkOR stall_tmp1 rs_int_issue_full stall_tmp2,
     Gate.mkOR stall_tmp2 rs_mem_issue_full stall_tmp3,
     Gate.mkOR stall_tmp3 rs_branch_issue_full stall_tmp4] ++
    (if enableM && enableF then
      [Gate.mkOR stall_tmp4 rs_muldiv_issue_full stall_tmp5,
       Gate.mkOR stall_tmp5 rs_fp_issue_full stall_tmp6,
       Gate.mkOR stall_tmp6 fp_rename_stall stall_tmp7,
       Gate.mkOR stall_tmp7 fp_crossdomain_stall stall_tmp8,
       Gate.mkOR stall_tmp8 mem_fp_src_stall stall_tmp9,
       Gate.mkOR stall_tmp9 lsu_sb_full global_stall]
    else if enableM then
      [Gate.mkOR stall_tmp4 rs_muldiv_issue_full stall_tmp5,
       Gate.mkOR stall_tmp5 lsu_sb_full global_stall]
    else if enableF then
      [Gate.mkOR stall_tmp4 rs_fp_issue_full stall_tmp5,
       Gate.mkOR stall_tmp5 fp_rename_stall stall_tmp6,
       Gate.mkOR stall_tmp6 fp_crossdomain_stall stall_tmp7,
       Gate.mkOR stall_tmp7 mem_fp_src_stall stall_tmp8,
       Gate.mkOR stall_tmp8 lsu_sb_full global_stall]
    else
      [Gate.mkOR stall_tmp4 lsu_sb_full global_stall])

  -- === MEMORY INTERFACE ===
  let dmem_req_valid := Wire.mk "dmem_req_valid"
  let dmem_req_we := Wire.mk "dmem_req_we"
  let dmem_req_addr := makeIndexedWires "dmem_req_addr" 32
  let dmem_req_data := makeIndexedWires "dmem_req_data" 32
  let dmem_req_size := makeIndexedWires "dmem_req_size" 2

  let not_is_load := Wire.mk "not_is_load"
  let sb_enq_ungated := Wire.mk "sb_enq_ungated"
  let not_flush_comb := Wire.mk "not_flush_comb"
  let sb_enq_gate_gates := [
    Gate.mkNOT is_load not_is_load,
    Gate.mkAND rs_mem_dispatch_valid not_is_load sb_enq_ungated,
    -- Block wrong-path stores from entering SB during pipeline flush
    Gate.mkNOT pipeline_flush_comb not_flush_comb,
    Gate.mkAND sb_enq_ungated not_flush_comb sb_enq_en
  ]

  let dmem_valid_tmp := Wire.mk "dmem_valid_tmp"
  let dmem_gates := sb_enq_gate_gates ++ [
    Gate.mkOR load_no_fwd lsu_sb_deq_valid dmem_valid_tmp,
    Gate.mkBUF dmem_valid_tmp dmem_req_valid,
    Gate.mkBUF lsu_sb_deq_valid dmem_req_we] ++
    (List.range 32).map (fun i =>
      Gate.mkMUX mem_address[i]! lsu_sb_deq_bits[i]! lsu_sb_deq_valid dmem_req_addr[i]!) ++
    (List.range 32).map (fun i =>
      Gate.mkBUF lsu_sb_deq_bits[32+i]! dmem_req_data[i]!) ++
    -- dmem_req_size: from SB dequeue bits[65:64] on stores, 10 (word) on loads
    -- On store (dmem_req_we=1): use sb_deq_bits[64:65]
    -- On load (dmem_req_we=0): size=10 (word) since DMEM always returns full word
    [Gate.mkMUX zero lsu_sb_deq_bits[64]! dmem_req_we dmem_req_size[0]!,
     Gate.mkMUX one lsu_sb_deq_bits[65]! dmem_req_we dmem_req_size[1]!]

  -- === OUTPUT BUFFERS ===
  let global_stall_out := Wire.mk "global_stall_out"
  let output_gates := [Gate.mkBUF global_stall global_stall_out]

  { name := s!"CPU_{config.isaString}"
    inputs := [clock, reset, zero, one] ++
              imem_resp_data ++
              [dmem_req_ready, dmem_resp_valid] ++ dmem_resp_data
    outputs := fetch_pc ++ [fetch_stalled, global_stall_out] ++
               [dmem_req_valid, dmem_req_we] ++ dmem_req_addr ++ dmem_req_data ++ dmem_req_size ++
               [rob_empty] ++
               -- RVVI-TRACE outputs
               [rvvi_valid, rvvi_trap] ++ rvvi_pc_rdata ++ rvvi_insn ++
               rvvi_rd ++ [rvvi_rd_valid] ++ rvvi_rd_data ++
               rvvi_frd ++ [rvvi_frd_valid] ++ rvvi_frd_data ++
               fflags_acc
    gates := flush_gate ++ dispatch_gates ++ rd_nonzero_gates ++ int_dest_tag_mask_gates ++ branch_alloc_physRd_gates ++ src2_mux_gates ++ [busy_set_gate] ++ busy_gates ++
             cdb_prf_route_gates ++
             (if enableF then [fp_busy_set_gate] ++ fp_busy_gates else []) ++
             fp_crossdomain_gates ++ fp_cdb_fwd_gates ++ fp_fwd_data_gates ++
             fpu_lut_gates ++ fp_rs_dispatch_gate ++
             fp_src3_alloc_decode ++ fp_src3_dff_gates ++ fp_src3_read_gates ++
             (if enableF then fp_op_gates else []) ++
             cdb_fwd_gates ++ fwd_src1_data_gates ++ fwd_src2_data_gates ++
             alu_lut_gates ++ muldiv_lut_gates ++ cdb_tag_nz_gates ++ cdb_arb_gates ++
             rob_fp_shadow_gates ++ rob_isStore_shadow_gates ++ redir_shadow_all_gates ++ rob_old_phys_mux_gates ++ fp_retire_gates ++
             sb_commit_ptr_gates ++
             imm_rf_we_gates ++ imm_rf_gates ++ imm_rf_sel_gates ++
             int_imm_rf_we_gates ++ int_imm_rf_gates ++ int_imm_rf_sel_gates ++
             int_pc_rf_gates ++
             lui_match_gates ++ auipc_match_gates ++ lui_auipc_gates ++
             br_pred_taken_gates ++ br_pred_read_gates ++
             br_pc_rf_we_gates ++ br_pc_rf_gates ++ br_pc_rf_sel_gates ++
             br_imm_rf_gates ++
             br_pc_plus_4_b_gates ++ branch_result_mux_gates ++
             jal_match_gates ++ jalr_match_gates ++ jal_jalr_or_gate ++
             beq_match_gates ++ bne_match_gates ++ blt_match_gates ++
             bge_match_gates ++ bltu_match_gates ++ bgeu_match_gates ++
             branch_cond_gates ++ branch_mispredicted_gate ++ branch_redirect_gate ++ mispredict_redirect_gates ++ branch_target_wire_gates ++
             jalr_target_gates ++ target_sel_gates ++
             fp_mem_mux_gates ++ flw_match_gates ++
             lw_match_gates ++ lh_match_gates ++ lhu_match_gates ++
             lb_match_gates ++ lbu_match_gates ++ is_load_gates ++
             sw_match_gates ++ sh_match_gates ++ sb_match_gates ++ fsw_match_gates ++
             mem_size_gates ++ sign_extend_gates ++ sb_enq_size_gates ++ store_mask_gates ++
             fwd_size_check_gates ++ load_fwd_gates ++ lsu_sb_fwd_format_all ++
             lsu_valid_gate ++ lsu_tag_data_mux_gates ++
             lsu_is_fp_gates ++ dmem_is_fp_gates ++ dmem_meta_capture_gates ++ dmem_resp_format_all ++
             cdb_redirect_extract_gates ++
             commit_gates ++ crossdomain_stall_gates ++ stall_gates ++ dmem_gates ++ output_gates ++ rvvi_gates ++
             rvvi_fp_gates ++
             fflags_gates
    instances := [fetch_inst, decoder_inst, rename_inst] ++
                  (if enableF then [fp_rename_inst] else []) ++
                  [redirect_valid_dff_inst, flush_dff_dispatch] ++ flush_dff_insts ++
                  redirect_target_dff_insts ++
                  busy_instances ++
                  (if enableF then fp_busy_instances else []) ++
                  cdb_fwd_instances ++
                  fp_cdb_fwd_instances ++
                  [rs_int_inst, rs_mem_inst, rs_branch_inst] ++
                  (if enableM then [rs_muldiv_inst] else []) ++
                  (if enableF then [rs_fp_inst] else []) ++
                  [int_exec_inst, branch_exec_inst, mem_exec_inst] ++
                  (if enableM then [muldiv_exec_inst] else []) ++
                  (if enableF then [fp_exec_inst] else []) ++
                  [rob_inst, lsu_inst,
                  imm_rf_decoder_inst, imm_rf_mux_inst,
                  int_imm_rf_decoder_inst, int_imm_rf_mux_inst, int_pc_rf_mux_inst,
                  br_pc_rf_decoder_inst, br_pc_rf_mux_inst, br_imm_rf_mux_inst,
                  auipc_adder_inst, br_pc_plus_4_adder_inst,
                  branch_target_adder_inst, jalr_target_adder_inst,
                  br_cmp_inst] ++
                  cdb_reg_insts ++
                  [ib_fifo_inst, lsu_fifo_inst] ++
                  (if enableM then [muldiv_fifo_inst] else []) ++
                  (if enableF then [fp_fifo_inst] else []) ++
                  lsu_pipeline_insts ++
                  [pc_queue_inst, insn_queue_inst] ++
                  fflags_dff_instances ++
                  sb_commit_ptr_insts ++
                  rob_isStore_shadow_insts ++
                  redir_tag_cmp_insts ++ redir_target_shadow_insts ++
                  [dmem_pending_inst] ++ dmem_tag_capture_insts ++ dmem_is_fp_insts ++
                  dmem_meta_capture_insts
    signalGroups :=
      [{ name := "imem_resp_data", width := 32, wires := imem_resp_data },
       { name := "dmem_resp_data", width := 32, wires := dmem_resp_data },
       { name := "decode_optype", width := opcodeWidth, wires := decode_optype },
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
       { name := "muldiv_tag_out", width := 6, wires := muldiv_tag_out },
       { name := "muldiv_fifo_enq_data", width := 39, wires := muldiv_fifo_enq_data },
       { name := "muldiv_fifo_deq", width := 39, wires := muldiv_fifo_deq }] else []) ++
      [{ name := "ib_fifo_enq_data", width := 72, wires := ib_fifo_enq_data },
       { name := "ib_fifo_deq", width := 72, wires := ib_fifo_deq },
       { name := "lsu_fifo_enq_data", width := 39, wires := lsu_fifo_enq_data },
       { name := "lsu_fifo_deq", width := 39, wires := lsu_fifo_deq }] ++
      (if enableF then [
       { name := "fp_fifo_enq_data", width := 39, wires := fp_fifo_enq_data },
       { name := "fp_fifo_deq", width := 39, wires := fp_fifo_deq }] else []) ++
      [{ name := "lsu_agu_address", width := 32, wires := lsu_agu_address },
       { name := "lsu_agu_tag", width := 6, wires := lsu_agu_tag },
       { name := "lsu_sb_fwd_data", width := 32, wires := lsu_sb_fwd_data },
       { name := "lsu_sb_fwd_size", width := 2, wires := lsu_sb_fwd_size },
       { name := "lsu_sb_deq_bits", width := 66, wires := lsu_sb_deq_bits },
       { name := "lsu_sb_enq_idx", width := 3, wires := lsu_sb_enq_idx },
       { name := "dmem_req_addr", width := 32, wires := dmem_req_addr },
       { name := "dmem_req_data", width := 32, wires := dmem_req_data },
       { name := "dmem_req_size", width := 2, wires := dmem_req_size },
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
       { name := "muldiv_fifo_deq", width := 39, wires := muldiv_fifo_deq }] else []) ++
      [{ name := "rvvi_pc_rdata", width := 32, wires := rvvi_pc_rdata },
       { name := "rvvi_insn", width := 32, wires := rvvi_insn },
       { name := "rvvi_rd", width := 5, wires := rvvi_rd },
       { name := "rvvi_rd_data", width := 32, wires := rvvi_rd_data },
       { name := "rvvi_frd", width := 5, wires := rvvi_frd },
       { name := "rvvi_frd_data", width := 32, wires := rvvi_frd_data },
       { name := "fflags_acc", width := 5, wires := fflags_acc },
       { name := "rob_head_idx", width := 4, wires := rob_head_idx }] ++
      (if enableF then [
       { name := "fp_rs1_phys", width := 6, wires := fp_rs1_phys },
       { name := "fp_rs2_phys", width := 6, wires := fp_rs2_phys },
       { name := "fp_rd_phys", width := 6, wires := fp_rd_phys },
       { name := "fp_result", width := 32, wires := fp_result },
       { name := "fp_tag_out", width := 6, wires := fp_tag_out },
       { name := "rs_fp_dispatch_opcode", width := 6, wires := rs_fp_dispatch_opcode },
       { name := "rs_fp_dispatch_src1", width := 32, wires := rs_fp_dispatch_src1 },
       { name := "rs_fp_dispatch_src2", width := 32, wires := rs_fp_dispatch_src2 },
       { name := "rs_fp_dispatch_tag", width := 6, wires := rs_fp_dispatch_tag },
       { name := "fp_rvvi_rd_data", width := 32, wires := fp_rvvi_rd_data }] else [])
  }

/-- RV32I CPU (backward-compatible alias) -/
def mkCPU_RV32I : Circuit := mkCPU rv32iConfig

/-- RV32IM CPU (backward-compatible alias) -/
def mkCPU_RV32IM : Circuit := mkCPU rv32imConfig

/-- RV32IF CPU (F extension only) -/
def mkCPU_RV32IF : Circuit := mkCPU rv32ifConfig

/-- RV32IMF CPU (M + F extensions) -/
def mkCPU_RV32IMF : Circuit := mkCPU rv32imfConfig

end -- section

end Shoumei.RISCV.CPU
