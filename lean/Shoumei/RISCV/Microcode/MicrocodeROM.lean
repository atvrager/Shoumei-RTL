/-
Microcode ROM - Pure function defining ROM contents

64-entry ROM, 8 entries per sequence. Each entry is a ROMEntry (opcode + dst + src).
The ROM is a pure Lean function Fin 64 → ROMEntry, which will be realized as a
combinational mux tree in the structural circuit.
-/

import Shoumei.RISCV.Microcode.MicrocodeTypes

namespace Shoumei.RISCV.Microcode

open MicroOp

/-- Helper to construct a ROM entry with temp register indices -/
private def re (op : MicroOp) (dst src : Nat) (imm : Nat := 0) : ROMEntry :=
  { opcode := op, dst := ⟨dst % 2, by omega⟩, src := ⟨src % 2, by omega⟩, imm := ⟨imm % 65536, by omega⟩ }

/-- The microcode ROM contents: Fin 64 → ROMEntry -/
def romContents : Fin 64 → ROMEntry
  -- Sequence 0: CSRRW/CSRRWI (addr 0-7)
  | ⟨0, _⟩  => re DRAIN     0 0   -- stall until ROB empty
  | ⟨1, _⟩  => re READ_CSR  0 0   -- temp0 := CSR[addr]
  | ⟨2, _⟩  => re ALU_MOV   1 0   -- temp1 := rs1Val
  | ⟨3, _⟩  => re WRITE_CSR 0 1   -- CSR[addr] := temp1
  | ⟨4, _⟩  => re MOV_TO_RD 0 0   -- rd := temp0 (old CSR value)
  | ⟨5, _⟩  => re DONE      0 0
  | ⟨6, _⟩  => re DONE      0 0
  | ⟨7, _⟩  => re DONE      0 0
  -- Sequence 1: CSRRS/CSRRSI (addr 8-15)
  | ⟨8, _⟩  => re DRAIN     0 0
  | ⟨9, _⟩  => re READ_CSR  0 0   -- temp0 := CSR[addr]
  | ⟨10, _⟩ => re ALU_OR    1 0   -- temp1 := temp0 | rs1Val
  | ⟨11, _⟩ => re WRITE_CSR 0 1   -- CSR[addr] := temp1
  | ⟨12, _⟩ => re MOV_TO_RD 0 0   -- rd := temp0
  | ⟨13, _⟩ => re DONE      0 0
  | ⟨14, _⟩ => re DONE      0 0
  | ⟨15, _⟩ => re DONE      0 0
  -- Sequence 2: CSRRC/CSRRCI (addr 16-23)
  | ⟨16, _⟩ => re DRAIN     0 0
  | ⟨17, _⟩ => re READ_CSR  0 0   -- temp0 := CSR[addr]
  | ⟨18, _⟩ => re ALU_ANDN  1 0   -- temp1 := temp0 & ~rs1Val
  | ⟨19, _⟩ => re WRITE_CSR 0 1   -- CSR[addr] := temp1
  | ⟨20, _⟩ => re MOV_TO_RD 0 0   -- rd := temp0
  | ⟨21, _⟩ => re DONE      0 0
  | ⟨22, _⟩ => re DONE      0 0
  | ⟨23, _⟩ => re DONE      0 0
  -- Sequence 3: FENCE.I (addr 24-31)
  | ⟨24, _⟩ => re DRAIN     0 0
  | ⟨25, _⟩ => re DRAIN_SB  0 0
  | ⟨26, _⟩ => re FLUSH_FETCH 0 0
  | ⟨27, _⟩ => re DONE      0 0
  | ⟨28, _⟩ => re DONE      0 0
  | ⟨29, _⟩ => re DONE      0 0
  | ⟨30, _⟩ => re DONE      0 0
  | ⟨31, _⟩ => re DONE      0 0
  -- Sequence 4: TRAP_ENTRY (addr 32-47, uses 16-entry range)
  | ⟨32, _⟩ => re DRAIN          0 0         -- wait for ROB empty
  | ⟨33, _⟩ => re MSTATUS_TRAP   0 0         -- mstatus: MPIE=MIE, MIE=0, MPP=M
  | ⟨34, _⟩ => re SET_CSR_ADDR   0 0 0x341   -- csrAddr := mepc
  | ⟨35, _⟩ => re LOAD_PC        0 0         -- temp0 := PC of ECALL
  | ⟨36, _⟩ => re WRITE_CSR      0 0         -- mepc := temp0
  | ⟨37, _⟩ => re SET_CSR_ADDR   0 0 0x342   -- csrAddr := mcause
  | ⟨38, _⟩ => re LOAD_CONST     0 0 11      -- temp0 := 11 (ecall from M-mode)
  | ⟨39, _⟩ => re WRITE_CSR      0 0         -- mcause := temp0
  | ⟨40, _⟩ => re SET_CSR_ADDR   0 0 0x305   -- csrAddr := mtvec
  | ⟨41, _⟩ => re DRAIN_SB       0 0         -- wait 1 cycle for addr to register
  | ⟨42, _⟩ => re READ_CSR       1 0         -- temp1 := mtvec
  | ⟨43, _⟩ => re SET_PC         0 1         -- redirect PC to temp1
  | ⟨44, _⟩ => re DONE           0 0
  | ⟨45, _⟩ => re DONE           0 0
  | ⟨46, _⟩ => re DONE           0 0
  | ⟨47, _⟩ => re DONE           0 0
  -- Sequence 5: MRET (addr 48-55)
  | ⟨48, _⟩ => re DRAIN          0 0         -- wait for ROB empty
  | ⟨49, _⟩ => re DRAIN_SB       0 0         -- wait for store buffer empty
  | ⟨50, _⟩ => re SET_CSR_ADDR   0 0 0x341   -- csrAddr := mepc
  | ⟨51, _⟩ => re DRAIN_SB       0 0         -- wait 1 cycle for addr to register
  | ⟨52, _⟩ => re READ_CSR       1 0         -- temp1 := mepc
  | ⟨53, _⟩ => re MSTATUS_MRET   0 0         -- mstatus: MIE=MPIE, MPIE=1, MPP=0
  | ⟨54, _⟩ => re SET_PC         0 1         -- redirect PC to temp1 (mepc)
  | ⟨55, _⟩ => re DONE           0 0
  -- Remaining (56-63): DONE
  | ⟨_, _⟩  => re DONE           0 0

/-- Number of active (non-DONE) steps in each sequence -/
def sequenceLength : SequenceID → Nat
  | .CSRRW     => 6
  | .CSRRS     => 6
  | .CSRRC     => 6
  | .FENCE_I   => 4
  | .TRAP_ENTRY => 13
  | .MRET       => 8

/-- Look up a ROM entry by sequence ID and step offset -/
def lookupROM (seq : SequenceID) (step : Fin 8) : ROMEntry :=
  romContents ⟨seq.baseAddr.val + step.val, by cases seq <;> simp [SequenceID.baseAddr] <;> omega⟩

/-- Behavioral model: execute one microcode step on state.
    Returns (newState, csrRead?, csrWrite?, cdbInject?, flushFetch?, done?) -/
def stepMicrocode (s : MicrocodeState) (csrReadVal : UInt32) (robEmpty sbEmpty : Bool)
    : MicrocodeState × Bool × Bool × Bool × Bool × Bool :=
  if !s.active then (s, false, false, false, false, false)
  else
    let entry := romContents s.upc
    let nextUpc : Fin 64 := ⟨(s.upc.val + 1) % 64, by omega⟩
    match entry.opcode with
    | .DRAIN =>
      if robEmpty then
        ({ s with upc := nextUpc, waitDrain := false }, false, false, false, false, false)
      else
        ({ s with waitDrain := true }, false, false, false, false, false)
    | .DRAIN_SB =>
      if sbEmpty then
        ({ s with upc := nextUpc, waitSB := false }, false, false, false, false, false)
      else
        ({ s with waitSB := true }, false, false, false, false, false)
    | .READ_CSR =>
      let s' := if entry.dst == ⟨0, by omega⟩
                then { s with temp0 := csrReadVal, upc := nextUpc }
                else { s with temp1 := csrReadVal, upc := nextUpc }
      (s', true, false, false, false, false)
    | .WRITE_CSR =>
      if s.skipWrite then
        ({ s with upc := nextUpc }, false, false, false, false, false)
      else
        ({ s with upc := nextUpc }, false, true, false, false, false)
    | .MOV_TO_RD =>
      ({ s with upc := nextUpc }, false, false, true, false, false)
    | .ALU_MOV =>
      let s' := if entry.dst == ⟨0, by omega⟩
                then { s with temp0 := s.rs1Val, upc := nextUpc }
                else { s with temp1 := s.rs1Val, upc := nextUpc }
      (s', false, false, false, false, false)
    | .ALU_OR =>
      let srcVal := if entry.src == ⟨0, by omega⟩ then s.temp0 else s.temp1
      let result := srcVal ||| s.rs1Val
      let s' := if entry.dst == ⟨0, by omega⟩
                then { s with temp0 := result, upc := nextUpc }
                else { s with temp1 := result, upc := nextUpc }
      (s', false, false, false, false, false)
    | .ALU_ANDN =>
      let srcVal := if entry.src == ⟨0, by omega⟩ then s.temp0 else s.temp1
      let result := srcVal &&& (~~~s.rs1Val)
      let s' := if entry.dst == ⟨0, by omega⟩
                then { s with temp0 := result, upc := nextUpc }
                else { s with temp1 := result, upc := nextUpc }
      (s', false, false, false, false, false)
    | .FLUSH_FETCH =>
      ({ s with upc := nextUpc }, false, false, false, true, false)
    | .SET_PC =>
      ({ s with upc := nextUpc }, false, false, false, true, false)
    | .LOAD_PC =>
      let s' := if entry.dst == ⟨0, by omega⟩
                then { s with temp0 := s.pcVal, upc := nextUpc }
                else { s with temp1 := s.pcVal, upc := nextUpc }
      (s', false, false, false, false, false)
    | .LOAD_CONST =>
      let constVal : UInt32 := UInt32.ofNat entry.imm.val
      let s' := if entry.dst == ⟨0, by omega⟩
                then { s with temp0 := constVal, upc := nextUpc }
                else { s with temp1 := constVal, upc := nextUpc }
      (s', false, false, false, false, false)
    | .MSTATUS_TRAP =>
      -- Read mstatus, set MPIE=MIE, clear MIE, set MPP=M, write back
      -- Handled externally via CSR read/write ports; sequencer signals the operation
      ({ s with upc := nextUpc }, true, true, false, false, false)
    | .MSTATUS_MRET =>
      -- Read mstatus, set MIE=MPIE, set MPIE=1, clear MPP, write back
      ({ s with upc := nextUpc }, true, true, false, false, false)
    | .SET_CSR_ADDR =>
      let newAddr : Fin 4096 := ⟨entry.imm.val % 4096, by omega⟩
      ({ s with csrAddr := newAddr, upc := nextUpc }, false, false, false, false, false)
    | .DONE =>
      ({ s with active := false, waitDrain := false, waitSB := false }, false, false, false, false, true)

end Shoumei.RISCV.Microcode
