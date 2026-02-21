/-
Microcode Types - µop encoding, ROM entry structure, sequencer state

Defines the microcode instruction set for Zicsr + Zifencei + trap execution.
Each ROM entry is 24 bits: [23:20] opcode, [19:18] dst, [17:16] src, [15:0] immediate.
The 16-bit immediate field carries CSR addresses (for SET_CSR_ADDR) and
constants (for LOAD_CONST).
-/

namespace Shoumei.RISCV.Microcode

/-- Micro-operation opcodes (4-bit encoding) -/
inductive MicroOp where
  | DRAIN       -- 0x0: Stall until ROB empty
  | DRAIN_SB    -- 0x1: Stall until store buffer empty
  | READ_CSR    -- 0x2: temp[dst] := CSR[csrAddr]
  | WRITE_CSR   -- 0x3: CSR[csrAddr] := temp[src] (skipped if skipWrite)
  | MOV_TO_RD   -- 0x4: PRF[rdTag] := temp[src] via CDB inject
  | ALU_MOV     -- 0x5: temp[dst] := rs1Val
  | ALU_OR      -- 0x6: temp[dst] := temp[src] | rs1Val
  | ALU_ANDN    -- 0x7: temp[dst] := temp[src] & ~rs1Val
  | FLUSH_FETCH -- 0x8: Redirect fetch to captured PC+4
  | SET_PC      -- 0x9: Redirect fetch to temp[src] (future MRET)
  | DONE        -- 0xA: Clear active, resume normal decode
  | LOAD_PC     -- 0xB: temp[dst] := capturedPC (PC of trapping instruction)
  | LOAD_CONST  -- 0xC: temp[dst] := zext(ROM[15:0]) (immediate from ROM entry)
  | MSTATUS_TRAP -- 0xD: mstatus: set MPIE=MIE, clear MIE, set MPP=M
  | SET_CSR_ADDR -- 0xE: csrAddr := ROM[11:0] (override CSR address mid-sequence)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Encode MicroOp to 4-bit natural number -/
def MicroOp.toNat : MicroOp → Nat
  | .DRAIN       => 0
  | .DRAIN_SB    => 1
  | .READ_CSR    => 2
  | .WRITE_CSR   => 3
  | .MOV_TO_RD   => 4
  | .ALU_MOV     => 5
  | .ALU_OR      => 6
  | .ALU_ANDN    => 7
  | .FLUSH_FETCH   => 8
  | .SET_PC        => 9
  | .DONE          => 10
  | .LOAD_PC       => 11
  | .LOAD_CONST    => 12
  | .MSTATUS_TRAP  => 13
  | .SET_CSR_ADDR  => 14

/-- Decode 4-bit natural to MicroOp -/
def MicroOp.fromNat : Nat → MicroOp
  | 0 => .DRAIN
  | 1 => .DRAIN_SB
  | 2 => .READ_CSR
  | 3 => .WRITE_CSR
  | 4 => .MOV_TO_RD
  | 5 => .ALU_MOV
  | 6 => .ALU_OR
  | 7 => .ALU_ANDN
  | 8 => .FLUSH_FETCH
  | 9  => .SET_PC
  | 10 => .DONE
  | 11 => .LOAD_PC
  | 12 => .LOAD_CONST
  | 13 => .MSTATUS_TRAP
  | 14 => .SET_CSR_ADDR
  | _  => .DONE

theorem MicroOp.roundtrip (op : MicroOp) : MicroOp.fromNat op.toNat = op := by
  cases op <;> rfl

/-- ROM entry: 24-bit microinstruction -/
structure ROMEntry where
  opcode : MicroOp
  dst    : Fin 2     -- temp register destination index
  src    : Fin 2     -- temp register source index
  imm    : Fin 65536 -- 16-bit immediate (CSR addr for SET_CSR_ADDR, constant for LOAD_CONST)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Encode ROMEntry to 24-bit natural: [23:20] opcode, [19:18] dst, [17:16] src, [15:0] imm -/
def ROMEntry.encode (e : ROMEntry) : Nat :=
  (e.opcode.toNat <<< 20) ||| (e.dst.val <<< 18) ||| (e.src.val <<< 16) ||| e.imm.val

/-- Decode 24-bit natural to ROMEntry -/
def ROMEntry.decode (n : Nat) : ROMEntry :=
  { opcode := MicroOp.fromNat ((n >>> 20) % 16)
    dst := ⟨(n >>> 18) % 2, by omega⟩
    src := ⟨(n >>> 16) % 2, by omega⟩
    imm := ⟨n % 65536, by omega⟩ }

/-- Microcode sequence identifiers -/
inductive SequenceID where
  | CSRRW     -- CSRRW / CSRRWI
  | CSRRS     -- CSRRS / CSRRSI
  | CSRRC     -- CSRRC / CSRRCI
  | FENCE_I   -- FENCE.I
  | TRAP_ENTRY -- (reserved)
  | MRET       -- (reserved)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Base ROM address for each sequence (8 entries per sequence) -/
def SequenceID.baseAddr : SequenceID → Fin 64
  | .CSRRW     => ⟨0, by omega⟩
  | .CSRRS     => ⟨8, by omega⟩
  | .CSRRC     => ⟨16, by omega⟩
  | .FENCE_I   => ⟨24, by omega⟩
  | .TRAP_ENTRY => ⟨32, by omega⟩
  | .MRET       => ⟨48, by omega⟩

/-- Sequencer FSM state -/
structure MicrocodeState where
  active       : Bool        -- sequencer is running
  upc          : Fin 64      -- micro program counter
  temp0        : UInt32      -- temp register 0
  temp1        : UInt32      -- temp register 1
  rs1Val       : UInt32      -- captured rs1/zimm value
  csrAddr      : Fin 4096    -- captured CSR address
  rdTag        : Fin 64      -- captured physical destination register tag
  hasRd        : Bool        -- instruction writes rd
  skipWrite    : Bool        -- skip CSR write (rs1=x0 for CSRRS/C)
  csrFlag      : Bool        -- true = CSR op, false = FENCE.I
  pcVal        : UInt32      -- captured PC of trapping instruction
  waitDrain    : Bool        -- waiting for ROB drain
  waitSB       : Bool        -- waiting for store buffer drain
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Initial (idle) sequencer state -/
def MicrocodeState.idle : MicrocodeState :=
  { active := false, upc := ⟨0, by omega⟩, temp0 := 0, temp1 := 0
    rs1Val := 0, csrAddr := ⟨0, by omega⟩, rdTag := ⟨0, by omega⟩
    hasRd := false, skipWrite := false, csrFlag := false
    pcVal := 0, waitDrain := false, waitSB := false }

end Shoumei.RISCV.Microcode
