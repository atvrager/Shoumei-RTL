/-
FallbackTypes.lean - Microcode types for fallback instruction emulation.

Defines the micro-operation instruction set, control store word format,
and sequencer state for emulating un-decoded instructions (Zb* proving ground)
and raising architectural illegal instruction exceptions.
-/

namespace Shoumei.RISCV.Microcode

/-- Micro-operation opcodes for fallback execution and emulation -/
inductive FallbackOp where
  -- Pipeline synchronization & Control
  | DRAIN         -- 0x00: Wait for ROB and StoreBuffer empty
  | DONE          -- 0x01: Complete sequence, inject to CDB, advance PC+4
  | TRAP_ILLEGAL  -- 0x02: Fault to mtvec (mcause=2, mepc=pc, mtval=insn)
  | JMP           -- 0x03: Unconditional jump (upc := imm)
  | JMP_ZERO      -- 0x04: Jump if temp[src1] == 0 (upc := imm)
  | JMP_NZERO     -- 0x05: Jump if temp[src1] != 0 (upc := imm)
  | JMP_EQ        -- 0x06: Jump if temp[src1] == temp[src2] (upc := imm)

  -- Register & Data movement
  | LOAD_RS1      -- 0x07: temp[dst] := rs1Val
  | LOAD_RS2      -- 0x08: temp[dst] := rs2Val
  | LOAD_IMM      -- 0x09: temp[dst] := zext/sext(imm16)
  | LOAD_INSN     -- 0x0A: temp[dst] := zext(raw_insn)
  | LOAD_PC       -- 0x0B: temp[dst] := pcVal
  | MOV_TO_RD     -- 0x0C: PRF[rdTag] := temp[src1] via CDB
  | LOAD_SHAMT    -- 0x31: temp[dst] := zext(insn[25:20]), range 0..63

  -- Micro-ALU: Basic Arithmetic & Logic
  | ALU_ADD       -- 0x0D: temp[dst] := temp[src1] + temp[src2]
  | ALU_SUB       -- 0x0E: temp[dst] := temp[src1] - temp[src2]
  | ALU_AND       -- 0x0F: temp[dst] := temp[src1] &&& temp[src2]
  | ALU_OR        -- 0x10: temp[dst] := temp[src1] ||| temp[src2]
  | ALU_XOR       -- 0x11: temp[dst] := temp[src1] ^^^ temp[src2]
  | ALU_ANDN      -- 0x12: temp[dst] := temp[src1] &&& ~~~temp[src2]
  | ALU_ORN       -- 0x13: temp[dst] := temp[src1] ||| ~~~temp[src2]
  | ALU_XNOR      -- 0x14: temp[dst] := ~~~(temp[src1] ^^^ temp[src2])

  -- Micro-ALU: Shifts & Rotates
  | ALU_SLL       -- 0x15: temp[dst] := temp[src1] <<< (temp[src2] &&& 63)
  | ALU_SRL       -- 0x16: temp[dst] := temp[src1] >>> (temp[src2] &&& 63)
  | ALU_SRA       -- 0x17: temp[dst] := arithmetic right shift
  | ALU_ROL       -- 0x18: temp[dst] := 64-bit rotate left
  | ALU_ROR       -- 0x19: temp[dst] := 64-bit rotate right

  -- Micro-ALU: Compares
  | ALU_SLT       -- 0x1A: temp[dst] := (signed(src1) < signed(src2)) ? 1 : 0
  | ALU_SLTU      -- 0x1B: temp[dst] := (src1 < src2) ? 1 : 0
  | ALU_MIN       -- 0x1C: temp[dst] := signed min
  | ALU_MAX       -- 0x1D: temp[dst] := signed max
  | ALU_MINU      -- 0x1E: temp[dst] := unsigned min
  | ALU_MAXU      -- 0x1F: temp[dst] := unsigned max

  -- Micro-ALU: Complex Bitmanip
  | ALU_REV8      -- 0x20: byte-reverse (endian swap)
  | ALU_ORCB      -- 0x21: byte-wise OR-combine
  | ALU_CLZ       -- 0x22: count leading zeros
  | ALU_CTZ       -- 0x23: count trailing zeros
  | ALU_CPOP      -- 0x24: population count
  | ALU_CLMUL     -- 0x25: carry-less multiply (low 64 bits)
  | ALU_CLMULH    -- 0x26: carry-less multiply (high 64 bits)
  | ALU_CLMULR    -- 0x27: carry-less multiply (reversed)

  -- Immediate shift/add helpers (Zba / Zbs)
  | ALU_SH1ADD    -- 0x28: temp[dst] := (temp[src1] <<< 1) + temp[src2]
  | ALU_SH2ADD    -- 0x29: temp[dst] := (temp[src1] <<< 2) + temp[src2]
  | ALU_SH3ADD    -- 0x2A: temp[dst] := (temp[src1] <<< 3) + temp[src2]
  | ALU_BSET      -- 0x2B: temp[dst] := temp[src1] ||| (1 <<< (temp[src2] &&& 63))
  | ALU_BCLR      -- 0x2C: temp[dst] := temp[src1] &&& ~~~(1 <<< (temp[src2] &&& 63))
  | ALU_BINV      -- 0x2D: temp[dst] := temp[src1] ^^^ (1 <<< (temp[src2] &&& 63))
  | ALU_BEXT      -- 0x2E: temp[dst] := (temp[src1] >>> (temp[src2] &&& 63)) &&& 1

  -- 32-bit word variants (W-instructions in RV64)
  | ALU_SEXT_W    -- 0x2F: sign-extend 32-bit to 64-bit
  | ALU_ZEXT_W    -- 0x30: zero-extend 32-bit to 64-bit
  | ALU_ROLW      -- 0x32: temp[dst] := sext32(rol(temp[src1][31:0], temp[src2][4:0]))
  | ALU_RORW      -- 0x33: temp[dst] := sext32(ror(temp[src1][31:0], temp[src2][4:0]))
  | ALU_CTZW      -- 0x34: temp[dst] := (temp[src1][31:0] == 0) ? 32 : ctz32(temp[src1][31:0])
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Convert FallbackOp to 6-bit natural encoding -/
def FallbackOp.toNat : FallbackOp → Nat
  | .DRAIN        => 0
  | .DONE         => 1
  | .TRAP_ILLEGAL => 2
  | .JMP          => 3
  | .JMP_ZERO     => 4
  | .JMP_NZERO    => 5
  | .JMP_EQ       => 6
  | .LOAD_RS1     => 7
  | .LOAD_RS2     => 8
  | .LOAD_IMM     => 9
  | .LOAD_INSN    => 10
  | .LOAD_PC      => 11
  | .MOV_TO_RD    => 12
  | .LOAD_SHAMT   => 49
  | .ALU_ADD      => 13
  | .ALU_SUB      => 14
  | .ALU_AND      => 15
  | .ALU_OR       => 16
  | .ALU_XOR      => 17
  | .ALU_ANDN     => 18
  | .ALU_ORN      => 19
  | .ALU_XNOR     => 20
  | .ALU_SLL      => 21
  | .ALU_SRL      => 22
  | .ALU_SRA      => 23
  | .ALU_ROL      => 24
  | .ALU_ROR      => 25
  | .ALU_SLT      => 26
  | .ALU_SLTU     => 27
  | .ALU_MIN      => 28
  | .ALU_MAX      => 29
  | .ALU_MINU     => 30
  | .ALU_MAXU     => 31
  | .ALU_REV8     => 32
  | .ALU_ORCB     => 33
  | .ALU_CLZ      => 34
  | .ALU_CTZ      => 35
  | .ALU_CPOP     => 36
  | .ALU_CLMUL    => 37
  | .ALU_CLMULH   => 38
  | .ALU_CLMULR   => 39
  | .ALU_SH1ADD   => 40
  | .ALU_SH2ADD   => 41
  | .ALU_SH3ADD   => 42
  | .ALU_BSET     => 43
  | .ALU_BCLR     => 44
  | .ALU_BINV     => 45
  | .ALU_BEXT     => 46
  | .ALU_SEXT_W   => 47
  | .ALU_ZEXT_W   => 48
  | .ALU_ROLW     => 50
  | .ALU_RORW     => 51
  | .ALU_CTZW     => 52

/-- Decode 6-bit natural to FallbackOp -/
def FallbackOp.fromNat : Nat → FallbackOp
  | 0  => .DRAIN
  | 1  => .DONE
  | 2  => .TRAP_ILLEGAL
  | 3  => .JMP
  | 4  => .JMP_ZERO
  | 5  => .JMP_NZERO
  | 6  => .JMP_EQ
  | 7  => .LOAD_RS1
  | 8  => .LOAD_RS2
  | 9  => .LOAD_IMM
  | 10 => .LOAD_INSN
  | 11 => .LOAD_PC
  | 12 => .MOV_TO_RD
  | 49 => .LOAD_SHAMT
  | 13 => .ALU_ADD
  | 14 => .ALU_SUB
  | 15 => .ALU_AND
  | 16 => .ALU_OR
  | 17 => .ALU_XOR
  | 18 => .ALU_ANDN
  | 19 => .ALU_ORN
  | 20 => .ALU_XNOR
  | 21 => .ALU_SLL
  | 22 => .ALU_SRL
  | 23 => .ALU_SRA
  | 24 => .ALU_ROL
  | 25 => .ALU_ROR
  | 26 => .ALU_SLT
  | 27 => .ALU_SLTU
  | 28 => .ALU_MIN
  | 29 => .ALU_MAX
  | 30 => .ALU_MINU
  | 31 => .ALU_MAXU
  | 32 => .ALU_REV8
  | 33 => .ALU_ORCB
  | 34 => .ALU_CLZ
  | 35 => .ALU_CTZ
  | 36 => .ALU_CPOP
  | 37 => .ALU_CLMUL
  | 38 => .ALU_CLMULH
  | 39 => .ALU_CLMULR
  | 40 => .ALU_SH1ADD
  | 41 => .ALU_SH2ADD
  | 42 => .ALU_SH3ADD
  | 43 => .ALU_BSET
  | 44 => .ALU_BCLR
  | 45 => .ALU_BINV
  | 46 => .ALU_BEXT
  | 47 => .ALU_SEXT_W
  | 48 => .ALU_ZEXT_W
  | 50 => .ALU_ROLW
  | 51 => .ALU_RORW
  | 52 => .ALU_CTZW
  | _  => .DONE

theorem FallbackOp.roundtrip (op : FallbackOp) : FallbackOp.fromNat op.toNat = op := by
  cases op <;> rfl

/-- Control Store Word (32 bits):
    [31:26] opcode (6 bits, 0-63)
    [25:24] dst    (2 bits, temp0..temp3)
    [23:22] src1   (2 bits, temp0..temp3)
    [21:20] src2   (2 bits, temp0..temp3)
    [19:16] reserved (4 bits)
    [15:0]  imm    (16 bits, immediate / jump target)
-/
structure FallbackEntry where
  opcode : FallbackOp
  dst    : Fin 4
  src1   : Fin 4
  src2   : Fin 4
  imm    : Fin 65536
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Encode FallbackEntry to 32-bit natural -/
def FallbackEntry.encode (e : FallbackEntry) : Nat :=
  (e.opcode.toNat <<< 26) |||
  (e.dst.val <<< 24) |||
  (e.src1.val <<< 22) |||
  (e.src2.val <<< 20) |||
  e.imm.val

/-- Decode 32-bit natural to FallbackEntry -/
def FallbackEntry.decode (n : Nat) : FallbackEntry :=
  { opcode := FallbackOp.fromNat ((n >>> 26) % 64)
    dst    := ⟨(n >>> 24) % 4, by omega⟩
    src1   := ⟨(n >>> 22) % 4, by omega⟩
    src2   := ⟨(n >>> 20) % 4, by omega⟩
    imm    := ⟨n % 65536, by omega⟩ }

/-- State of the Fallback Emulation Sequencer -/
structure FallbackState where
  active    : Bool       -- Sequencer running
  upc       : Fin 512    -- Micro-PC (512-entry control store)
  temp0     : UInt64     -- Scratchpad register 0
  temp1     : UInt64     -- Scratchpad register 1
  temp2     : UInt64     -- Scratchpad register 2
  temp3     : UInt64     -- Scratchpad register 3
  rs1Val    : UInt64     -- Captured source operand 1
  rs2Val    : UInt64     -- Captured source operand 2
  rawInsn   : UInt32     -- Captured 32-bit instruction
  pcVal     : UInt64     -- Captured PC
  rdTag     : Fin 64     -- Captured physical destination register
  waitDrain : Bool       -- Waiting for pipeline drain
  trapTaken : Bool       -- High if trapped
  trapCause : UInt64     -- Architectural mcause (2 for illegal insn)
  trapVal   : UInt64     -- Architectural mtval (raw_insn)
  redirPC   : UInt64     -- Next PC (pc+4 or mtvec)
  done      : Bool       -- Finished sequence
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Idle state -/
def FallbackState.idle : FallbackState :=
  { active    := false
    upc       := ⟨0, by omega⟩
    temp0     := 0
    temp1     := 0
    temp2     := 0
    temp3     := 0
    rs1Val    := 0
    rs2Val    := 0
    rawInsn   := 0
    pcVal     := 0
    rdTag     := ⟨0, by omega⟩
    waitDrain := false
    trapTaken := false
    trapCause := 0
    trapVal   := 0
    redirPC   := 0
    done      := false }

end Shoumei.RISCV.Microcode
