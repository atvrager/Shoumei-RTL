/-
  RISC-V Instruction Semantics

  Defines the operational semantics for all RV32I instructions.
  This is the ISA specification - what each instruction actually does.
-/

import Shoumei.RISCV.ISA
import Shoumei.RISCV.Decoder

namespace Shoumei.RISCV

/-- CPU architectural state (simplified for now) -/
structure ArchState where
  /-- Program counter (32-bit) -/
  pc : UInt32
  /-- 32 architectural registers (x0 is always 0) -/
  regs : Fin 32 → UInt32
  /-- Memory (simplified: address → value) -/
  memory : UInt32 → UInt32
  deriving Inhabited

instance : Repr ArchState where
  reprPrec s _ := s!"⟨pc: {s.pc}⟩"

/-- Result of instruction execution -/
inductive ExecResult where
  | ok (newState : ArchState)
  | illegalInstruction
  | ecall
  | ebreak
  deriving Repr

/-- Read register value (x0 is always 0) -/
def ArchState.readReg (state : ArchState) (reg : Fin 32) : UInt32 :=
  if reg.val = 0 then 0 else state.regs reg

/-- Write register value (writing to x0 is a no-op) -/
def ArchState.writeReg (state : ArchState) (reg : Fin 32) (value : UInt32) : ArchState :=
  if reg.val = 0 then
    state  -- Writing to x0 has no effect
  else
    { state with regs := fun r => if r = reg then value else state.regs r }

/-- Read memory word (32-bit aligned) -/
def ArchState.readMem32 (state : ArchState) (addr : UInt32) : UInt32 :=
  state.memory addr

/-- Write memory word (32-bit aligned) -/
def ArchState.writeMem32 (state : ArchState) (addr : UInt32) (value : UInt32) : ArchState :=
  { state with memory := fun a => if a = addr then value else state.memory a }

/-- Read memory halfword (16-bit aligned, sign-extended) -/
def ArchState.readMem16 (state : ArchState) (addr : UInt32) (unsigned : Bool) : UInt32 :=
  let halfword := (state.memory (addr &&& 0xFFFFFFFC)).land 0xFFFF
  if unsigned then
    halfword
  else
    -- Sign extend from 16 bits
    if (halfword &&& 0x8000) != 0 then
      halfword ||| 0xFFFF0000
    else
      halfword

/-- Read memory byte (sign-extended or zero-extended) -/
def ArchState.readMem8 (state : ArchState) (addr : UInt32) (unsigned : Bool) : UInt32 :=
  let byte := (state.memory (addr &&& 0xFFFFFFFC)).land 0xFF
  if unsigned then
    byte
  else
    -- Sign extend from 8 bits
    if (byte &&& 0x80) != 0 then
      byte ||| 0xFFFFFF00
    else
      byte

/-- Increment PC by 4 (next instruction) -/
def ArchState.nextPC (state : ArchState) : ArchState :=
  { state with pc := state.pc + 4 }

/-- Set PC to specific address -/
def ArchState.setPC (state : ArchState) (newPC : UInt32) : ArchState :=
  { state with pc := newPC }

/-! ## ALU Operations -/

/-- Convert UInt32 to signed Int32 interpretation -/
def toInt32 (x : UInt32) : Int :=
  if x.toNat >= 2^31 then
    Int.ofNat x.toNat - Int.ofNat (2^32)
  else
    Int.ofNat x.toNat

/-- Execute ALU operation (arithmetic and logic) -/
def executeALU (op : OpType) (a b : UInt32) : UInt32 :=
  match op with
  | .ADD   => a + b
  | .SUB   => a - b
  | .AND   => a &&& b
  | .OR    => a ||| b
  | .XOR   => a ^^^ b
  | .SLT   => if toInt32 a < toInt32 b then 1 else 0  -- Signed comparison
  | .SLTU  => if a < b then 1 else 0                  -- Unsigned comparison
  | .SLL   => a <<< UInt32.ofNat ((b &&& 0x1F).toNat)  -- Shift left logical
  | .SRL   => a >>> UInt32.ofNat ((b &&& 0x1F).toNat)  -- Shift right logical
  | .SRA   =>                                          -- Shift right arithmetic
      let shamt := (b &&& 0x1F).toNat
      let shamtU32 := UInt32.ofNat shamt
      let signBit := (a >>> UInt32.ofNat 31) &&& 1
      if signBit == 1 then
        -- Negative: fill with 1s
        let shifted := a >>> shamtU32
        let fillBits := 0xFFFFFFFF <<< UInt32.ofNat (32 - shamt)
        shifted ||| fillBits
      else
        -- Positive: fill with 0s
        a >>> shamtU32
  | _ => 0  -- Not an ALU op

/-! ## M Extension: Multiply/Divide Operations -/

/-- Convert Int to UInt32 (handling negative values via two's complement) -/
private def intToUInt32 (x : Int) : UInt32 :=
  UInt32.ofNat ((x % (2^32 : Int)).toNat)

/-- Execute M-extension multiply/divide operation.
    All operations take rs1 and rs2 as 32-bit values.
    Signed interpretation uses toInt32.

    Edge cases per RISC-V spec:
    - DIV/REM by zero: DIV returns -1 (0xFFFFFFFF), REM returns dividend
    - DIVU/REMU by zero: DIVU returns 2^32-1 (0xFFFFFFFF), REMU returns dividend
    - Signed overflow (-2^31 / -1): DIV returns -2^31 (0x80000000), REM returns 0
-/
def executeMulDiv (op : OpType) (a b : UInt32) : UInt32 :=
  match op with
  | .MUL =>
      -- Lower 32 bits of product
      let prod := a.toNat * b.toNat
      UInt32.ofNat (prod % (2^32))
  | .MULH =>
      -- Upper 32 bits of signed * signed
      let sa := toInt32 a
      let sb := toInt32 b
      let prod := sa * sb
      -- Arithmetic right shift by 32 to get upper bits
      intToUInt32 (prod / (2^32 : Int))
  | .MULHSU =>
      -- Upper 32 bits of signed * unsigned
      let sa := toInt32 a
      let ub := (b.toNat : Int)
      let prod := sa * ub
      intToUInt32 (prod / (2^32 : Int))
  | .MULHU =>
      -- Upper 32 bits of unsigned * unsigned
      let prod := a.toNat * b.toNat
      UInt32.ofNat (prod / (2^32))
  | .DIV =>
      -- Signed division
      if b == 0 then
        0xFFFFFFFF  -- Division by zero: result is -1
      else
        let sa := toInt32 a
        let sb := toInt32 b
        if sa == -(2^31 : Int) && sb == -1 then
          -- Overflow: -2^31 / -1 doesn't fit in 32 bits -> result is -2^31
          0x80000000
        else
          intToUInt32 (sa / sb)
  | .DIVU =>
      -- Unsigned division
      if b == 0 then
        0xFFFFFFFF  -- Division by zero: result is 2^32 - 1
      else
        UInt32.ofNat (a.toNat / b.toNat)
  | .REM =>
      -- Signed remainder
      if b == 0 then
        a  -- Division by zero: result is dividend
      else
        let sa := toInt32 a
        let sb := toInt32 b
        if sa == -(2^31 : Int) && sb == -1 then
          0  -- Overflow: -2^31 % -1 = 0
        else
          intToUInt32 (sa % sb)
  | .REMU =>
      -- Unsigned remainder
      if b == 0 then
        a  -- Division by zero: result is dividend
      else
        UInt32.ofNat (a.toNat % b.toNat)
  | _ => 0  -- Not a MulDiv op

/-! ## Instruction Execution -/

/-- Execute a single decoded instruction -/
def executeInstruction (state : ArchState) (decoded : DecodedInstruction) : ExecResult :=
  match decoded.opType with

  -- R-type ALU operations (register-register)
  | .ADD | .SUB | .AND | .OR | .XOR | .SLT | .SLTU | .SLL | .SRL | .SRA =>
    match decoded.rd, decoded.rs1, decoded.rs2 with
    | some rd, some rs1, some rs2 =>
      let val1 := state.readReg rs1
      let val2 := state.readReg rs2
      let result := executeALU decoded.opType val1 val2
      .ok (state.writeReg rd result |>.nextPC)
    | _, _, _ => .illegalInstruction

  -- M-extension (register-register multiply/divide)
  | .MUL | .MULH | .MULHSU | .MULHU | .DIV | .DIVU | .REM | .REMU =>
    match decoded.rd, decoded.rs1, decoded.rs2 with
    | some rd, some rs1, some rs2 =>
      let val1 := state.readReg rs1
      let val2 := state.readReg rs2
      let result := executeMulDiv decoded.opType val1 val2
      .ok (state.writeReg rd result |>.nextPC)
    | _, _, _ => .illegalInstruction

  -- I-type ALU operations (register-immediate)
  | .ADDI | .ANDI | .ORI | .XORI | .SLTI | .SLTIU | .SLLI | .SRLI | .SRAI =>
    match decoded.rd, decoded.rs1, decoded.imm with
    | some rd, some rs1, some imm =>
      let val1 := state.readReg rs1
      let val2 := UInt32.ofNat imm.toNat
      -- Map I-type op to corresponding R-type for executeALU
      let aluOp := match decoded.opType with
        | .ADDI  => OpType.ADD
        | .ANDI  => OpType.AND
        | .ORI   => OpType.OR
        | .XORI  => OpType.XOR
        | .SLTI  => OpType.SLT
        | .SLTIU => OpType.SLTU
        | .SLLI  => OpType.SLL
        | .SRLI  => OpType.SRL
        | .SRAI  => OpType.SRA
        | _ => OpType.ADD  -- unreachable
      let result := executeALU aluOp val1 val2
      .ok (state.writeReg rd result |>.nextPC)
    | _, _, _ => .illegalInstruction

  -- Load instructions
  | .LW =>  -- Load word
    match decoded.rd, decoded.rs1, decoded.imm with
    | some rd, some rs1, some offset =>
      let addr := state.readReg rs1 + UInt32.ofNat offset.toNat
      let value := state.readMem32 addr
      .ok (state.writeReg rd value |>.nextPC)
    | _, _, _ => .illegalInstruction

  | .LH =>  -- Load halfword (sign-extended)
    match decoded.rd, decoded.rs1, decoded.imm with
    | some rd, some rs1, some offset =>
      let addr := state.readReg rs1 + UInt32.ofNat offset.toNat
      let value := state.readMem16 addr false
      .ok (state.writeReg rd value |>.nextPC)
    | _, _, _ => .illegalInstruction

  | .LHU =>  -- Load halfword unsigned
    match decoded.rd, decoded.rs1, decoded.imm with
    | some rd, some rs1, some offset =>
      let addr := state.readReg rs1 + UInt32.ofNat offset.toNat
      let value := state.readMem16 addr true
      .ok (state.writeReg rd value |>.nextPC)
    | _, _, _ => .illegalInstruction

  | .LB =>  -- Load byte (sign-extended)
    match decoded.rd, decoded.rs1, decoded.imm with
    | some rd, some rs1, some offset =>
      let addr := state.readReg rs1 + UInt32.ofNat offset.toNat
      let value := state.readMem8 addr false
      .ok (state.writeReg rd value |>.nextPC)
    | _, _, _ => .illegalInstruction

  | .LBU =>  -- Load byte unsigned
    match decoded.rd, decoded.rs1, decoded.imm with
    | some rd, some rs1, some offset =>
      let addr := state.readReg rs1 + UInt32.ofNat offset.toNat
      let value := state.readMem8 addr true
      .ok (state.writeReg rd value |>.nextPC)
    | _, _, _ => .illegalInstruction

  -- Store instructions
  | .SW =>  -- Store word
    match decoded.rs1, decoded.rs2, decoded.imm with
    | some rs1, some rs2, some offset =>
      let addr := state.readReg rs1 + UInt32.ofNat offset.toNat
      let value := state.readReg rs2
      .ok (state.writeMem32 addr value |>.nextPC)
    | _, _, _ => .illegalInstruction

  | .SH =>  -- Store halfword
    match decoded.rs1, decoded.rs2, decoded.imm with
    | some rs1, some rs2, some offset =>
      let addr := state.readReg rs1 + UInt32.ofNat offset.toNat
      let value := state.readReg rs2 &&& 0xFFFF  -- Only lower 16 bits
      .ok (state.writeMem32 addr value |>.nextPC)
    | _, _, _ => .illegalInstruction

  | .SB =>  -- Store byte
    match decoded.rs1, decoded.rs2, decoded.imm with
    | some rs1, some rs2, some offset =>
      let addr := state.readReg rs1 + UInt32.ofNat offset.toNat
      let value := state.readReg rs2 &&& 0xFF  -- Only lower 8 bits
      .ok (state.writeMem32 addr value |>.nextPC)
    | _, _, _ => .illegalInstruction

  -- Branch instructions
  | .BEQ =>  -- Branch if equal
    match decoded.rs1, decoded.rs2, decoded.imm with
    | some rs1, some rs2, some offset =>
      let val1 := state.readReg rs1
      let val2 := state.readReg rs2
      if val1 == val2 then
        .ok (state.setPC (state.pc + UInt32.ofNat offset.toNat))
      else
        .ok state.nextPC
    | _, _, _ => .illegalInstruction

  | .BNE =>  -- Branch if not equal
    match decoded.rs1, decoded.rs2, decoded.imm with
    | some rs1, some rs2, some offset =>
      let val1 := state.readReg rs1
      let val2 := state.readReg rs2
      if val1 != val2 then
        .ok (state.setPC (state.pc + UInt32.ofNat offset.toNat))
      else
        .ok state.nextPC
    | _, _, _ => .illegalInstruction

  | .BLT =>  -- Branch if less than (signed)
    match decoded.rs1, decoded.rs2, decoded.imm with
    | some rs1, some rs2, some offset =>
      let val1 := state.readReg rs1
      let val2 := state.readReg rs2
      if toInt32 val1 < toInt32 val2 then
        .ok (state.setPC (state.pc + UInt32.ofNat offset.toNat))
      else
        .ok state.nextPC
    | _, _, _ => .illegalInstruction

  | .BGE =>  -- Branch if greater or equal (signed)
    match decoded.rs1, decoded.rs2, decoded.imm with
    | some rs1, some rs2, some offset =>
      let val1 := state.readReg rs1
      let val2 := state.readReg rs2
      if toInt32 val1 >= toInt32 val2 then
        .ok (state.setPC (state.pc + UInt32.ofNat offset.toNat))
      else
        .ok state.nextPC
    | _, _, _ => .illegalInstruction

  | .BLTU =>  -- Branch if less than (unsigned)
    match decoded.rs1, decoded.rs2, decoded.imm with
    | some rs1, some rs2, some offset =>
      let val1 := state.readReg rs1
      let val2 := state.readReg rs2
      if val1 < val2 then
        .ok (state.setPC (state.pc + UInt32.ofNat offset.toNat))
      else
        .ok state.nextPC
    | _, _, _ => .illegalInstruction

  | .BGEU =>  -- Branch if greater or equal (unsigned)
    match decoded.rs1, decoded.rs2, decoded.imm with
    | some rs1, some rs2, some offset =>
      let val1 := state.readReg rs1
      let val2 := state.readReg rs2
      if val1 >= val2 then
        .ok (state.setPC (state.pc + UInt32.ofNat offset.toNat))
      else
        .ok state.nextPC
    | _, _, _ => .illegalInstruction

  -- Jump instructions
  | .JAL =>  -- Jump and link
    match decoded.rd, decoded.imm with
    | some rd, some offset =>
      let returnAddr := state.pc + 4
      let targetAddr := state.pc + UInt32.ofNat offset.toNat
      .ok (state.writeReg rd returnAddr |>.setPC targetAddr)
    | _, _ => .illegalInstruction

  | .JALR =>  -- Jump and link register
    match decoded.rd, decoded.rs1, decoded.imm with
    | some rd, some rs1, some offset =>
      let returnAddr := state.pc + 4
      let base := state.readReg rs1
      let targetAddr := (base + UInt32.ofNat offset.toNat) &&& 0xFFFFFFFE  -- Clear LSB
      .ok (state.writeReg rd returnAddr |>.setPC targetAddr)
    | _, _, _ => .illegalInstruction

  -- Upper immediate instructions
  | .LUI =>  -- Load upper immediate
    match decoded.rd, decoded.imm with
    | some rd, some imm =>
      let value := UInt32.ofNat imm.toNat  -- Already shifted by decoder
      .ok (state.writeReg rd value |>.nextPC)
    | _, _ => .illegalInstruction

  | .AUIPC =>  -- Add upper immediate to PC
    match decoded.rd, decoded.imm with
    | some rd, some imm =>
      let value := state.pc + UInt32.ofNat imm.toNat
      .ok (state.writeReg rd value |>.nextPC)
    | _, _ => .illegalInstruction

  -- System instructions
  | .FENCE =>
    -- FENCE is a no-op in our simplified model (no memory reordering)
    .ok state.nextPC

  | .FENCE_I =>
    -- FENCE.I: in the behavioral model, a no-op (pipeline drain is structural).
    -- The OoO pipeline handles this via serialize-then-flush in cpuStep.
    .ok state.nextPC

  | .ECALL =>
    -- Environment call - return special result
    .ecall

  | .EBREAK =>
    -- Breakpoint - return special result
    .ebreak

  -- F extension: not yet implemented in behavioral semantics
  | .FADD_S | .FSUB_S | .FMUL_S | .FDIV_S | .FSQRT_S
  | .FMADD_S | .FMSUB_S | .FNMADD_S | .FNMSUB_S
  | .FEQ_S | .FLT_S | .FLE_S
  | .FCVT_W_S | .FCVT_WU_S | .FCVT_S_W | .FCVT_S_WU
  | .FMV_X_W | .FMV_W_X | .FCLASS_S
  | .FMIN_S | .FMAX_S | .FSGNJ_S | .FSGNJN_S | .FSGNJX_S
  | .FLW | .FSW =>
    .illegalInstruction  -- TODO: implement FP semantics

  -- Zicsr: not yet implemented in behavioral semantics
  | .CSRRW | .CSRRS | .CSRRC | .CSRRWI | .CSRRSI | .CSRRCI =>
    .illegalInstruction  -- TODO: implement CSR semantics

/-- Execute a full instruction fetch-decode-execute cycle -/
def executeStep (state : ArchState) (instrDefs : List InstructionDef) : ExecResult :=
  -- Fetch instruction from memory at PC
  let instrWord := state.readMem32 state.pc

  -- Decode instruction
  match decodeInstruction instrDefs instrWord with
  | some decoded => executeInstruction state decoded
  | none => .illegalInstruction

end Shoumei.RISCV
