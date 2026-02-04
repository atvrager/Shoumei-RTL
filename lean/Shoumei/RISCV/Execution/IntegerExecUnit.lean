/-
RISCV/Execution/IntegerExecUnit.lean - Integer Execution Unit for RV32I

Wraps the ALU32 combinational circuit to create an execution unit that:
1. Receives dispatched instructions from Reservation Stations
2. Executes integer operations (arithmetic, logic, shifts, comparisons)
3. Broadcasts results on the Common Data Bus (CDB)

Supported operations (from ALU32):
- Arithmetic: ADD, SUB, SLT, SLTU
- Logic: AND, OR, XOR
- Shifts: SLL, SRL, SRA

For RV32I, this handles all register-register and register-immediate ALU operations:
- R-type: ADD, SUB, AND, OR, XOR, SLT, SLTU, SLL, SRL, SRA
- I-type: ADDI, ANDI, ORI, XORI, SLTI, SLTIU, SLLI, SRLI, SRAI

Immediate handling:
- The Reservation Station already captured the immediate value in src2_data
- This unit treats it as a regular operand (no distinction needed)

Architecture:
- **Combinational execution** (single cycle)
- Takes (opcode, src1, src2, dest_tag) from RS
- Returns (dest_tag, result) for CDB broadcast
- Reuses verified ALU32 from Phase 1
-/

import Shoumei.RISCV.ISA
import Shoumei.Circuits.Combinational.ALU

namespace Shoumei.RISCV.Execution

open Shoumei.RISCV

/-! ## Operation Encoding -/

/-- Map RISC-V OpType to ALU32 opcode (4 bits).

    ALU32 opcode encoding:
    - 0000: ADD
    - 0001: SUB
    - 0010: SLT (signed less-than)
    - 0011: SLTU (unsigned less-than)
    - 0100: AND
    - 0101: OR
    - 0110: XOR
    - 0111: SLL (shift left logical)
    - 1000: SRL (shift right logical)
    - 1001: SRA (shift right arithmetic)

    Note: Immediate variants (ADDI, ANDI, etc.) use the same ALU operations,
    just with src2 = immediate value (already handled by RS).
-/
def opTypeToALUOpcode (op : OpType) : Nat :=
  match op with
  | .ADD | .ADDI  => 0  -- ADD (same for immediate)
  | .SUB          => 1  -- SUB (no SUBI in RV32I)
  | .SLT | .SLTI  => 2  -- SLT signed
  | .SLTU | .SLTIU => 3  -- SLTU unsigned
  | .AND | .ANDI  => 4  -- AND bitwise
  | .OR | .ORI    => 5  -- OR bitwise
  | .XOR | .XORI  => 6  -- XOR bitwise
  | .SLL | .SLLI  => 7  -- Shift left logical
  | .SRL | .SRLI  => 8  -- Shift right logical
  | .SRA | .SRAI  => 9  -- Shift right arithmetic
  -- Non-ALU operations (shouldn't reach IntegerExecUnit)
  | .BEQ | .BNE | .BLT | .BGE | .BLTU | .BGEU => 0  -- Branches (handled by BranchUnit)
  | .JAL | .JALR => 0  -- Jumps (handled by JumpUnit)
  | .LB | .LH | .LW | .LBU | .LHU => 0  -- Loads (handled by MemoryUnit)
  | .SB | .SH | .SW => 0  -- Stores (handled by MemoryUnit)
  | .LUI | .AUIPC => 0  -- Upper immediates (special handling)
  | .FENCE | .ECALL | .EBREAK => 0  -- System ops (special handling)
  -- M extension operations (handled by MulDivExecUnit)
  | .MUL | .MULH | .MULHSU | .MULHU => 0
  | .DIV | .DIVU | .REM | .REMU => 0

/-! ## Behavioral Model -/

/-- Execute an integer operation.

    **Inputs:**
    - opcode: RISC-V operation type (ADD, SUB, AND, etc.)
    - src1: First operand value (32 bits)
    - src2: Second operand value (32 bits, could be register or immediate)
    - dest_tag: Physical register tag for result

    **Output:**
    - (dest_tag, result): Tuple for CDB broadcast

    **Execution:**
    - Convert OpType to ALU opcode
    - Execute combinationally using ALU32 semantics
    - Return tagged result

    **Timing:**
    - Single cycle (combinational)
    - In hardware: ~2-3ns for 32-bit ALU at modern process nodes
-/
def executeInteger
    (opcode : OpType)
    (src1 : UInt32)
    (src2 : UInt32)
    (dest_tag : Fin 64)
    : (Fin 64 × UInt32) :=
  let alu_op := opTypeToALUOpcode opcode

  -- Execute using ALU semantics (simplified behavioral model)
  let result := match alu_op with
    | 0 => src1 + src2  -- ADD
    | 1 => src1 - src2  -- SUB
    | 2 =>  -- SLT (signed comparison)
        if (src1.toNat : Int) < (src2.toNat : Int) then 1 else 0
    | 3 =>  -- SLTU (unsigned comparison)
        if src1 < src2 then 1 else 0
    | 4 => src1 &&& src2  -- AND
    | 5 => src1 ||| src2  -- OR
    | 6 => src1 ^^^ src2  -- XOR
    | 7 =>  -- SLL (shift left logical)
        let shamt := src2.toNat % 32
        (src1.toNat <<< shamt).toUInt32
    | 8 =>  -- SRL (shift right logical)
        let shamt := src2.toNat % 32
        (src1.toNat >>> shamt).toUInt32
    | 9 =>  -- SRA (shift right arithmetic)
        -- Note: UInt32 doesn't have arithmetic shift, use Int conversion
        let signed_src1 := (src1.toNat : Int)
        let shift_amount := src2.toNat % 32
        let shifted := signed_src1 >>> shift_amount
        shifted.toNat.toUInt32
    | _ => 0  -- Invalid opcode (shouldn't happen)

  (dest_tag, result)

/-! ## Common Data Bus (CDB) Interface -/

/-- CDB broadcast message.

    When an execution unit completes, it broadcasts on the CDB:
    - tag: Which physical register is being written
    - data: The computed value

    All Reservation Stations snoop this broadcast to wake up waiting instructions.
-/
structure CDBBroadcast where
  /-- Physical register tag being written -/
  tag : Fin 64
  /-- Computed data value -/
  data : UInt32
  deriving Repr

/-- Execute and create CDB broadcast.

    Convenience function that wraps executeInteger and packages result as CDB broadcast.
-/
def executeToCDB
    (opcode : OpType)
    (src1 : UInt32)
    (src2 : UInt32)
    (dest_tag : Fin 64)
    : CDBBroadcast :=
  let (tag, result) := executeInteger opcode src1 src2 dest_tag
  { tag := tag, data := result }

/-! ## Integration with Reservation Station -/

/-- Execute instruction from RS dispatch.

    This is the main entry point when a Reservation Station dispatches
    a ready instruction to the Integer Execution Unit.

    **Input format (from RS.dispatch):**
    - (opcode, src1_data, src2_data, dest_tag)

    **Output:**
    - CDB broadcast ready for snooping by all RS entries

    **Example workflow:**
    1. RS dispatches: (ADD, 100, 200, p32)
    2. IntegerExecUnit executes: 100 + 200 = 300
    3. CDB broadcasts: (p32, 300)
    4. All RS entries snoop and wake up instructions waiting for p32
-/
def executeFromRS
    (dispatch_bundle : OpType × UInt32 × UInt32 × Fin 64)
    : CDBBroadcast :=
  let (opcode, src1, src2, dest_tag) := dispatch_bundle
  executeToCDB opcode src1 src2 dest_tag

/-! ## Verification Helpers -/

/-- Verify ADD operation. -/
def verifyADD (a b : UInt32) : Bool :=
  let result := executeInteger OpType.ADD a b 0
  result.2 == a + b

/-- Verify SUB operation. -/
def verifySUB (a b : UInt32) : Bool :=
  let result := executeInteger OpType.SUB a b 0
  result.2 == a - b

/-- Verify AND operation. -/
def verifyAND (a b : UInt32) : Bool :=
  let result := executeInteger OpType.AND a b 0
  result.2 == (a &&& b)

/-- Verify OR operation. -/
def verifyOR (a b : UInt32) : Bool :=
  let result := executeInteger OpType.OR a b 0
  result.2 == (a ||| b)

/-- Verify XOR operation. -/
def verifyXOR (a b : UInt32) : Bool :=
  let result := executeInteger OpType.XOR a b 0
  result.2 == (a ^^^ b)

/-- Verify shift left logical. -/
def verifySLL (a : UInt32) (shamt : Nat) : Bool :=
  let result := executeInteger OpType.SLL a (shamt.toUInt32) 0
  result.2 == ((a.toNat <<< (shamt % 32)).toUInt32)

/-- Verify unsigned less-than. -/
def verifySLTU (a b : UInt32) : Bool :=
  let result := executeInteger OpType.SLTU a b 0
  if a < b then result.2 == 1 else result.2 == 0

/-! ## Structural Circuit -/

open Shoumei
open Shoumei.Circuits.Combinational

/-- Build Integer Execution Unit structural circuit.

    **Architecture:**
    - Wraps verified ALU32 from Phase 1
    - Adds tag pass-through for CDB broadcast
    - Single-cycle combinational execution

    **Inputs:**
    - a[31:0]: Source operand 1
    - b[31:0]: Source operand 2
    - opcode[3:0]: ALU operation selector (encoded from OpType)
    - dest_tag[5:0]: Physical register tag for result
    - zero, one: Constant inputs (for ALU32)

    **Outputs:**
    - result[31:0]: ALU computation result
    - tag_out[5:0]: Pass-through of dest_tag (for CDB broadcast)

    **Instances:**
    - ALU32: 32-bit ALU (verified in Phase 1)

    **Gates:**
    - 6 BUF gates for tag pass-through

    **Note:** Opcode encoding must match ALU32:
    - 0000=ADD, 0001=SUB, 0010=SLT, 0011=SLTU
    - 0100=AND, 0101=OR, 0110=XOR
    - 0111=SLL, 1000=SRL, 1001=SRA
-/
def mkIntegerExecUnit : Circuit :=
  let a := makeIndexedWires "a" 32
  let b := makeIndexedWires "b" 32
  let opcode := makeIndexedWires "opcode" 4
  let dest_tag := makeIndexedWires "dest_tag" 6
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- Output wires
  let result := makeIndexedWires "result" 32
  let tag_out := makeIndexedWires "tag_out" 6

  -- Instance ALU32 (reuse verified module from Phase 1)
  let alu_inst : CircuitInstance := {
    moduleName := "ALU32"
    instName := "u_alu"
    portMap := [
      ("a", a),
      ("b", b),
      ("op", opcode),
      ("zero", [zero]),
      ("one", [one]),
      ("result", result)
    ].flatMap (fun (name, wires) => wires.map (fun w => (name, w)))
  }

  -- Tag pass-through (BUF gates to maintain structural clarity)
  let tag_passthrough := List.zipWith (fun src dst =>
    Gate.mkBUF src dst
  ) dest_tag tag_out

  { name := "IntegerExecUnit"
    inputs := a ++ b ++ opcode ++ dest_tag ++ [zero, one]
    outputs := result ++ tag_out
    gates := tag_passthrough
    instances := [alu_inst]
    -- V2 codegen annotations
    signalGroups := [
      { name := "a", width := 32, wires := a },
      { name := "b", width := 32, wires := b },
      { name := "opcode", width := 4, wires := opcode },
      { name := "dest_tag", width := 6, wires := dest_tag },
      { name := "result", width := 32, wires := result },
      { name := "tag_out", width := 6, wires := tag_out }
    ]
  }

/-- Convenience constructors for specific configurations -/
def integerExecUnit : Circuit := mkIntegerExecUnit

end Shoumei.RISCV.Execution
