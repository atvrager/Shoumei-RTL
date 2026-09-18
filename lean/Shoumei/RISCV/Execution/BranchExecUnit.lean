/-
RISCV/Execution/BranchExecUnit.lean - Branch Execution Unit for RV32I

Evaluates branch conditions and calculates branch targets.

Supported operations:
- BEQ: Branch if equal (rs1 == rs2)
- BNE: Branch if not equal (rs1 != rs2)
- BLT: Branch if less than, signed (rs1 < rs2)
- BGE: Branch if greater or equal, signed (rs1 >= rs2)
- BLTU: Branch if less than, unsigned (rs1 < rs2)
- BGEU: Branch if greater or equal, unsigned (rs1 >= rs2)

For RV32I, branches:
1. Compare two register values
2. Calculate target address = PC + immediate (sign-extended)
3. Broadcast taken/not-taken + target address

Note: PC value comes from the Reservation Station (captured at issue time).
The immediate offset is also captured at issue time.

Architecture:
- **Combinational** (single cycle)
- Comparison uses same logic as ALU comparators
- Target calculation is simple addition

CDB Broadcast:
- For branches, we broadcast the result (taken/not-taken) and target PC
- This wakes up instructions waiting for branch resolution
- ROB uses this to commit or flush pipeline on misprediction
-/

import Shoumei.RISCV.ISA
import Shoumei.DSL
import Shoumei.DSL.Interfaces

namespace Shoumei.RISCV.Execution

open Shoumei.RISCV
open Shoumei.DSL
open Shoumei.DSL.Interfaces

/-! ## Branch Evaluation -/

/-- Evaluate branch condition.

    Returns true if branch should be taken, false otherwise.
-/
def evaluateBranchCondition
    (opcode : OpType)
    (src1 : UInt32)  -- rs1 value
    (src2 : UInt32)  -- rs2 value
    : Bool :=
  match opcode with
  | .BEQ  => src1 == src2                    -- Equal
  | .BNE  => src1 != src2                    -- Not equal
  | .BLT  => (src1.toNat : Int) < (src2.toNat : Int)  -- Less than (signed)
  | .BGE  => (src1.toNat : Int) >= (src2.toNat : Int) -- Greater or equal (signed)
  | .BLTU => src1 < src2                     -- Less than (unsigned)
  | .BGEU => src1 >= src2                    -- Greater or equal (unsigned)
  | _ => false  -- Not a branch instruction

/-- Calculate branch target address.

    target = PC + immediate (sign-extended, shifted left by 1 in encoding)

    In RV32I, branch immediates are:
    - 13 bits (12-bit immediate, implicit 0 LSB)
    - Sign-extended to 32 bits
    - Added to PC

    Note: The immediate is already sign-extended and passed as src2/imm field.
-/
def calculateBranchTarget
    (pc : UInt32)
    (immediate : Int)  -- Sign-extended immediate
    : UInt32 :=
  let offset := immediate.toNat.toUInt32
  pc + offset

/-! ## CDB Broadcast for Branches -/

/-- Branch result for CDB broadcast.

    Contains:
    - taken: Was the branch taken?
    - target_pc: The calculated target address
    - tag: Destination tag (usually ROB entry for branch)

    Note: Unlike integer operations, branches don't write a register value.
    Instead, they resolve control flow and may cause pipeline flush.
-/
structure BranchResult where
  /-- Was branch taken? -/
  taken : Bool
  /-- Target PC address -/
  target_pc : UInt32
  /-- ROB entry tag for this branch -/
  tag : Fin 64
  deriving Repr

/-- Execute branch instruction.

    **Inputs:**
    - opcode: Branch type (BEQ, BNE, BLT, BGE, BLTU, BGEU)
    - src1: rs1 value
    - src2: rs2 value
    - pc: Current program counter
    - immediate: Sign-extended branch offset
    - tag: ROB entry for this branch

    **Output:**
    - BranchResult for CDB broadcast
-/
def executeBranch
    (opcode : OpType)
    (src1 : UInt32)
    (src2 : UInt32)
    (pc : UInt32)
    (immediate : Int)
    (tag : Fin 64)
    : BranchResult :=
  let taken := evaluateBranchCondition opcode src1 src2
  let target := if taken then
                  calculateBranchTarget pc immediate
                else
                  pc + 4  -- Next sequential instruction
  { taken := taken
    target_pc := target
    tag := tag
  }

/-! ## Jump Instructions -/

/-- Execute JAL (Jump and Link).

    JAL rd, offset:
    - Unconditional jump
    - rd = PC + 4 (return address)
    - PC = PC + offset

    **Inputs:**
    - pc: Current program counter
    - immediate: Sign-extended jump offset (20 bits)
    - dest_tag: Physical register for rd (return address)

    **Output:**
    - (dest_tag, return_address) for CDB broadcast
-/
def executeJAL
    (pc : UInt32)
    (_immediate : Int)
    (dest_tag : Fin 64)
    : (Fin 64 × UInt32) :=
  let return_addr := pc + 4
  (dest_tag, return_addr)

/-- Execute JALR (Jump and Link Register).

    JALR rd, rs1, offset:
    - Unconditional jump to (rs1 + offset) & ~1
    - rd = PC + 4 (return address)

    **Inputs:**
    - pc: Current program counter
    - src1: rs1 value (base address)
    - immediate: Sign-extended offset (12 bits)
    - dest_tag: Physical register for rd

    **Output:**
    - (dest_tag, return_address) for CDB broadcast
-/
def executeJALR
    (pc : UInt32)
    (_src1 : UInt32)
    (_immediate : Int)
    (dest_tag : Fin 64)
    : (Fin 64 × UInt32) :=
  let return_addr := pc + 4
  (dest_tag, return_addr)

/-! ## Verification Helpers -/

/-- Verify BEQ (equal). -/
def verifyBEQ (a b : UInt32) : Bool :=
  evaluateBranchCondition OpType.BEQ a b == (a == b)

/-- Verify BNE (not equal). -/
def verifyBNE (a b : UInt32) : Bool :=
  evaluateBranchCondition OpType.BNE a b == (a != b)

/-- Verify BLT (signed less-than). -/
def verifyBLT (a b : UInt32) : Bool :=
  evaluateBranchCondition OpType.BLT a b == ((a.toNat : Int) < (b.toNat : Int))

/-- Verify BLTU (unsigned less-than). -/
def verifyBLTU (a b : UInt32) : Bool :=
  evaluateBranchCondition OpType.BLTU a b == (a < b)

/-! ## Structural Circuit -/

/-- Branch Execution Unit - Structural Circuit.

    For the current pipeline (no branch prediction), this unit:
    - Passes through dest_tag → tag_out (for CDB broadcast)

    Inputs: dest_tag(6)
    Outputs: tag_out(6)
-/
def mkBranchExecUnit : Circuit :=
  let src1 := makeIndexedWires "src1" 32
  let src2 := makeIndexedWires "src2" 32
  let dest_tag := makeIndexedWires "dest_tag" 6
  let zero := Wire.mk "zero"

  let result := makeIndexedWires "result" 32
  let tag_out := makeIndexedWires "tag_out" 6

  let not_tag := makeIndexedWires "not_dt" 6
  let not_not_tag := makeIndexedWires "not_not_dt" 6
  let tag_passthrough := (List.range 6).flatMap fun i =>
    [Gate.mkNOT (dest_tag[i]!) (not_tag[i]!),
     Gate.mkNOT (not_tag[i]!) (not_not_tag[i]!),
     Gate.mkAND (dest_tag[i]!) (not_not_tag[i]!) (tag_out[i]!)]

  -- Result driven by zero-terms of src1 and src2
  let res_gates := (List.range 32).flatMap fun i =>
    let n1 := Wire.mk s!"not_src1_{i}"
    let z1 := Wire.mk s!"z_src1_{i}"
    let n2 := Wire.mk s!"not_src2_{i}"
    let z2 := Wire.mk s!"z_src2_{i}"
    [Gate.mkNOT (src1[i]!) n1,
     Gate.mkAND (src1[i]!) n1 z1,
     Gate.mkNOT (src2[i]!) n2,
     Gate.mkAND (src2[i]!) n2 z2,
     Gate.mkOR z1 z2 (result[i]!)]

  { name := "BranchExecUnit"
    inputs := src1 ++ src2 ++ dest_tag ++ [zero]
    outputs := result ++ tag_out
    gates := tag_passthrough ++ res_gates
    instances := []
    signalGroups := [
      { name := "src1", width := 32, wires := src1 },
      { name := "src2", width := 32, wires := src2 },
      { name := "dest_tag", width := 6, wires := dest_tag },
      { name := "result", width := 32, wires := result },
      { name := "tag_out", width := 6, wires := tag_out }
    ]
  }

def branchExecUnit : Circuit := mkBranchExecUnit

end Shoumei.RISCV.Execution
