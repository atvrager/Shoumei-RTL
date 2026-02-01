/-
Circuits/Combinational/Shifter.lean - 32-bit Barrel Shifter

A barrel shifter performs shift operations on 32-bit values in a single cycle.
Supports three RISC-V shift operations:
- SLL: Shift Left Logical (fill with 0)
- SRL: Shift Right Logical (fill with 0)
- SRA: Shift Right Arithmetic (fill with sign bit)

Architecture:
- 5 stages for shifts up to 31 positions
- Each stage controlled by one bit of shamt (shift amount)
- Stage i: if shamt[i] then shift by 2^i, else pass through
- Final MUX selects between SLL/SRL/SRA based on op[1:0]

Stage structure (for right shift):
  Stage 0: shift by 1  if shamt[0]
  Stage 1: shift by 2  if shamt[1]
  Stage 2: shift by 4  if shamt[2]
  Stage 3: shift by 8  if shamt[3]
  Stage 4: shift by 16 if shamt[4]

Operation encoding:
- op = 00: SLL (shift left logical)
- op = 01: SRL (shift right logical)
- op = 10: SRA (shift right arithmetic)
- op = 11: Reserved (acts as SRA)

Implementation strategy:
Build three separate 5-stage shifters (SLL, SRL, SRA) and MUX between them.
This is simpler than trying to merge the logic, at the cost of more gates.

Gates per shifter: 32 bits × 5 stages = 160 MUXes
Total: 3 shifters × 160 + 64 final MUX = 544 gates
-/

import Shoumei.DSL

namespace Shoumei.Circuits.Combinational

open Shoumei

-- Helper: Create a list of wires with indexed names (private to this module)
private def makeIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}{i}")

-- Helper: Build one stage of left shifter
-- Shifts left by 'amount' positions if 'enable' is true
-- stage_in: current values, stage_out: shifted values, enable: shift enable, zero: constant 0 wire
-- width: bit width of the shifter
private def mkLeftShiftStage (stage_in : List Wire) (stage_out : List Wire)
                              (enable : Wire) (zero : Wire) (amount : Nat) (width : Nat) (_stageNum : Nat) : List Gate :=
  List.range width |>.map (fun i =>
    let shifted_input :=
      if i >= amount
      then stage_in.get! (i - amount)  -- Shift left: take from lower index
      else zero  -- Fill with 0 for left shift
    let current_input := stage_in.get! i
    -- MUX: if enable then use shifted value, else pass through
    Gate.mkMUX current_input shifted_input enable (stage_out.get! i)
  )

-- Helper: Build one stage of right shifter (logical)
-- Shifts right by 'amount' positions if 'enable' is true
-- Fills with 0 for logical shift
private def mkRightShiftStageLogical (stage_in : List Wire) (stage_out : List Wire)
                                      (enable : Wire) (zero : Wire) (amount : Nat) (width : Nat) (_stageNum : Nat) : List Gate :=
  List.range width |>.map (fun i =>
    let shifted_idx := i + amount
    let shifted_input :=
      if shifted_idx < width
      then stage_in.get! shifted_idx
      else zero  -- Fill with 0 for logical shift
    let current_input := stage_in.get! i
    Gate.mkMUX current_input shifted_input enable (stage_out.get! i)
  )

-- Helper: Build one stage of right shifter (arithmetic)
-- Shifts right by 'amount' positions if 'enable' is true
-- Fills with sign bit for arithmetic shift
private def mkRightShiftStageArithmetic (stage_in : List Wire) (stage_out : List Wire)
                                         (enable : Wire) (sign : Wire) (amount : Nat) (width : Nat) (_stageNum : Nat) : List Gate :=
  List.range width |>.map (fun i =>
    let shifted_idx := i + amount
    let shifted_input :=
      if shifted_idx < width
      then stage_in.get! shifted_idx
      else sign  -- Fill with sign bit for arithmetic shift
    let current_input := stage_in.get! i
    Gate.mkMUX current_input shifted_input enable (stage_out.get! i)
  )

-- Build complete 5-stage left shifter
def mkLeftShifter (input : List Wire) (shamt : List Wire) (zero : Wire) (output : List Wire) : List Gate :=
  -- Create intermediate wires for each stage
  let stage0_out := makeIndexedWires "sll_s0" 32
  let stage1_out := makeIndexedWires "sll_s1" 32
  let stage2_out := makeIndexedWires "sll_s2" 32
  let stage3_out := makeIndexedWires "sll_s3" 32
  let stage4_out := output  -- Final stage outputs directly

  let stage0 := mkLeftShiftStage input stage0_out (shamt.get! 0) zero 1 32 0
  let stage1 := mkLeftShiftStage stage0_out stage1_out (shamt.get! 1) zero 2 32 1
  let stage2 := mkLeftShiftStage stage1_out stage2_out (shamt.get! 2) zero 4 32 2
  let stage3 := mkLeftShiftStage stage2_out stage3_out (shamt.get! 3) zero 8 32 3
  let stage4 := mkLeftShiftStage stage3_out stage4_out (shamt.get! 4) zero 16 32 4

  stage0 ++ stage1 ++ stage2 ++ stage3 ++ stage4

-- Build complete 5-stage right logical shifter
def mkRightLogicalShifter (input : List Wire) (shamt : List Wire) (zero : Wire) (output : List Wire) : List Gate :=
  let stage0_out := makeIndexedWires "srl_s0" 32
  let stage1_out := makeIndexedWires "srl_s1" 32
  let stage2_out := makeIndexedWires "srl_s2" 32
  let stage3_out := makeIndexedWires "srl_s3" 32
  let stage4_out := output

  let stage0 := mkRightShiftStageLogical input stage0_out (shamt.get! 0) zero 1 32 0
  let stage1 := mkRightShiftStageLogical stage0_out stage1_out (shamt.get! 1) zero 2 32 1
  let stage2 := mkRightShiftStageLogical stage1_out stage2_out (shamt.get! 2) zero 4 32 2
  let stage3 := mkRightShiftStageLogical stage2_out stage3_out (shamt.get! 3) zero 8 32 3
  let stage4 := mkRightShiftStageLogical stage3_out stage4_out (shamt.get! 4) zero 16 32 4

  stage0 ++ stage1 ++ stage2 ++ stage3 ++ stage4

-- Build complete 5-stage right arithmetic shifter
def mkRightArithmeticShifter (input : List Wire) (shamt : List Wire) (sign : Wire) (output : List Wire) : List Gate :=
  let stage0_out := makeIndexedWires "sra_s0" 32
  let stage1_out := makeIndexedWires "sra_s1" 32
  let stage2_out := makeIndexedWires "sra_s2" 32
  let stage3_out := makeIndexedWires "sra_s3" 32
  let stage4_out := output

  let stage0 := mkRightShiftStageArithmetic input stage0_out (shamt.get! 0) sign 1 32 0
  let stage1 := mkRightShiftStageArithmetic stage0_out stage1_out (shamt.get! 1) sign 2 32 1
  let stage2 := mkRightShiftStageArithmetic stage1_out stage2_out (shamt.get! 2) sign 4 32 2
  let stage3 := mkRightShiftStageArithmetic stage2_out stage3_out (shamt.get! 3) sign 8 32 3
  let stage4 := mkRightShiftStageArithmetic stage3_out stage4_out (shamt.get! 4) sign 16 32 4

  stage0 ++ stage1 ++ stage2 ++ stage3 ++ stage4

-- Build complete 32-bit shifter with all three operations
def mkShifter32 : Circuit :=
  let input := makeIndexedWires "in" 32
  let shamt := makeIndexedWires "shamt" 5  -- 5-bit shift amount (0-31)
  let op0 := Wire.mk "op0"  -- LSB of operation selector
  let op1 := Wire.mk "op1"  -- MSB of operation selector
  let zero := Wire.mk "zero"  -- Constant 0 input (must be tied to 0)
  let result := makeIndexedWires "result" 32

  -- Intermediate outputs from each shifter
  let sll_out := makeIndexedWires "sll_out" 32
  let srl_out := makeIndexedWires "srl_out" 32
  let sra_out := makeIndexedWires "sra_out" 32

  -- Sign bit for arithmetic shift
  let sign := input.get! 31

  -- Build all three shifters
  let sll_gates := mkLeftShifter input shamt zero sll_out
  let srl_gates := mkRightLogicalShifter input shamt zero srl_out
  let sra_gates := mkRightArithmeticShifter input shamt sign sra_out

  -- Final MUX: select between SLL, SRL, SRA based on op[1:0]
  -- op=00 (0): SLL, op=01 (1): SRL, op=10 (2): SRA, op=11 (3): SRA
  -- We'll use a 2-level MUX tree:
  --   Level 1: MUX(SLL, SRL, op0) -> mux1
  --   Level 2: MUX(mux1, SRA, op1) -> result
  let mux1 := makeIndexedWires "mux1" 32
  let mux_level1 := List.range 32 |>.map (fun i =>
    Gate.mkMUX (sll_out.get! i) (srl_out.get! i) op0 (mux1.get! i)
  )
  let mux_level2 := List.range 32 |>.map (fun i =>
    Gate.mkMUX (mux1.get! i) (sra_out.get! i) op1 (result.get! i)
  )

  { name := "Shifter32"
    inputs := input ++ shamt ++ [op0, op1, zero]
    outputs := result
    gates := sll_gates ++ srl_gates ++ sra_gates ++ mux_level1 ++ mux_level2
    instances := []
  }

-- Smaller variants for testing
def mkShifter4 : Circuit :=
  let input := makeIndexedWires "in" 4
  let shamt := makeIndexedWires "shamt" 2  -- 2-bit shift amount (0-3)
  let op0 := Wire.mk "op0"
  let op1 := Wire.mk "op1"
  let zero := Wire.mk "zero"
  let result := makeIndexedWires "result" 4

  let sll_out := makeIndexedWires "sll_out" 4
  let srl_out := makeIndexedWires "srl_out" 4
  let sra_out := makeIndexedWires "sra_out" 4
  let sign := input.get! 3

  -- 2 stages for 4-bit shifter
  let sll_s0 := makeIndexedWires "sll_s0" 4
  let srl_s0 := makeIndexedWires "srl_s0" 4
  let sra_s0 := makeIndexedWires "sra_s0" 4

  let sll_stage0 := mkLeftShiftStage input sll_s0 (shamt.get! 0) zero 1 4 0
  let sll_stage1 := mkLeftShiftStage sll_s0 sll_out (shamt.get! 1) zero 2 4 1

  let srl_stage0 := mkRightShiftStageLogical input srl_s0 (shamt.get! 0) zero 1 4 0
  let srl_stage1 := mkRightShiftStageLogical srl_s0 srl_out (shamt.get! 1) zero 2 4 1

  let sra_stage0 := mkRightShiftStageArithmetic input sra_s0 (shamt.get! 0) sign 1 4 0
  let sra_stage1 := mkRightShiftStageArithmetic sra_s0 sra_out (shamt.get! 1) sign 2 4 1

  let mux1 := makeIndexedWires "mux1" 4
  let mux_level1 := List.range 4 |>.map (fun i =>
    Gate.mkMUX (sll_out.get! i) (srl_out.get! i) op0 (mux1.get! i)
  )
  let mux_level2 := List.range 4 |>.map (fun i =>
    Gate.mkMUX (mux1.get! i) (sra_out.get! i) op1 (result.get! i)
  )

  { name := "Shifter4"
    inputs := input ++ shamt ++ [op0, op1, zero]
    outputs := result
    gates := sll_stage0 ++ sll_stage1 ++ srl_stage0 ++ srl_stage1 ++ sra_stage0 ++ sra_stage1 ++ mux_level1 ++ mux_level2
    instances := []
  }

end Shoumei.Circuits.Combinational
