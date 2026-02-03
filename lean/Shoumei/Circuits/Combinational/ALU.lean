/-
Circuits/Combinational/ALU.lean - 32-bit ALU for RV32I

Arithmetic Logic Unit integrating all arithmetic and logic operations.
Supports all RV32I ALU operations (10 total):

Arithmetic:
- ADD: a + b
- SUB: a - b
- SLT: (signed)a < (signed)b ? 1 : 0
- SLTU: (unsigned)a < (unsigned)b ? 1 : 0

Logic:
- AND: a & b (bitwise)
- OR: a | b (bitwise)
- XOR: a ^ b (bitwise)

Shift:
- SLL: a << b[4:0] (shift left logical)
- SRL: a >>> b[4:0] (shift right logical)
- SRA: a >> b[4:0] (shift right arithmetic)

Architecture:
- All functional units operate in parallel
- Multi-level MUX tree selects result based on opcode[3:0]
- Total gate count: sum of all units + MUX overhead

Opcode encoding (4 bits):
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
- 1010-1111: Reserved (currently output 0)
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.RippleCarryAdder
import Shoumei.Circuits.Combinational.Subtractor
import Shoumei.Circuits.Combinational.Comparator
import Shoumei.Circuits.Combinational.LogicUnit
import Shoumei.Circuits.Combinational.Shifter

namespace Shoumei.Circuits.Combinational

open Shoumei

-- Helper: Zero-extend a single bit to 32 bits
-- bit_wire is connected to result[0], all other bits connected to zero
private def zeroExtend1to32 (bit_wire : Wire) (zero : Wire) (output : List Wire) : List Gate :=
  let gate0 := Gate.mkBUF bit_wire (output[0]!)
  let rest_gates := List.range 31 |>.map (fun i =>
    Gate.mkBUF zero (output[i + 1]!)
  )
  gate0 :: rest_gates

-- Build complete 32-bit ALU
def mkALU32 : Circuit :=
  let a := makeIndexedWires "a" 32
  let b := makeIndexedWires "b" 32
  let opcode := makeIndexedWires "op" 4  -- 4-bit opcode
  let result := makeIndexedWires "result" 32
  let zero := Wire.mk "zero"  -- Constant 0 input
  let one := Wire.mk "one"    -- Constant 1 input

  -- Extract shift amount from b (lower 5 bits)
  let shamt := List.range 5 |>.map (fun i => b[i]!)

  -- Outputs from each functional unit
  let add_result := makeIndexedWires "add_out" 32
  let sub_result := makeIndexedWires "sub_out" 32
  let slt_result := makeIndexedWires "slt_out" 32
  let sltu_result := makeIndexedWires "sltu_out" 32
  let and_result := makeIndexedWires "and_out" 32
  let or_result := makeIndexedWires "or_out" 32
  let xor_result := makeIndexedWires "xor_out" 32
  let sll_result := makeIndexedWires "sll_out" 32
  let srl_result := makeIndexedWires "srl_out" 32
  let sra_result := makeIndexedWires "sra_out" 32

  -- Intermediate wires for comparator (only need lt and ltu for RV32I)
  let cmp_lt := Wire.mk "cmp_lt"
  let cmp_ltu := Wire.mk "cmp_ltu"

  -- Build RippleCarryAdder for ADD (cin=0)
  let add_internal_carries := makeIndexedWires "add_c" 31
  let add_cout := Wire.mk "add_cout"
  let add_carries := zero :: add_internal_carries ++ [add_cout]
  let add_gates := buildFullAdderChain a b add_carries add_result "add_"

  -- Build Subtractor for SUB (reuse 2's complement logic)
  let b_inv := makeIndexedWires "b_inv" 32
  let sub_not_gates := List.zipWith (fun b_wire b_inv_wire =>
    Gate.mkNOT b_wire b_inv_wire
  ) b b_inv
  let sub_internal_carries := makeIndexedWires "sub_c" 31
  let sub_borrow := Wire.mk "sub_borrow"
  let sub_carries := one :: sub_internal_carries ++ [sub_borrow]
  let sub_rca_gates := buildFullAdderChain a b_inv sub_carries sub_result "sub_"

  -- Build Comparator for SLT/SLTU (shares subtraction logic)
  -- We'll build it inline to get the comparison outputs
  let cmp_diff := makeIndexedWires "cmp_diff" 32
  let cmp_b_inv := makeIndexedWires "cmp_b_inv" 32
  let cmp_not_gates := List.zipWith (fun b_wire b_inv_wire =>
    Gate.mkNOT b_wire b_inv_wire
  ) b cmp_b_inv
  let cmp_internal_carries := makeIndexedWires "cmp_c" 31
  let cmp_borrow := Wire.mk "cmp_borrow"
  let cmp_carries := one :: cmp_internal_carries ++ [cmp_borrow]
  let cmp_sub_gates := buildFullAdderChain a cmp_b_inv cmp_carries cmp_diff "cmp_"

  -- Comparison logic (eq, lt, ltu) - simplified from Comparator
  -- For now, just use borrow for ltu, and compute lt from sign bits
  let cmp_ltu_gate := Gate.mkBUF cmp_borrow cmp_ltu

  -- Simplified signed comparison: just use diff sign and input signs
  let a_sign := a[31]!
  let b_sign := b[31]!
  let diff_sign := cmp_diff[31]!
  let b_sign_inv := Wire.mk "cmp_b_sign_inv"
  let a_neg_b_pos := Wire.mk "cmp_a_neg_b_pos"
  let signs_xor := Wire.mk "cmp_signs_xor"
  let signs_same := Wire.mk "cmp_signs_same"
  let same_sign_cmp := Wire.mk "cmp_same_sign_cmp"

  let cmp_lt_gates := [
    Gate.mkNOT b_sign b_sign_inv,
    Gate.mkAND a_sign b_sign_inv a_neg_b_pos,
    Gate.mkXOR a_sign b_sign signs_xor,
    Gate.mkNOT signs_xor signs_same,
    Gate.mkAND signs_same diff_sign same_sign_cmp,
    Gate.mkOR a_neg_b_pos same_sign_cmp cmp_lt
  ]

  -- Zero-extend comparison results to 32 bits
  let slt_extend_gates := zeroExtend1to32 cmp_lt zero slt_result
  let sltu_extend_gates := zeroExtend1to32 cmp_ltu zero sltu_result

  -- Build LogicUnit for AND/OR/XOR
  -- We need to run it 3 times with different op values, or build inline
  -- Let's build inline to save complexity
  let and_gates := List.range 32 |>.map (fun i =>
    Gate.mkAND (a[i]!) (b[i]!) (and_result[i]!)
  )
  let or_gates := List.range 32 |>.map (fun i =>
    Gate.mkOR (a[i]!) (b[i]!) (or_result[i]!)
  )
  let xor_gates := List.range 32 |>.map (fun i =>
    Gate.mkXOR (a[i]!) (b[i]!) (xor_result[i]!)
  )

  -- Build Shifter (inline simplified - just build 3 shifters)
  -- This will be complex, so let's use the existing Shifter32 structure
  let sll_gates := mkLeftShifter a shamt zero sll_result
  let srl_gates := mkRightLogicalShifter a shamt zero srl_result
  let a_sign_for_sra := a[31]!
  let sra_gates := mkRightArithmeticShifter a shamt a_sign_for_sra sra_result

  -- MUX tree to select result based on opcode
  -- Level 1: Select between arithmetic operations (4 operations: ADD, SUB, SLT, SLTU)
  let arith_mux1 := makeIndexedWires "arith_mux1" 32  -- ADD or SUB
  let arith_mux2 := makeIndexedWires "arith_mux2" 32  -- SLT or SLTU
  let arith_final := makeIndexedWires "arith_out" 32  -- arith_mux1 or arith_mux2

  let arith_level1_gates := List.range 32 |>.map (fun i =>
    Gate.mkMUX (add_result[i]!) (sub_result[i]!) (opcode[0]!) (arith_mux1[i]!)
  )
  let arith_level2_gates := List.range 32 |>.map (fun i =>
    Gate.mkMUX (slt_result[i]!) (sltu_result[i]!) (opcode[0]!) (arith_mux2[i]!)
  )
  let arith_level3_gates := List.range 32 |>.map (fun i =>
    Gate.mkMUX (arith_mux1[i]!) (arith_mux2[i]!) (opcode[1]!) (arith_final[i]!)
  )

  -- Level 2: Select between logic operations (3 operations: AND, OR, XOR)
  let logic_mux1 := makeIndexedWires "logic_mux1" 32  -- AND or OR
  let logic_final := makeIndexedWires "logic_out" 32  -- logic_mux1 or XOR

  let logic_level1_gates := List.range 32 |>.map (fun i =>
    Gate.mkMUX (and_result[i]!) (or_result[i]!) (opcode[0]!) (logic_mux1[i]!)
  )
  let logic_level2_gates := List.range 32 |>.map (fun i =>
    Gate.mkMUX (logic_mux1[i]!) (xor_result[i]!) (opcode[1]!) (logic_final[i]!)
  )

  -- Level 3: Select between shift operations (3 operations: SLL, SRL, SRA)
  let shift_mux1 := makeIndexedWires "shift_mux1" 32  -- SLL or SRL
  let shift_final := makeIndexedWires "shift_out" 32  -- shift_mux1 or SRA

  let shift_level1_gates := List.range 32 |>.map (fun i =>
    Gate.mkMUX (sll_result[i]!) (srl_result[i]!) (opcode[0]!) (shift_mux1[i]!)
  )
  let shift_level2_gates := List.range 32 |>.map (fun i =>
    Gate.mkMUX (shift_mux1[i]!) (sra_result[i]!) (opcode[1]!) (shift_final[i]!)
  )

  -- Top level: Select between arithmetic, logic, and shift
  -- op[3:2] determines the category:
  -- 00: arithmetic, 01: logic, 10: shift, 11: reserved (output 0)
  let top_mux1 := makeIndexedWires "top_mux1" 32  -- arith or logic
  let top_mux2 := makeIndexedWires "top_mux2" 32  -- shift or zero

  let top_level1_gates := List.range 32 |>.map (fun i =>
    Gate.mkMUX (arith_final[i]!) (logic_final[i]!) (opcode[2]!) (top_mux1[i]!)
  )
  let top_level2_gates := List.range 32 |>.map (fun i =>
    Gate.mkMUX (shift_final[i]!) zero (opcode[2]!) (top_mux2[i]!)
  )
  let top_level3_gates := List.range 32 |>.map (fun i =>
    Gate.mkMUX (top_mux1[i]!) (top_mux2[i]!) (opcode[3]!) (result[i]!)
  )

  { name := "ALU32"
    inputs := a ++ b ++ opcode ++ [zero, one]
    outputs := result
    gates := add_gates ++ sub_not_gates ++ sub_rca_gates
             ++ cmp_not_gates ++ cmp_sub_gates ++ [cmp_ltu_gate] ++ cmp_lt_gates
             ++ slt_extend_gates ++ sltu_extend_gates
             ++ and_gates ++ or_gates ++ xor_gates
             ++ sll_gates ++ srl_gates ++ sra_gates
             ++ arith_level1_gates ++ arith_level2_gates ++ arith_level3_gates
             ++ logic_level1_gates ++ logic_level2_gates
             ++ shift_level1_gates ++ shift_level2_gates
             ++ top_level1_gates ++ top_level2_gates ++ top_level3_gates
    instances := []
  }

/-! ## Codegen V2: Annotated ALU32

Adds SignalGroup and InterfaceBundle annotations to the ALU32 circuit.
The gate list is unchanged -- annotations are purely additive metadata.

Wire naming:
  Inputs:  a_0..31, b_0..31, op_0..3, zero, one
  Outputs: result_0..31

Signal groups (buses):
  a[31:0]        -- Operand A
  b[31:0]        -- Operand B
  op[3:0]        -- Opcode
  result[31:0]   -- Final result
  add_out[31:0]  -- Adder output
  sub_out[31:0]  -- Subtractor output
  slt_out[31:0]  -- Signed less-than output
  sltu_out[31:0] -- Unsigned less-than output
  and_out[31:0]  -- AND output
  or_out[31:0]   -- OR output
  xor_out[31:0]  -- XOR output
  sll_out[31:0]  -- Shift left logical output
  srl_out[31:0]  -- Shift right logical output
  sra_out[31:0]  -- Shift right arithmetic output
-/

/-- ALU32 with codegen v2 annotations.
    Same circuit as mkALU32, plus signal groups and interface bundles. -/
def mkALU32Annotated : Circuit :=
  let base := mkALU32
  { base with
    signalGroups := [
      -- Input buses
      { name := "a",   width := 32, wires := makeIndexedWires "a" 32 },
      { name := "b",   width := 32, wires := makeIndexedWires "b" 32 },
      { name := "op",  width := 4,  wires := makeIndexedWires "op" 4 },
      -- Output bus
      { name := "result", width := 32, wires := makeIndexedWires "result" 32 },
      -- Functional unit outputs
      { name := "add_out",  width := 32, wires := makeIndexedWires "add_out" 32 },
      { name := "sub_out",  width := 32, wires := makeIndexedWires "sub_out" 32 },
      { name := "slt_out",  width := 32, wires := makeIndexedWires "slt_out" 32 },
      { name := "sltu_out", width := 32, wires := makeIndexedWires "sltu_out" 32 },
      { name := "and_out",  width := 32, wires := makeIndexedWires "and_out" 32 },
      { name := "or_out",   width := 32, wires := makeIndexedWires "or_out" 32 },
      { name := "xor_out",  width := 32, wires := makeIndexedWires "xor_out" 32 },
      { name := "sll_out",  width := 32, wires := makeIndexedWires "sll_out" 32 },
      { name := "srl_out",  width := 32, wires := makeIndexedWires "srl_out" 32 },
      { name := "sra_out",  width := 32, wires := makeIndexedWires "sra_out" 32 }
    ]
    inputBundles := [
      { name := "alu"
        signals := [("a", .UInt 32), ("b", .UInt 32), ("op", .UInt 4)] }
    ]
    outputBundles := [
      { name := "alu"
        signals := [("result", .UInt 32)] }
    ]
  }

end Shoumei.Circuits.Combinational
