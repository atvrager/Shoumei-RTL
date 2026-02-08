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

-- Build complete 32-bit ALU (hierarchical version using verified submodules)
def mkALU32 : Circuit :=
  let a := makeIndexedWires "a" 32
  let b := makeIndexedWires "b" 32
  let opcode := makeIndexedWires "op" 4  -- 4-bit opcode
  let result := makeIndexedWires "result" 32
  let zero := Wire.mk "zero"  -- Constant 0 input
  let one := Wire.mk "one"    -- Constant 1 input

  -- Outputs from each functional unit
  let add_result := makeIndexedWires "add_out" 32
  let sub_result := makeIndexedWires "sub_out" 32
  let sub_borrow := Wire.mk "sub_borrow"  -- Unused output
  let cmp_lt := Wire.mk "cmp_lt"
  let cmp_ltu := Wire.mk "cmp_ltu"
  let cmp_eq := Wire.mk "cmp_eq"    -- Unused output
  let cmp_gt := Wire.mk "cmp_gt"    -- Unused output
  let cmp_gtu := Wire.mk "cmp_gtu"  -- Unused output
  let slt_result := makeIndexedWires "slt_out" 32
  let sltu_result := makeIndexedWires "sltu_out" 32
  let logic_result := makeIndexedWires "logic_out" 32
  let shift_result := makeIndexedWires "shift_out" 32

  -- Logic unit control: opcode[1:0] for AND/OR/XOR selection
  let logic_op := [opcode[0]!, opcode[1]!]

  -- Shifter control: opcode[1:0] for SLL/SRL/SRA + direction
  let shift_amt := List.range 5 |>.map (fun i => b[i]!)
  let shift_dir := opcode[0]!  -- 0=left, 1=right
  let shift_arith := opcode[1]!  -- 0=logical, 1=arithmetic (for right shifts)

  -- Zero-extend comparison results to 32 bits
  let slt_extend_gates := zeroExtend1to32 cmp_lt zero slt_result
  let sltu_extend_gates := zeroExtend1to32 cmp_ltu zero sltu_result

  -- MUX tree to select result based on opcode
  -- Level 1: Select between arithmetic operations (4 operations)
  let arith_mux1 := makeIndexedWires "arith_mux1" 32  -- ADD or SUB
  let arith_mux2 := makeIndexedWires "arith_mux2" 32  -- SLT or SLTU
  let arith_final := makeIndexedWires "arith_out" 32  -- Final arithmetic result

  let arith_level1_gates := List.range 32 |>.map (fun i =>
    Gate.mkMUX (add_result[i]!) (sub_result[i]!) (opcode[0]!) (arith_mux1[i]!)
  )
  let arith_level2_gates := List.range 32 |>.map (fun i =>
    Gate.mkMUX (slt_result[i]!) (sltu_result[i]!) (opcode[0]!) (arith_mux2[i]!)
  )
  let arith_level3_gates := List.range 32 |>.map (fun i =>
    Gate.mkMUX (arith_mux1[i]!) (arith_mux2[i]!) (opcode[1]!) (arith_final[i]!)
  )

  -- Top level: Select between arithmetic, logic, and shift
  -- op[3:2] determines the category:
  -- 00: arithmetic, 01: logic, 10: shift, 11: reserved (output 0)
  let top_mux1 := makeIndexedWires "top_mux1" 32  -- arith or logic
  let top_mux2 := makeIndexedWires "top_mux2" 32  -- shift or zero

  let top_level1_gates := List.range 32 |>.map (fun i =>
    Gate.mkMUX (arith_final[i]!) (logic_result[i]!) (opcode[2]!) (top_mux1[i]!)
  )
  let top_level2_gates := List.range 32 |>.map (fun i =>
    Gate.mkMUX (shift_result[i]!) zero (opcode[2]!) (top_mux2[i]!)
  )
  let top_level3_gates := List.range 32 |>.map (fun i =>
    Gate.mkMUX (top_mux1[i]!) (top_mux2[i]!) (opcode[3]!) (result[i]!)
  )

  { name := "ALU32"
    inputs := a ++ b ++ opcode ++ [zero, one]
    outputs := result
    gates := slt_extend_gates ++ sltu_extend_gates
             ++ arith_level1_gates ++ arith_level2_gates ++ arith_level3_gates
             ++ top_level1_gates ++ top_level2_gates ++ top_level3_gates
    instances := [
      -- KoggeStoneAdder32 for ADD operation
      { moduleName := "KoggeStoneAdder32"
        instName := "u_add"
        portMap := (List.range 32 |>.flatMap (fun i =>
          [ (s!"a{i}", a[i]!)
          , (s!"b{i}", b[i]!)
          , (s!"sum{i}", add_result[i]!)
          ]
        )) ++ [("cin", zero)]
      },
      -- Subtractor32 for SUB operation
      { moduleName := "Subtractor32"
        instName := "u_sub"
        portMap := (List.range 32 |>.flatMap (fun i =>
          [ (s!"a{i}", a[i]!)
          , (s!"b{i}", b[i]!)
          , (s!"diff{i}", sub_result[i]!)
          ]
        )) ++ [("one", one), ("borrow", sub_borrow)]
      },
      -- Comparator32 for SLT/SLTU operations
      { moduleName := "Comparator32"
        instName := "u_cmp"
        portMap := (List.range 32 |>.flatMap (fun i =>
          [ (s!"a{i}", a[i]!)
          , (s!"b{i}", b[i]!)
          ]
        )) ++ [("one", one), ("lt", cmp_lt), ("ltu", cmp_ltu),
               ("eq", cmp_eq), ("gt", cmp_gt), ("gtu", cmp_gtu)]
      },
      -- LogicUnit32 for AND/OR/XOR operations
      { moduleName := "LogicUnit32"
        instName := "u_logic"
        portMap := (List.range 32 |>.flatMap (fun i =>
          [ (s!"a{i}", a[i]!)
          , (s!"b{i}", b[i]!)
          , (s!"result{i}", logic_result[i]!)
          ]
        )) ++ List.zip ["op0", "op1"] logic_op
      },
      -- Shifter32 for SLL/SRL/SRA operations
      { moduleName := "Shifter32"
        instName := "u_shift"
        portMap := (List.range 32 |>.flatMap (fun i =>
          [ (s!"in{i}", a[i]!)
          , (s!"result{i}", shift_result[i]!)
          ]
        )) ++ (List.range 5 |>.map (fun i => (s!"shamt{i}", shift_amt[i]!)))
           ++ [("op0", shift_dir), ("op1", shift_arith), ("zero", zero)]
      }
    ]
    signalGroups := [
      { name := "a",      width := 32, wires := a },
      { name := "b",      width := 32, wires := b },
      { name := "op",     width := 4,  wires := opcode },
      { name := "result", width := 32, wires := result }
    ]
    keepHierarchy := true
  }

end Shoumei.Circuits.Combinational
