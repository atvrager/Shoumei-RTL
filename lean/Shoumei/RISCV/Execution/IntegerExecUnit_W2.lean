import Shoumei.RISCV.ISA
import Shoumei.Circuits.Combinational.ALU

namespace Shoumei.RISCV.Execution

open Shoumei
open Shoumei.Circuits.Combinational

/--
Dual-Issue Integer Execution Unit (V2).
Contains two independent ALU32 instances to execute two arbitrary integer instructions per cycle.
-/
def mkIntegerExecUnit_W2 : Circuit :=
  -- Issue 0
  let a0 := makeIndexedWires "a0" 32
  let b0 := makeIndexedWires "b0" 32
  let opcode0 := makeIndexedWires "opcode0" 4
  let dest_tag0 := makeIndexedWires "dest_tag0" 6
  let result0 := makeIndexedWires "result0" 32
  let tag_out0 := makeIndexedWires "tag_out0" 6
  
  -- Issue 1
  let a1 := makeIndexedWires "a1" 32
  let b1 := makeIndexedWires "b1" 32
  let opcode1 := makeIndexedWires "opcode1" 4
  let dest_tag1 := makeIndexedWires "dest_tag1" 6
  let result1 := makeIndexedWires "result1" 32
  let tag_out1 := makeIndexedWires "tag_out1" 6
  
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- Instance ALU0
  let alu0_inst : CircuitInstance := {
    moduleName := "ALU32"
    instName := "u_alu0"
    portMap :=
      (a0.enum.map (fun ⟨i, w⟩ => (s!"a[{i}]", w))) ++
      (b0.enum.map (fun ⟨i, w⟩ => (s!"b[{i}]", w))) ++
      (opcode0.enum.map (fun ⟨i, w⟩ => (s!"op[{i}]", w))) ++
      [("zero", zero), ("one", one)] ++
      (result0.enum.map (fun ⟨i, w⟩ => (s!"result[{i}]", w)))
  }

  -- Instance ALU1
  let alu1_inst : CircuitInstance := {
    moduleName := "ALU32"
    instName := "u_alu1"
    portMap :=
      (a1.enum.map (fun ⟨i, w⟩ => (s!"a[{i}]", w))) ++
      (b1.enum.map (fun ⟨i, w⟩ => (s!"b[{i}]", w))) ++
      (opcode1.enum.map (fun ⟨i, w⟩ => (s!"op[{i}]", w))) ++
      [("zero", zero), ("one", one)] ++
      (result1.enum.map (fun ⟨i, w⟩ => (s!"result[{i}]", w)))
  }

  -- Tag pass-through
  let tag0_passthrough := List.zipWith Gate.mkBUF dest_tag0 tag_out0
  let tag1_passthrough := List.zipWith Gate.mkBUF dest_tag1 tag_out1

  { name := "IntegerExecUnit_W2"
    inputs := a0 ++ b0 ++ opcode0 ++ dest_tag0 ++
              a1 ++ b1 ++ opcode1 ++ dest_tag1 ++
              [zero, one]
    outputs := result0 ++ tag_out0 ++ result1 ++ tag_out1
    gates := tag0_passthrough ++ tag1_passthrough
    instances := [alu0_inst, alu1_inst]
  }

def integerExecUnitW2 : Circuit := mkIntegerExecUnit_W2

end Shoumei.RISCV.Execution
