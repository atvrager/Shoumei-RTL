/-
Circuits/Combinational/FPLongConverter.lean - 64-Bit FP/Integer Conversion Circuit (Hierarchical)

Implements all 64-bit integer conversion operations for RV64D/RV64F:
- FCVT.L.S  (op=0): SP float -> signed 64-bit int
- FCVT.LU.S (op=1): SP float -> unsigned 64-bit int
- FCVT.S.L  (op=2): signed 64-bit int -> SP float (NaN-boxed)
- FCVT.S.LU (op=3): unsigned 64-bit int -> SP float (NaN-boxed)
- FCVT.L.D  (op=4): DP float -> signed 64-bit int
- FCVT.LU.D (op=5): DP float -> unsigned 64-bit int
- FCVT.D.L  (op=6): signed 64-bit int -> DP float
- FCVT.D.LU (op=7): unsigned 64-bit int -> DP float

Architecture:
  Hierarchical composition of:
  - Int64ToFP: Int64 -> Single/Double precision float converter
  - FPToInt64: Single/Double precision float -> Int64 converter

Interface:
- Inputs:
  * src1[63:0]: Operand
  * op[2:0]: Sub-op (bit2=DP, bit1=Int->FP, bit0=unsigned)
  * rm[2:0]: Rounding mode (0=RNE, 1=RTZ, 2=RDN, 3=RUP, 4=RMM)
  * zero, one: Constant wires
- Outputs:
  * result[63:0]: Converted value
  * exc[4:0]: Exceptions (NV, DZ, OF, UF, NX)
  * result_is_int: High when targeting INT PRF (Float -> Int)
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.Int64ToFP
import Shoumei.Circuits.Combinational.FPToInt64

namespace Shoumei.Circuits.Combinational

open Shoumei

/-- 64-bit FP/Integer Converter Circuit (Hierarchical) -/
def fpLongConverterCircuit : Circuit :=
  let src1 := makeIndexedWires "src1" 64
  let op := makeIndexedWires "op" 3
  let rm := makeIndexedWires "rm" 3
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  let result := makeIndexedWires "result" 64
  let exc := makeIndexedWires "exc" 5
  let result_is_int := Wire.mk "result_is_int"

  -- Opcode bit decoding
  let is_dp := op[2]!
  let is_int_to_fp := op[1]!
  let is_unsigned := op[0]!

  let not_is_dp := Wire.mk "not_is_dp"
  let not_is_int_to_fp := Wire.mk "not_is_int_to_fp"
  let not_is_unsigned := Wire.mk "not_is_unsigned"
  let op_inv_gates := [
    Gate.mkNOT is_dp not_is_dp,
    Gate.mkNOT is_int_to_fp not_is_int_to_fp,
    Gate.mkNOT is_unsigned not_is_unsigned,
    Gate.mkBUF not_is_int_to_fp result_is_int
  ]

  -- Submodule instances
  let i2f_result := makeIndexedWires "i2f_res" 64
  let i2f_exc_nx := Wire.mk "i2f_exc_nx"
  let u_i2f : CircuitInstance := {
    moduleName := "Int64ToFP"
    instName := "u_int64_to_fp"
    portMap :=
      (src1.enum.map (fun ⟨i, w⟩ => (s!"src1[{i}]", w))) ++
      [("is_dp", is_dp), ("is_unsigned", is_unsigned)] ++
      (rm.enum.map (fun ⟨i, w⟩ => (s!"rm[{i}]", w))) ++
      [("zero", zero), ("one", one)] ++
      (i2f_result.enum.map (fun ⟨i, w⟩ => (s!"result[{i}]", w))) ++
      [("exc_nx", i2f_exc_nx)]
  }

  let f2i_result := makeIndexedWires "f2i_res" 64
  let f2i_exc_nv := Wire.mk "f2i_exc_nv"
  let f2i_exc_nx := Wire.mk "f2i_exc_nx"
  let u_f2i : CircuitInstance := {
    moduleName := "FPToInt64"
    instName := "u_fp_to_int64"
    portMap :=
      (src1.enum.map (fun ⟨i, w⟩ => (s!"src1[{i}]", w))) ++
      [("is_dp", is_dp), ("is_unsigned", is_unsigned)] ++
      (rm.enum.map (fun ⟨i, w⟩ => (s!"rm[{i}]", w))) ++
      [("zero", zero), ("one", one)] ++
      (f2i_result.enum.map (fun ⟨i, w⟩ => (s!"result[{i}]", w))) ++
      [("exc_nv", f2i_exc_nv), ("exc_nx", f2i_exc_nx)]
  }

  -- Select between Float -> Int and Int -> Float outputs
  let master_result_gates := (List.range 64).map fun i =>
    Gate.mkMUX (f2i_result[i]!) (i2f_result[i]!) is_int_to_fp (result[i]!)

  -- Exceptions:
  -- exc[4] = NV: active only for Float -> Int
  -- exc[3] = DZ: always 0
  -- exc[2] = OF: always 0
  -- exc[1] = UF: always 0
  -- exc[0] = NX: active for both
  let master_exc_nv := Wire.mk "m_exc_nv"
  let master_exc_nx := Wire.mk "m_exc_nx"
  let master_exc_gates := [
    Gate.mkAND f2i_exc_nv not_is_int_to_fp master_exc_nv,
    Gate.mkMUX f2i_exc_nx i2f_exc_nx is_int_to_fp master_exc_nx,
    Gate.mkBUF master_exc_nv (exc[4]!),
    Gate.mkNOT (rm[2]!) (Wire.mk "not_lc_rm2"),
    Gate.mkAND (rm[2]!) (Wire.mk "not_lc_rm2") (exc[3]!),
    Gate.mkNOT (rm[1]!) (Wire.mk "not_lc_rm1"),
    Gate.mkAND (rm[1]!) (Wire.mk "not_lc_rm1") (exc[2]!),
    Gate.mkNOT (rm[0]!) (Wire.mk "not_lc_rm0"),
    Gate.mkAND (rm[0]!) (Wire.mk "not_lc_rm0") (exc[1]!),
    Gate.mkBUF master_exc_nx (exc[0]!)
  ]

  let all_gates := op_inv_gates ++ master_result_gates ++ master_exc_gates

  { name := "FPLongConverter",
    inputs := src1 ++ op ++ rm ++ [zero, one],
    outputs := result ++ exc ++ [result_is_int],
    gates := all_gates,
    instances := [u_i2f, u_f2i],
    signalGroups := [
      { name := "src1", width := 64, wires := src1 },
      { name := "op", width := 3, wires := op },
      { name := "rm", width := 3, wires := rm },
      { name := "result", width := 64, wires := result },
      { name := "exc", width := 5, wires := exc }
    ],
    keepHierarchy := true }

end Shoumei.Circuits.Combinational
