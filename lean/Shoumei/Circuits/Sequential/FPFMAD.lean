/-
Circuits/Sequential/FPFMAD.lean - Pipelined Double-Precision Fused Multiply-Add

Computes src1 * src2 ± src3 by chaining:
  FPMultiplierD (2 cycles) -> sign adjustment -> FPAdderD (4 cycles) = 6 cycles total.

src3, negate_product, subtract_addend, and rm are delayed 2 cycles to align
with the multiplier output.

Interface:
- Inputs: src1[63:0], src2[63:0], src3[63:0], rm[2:0], dest_tag[5:0],
          negate_product, subtract_addend, valid_in, clock, reset, zero
- Outputs: result[63:0], tag_out[5:0], exc[4:0], valid_out
-/

import Shoumei.DSL
import Shoumei.Circuits.Sequential.FPMultiplierD
import Shoumei.Circuits.Sequential.FPAdderD

namespace Shoumei.Circuits.Sequential

open Shoumei

private def makeIndexedWires (pfx : String) (n : Nat) : List Wire :=
  (List.range n).map fun i => Wire.mk (pfx ++ "_" ++ toString i)

private def mkDFFBank (d_wires q_wires : List Wire) (clock reset : Wire) : List Gate :=
  List.zipWith (fun d q => Gate.mkDFF d clock reset q) d_wires q_wires

def mkFPFMAD : Circuit :=
  let src1 := makeIndexedWires "src1" 64
  let src2 := makeIndexedWires "src2" 64
  let src3 := makeIndexedWires "src3" 64
  let rm := makeIndexedWires "rm" 3
  let dest_tag := makeIndexedWires "dest_tag" 6
  let negate_product := Wire.mk "negate_product"
  let subtract_addend := Wire.mk "subtract_addend"
  let valid_in := Wire.mk "valid_in"
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"

  let result := makeIndexedWires "result" 64
  let tag_out := makeIndexedWires "tag_out" 6
  let exc := makeIndexedWires "exc" 5
  let valid_out := Wire.mk "valid_out"

  let mul_result := makeIndexedWires "mul_result" 64
  let mul_tag := makeIndexedWires "mul_tag" 6
  let mul_exc := makeIndexedWires "mul_exc" 5
  let mul_valid := Wire.mk "mul_valid"

  -- src3 delay line: 2 stages × 64 bits
  let dl1_src3 := makeIndexedWires "dl1_src3" 64
  let dl2_src3 := makeIndexedWires "dl2_src3" 64
  let src3_dl_dffs :=
    mkDFFBank src3 dl1_src3 clock reset ++
    mkDFFBank dl1_src3 dl2_src3 clock reset

  -- Control delay lines: 2 stages each
  let dl1_neg := Wire.mk "dl1_neg"
  let dl2_neg := Wire.mk "dl2_neg"
  let neg_dl_dffs :=
    [ Gate.mkDFF negate_product clock reset dl1_neg,
      Gate.mkDFF dl1_neg clock reset dl2_neg ]

  let dl1_sub := Wire.mk "dl1_sub"
  let dl2_sub := Wire.mk "dl2_sub"
  let sub_dl_dffs :=
    [ Gate.mkDFF subtract_addend clock reset dl1_sub,
      Gate.mkDFF dl1_sub clock reset dl2_sub ]

  let dl1_rm := makeIndexedWires "dl1_rm" 3
  let dl2_rm := makeIndexedWires "dl2_rm" 3
  let rm_dl_dffs :=
    mkDFFBank rm dl1_rm clock reset ++
    mkDFFBank dl1_rm dl2_rm clock reset

  -- Sign adjustment: adj_result[63] = mul_result[63] XOR dl2_neg
  let adj_result := makeIndexedWires "adj_result" 64
  let adj_sign := Wire.mk "adj_sign"
  let sign_adj_gates :=
    [ Gate.mkXOR (mul_result[63]!) dl2_neg adj_sign,
      Gate.mkBUF adj_sign (adj_result[63]!) ] ++
    (List.range 63).map (fun i =>
      Gate.mkBUF (mul_result[i]!) (adj_result[i]!))

  let mul_inst : CircuitInstance :=
    { moduleName := "FPMultiplierD"
      instName := "u_mul_d"
      portMap :=
        (List.range 64 |>.flatMap fun i =>
          [ (s!"src1_{i}", src1[i]!), (s!"src2_{i}", src2[i]!) ]) ++
        (List.range 3 |>.map fun i => (s!"rm_{i}", rm[i]!)) ++
        (List.range 6 |>.map fun i => (s!"dest_tag_{i}", dest_tag[i]!)) ++
        [ ("valid_in", valid_in),
          ("clock", clock),
          ("reset", reset),
          ("zero", zero) ] ++
        (List.range 64 |>.map fun i => (s!"result_{i}", mul_result[i]!)) ++
        (List.range 6 |>.map fun i => (s!"tag_out_{i}", mul_tag[i]!)) ++
        (List.range 5 |>.map fun i => (s!"exc_{i}", mul_exc[i]!)) ++
        [ ("valid_out", mul_valid) ] }

  let add_inst : CircuitInstance :=
    { moduleName := "FPAdderD"
      instName := "u_add_d"
      portMap :=
        (List.range 64 |>.flatMap fun i =>
          [ (s!"src1_{i}", adj_result[i]!), (s!"src2_{i}", dl2_src3[i]!) ]) ++
        [ ("op_sub", dl2_sub) ] ++
        (List.range 3 |>.map fun i => (s!"rm_{i}", dl2_rm[i]!)) ++
        (List.range 6 |>.map fun i => (s!"dest_tag_{i}", mul_tag[i]!)) ++
        [ ("valid_in", mul_valid),
          ("clock", clock),
          ("reset", reset),
          ("zero", zero) ] ++
        (List.range 64 |>.map fun i => (s!"result_{i}", result[i]!)) ++
        (List.range 6 |>.map fun i => (s!"tag_out_{i}", tag_out[i]!)) ++
        (List.range 5 |>.map fun i => (s!"exc_{i}", exc[i]!)) ++
        [ ("valid_out", valid_out) ] }

  let all_gates :=
    src3_dl_dffs ++
    neg_dl_dffs ++
    sub_dl_dffs ++
    rm_dl_dffs ++
    sign_adj_gates

  { name := "FPFMAD"
    inputs := src1 ++ src2 ++ src3 ++ rm ++ dest_tag ++
              [negate_product, subtract_addend, valid_in, clock, reset, zero]
    outputs := result ++ tag_out ++ exc ++ [valid_out]
    gates := all_gates
    instances := [mul_inst, add_inst] }

def fpFMADCircuit : Circuit := mkFPFMAD

end Shoumei.Circuits.Sequential
