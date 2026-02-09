/-
Circuits/Sequential/FPAdder.lean - 4-Stage Pipelined FP Adder/Subtractor

A pipelined floating-point adder/subtractor for IEEE 754 binary32.

Pipeline stages (4-cycle latency):
  Stage 1: Latch inputs into pipeline registers
  Stage 2: Pass through (alignment placeholder)
  Stage 3: Pass through (addition placeholder)
  Stage 4: Output result

This is a pipeline skeleton — data flows through 3 DFF boundaries.
Actual FP arithmetic will replace the BUF placeholders with real computation.

Interface:
- Inputs: src1[31:0], src2[31:0], op_sub, rm[2:0], dest_tag[5:0], valid_in,
          clock, reset, zero
- Outputs: result[31:0], tag_out[5:0], exc[4:0], valid_out
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.RippleCarryAdder

namespace Shoumei.Circuits.Sequential

open Shoumei

/-! ## Helper: Indexed Wire Generation -/

private def makeIndexedWires (pfx : String) (n : Nat) : List Wire :=
  (List.range n).map fun i => Wire.mk (pfx ++ "_" ++ toString i)

/-! ## Helper: DFF Bank -/

/-- Create a bank of DFFs: for each i, mkDFF (d[i]) clock reset (q[i]). -/
private def mkDFFBank (d_wires q_wires : List Wire) (clock reset : Wire) : List Gate :=
  List.zipWith (fun d q => Gate.mkDFF d clock reset q) d_wires q_wires

/-- Create a bank of BUF gates: for each i, mkBUF (src[i]) (dst[i]). -/
private def mkBUFBank (src dst : List Wire) : List Gate :=
  List.zipWith (fun s d => Gate.mkBUF s d) src dst

/-! ## Circuit Definition -/

def fpAdderCircuit : Circuit :=
  -- Primary inputs
  let src1       := makeIndexedWires "src1" 32
  let src2       := makeIndexedWires "src2" 32
  let op_sub     := Wire.mk "op_sub"
  let rm         := makeIndexedWires "rm" 3
  let dest_tag   := makeIndexedWires "dest_tag" 6
  let valid_in   := Wire.mk "valid_in"
  let clock      := Wire.mk "clock"
  let reset      := Wire.mk "reset"
  let zero       := Wire.mk "zero"

  -- Primary outputs
  let result     := makeIndexedWires "result" 32
  let tag_out    := makeIndexedWires "tag_out" 6
  let exc        := makeIndexedWires "exc" 5
  let valid_out  := Wire.mk "valid_out"

  -- Stage 1 registers (input → s1)
  let s1_src1    := makeIndexedWires "s1_src1" 32
  let s1_src2    := makeIndexedWires "s1_src2" 32
  let s1_sub     := Wire.mk "s1_sub"
  let s1_rm      := makeIndexedWires "s1_rm" 3
  let s1_tag     := makeIndexedWires "s1_tag" 6
  let s1_valid   := Wire.mk "s1_valid"

  -- Stage 2 registers (s1 → s2)
  let s2_src1    := makeIndexedWires "s2_src1" 32
  let s2_src2    := makeIndexedWires "s2_src2" 32
  let s2_sub     := Wire.mk "s2_sub"
  let s2_rm      := makeIndexedWires "s2_rm" 3
  let s2_tag     := makeIndexedWires "s2_tag" 6
  let s2_valid   := Wire.mk "s2_valid"

  -- Stage 3 registers (s2 → s3)
  let s3_src1    := makeIndexedWires "s3_src1" 32
  let s3_src2    := makeIndexedWires "s3_src2" 32
  let s3_sub     := Wire.mk "s3_sub"
  let s3_rm      := makeIndexedWires "s3_rm" 3
  let s3_tag     := makeIndexedWires "s3_tag" 6
  let s3_valid   := Wire.mk "s3_valid"

  -- Stage 1 DFFs: latch inputs
  let stage1_gates :=
    mkDFFBank src1 s1_src1 clock reset ++
    mkDFFBank src2 s1_src2 clock reset ++
    [Gate.mkDFF op_sub clock reset s1_sub] ++
    mkDFFBank rm s1_rm clock reset ++
    mkDFFBank dest_tag s1_tag clock reset ++
    [Gate.mkDFF valid_in clock reset s1_valid]

  -- Stage 2 DFFs: pass through
  let stage2_gates :=
    mkDFFBank s1_src1 s2_src1 clock reset ++
    mkDFFBank s1_src2 s2_src2 clock reset ++
    [Gate.mkDFF s1_sub clock reset s2_sub] ++
    mkDFFBank s1_rm s2_rm clock reset ++
    mkDFFBank s1_tag s2_tag clock reset ++
    [Gate.mkDFF s1_valid clock reset s2_valid]

  -- Stage 3 DFFs: pass through
  let stage3_gates :=
    mkDFFBank s2_src1 s3_src1 clock reset ++
    mkDFFBank s2_src2 s3_src2 clock reset ++
    [Gate.mkDFF s2_sub clock reset s3_sub] ++
    mkDFFBank s2_rm s3_rm clock reset ++
    mkDFFBank s2_tag s3_tag clock reset ++
    [Gate.mkDFF s2_valid clock reset s3_valid]

  -- Stage 4 outputs: BUF from stage 3 (placeholder for real computation)
  let output_gates :=
    mkBUFBank s3_src1 result ++          -- result = s3_src1 (placeholder)
    mkBUFBank s3_tag tag_out ++          -- tag passthrough
    [Gate.mkBUF s3_valid valid_out] ++   -- valid passthrough
    (exc.map fun e => Gate.mkBUF zero e) -- exc = all zeros (placeholder)

  { name := "FPAdder"
    inputs := src1 ++ src2 ++ [op_sub] ++ rm ++ dest_tag ++ [valid_in, clock, reset, zero]
    outputs := result ++ tag_out ++ exc ++ [valid_out]
    gates := stage1_gates ++ stage2_gates ++ stage3_gates ++ output_gates
    instances := [] }

end Shoumei.Circuits.Sequential
