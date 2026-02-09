/-
Circuits/Sequential/FPFMA.lean - 5-Stage Pipelined Fused Multiply-Add

A pipeline timing skeleton for IEEE 754 binary32 fused multiply-add (FMA).
Real arithmetic is computed by the behavioral model; this circuit
provides the structural pipeline registers for timing/scheduling.

Pipeline stages:
  Stage 1: Latch inputs (src1, src2, src3, rm, tag, valid)
  Stage 2: Hold (placeholder for multiply)
  Stage 3: Hold (placeholder for alignment/add)
  Stage 4: Hold (placeholder for normalize/round)
  Stage 5: Output

Inputs (109):
  src1[31:0], src2[31:0], src3[31:0] - three FP operands
  rm[2:0]                            - rounding mode
  dest_tag[5:0]                      - physical register tag
  valid_in                           - input valid
  clock, reset                       - sequential control
  zero                               - constant low

Outputs (44):
  result[31:0]  - FP FMA result (placeholder: BUF s4_src1)
  tag_out[5:0]  - destination tag
  exc[4:0]      - exception flags (tied to zero)
  valid_out     - output valid
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.RippleCarryAdder

namespace Shoumei.Circuits.Sequential

open Shoumei
open Shoumei.Circuits.Combinational

/-- Create a bank of DFFs with matching d/q wire lists. -/
private def mkDFFBank (d_wires q_wires : List Wire) (clock reset : Wire) : List Gate :=
  List.zipWith (fun d q => Gate.mkDFF d clock reset q) d_wires q_wires

/-- Build a 5-stage pipelined FP fused multiply-add skeleton circuit.

    **Inputs (109 total):**
    - src1[31:0]: First FP operand
    - src2[31:0]: Second FP operand
    - src3[31:0]: Third FP operand (addend)
    - rm[2:0]: Rounding mode
    - dest_tag[5:0]: Physical register destination tag
    - valid_in: Input valid signal
    - clock, reset: Sequential control
    - zero: Constant low

    **Outputs (44 total):**
    - result[31:0]: FP FMA result (placeholder)
    - tag_out[5:0]: Pass-through destination tag
    - exc[4:0]: Exception flags (tied low)
    - valid_out: Output valid

    **Pipeline DFF banks (106 DFFs per stage boundary):**
    - Stage 1→2: s1_src1[31:0], s1_src2[31:0], s1_src3[31:0], s1_rm[2:0], s1_tag[5:0], s1_valid
    - Stage 2→3: s2_*
    - Stage 3→4: s3_*
    - Stage 4→5: s4_*
    Total: 424 DFFs
-/
def mkFPFMA : Circuit :=
  -- ══════════════════════════════════════════════
  -- Input wires
  -- ══════════════════════════════════════════════
  let src1 := makeIndexedWires "src1" 32
  let src2 := makeIndexedWires "src2" 32
  let src3 := makeIndexedWires "src3" 32
  let rm := makeIndexedWires "rm" 3
  let dest_tag := makeIndexedWires "dest_tag" 6
  let valid_in := Wire.mk "valid_in"
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"

  -- ══════════════════════════════════════════════
  -- Output wires
  -- ══════════════════════════════════════════════
  let result := makeIndexedWires "result" 32
  let tag_out := makeIndexedWires "tag_out" 6
  let exc := makeIndexedWires "exc" 5
  let valid_out := Wire.mk "valid_out"

  -- ══════════════════════════════════════════════
  -- Stage 1 pipeline registers (input → stage 1)
  -- ══════════════════════════════════════════════
  let s1_src1 := makeIndexedWires "s1_src1" 32
  let s1_src2 := makeIndexedWires "s1_src2" 32
  let s1_src3 := makeIndexedWires "s1_src3" 32
  let s1_rm := makeIndexedWires "s1_rm" 3
  let s1_tag := makeIndexedWires "s1_tag" 6
  let s1_valid := Wire.mk "s1_valid"

  let s1_dffs :=
    mkDFFBank src1 s1_src1 clock reset ++
    mkDFFBank src2 s1_src2 clock reset ++
    mkDFFBank src3 s1_src3 clock reset ++
    mkDFFBank rm s1_rm clock reset ++
    mkDFFBank dest_tag s1_tag clock reset ++
    [Gate.mkDFF valid_in clock reset s1_valid]

  -- ══════════════════════════════════════════════
  -- Stage 2 pipeline registers (stage 1 → stage 2)
  -- ══════════════════════════════════════════════
  let s2_src1 := makeIndexedWires "s2_src1" 32
  let s2_src2 := makeIndexedWires "s2_src2" 32
  let s2_src3 := makeIndexedWires "s2_src3" 32
  let s2_rm := makeIndexedWires "s2_rm" 3
  let s2_tag := makeIndexedWires "s2_tag" 6
  let s2_valid := Wire.mk "s2_valid"

  let s2_dffs :=
    mkDFFBank s1_src1 s2_src1 clock reset ++
    mkDFFBank s1_src2 s2_src2 clock reset ++
    mkDFFBank s1_src3 s2_src3 clock reset ++
    mkDFFBank s1_rm s2_rm clock reset ++
    mkDFFBank s1_tag s2_tag clock reset ++
    [Gate.mkDFF s1_valid clock reset s2_valid]

  -- ══════════════════════════════════════════════
  -- Stage 3 pipeline registers (stage 2 → stage 3)
  -- ══════════════════════════════════════════════
  let s3_src1 := makeIndexedWires "s3_src1" 32
  let s3_src2 := makeIndexedWires "s3_src2" 32
  let s3_src3 := makeIndexedWires "s3_src3" 32
  let s3_rm := makeIndexedWires "s3_rm" 3
  let s3_tag := makeIndexedWires "s3_tag" 6
  let s3_valid := Wire.mk "s3_valid"

  let s3_dffs :=
    mkDFFBank s2_src1 s3_src1 clock reset ++
    mkDFFBank s2_src2 s3_src2 clock reset ++
    mkDFFBank s2_src3 s3_src3 clock reset ++
    mkDFFBank s2_rm s3_rm clock reset ++
    mkDFFBank s2_tag s3_tag clock reset ++
    [Gate.mkDFF s2_valid clock reset s3_valid]

  -- ══════════════════════════════════════════════
  -- Stage 4 pipeline registers (stage 3 → stage 4)
  -- ══════════════════════════════════════════════
  let s4_src1 := makeIndexedWires "s4_src1" 32
  let s4_src2 := makeIndexedWires "s4_src2" 32
  let s4_src3 := makeIndexedWires "s4_src3" 32
  let s4_rm := makeIndexedWires "s4_rm" 3
  let s4_tag := makeIndexedWires "s4_tag" 6
  let s4_valid := Wire.mk "s4_valid"

  let s4_dffs :=
    mkDFFBank s3_src1 s4_src1 clock reset ++
    mkDFFBank s3_src2 s4_src2 clock reset ++
    mkDFFBank s3_src3 s4_src3 clock reset ++
    mkDFFBank s3_rm s4_rm clock reset ++
    mkDFFBank s3_tag s4_tag clock reset ++
    [Gate.mkDFF s3_valid clock reset s4_valid]

  -- ══════════════════════════════════════════════
  -- Output logic (placeholder: result = BUF s4_src1)
  -- ══════════════════════════════════════════════
  let result_gates := (List.range 32).map (fun i =>
    Gate.mkBUF (s4_src1[i]!) (result[i]!)
  )

  let tag_out_gates := (List.range 6).map (fun i =>
    Gate.mkBUF (s4_tag[i]!) (tag_out[i]!)
  )

  let valid_gate := [Gate.mkBUF s4_valid valid_out]

  -- Exception flags tied to zero
  let exc_gates := (List.range 5).map (fun i =>
    Gate.mkBUF zero (exc[i]!)
  )

  -- ══════════════════════════════════════════════
  -- Assemble circuit
  -- ══════════════════════════════════════════════
  let all_gates :=
    s1_dffs ++
    s2_dffs ++
    s3_dffs ++
    s4_dffs ++
    result_gates ++
    tag_out_gates ++
    valid_gate ++
    exc_gates

  { name := "FPFMA"
    inputs := src1 ++ src2 ++ src3 ++ rm ++ dest_tag ++ [valid_in, clock, reset, zero]
    outputs := result ++ tag_out ++ exc ++ [valid_out]
    gates := all_gates
    instances := []
    signalGroups := [
      { name := "src1", width := 32, wires := src1 },
      { name := "src2", width := 32, wires := src2 },
      { name := "src3", width := 32, wires := src3 },
      { name := "rm", width := 3, wires := rm },
      { name := "dest_tag", width := 6, wires := dest_tag },
      { name := "result", width := 32, wires := result },
      { name := "tag_out", width := 6, wires := tag_out },
      { name := "exc", width := 5, wires := exc }
    ]
  }

/-- Convenience definition for the FP FMA circuit. -/
def fpFMACircuit : Circuit := mkFPFMA

end Shoumei.Circuits.Sequential
