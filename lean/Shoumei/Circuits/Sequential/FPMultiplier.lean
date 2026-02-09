/-
Circuits/Sequential/FPMultiplier.lean - 3-Stage Pipelined FP Multiplier

A pipeline timing skeleton for IEEE 754 binary32 multiplication.
Real arithmetic is computed by the behavioral model; this circuit
provides the structural pipeline registers for timing/scheduling.

Pipeline stages:
  Stage 1: Latch inputs (src1, src2, rm, tag, valid)
  Stage 2: Hold (placeholder for mantissa multiply)
  Stage 3: Output (placeholder for normalize/round)

Inputs (75):
  src1[31:0], src2[31:0] - FP operands
  rm[2:0]                - rounding mode
  dest_tag[5:0]          - physical register tag
  valid_in               - input valid
  clock, reset           - sequential control
  zero                   - constant low

Outputs (44):
  result[31:0]  - FP product (placeholder: BUF src2 stage output)
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
def mkDFFBank (d_wires q_wires : List Wire) (clock reset : Wire) : List Gate :=
  List.zipWith (fun d q => Gate.mkDFF d clock reset q) d_wires q_wires

/-- Build a 3-stage pipelined FP multiplier skeleton circuit.

    **Inputs (75 total):**
    - src1[31:0]: First FP operand
    - src2[31:0]: Second FP operand
    - rm[2:0]: Rounding mode
    - dest_tag[5:0]: Physical register destination tag
    - valid_in: Input valid signal
    - clock, reset: Sequential control
    - zero: Constant low

    **Outputs (44 total):**
    - result[31:0]: FP multiplication result (placeholder)
    - tag_out[5:0]: Pass-through destination tag
    - exc[4:0]: Exception flags (tied low)
    - valid_out: Output valid

    **Pipeline DFF banks:**
    - Stage 1→2: s1_src1[31:0], s1_src2[31:0], s1_rm[2:0], s1_tag[5:0], s1_valid (74 DFFs)
    - Stage 2→3: s2_src1[31:0], s2_src2[31:0], s2_rm[2:0], s2_tag[5:0], s2_valid (74 DFFs)
    Total: 148 DFFs
-/
def mkFPMultiplier : Circuit :=
  -- ══════════════════════════════════════════════
  -- Input wires
  -- ══════════════════════════════════════════════
  let src1 := makeIndexedWires "src1" 32
  let src2 := makeIndexedWires "src2" 32
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
  let s1_rm := makeIndexedWires "s1_rm" 3
  let s1_tag := makeIndexedWires "s1_tag" 6
  let s1_valid := Wire.mk "s1_valid"

  let s1_dffs :=
    mkDFFBank src1 s1_src1 clock reset ++
    mkDFFBank src2 s1_src2 clock reset ++
    mkDFFBank rm s1_rm clock reset ++
    mkDFFBank dest_tag s1_tag clock reset ++
    [Gate.mkDFF valid_in clock reset s1_valid]

  -- ══════════════════════════════════════════════
  -- Stage 2 pipeline registers (stage 1 → stage 2)
  -- ══════════════════════════════════════════════
  let s2_src1 := makeIndexedWires "s2_src1" 32
  let s2_src2 := makeIndexedWires "s2_src2" 32
  let s2_rm := makeIndexedWires "s2_rm" 3
  let s2_tag := makeIndexedWires "s2_tag" 6
  let s2_valid := Wire.mk "s2_valid"

  let s2_dffs :=
    mkDFFBank s1_src1 s2_src1 clock reset ++
    mkDFFBank s1_src2 s2_src2 clock reset ++
    mkDFFBank s1_rm s2_rm clock reset ++
    mkDFFBank s1_tag s2_tag clock reset ++
    [Gate.mkDFF s1_valid clock reset s2_valid]

  -- ══════════════════════════════════════════════
  -- Output logic (placeholder: result = BUF s2_src1)
  -- ══════════════════════════════════════════════
  let result_gates := (List.range 32).map (fun i =>
    Gate.mkBUF (s2_src1[i]!) (result[i]!)
  )

  let tag_out_gates := (List.range 6).map (fun i =>
    Gate.mkBUF (s2_tag[i]!) (tag_out[i]!)
  )

  let valid_gate := [Gate.mkBUF s2_valid valid_out]

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
    result_gates ++
    tag_out_gates ++
    valid_gate ++
    exc_gates

  { name := "FPMultiplier"
    inputs := src1 ++ src2 ++ rm ++ dest_tag ++ [valid_in, clock, reset, zero]
    outputs := result ++ tag_out ++ exc ++ [valid_out]
    gates := all_gates
    instances := []
    signalGroups := [
      { name := "src1", width := 32, wires := src1 },
      { name := "src2", width := 32, wires := src2 },
      { name := "rm", width := 3, wires := rm },
      { name := "dest_tag", width := 6, wires := dest_tag },
      { name := "result", width := 32, wires := result },
      { name := "tag_out", width := 6, wires := tag_out },
      { name := "exc", width := 5, wires := exc }
    ]
  }

/-- Convenience definition for the FP multiplier circuit. -/
def fpMultiplierCircuit : Circuit := mkFPMultiplier

end Shoumei.Circuits.Sequential
