/-
Circuits/Combinational/Multiplier.lean - 3-Stage Pipelined Array Multiplier (32x32 -> 64)

A pipelined unsigned 32x32 multiplier that produces a 64-bit product
in 3 clock cycles. The pipeline passes through metadata (destination tag,
operation type, valid bit) alongside the computation.

Architecture:
  Stage 1: Partial product generation (1024 AND gates) +
           CSA tree reduction via CSACompressor64 instances (32 rows -> 2)
  Stage 2: Pipeline register pass-through (timing closure)
  Stage 3: Final 64-bit ripple-carry addition + result selection

The CSA tree uses CSACompressor64 sub-modules (each compresses 3 rows to 2)
arranged hierarchically. This keeps each module within JVM class file limits
for Chisel code generation.

Interface:
  Inputs:  a[31:0], b[31:0], op[2:0], dest_tag[5:0], valid_in, clock, reset, zero
  Outputs: result[31:0], tag_out[5:0], valid_out

Operation types (op encoding):
  000 = MUL    (return low  32 bits of product)
  001 = MULH   (return high 32 bits, signed x signed)
  010 = MULHSU (return high 32 bits, signed x unsigned)
  011 = MULHU  (return high 32 bits, unsigned x unsigned)
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.RippleCarryAdder

namespace Shoumei.Circuits.Combinational

open Shoumei

/-! ## Behavioral Model -/

/-- Pipeline state for the 3-stage multiplier. -/
structure MulPipelineState where
  stage1_valid : Bool
  stage1_tag : Fin 64
  stage1_op : Nat
  stage1_partial : UInt64
  stage2_valid : Bool
  stage2_tag : Fin 64
  stage2_op : Nat
  stage2_sum : UInt64
  stage2_carry : UInt64
  result_valid : Bool
  result_tag : Fin 64
  result_data : UInt64
  result_op : Nat
  deriving Repr

/-- Initial (reset) state: all stages invalid. -/
def MulPipelineState.init : MulPipelineState :=
  { stage1_valid := false, stage1_tag := 0, stage1_op := 0, stage1_partial := 0
    stage2_valid := false, stage2_tag := 0, stage2_op := 0
    stage2_sum := 0, stage2_carry := 0
    result_valid := false, result_tag := 0, result_data := 0, result_op := 0 }

/-- Step the multiplier pipeline by one clock cycle. -/
def mulPipelineStep
    (state : MulPipelineState) (a b : UInt32)
    (tag : Fin 64) (op : Nat) (valid : Bool)
    : MulPipelineState × Option (Fin 64 × UInt32) :=
  let product := state.result_data
  let result32 : UInt32 :=
    if state.result_op == 0 then (product.toNat % (2^32)).toUInt32
    else (product.toNat / (2^32)).toUInt32
  let output := if state.result_valid then some (state.result_tag, result32) else none
  let full_product : UInt64 := (a.toNat * b.toNat).toUInt64
  let newState : MulPipelineState :=
    { stage1_valid := valid, stage1_tag := tag, stage1_op := op
      stage1_partial := full_product
      stage2_valid := state.stage1_valid, stage2_tag := state.stage1_tag
      stage2_op := state.stage1_op
      stage2_sum := state.stage1_partial, stage2_carry := 0
      result_valid := state.stage2_valid, result_tag := state.stage2_tag
      result_data := state.stage2_sum + state.stage2_carry
      result_op := state.stage2_op }
  (newState, output)

/-- Verify pipeline correctness (4 clock edges: inject + 3 register delays). -/
def verifyMulPipeline (a b : UInt32) : Bool :=
  let s0 := MulPipelineState.init
  let (s1, _) := mulPipelineStep s0 a b 0 0 true
  let (s2, _) := mulPipelineStep s1 0 0 0 0 false
  let (s3, _) := mulPipelineStep s2 0 0 0 0 false
  let (_, out) := mulPipelineStep s3 0 0 0 0 false
  match out with
  | some (_, result) => result == (a * b)
  | none => false

/-! ## CSA Compressor Sub-Module -/

/-- Build a 64-bit 3-to-2 carry-save compressor.

    At each bit position: sum = x XOR y XOR z, carry = majority(x, y, z).
    Carry output is shifted left by 1 (carry[0] = 0).

    Inputs: x[63:0], y[63:0], z[63:0], zero (193 total)
    Outputs: sum[63:0], carry[63:0] (128 total)
    Gates: 512 (7 per bit × 64 + 64 shift BUFs) -/
def mkCSACompressor64 : Circuit :=
  let width := 64
  let x := makeIndexedWires "x" width
  let y := makeIndexedWires "y" width
  let z := makeIndexedWires "z" width
  let zero := Wire.mk "zero"
  let s := makeIndexedWires "sum" width
  let c := makeIndexedWires "c" width
  let c_shifted := makeIndexedWires "carry" width  -- output carry (shifted)

  let csa_gates := List.flatten <| (List.range width).map fun j =>
    let xy := Wire.mk s!"xy{j}"
    [
      Gate.mkXOR (x[j]!) (y[j]!) xy,
      Gate.mkXOR xy (z[j]!) (s[j]!),
      Gate.mkAND (x[j]!) (y[j]!) (Wire.mk s!"ab{j}"),
      Gate.mkAND (y[j]!) (z[j]!) (Wire.mk s!"bc{j}"),
      Gate.mkAND (x[j]!) (z[j]!) (Wire.mk s!"ac{j}"),
      Gate.mkOR (Wire.mk s!"ab{j}") (Wire.mk s!"bc{j}") (Wire.mk s!"abbc{j}"),
      Gate.mkOR (Wire.mk s!"abbc{j}") (Wire.mk s!"ac{j}") (c[j]!)
    ]

  let shift_gates :=
    [Gate.mkBUF zero (c_shifted[0]!)] ++
    (List.range (width - 1)).map fun j =>
      Gate.mkBUF (c[j]!) (c_shifted[j + 1]!)

  { name := "CSACompressor64"
    inputs := x ++ y ++ z ++ [zero]
    outputs := s ++ c_shifted
    gates := csa_gates ++ shift_gates
    instances := []
    -- V2 codegen annotations
    signalGroups := [
      { name := "x", width := width, wires := x },
      { name := "y", width := width, wires := y },
      { name := "z", width := width, wires := z },
      { name := "sum", width := width, wires := s },
      { name := "carry", width := width, wires := c_shifted },
      { name := "c", width := width, wires := c }
    ]
  }

/-- Convenience alias for CSA compressor. -/
def csaCompressor64 : Circuit := mkCSACompressor64

/-! ## Structural Circuit Helpers -/

/-- Generate a single partial product row: pp_row_i[j] = a[i] AND b[j]
    shifted left by i positions. -/
private def mkPartialProductRow (i : Nat)
    (a_wires b_wires : List Wire) (zero_wire : Wire)
    : List Wire × List Gate :=
  let pp := makeIndexedWires s!"pp{i}_" 64
  let low_zero_gates := (List.range i).map fun j =>
    Gate.mkBUF zero_wire (pp[j]!)
  let and_gates := (List.range 32).map fun j =>
    Gate.mkAND (a_wires[i]!) (b_wires[j]!) (pp[i + j]!)
  let high_zero_gates := (List.range (64 - i - 32)).map fun j =>
    Gate.mkBUF zero_wire (pp[i + 32 + j]!)
  (pp, low_zero_gates ++ and_gates ++ high_zero_gates)

/-- Build an array of DFF gates for pipeline register storage. -/
private def mkPipelineRegister
    (d_wires q_wires : List Wire) (clock reset : Wire) : List Gate :=
  List.zipWith (fun d q => Gate.mkDFF d clock reset q) d_wires q_wires

/-- Build a hierarchical CSA tree using CSACompressor64 instances.

    Takes a list of 64-bit row wire lists and returns:
    - The two final rows (sum, carry) as wire lists
    - All BUF routing gates
    - All CSACompressor64 instances

    This is recursive: compress groups of 3 rows into 2, pass leftover
    rows through, repeat until 2 rows remain. -/
private partial def mkCSATreeHierarchical
    (rows : List (List Wire)) (zero_wire : Wire)
    (level : Nat := 0) (baseIdx : Nat := 0)
    : List Wire × List Wire × List Gate × List CircuitInstance :=
  match rows with
  | [] =>
    let s := makeIndexedWires "csa_empty_s" 64
    let c := makeIndexedWires "csa_empty_c" 64
    let g := (List.range 64).map fun j => Gate.mkBUF zero_wire (s[j]!)
    let g2 := (List.range 64).map fun j => Gate.mkBUF zero_wire (c[j]!)
    (s, c, g ++ g2, [])
  | [single] =>
    let c := makeIndexedWires s!"csa_l{level}_one_c" 64
    let g := (List.range 64).map fun j => Gate.mkBUF zero_wire (c[j]!)
    (single, c, g, [])
  | [r1, r2] => (r1, r2, [], [])
  | _ =>
    -- Compress groups of 3 into 2
    let rec compressGroups (rs : List (List Wire)) (idx : Nat)
        : List (List Wire) × List Gate × List CircuitInstance :=
      match rs with
      | x :: y :: z :: rest =>
        let tag := s!"csa_l{level}_g{idx}"
        let s_out := makeIndexedWires s!"{tag}_s" 64
        let c_out := makeIndexedWires s!"{tag}_c" 64
        let inst : CircuitInstance := {
          moduleName := "CSACompressor64"
          instName := s!"u_{tag}"
          portMap :=
            (x.enum.map (fun ⟨i, w⟩ => (s!"x[{i}]", w))) ++
            (y.enum.map (fun ⟨i, w⟩ => (s!"y[{i}]", w))) ++
            (z.enum.map (fun ⟨i, w⟩ => (s!"z[{i}]", w))) ++
            [("zero", zero_wire)] ++
            (s_out.enum.map (fun ⟨i, w⟩ => (s!"sum[{i}]", w))) ++
            (c_out.enum.map (fun ⟨i, w⟩ => (s!"carry[{i}]", w)))
        }
        let (more_rows, more_gates, more_insts) := compressGroups rest (idx + 1)
        (s_out :: c_out :: more_rows, more_gates, inst :: more_insts)
      | remaining => (remaining, [], [])
    let (next_rows, gates1, insts1) := compressGroups rows 0
    let (final_s, final_c, gates2, insts2) :=
      mkCSATreeHierarchical next_rows zero_wire (level + 1) (baseIdx + insts1.length)
    (final_s, final_c, gates1 ++ gates2, insts1 ++ insts2)

/-! ## Structural Circuit -/

/-- Build the 3-stage pipelined 32x32 unsigned multiplier (hierarchical).

    Uses CSACompressor64 instances for the reduction tree, keeping each
    module within Chisel/JVM class file size limits.

    Inputs (77): a[31:0], b[31:0], op[2:0], dest_tag[5:0], valid_in, clock, reset, zero
    Outputs (39): result[31:0], tag_out[5:0], valid_out

    Instances: ~30 CSACompressor64 + 1 RippleCarryAdder64 -/
def mkPipelinedMultiplier : Circuit :=
  let a := makeIndexedWires "a" 32
  let b := makeIndexedWires "b" 32
  let op := makeIndexedWires "op" 3
  let dest_tag := makeIndexedWires "dest_tag" 6
  let valid_in := Wire.mk "valid_in"
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"

  let result := makeIndexedWires "result" 32
  let tag_out := makeIndexedWires "tag_out" 6
  let valid_out := Wire.mk "valid_out"

  -- ========================================================================
  -- Stage 1: Partial Product Generation + Hierarchical CSA Tree
  -- ========================================================================

  let ppResults := (List.range 32).map fun i =>
    mkPartialProductRow i a b zero
  let pp_rows := ppResults.map (·.1)
  let pp_gates := ppResults.map (·.2) |> List.flatten

  -- Hierarchical CSA tree: instances instead of flat gates
  let (sum_s1, carry_s1, csa_routing_gates, csa_instances) :=
    mkCSATreeHierarchical pp_rows zero

  -- Pipeline register 1 (hierarchical: use Register instances)
  let s1_sum_q := makeIndexedWires "s1_sum_q" 64
  let s1_carry_q := makeIndexedWires "s1_carry_q" 64
  let s1_op_q := makeIndexedWires "s1_op_q" 3
  let s1_tag_q := makeIndexedWires "s1_tag_q" 6
  let s1_valid_q := Wire.mk "s1_valid_q"

  let pipe_reg1_instances := [
    {
      moduleName := "Register64"
      instName := "u_pipe1_sum"
      portMap :=
        (sum_s1.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
        [("clock", clock), ("reset", reset)] ++
        (s1_sum_q.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w)))
    },
    {
      moduleName := "Register64"
      instName := "u_pipe1_carry"
      portMap :=
        (carry_s1.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
        [("clock", clock), ("reset", reset)] ++
        (s1_carry_q.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w)))
    },
    {
      moduleName := "Register3"
      instName := "u_pipe1_op"
      portMap :=
        (op.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
        [("clock", clock), ("reset", reset)] ++
        (s1_op_q.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w)))
    },
    {
      moduleName := "Register6"
      instName := "u_pipe1_tag"
      portMap :=
        (dest_tag.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
        [("clock", clock), ("reset", reset)] ++
        (s1_tag_q.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w)))
    }
  ]

  let pipe_reg1_valid_gates := [Gate.mkDFF valid_in clock reset s1_valid_q]

  -- ========================================================================
  -- Stage 2: Pipeline pass-through (hierarchical: use Register instances)
  -- ========================================================================

  let s2_sum_q := makeIndexedWires "s2_sum_q" 64
  let s2_carry_q := makeIndexedWires "s2_carry_q" 64
  let s2_op_q := makeIndexedWires "s2_op_q" 3
  let s2_tag_q := makeIndexedWires "s2_tag_q" 6
  let s2_valid_q := Wire.mk "s2_valid_q"

  let pipe_reg2_instances := [
    {
      moduleName := "Register64"
      instName := "u_pipe2_sum"
      portMap :=
        (s1_sum_q.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
        [("clock", clock), ("reset", reset)] ++
        (s2_sum_q.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w)))
    },
    {
      moduleName := "Register64"
      instName := "u_pipe2_carry"
      portMap :=
        (s1_carry_q.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
        [("clock", clock), ("reset", reset)] ++
        (s2_carry_q.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w)))
    },
    {
      moduleName := "Register3"
      instName := "u_pipe2_op"
      portMap :=
        (s1_op_q.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
        [("clock", clock), ("reset", reset)] ++
        (s2_op_q.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w)))
    },
    {
      moduleName := "Register6"
      instName := "u_pipe2_tag"
      portMap :=
        (s1_tag_q.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
        [("clock", clock), ("reset", reset)] ++
        (s2_tag_q.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w)))
    }
  ]

  let pipe_reg2_valid_gates := [Gate.mkDFF s1_valid_q clock reset s2_valid_q]

  -- ========================================================================
  -- Stage 3: Final Addition + Output Selection
  -- ========================================================================

  let adder_sum := makeIndexedWires "add_sum" 64

  let rca64_inst : CircuitInstance := {
    moduleName := "RippleCarryAdder64"
    instName := "u_final_adder"
    portMap :=
      (s2_sum_q.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (s2_carry_q.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("cin", zero)] ++
      (adder_sum.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }

  -- Output selection: op==000 → low 32 bits, else → high 32 bits
  let op_nonzero_01 := Wire.mk "op_nz_01"
  let op_nonzero := Wire.mk "op_nonzero"
  let op_sel_gates := [
    Gate.mkOR s2_op_q[0]! s2_op_q[1]! op_nonzero_01,
    Gate.mkOR op_nonzero_01 s2_op_q[2]! op_nonzero
  ]

  let result_mux_gates := (List.range 32).map fun i =>
    Gate.mkMUX (adder_sum[i]!) (adder_sum[i + 32]!) op_nonzero (result[i]!)

  let tag_passthrough := List.zipWith (fun src dst =>
    Gate.mkBUF src dst) s2_tag_q tag_out

  let valid_passthrough := [Gate.mkBUF s2_valid_q valid_out]

  -- ========================================================================
  -- Assemble
  -- ========================================================================

  let all_gates :=
    pp_gates ++
    csa_routing_gates ++
    pipe_reg1_valid_gates ++
    pipe_reg2_valid_gates ++
    op_sel_gates ++
    result_mux_gates ++
    tag_passthrough ++
    valid_passthrough

  { name := "PipelinedMultiplier"
    inputs := a ++ b ++ op ++ dest_tag ++ [valid_in, clock, reset, zero]
    outputs := result ++ tag_out ++ [valid_out]
    gates := all_gates
    instances := csa_instances ++ pipe_reg1_instances ++ pipe_reg2_instances ++ [rca64_inst]
    -- V2 codegen annotations
    signalGroups := [
      { name := "a", width := 32, wires := a },
      { name := "b", width := 32, wires := b },
      { name := "op", width := 3, wires := op },
      { name := "dest_tag", width := 6, wires := dest_tag },
      { name := "result", width := 32, wires := result },
      { name := "tag_out", width := 6, wires := tag_out },
      { name := "s1_sum_q", width := 64, wires := s1_sum_q },
      { name := "s1_carry_q", width := 64, wires := s1_carry_q },
      { name := "s1_op_q", width := 3, wires := s1_op_q },
      { name := "s1_tag_q", width := 6, wires := s1_tag_q },
      { name := "s2_sum_q", width := 64, wires := s2_sum_q },
      { name := "s2_carry_q", width := 64, wires := s2_carry_q },
      { name := "s2_op_q", width := 3, wires := s2_op_q },
      { name := "s2_tag_q", width := 6, wires := s2_tag_q },
      { name := "add_sum", width := 64, wires := adder_sum }
    ]
  }

/-- Convenience alias. -/
def pipelinedMultiplier : Circuit := mkPipelinedMultiplier

end Shoumei.Circuits.Combinational
