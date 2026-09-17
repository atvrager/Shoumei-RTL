/-
Circuits/Combinational/Multiplier.lean - 3-Stage Pipelined Array Multiplier (32x32 -> 64)

A pipelined unsigned 32x32 multiplier that produces a 64-bit product
in 3 clock cycles. The pipeline passes through metadata (destination tag,
operation type, valid bit) alongside the computation.

Architecture:
  Stage 1: Partial product generation (1024 AND gates) +
           CSA tree reduction via CSACompressor64 instances (32 rows -> 2)
  Stage 2: Pipeline register pass-through (timing closure)
  Stage 3: Final 64-bit Kogge-Stone addition + result selection

The CSA tree uses CSACompressor64 sub-modules (each compresses 3 rows to 2)
arranged hierarchically, so no single module grows unmanageably large.

Interface:
  Inputs:  a[31:0], b[31:0], op[2:0], dest_tag[5:0], valid_in, clock, reset, zero, one
  Outputs: result[31:0], tag_out[5:0], valid_out

Operation types (op encoding):
  000 = MUL    (return low  32 bits of product)
  001 = MULH   (return high 32 bits, signed x signed)
  010 = MULHSU (return high 32 bits, signed x unsigned)
  011 = MULHU  (return high 32 bits, unsigned x unsigned)
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.RippleCarryAdder
import Shoumei.Circuits.Combinational.KoggeStoneAdder
import Shoumei.Circuits.Combinational.Subtractor

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
  -- Compute full 64-bit product with sign handling based on op
  let full_product : UInt64 := match op with
    | 1 => -- MULH: signed × signed
      let sa : Int := if a.toNat >= 2^31 then (a.toNat : Int) - 2^32 else a.toNat
      let sb : Int := if b.toNat >= 2^31 then (b.toNat : Int) - 2^32 else b.toNat
      let prod := sa * sb
      let wrapped := ((prod % (2^64 : Int)) + (2^64 : Int)).toNat % (2^64)
      wrapped.toUInt64
    | 2 => -- MULHSU: signed × unsigned
      let sa : Int := if a.toNat >= 2^31 then (a.toNat : Int) - 2^32 else a.toNat
      let prod := sa * (b.toNat : Int)
      let wrapped := ((prod % (2^64 : Int)) + (2^64 : Int)).toNat % (2^64)
      wrapped.toUInt64
    | _ => (a.toNat * b.toNat).toUInt64  -- MUL, MULHU: unsigned
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
    keepHierarchy := true
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
    module small.

    Inputs (78): a[31:0], b[31:0], op[2:0], dest_tag[5:0], valid_in, clock, reset, zero, one
    Outputs (39): result[31:0], tag_out[5:0], valid_out

    Instances: ~30 CSACompressor64 + 1 KoggeStoneAdder64 + 4 Register32 + 2 Subtractor32 -/
def mkPipelinedMultiplier : Circuit :=
  let a := makeIndexedWires "a" 32
  let b := makeIndexedWires "b" 32
  let op := makeIndexedWires "op" 3
  let dest_tag := makeIndexedWires "dest_tag" 6
  let valid_in := Wire.mk "valid_in"
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

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
  -- Pipeline a and b through stages 1-2 for sign correction at stage 3
  -- ========================================================================
  let s1_a_q := makeIndexedWires "s1_a_q" 32
  let s1_b_q := makeIndexedWires "s1_b_q" 32
  let s2_a_q := makeIndexedWires "s2_a_q" 32
  let s2_b_q := makeIndexedWires "s2_b_q" 32

  let pipe_ab_stage1_instances := [
    {
      moduleName := "Register32"
      instName := "u_pipe1_a"
      portMap :=
        (a.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
        [("clock", clock), ("reset", reset)] ++
        (s1_a_q.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w)))
    },
    {
      moduleName := "Register32"
      instName := "u_pipe1_b"
      portMap :=
        (b.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
        [("clock", clock), ("reset", reset)] ++
        (s1_b_q.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w)))
    }
  ]

  let pipe_ab_stage2_instances := [
    {
      moduleName := "Register32"
      instName := "u_pipe2_a"
      portMap :=
        (s1_a_q.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
        [("clock", clock), ("reset", reset)] ++
        (s2_a_q.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w)))
    },
    {
      moduleName := "Register32"
      instName := "u_pipe2_b"
      portMap :=
        (s1_b_q.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
        [("clock", clock), ("reset", reset)] ++
        (s2_b_q.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w)))
    }
  ]

  -- ========================================================================
  -- Stage 3: Final Addition + Sign Correction + Output Selection
  -- ========================================================================

  let adder_sum := makeIndexedWires "add_sum" 64

  let ksa64_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder64"
    instName := "u_final_adder"
    portMap :=
      (s2_sum_q.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (s2_carry_q.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("cin", zero)] ++
      (adder_sum.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }

  -- Baugh-Wooley sign correction for high 32 bits:
  --   MULH   (op=001): corrected_high = unsigned_high - (a[31]?b:0) - (b[31]?a:0)
  --   MULHSU (op=010): corrected_high = unsigned_high - (a[31]?b:0)
  --   MUL/MULHU:       no correction needed

  -- Decode op: is_mulh = !op[2] & !op[1] & op[0], is_mulhsu = !op[2] & op[1] & !op[0]
  let not_op2 := Wire.mk "sc_not_op2"
  let not_op1 := Wire.mk "sc_not_op1"
  let not_op0 := Wire.mk "sc_not_op0"
  let is_mulh_a := Wire.mk "sc_is_mulh_a"
  let is_mulh := Wire.mk "sc_is_mulh"
  let is_mulhsu_a := Wire.mk "sc_is_mulhsu_a"
  let is_mulhsu := Wire.mk "sc_is_mulhsu"
  let needs_sub_b_pre := Wire.mk "sc_needs_sub_b_pre"
  let needs_sub_b := Wire.mk "sc_needs_sub_b"
  let needs_sub_a := Wire.mk "sc_needs_sub_a"

  let sc_decode_gates := [
    Gate.mkNOT s2_op_q[2]! not_op2,
    Gate.mkNOT s2_op_q[1]! not_op1,
    Gate.mkNOT s2_op_q[0]! not_op0,
    -- is_mulh = !op[2] & !op[1] & op[0]
    Gate.mkAND not_op2 not_op1 is_mulh_a,
    Gate.mkAND is_mulh_a s2_op_q[0]! is_mulh,
    -- is_mulhsu = !op[2] & op[1] & !op[0]
    Gate.mkAND not_op2 s2_op_q[1]! is_mulhsu_a,
    Gate.mkAND is_mulhsu_a not_op0 is_mulhsu,
    -- needs_sub_b = (is_mulh | is_mulhsu) & a[31]
    Gate.mkOR is_mulh is_mulhsu needs_sub_b_pre,
    Gate.mkAND needs_sub_b_pre s2_a_q[31]! needs_sub_b,
    -- needs_sub_a = is_mulh & b[31]
    Gate.mkAND is_mulh s2_b_q[31]! needs_sub_a
  ]

  -- sub_b[i] = b[i] & needs_sub_b (32 AND gates)
  let sub_b := makeIndexedWires "sc_sub_b" 32
  let sub_b_gates := (List.range 32).map fun i =>
    Gate.mkAND (s2_b_q[i]!) needs_sub_b (sub_b[i]!)

  -- sub_a[i] = a[i] & needs_sub_a (32 AND gates)
  let sub_a := makeIndexedWires "sc_sub_a" 32
  let sub_a_gates := (List.range 32).map fun i =>
    Gate.mkAND (s2_a_q[i]!) needs_sub_a (sub_a[i]!)

  -- high32 = adder_sum[63:32]
  let high32 := makeIndexedWires "sc_high32" 32
  let high32_buf_gates := (List.range 32).map fun i =>
    Gate.mkBUF (adder_sum[i + 32]!) (high32[i]!)

  -- corrected1 = high32 - sub_b
  let corrected1 := makeIndexedWires "sc_corr1" 32
  let sub1_inst : CircuitInstance := {
    moduleName := "Subtractor32"
    instName := "u_sign_sub1"
    portMap :=
      (high32.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (sub_b.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("one", one)] ++
      (corrected1.enum.map (fun ⟨i, w⟩ => (s!"diff_{i}", w))) ++
      [("borrow", Wire.mk "sc_borrow1")]
  }

  -- corrected2 = corrected1 - sub_a
  let corrected2 := makeIndexedWires "sc_corr2" 32
  let sub2_inst : CircuitInstance := {
    moduleName := "Subtractor32"
    instName := "u_sign_sub2"
    portMap :=
      (corrected1.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (sub_a.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("one", one)] ++
      (corrected2.enum.map (fun ⟨i, w⟩ => (s!"diff_{i}", w))) ++
      [("borrow", Wire.mk "sc_borrow2")]
  }

  -- Output selection: op==000 → low 32 bits, else → corrected high 32 bits
  let op_nonzero_01 := Wire.mk "op_nz_01"
  let op_nonzero := Wire.mk "op_nonzero"
  let op_sel_gates := [
    Gate.mkOR s2_op_q[0]! s2_op_q[1]! op_nonzero_01,
    Gate.mkOR op_nonzero_01 s2_op_q[2]! op_nonzero
  ]

  let result_mux_gates := (List.range 32).map fun i =>
    Gate.mkMUX (adder_sum[i]!) (corrected2[i]!) op_nonzero (result[i]!)

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
    sc_decode_gates ++
    sub_b_gates ++
    sub_a_gates ++
    high32_buf_gates ++
    op_sel_gates ++
    result_mux_gates ++
    tag_passthrough ++
    valid_passthrough

  { name := "PipelinedMultiplier"
    inputs := a ++ b ++ op ++ dest_tag ++ [valid_in, clock, reset, zero, one]
    outputs := result ++ tag_out ++ [valid_out]
    gates := all_gates
    instances := csa_instances ++ pipe_reg1_instances ++ pipe_ab_stage1_instances ++
      pipe_reg2_instances ++ pipe_ab_stage2_instances ++
      [ksa64_inst, sub1_inst, sub2_inst]
    keepHierarchy := true
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
      { name := "add_sum", width := 64, wires := adder_sum },
      { name := "s1_a_q", width := 32, wires := s1_a_q },
      { name := "s1_b_q", width := 32, wires := s1_b_q },
      { name := "s2_a_q", width := 32, wires := s2_a_q },
      { name := "s2_b_q", width := 32, wires := s2_b_q },
      { name := "sc_sub_b", width := 32, wires := sub_b },
      { name := "sc_sub_a", width := 32, wires := sub_a },
      { name := "sc_high32", width := 32, wires := high32 },
      { name := "sc_corr1", width := 32, wires := corrected1 },
      { name := "sc_corr2", width := 32, wires := corrected2 }
    ]
  }

/-- Convenience alias. -/
def pipelinedMultiplier : Circuit := mkPipelinedMultiplier

/-! ## 64-Bit Multiplier Building Blocks -/

/-- Single 32x32 -> 64-bit unsigned combinational multiplier sub-module.
    Uses CSACompressor64 reduction tree + KoggeStoneAdder64. -/
def mkMul32x32To64 : Circuit :=
  let a := makeIndexedWires "a" 32
  let b := makeIndexedWires "b" 32
  let zero := Wire.mk "zero"
  let product := makeIndexedWires "product" 64

  let ppResults := (List.range 32).map fun i =>
    mkPartialProductRow i a b zero
  let pp_rows := ppResults.map (·.1)
  let pp_gates := ppResults.map (·.2) |> List.flatten

  let (sum_s1, carry_s1, csa_routing_gates, csa_instances) :=
    mkCSATreeHierarchical pp_rows zero

  let ksa_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder64"
    instName := "u_final_adder"
    portMap :=
      (sum_s1.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (carry_s1.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("cin", zero)] ++
      (product.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }

  { name := "Mul32x32To64"
    inputs := a ++ b ++ [zero]
    outputs := product
    gates := pp_gates ++ csa_routing_gates
    instances := csa_instances ++ [ksa_inst]
    keepHierarchy := true
    signalGroups := [
      { name := "a", width := 32, wires := a },
      { name := "b", width := 32, wires := b },
      { name := "product", width := 64, wires := product }
    ]
  }

/-- Convenience alias. -/
def mul32x32To64 : Circuit := mkMul32x32To64

/-- 3-stage pipelined 64-bit multiplier supporting RV64M operations:
    - MUL   (op=0): lower 64 bits of product
    - MULH  (op=1): upper 64 bits (signed × signed)
    - MULHSU(op=2): upper 64 bits (signed × unsigned)
    - MULHU (op=3): upper 64 bits (unsigned × unsigned)
    - MULW  (op=8): lower 32 bits of product sign-extended to 64 bits -/
def mkPipelinedMultiplier64 : Circuit :=
  let a := makeIndexedWires "a" 64
  let b := makeIndexedWires "b" 64
  let op := makeIndexedWires "op" 4
  let dest_tag := makeIndexedWires "dest_tag" 6
  let valid_in := Wire.mk "valid_in"
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  let result := makeIndexedWires "result" 64
  let tag_out := makeIndexedWires "tag_out" 6
  let valid_out := Wire.mk "valid_out"

  -- Operand splitting
  let a_lo := (List.range 32).map fun i => a[i]!
  let a_hi := (List.range 32).map fun i => a[32 + i]!
  let b_lo := (List.range 32).map fun i => b[i]!
  let b_hi := (List.range 32).map fun i => b[32 + i]!

  -- 4x 32x32 unsigned multipliers
  let p_ll := makeIndexedWires "p_ll" 64
  let p_lh := makeIndexedWires "p_lh" 64
  let p_hl := makeIndexedWires "p_hl" 64
  let p_hh := makeIndexedWires "p_hh" 64

  let mul_instances := [
    { moduleName := "Mul32x32To64", instName := "u_mul_ll",
      portMap := (a_lo.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
                 (b_lo.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
                 [("zero", zero)] ++
                 (p_ll.enum.map (fun ⟨i, w⟩ => (s!"product_{i}", w))) },
    { moduleName := "Mul32x32To64", instName := "u_mul_lh",
      portMap := (a_lo.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
                 (b_hi.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
                 [("zero", zero)] ++
                 (p_lh.enum.map (fun ⟨i, w⟩ => (s!"product_{i}", w))) },
    { moduleName := "Mul32x32To64", instName := "u_mul_hl",
      portMap := (a_hi.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
                 (b_lo.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
                 [("zero", zero)] ++
                 (p_hl.enum.map (fun ⟨i, w⟩ => (s!"product_{i}", w))) },
    { moduleName := "Mul32x32To64", instName := "u_mul_hh",
      portMap := (a_hi.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
                 (b_hi.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
                 [("zero", zero)] ++
                 (p_hh.enum.map (fun ⟨i, w⟩ => (s!"product_{i}", w))) }
  ]

  -- Stage 1 registers (DFFs)
  let s1_p_ll := makeIndexedWires "s1_p_ll" 64
  let s1_p_lh := makeIndexedWires "s1_p_lh" 64
  let s1_p_hl := makeIndexedWires "s1_p_hl" 64
  let s1_p_hh := makeIndexedWires "s1_p_hh" 64
  let s1_a := makeIndexedWires "s1_a64" 64
  let s1_b := makeIndexedWires "s1_b64" 64
  let s1_op := makeIndexedWires "s1_op64" 4
  let s1_tag := makeIndexedWires "s1_tag64" 6
  let s1_valid := Wire.mk "s1_valid64"

  let s1_reg_gates :=
    mkPipelineRegister p_ll s1_p_ll clock reset ++
    mkPipelineRegister p_lh s1_p_lh clock reset ++
    mkPipelineRegister p_hl s1_p_hl clock reset ++
    mkPipelineRegister p_hh s1_p_hh clock reset ++
    mkPipelineRegister a s1_a clock reset ++
    mkPipelineRegister b s1_b clock reset ++
    mkPipelineRegister op s1_op clock reset ++
    mkPipelineRegister dest_tag s1_tag clock reset ++
    [Gate.mkDFF valid_in clock reset s1_valid]

  -- Stage 2 registers (DFFs)
  let s2_p_ll := makeIndexedWires "s2_p_ll" 64
  let s2_p_lh := makeIndexedWires "s2_p_lh" 64
  let s2_p_hl := makeIndexedWires "s2_p_hl" 64
  let s2_p_hh := makeIndexedWires "s2_p_hh" 64
  let s2_a := makeIndexedWires "s2_a64" 64
  let s2_b := makeIndexedWires "s2_b64" 64
  let s2_op := makeIndexedWires "s2_op64" 4
  let s2_tag := makeIndexedWires "s2_tag64" 6
  let s2_valid := Wire.mk "s2_valid64"

  let s2_reg_gates :=
    mkPipelineRegister s1_p_ll s2_p_ll clock reset ++
    mkPipelineRegister s1_p_lh s2_p_lh clock reset ++
    mkPipelineRegister s1_p_hl s2_p_hl clock reset ++
    mkPipelineRegister s1_p_hh s2_p_hh clock reset ++
    mkPipelineRegister s1_a s2_a clock reset ++
    mkPipelineRegister s1_b s2_b clock reset ++
    mkPipelineRegister s1_op s2_op clock reset ++
    mkPipelineRegister s1_tag s2_tag clock reset ++
    [Gate.mkDFF s1_valid clock reset s2_valid]

  -- Stage 3: Combination & Sign Correction
  let mid_sum := makeIndexedWires "m64_mid_sum" 64
  let ksa_mid : CircuitInstance := {
    moduleName := "KoggeStoneAdder64"
    instName := "u_ksa_mid"
    portMap :=
      (s2_p_lh.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (s2_p_hl.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("cin", zero)] ++
      (mid_sum.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }
  -- Carry-out from mid_sum (s2_p_lh + s2_p_hl)
  let c_mid1_g := Wire.mk "m64_c_mid1_g"
  let c_mid1_p := Wire.mk "m64_c_mid1_p"
  let not_mid_sum63 := Wire.mk "m64_not_mid_sum63"
  let c_mid1_prop := Wire.mk "m64_c_mid1_prop"
  let c_mid1 := Wire.mk "m64_c_mid1"
  let c_mid1_gates := [
    Gate.mkAND (s2_p_lh[63]!) (s2_p_hl[63]!) c_mid1_g,
    Gate.mkOR (s2_p_lh[63]!) (s2_p_hl[63]!) c_mid1_p,
    Gate.mkNOT (mid_sum[63]!) not_mid_sum63,
    Gate.mkAND c_mid1_p not_mid_sum63 c_mid1_prop,
    Gate.mkOR c_mid1_g c_mid1_prop c_mid1
  ]

  let mid_shifted := (List.range 32 |>.map (fun _ => zero)) ++
                     (List.range 32 |>.map (fun i => mid_sum[i]!))

  let low_product := makeIndexedWires "m64_low_product" 64
  let ksa_low : CircuitInstance := {
    moduleName := "KoggeStoneAdder64"
    instName := "u_ksa_low"
    portMap :=
      (s2_p_ll.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (mid_shifted.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("cin", zero)] ++
      (low_product.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }

  -- Carry-out from column 1 (s2_p_ll[63:32] + mid_sum[31:0])
  let c_low_g := Wire.mk "m64_c_low_g"
  let c_low_p := Wire.mk "m64_c_low_p"
  let not_low_prod63 := Wire.mk "m64_not_low_prod63"
  let c_low_prop := Wire.mk "m64_c_low_prop"
  let c_low := Wire.mk "m64_c_low"
  let c_low_gates := [
    Gate.mkAND (s2_p_ll[63]!) (mid_sum[31]!) c_low_g,
    Gate.mkOR (s2_p_ll[63]!) (mid_sum[31]!) c_low_p,
    Gate.mkNOT (low_product[63]!) not_low_prod63,
    Gate.mkAND c_low_p not_low_prod63 c_low_prop,
    Gate.mkOR c_low_g c_low_prop c_low
  ]

  -- MULW result: lower 32 bits from p_ll, sign-extended to 64
  let mulw_res := makeIndexedWires "m64_mulw_res" 64
  let mulw_gates :=
    (List.range 32 |>.map (fun i => Gate.mkBUF (s2_p_ll[i]!) (mulw_res[i]!))) ++
    (List.range 32 |>.map (fun i => Gate.mkBUF (s2_p_ll[31]!) (mulw_res[32 + i]!)))

  -- High product: p_hh + {31'b0, c_mid1, mid_sum[63:32]} + c_low
  let mid_hi := (List.range 32 |>.map (fun i => mid_sum[32 + i]!)) ++
                [c_mid1] ++
                (List.range 31 |>.map (fun _ => zero))
  let high_product := makeIndexedWires "m64_high_product" 64
  let ksa_high : CircuitInstance := {
    moduleName := "KoggeStoneAdder64"
    instName := "u_ksa_high"
    portMap :=
      (s2_p_hh.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (mid_hi.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("cin", c_low)] ++
      (high_product.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }

  -- Baugh-Wooley sign correction for high product:
  --   MULH   (op=1): high - (a[63]?b:0) - (b[63]?a:0)
  --   MULHSU (op=2): high - (a[63]?b:0)
  --   MULHU  (op=3): high
  let not_op3 := Wire.mk "sc64_not_op3"
  let not_op2 := Wire.mk "sc64_not_op2"
  let not_op1 := Wire.mk "sc64_not_op1"
  let not_op0 := Wire.mk "sc64_not_op0"
  let is_mulh := Wire.mk "sc64_is_mulh"
  let is_mulhsu := Wire.mk "sc64_is_mulhsu"
  let needs_sub_b_pre := Wire.mk "sc64_sub_b_pre"
  let needs_sub_b := Wire.mk "sc64_needs_sub_b"
  let needs_sub_a := Wire.mk "sc64_needs_sub_a"

  let sc_ctrl_gates := [
    Gate.mkNOT (s2_op[3]!) not_op3,
    Gate.mkNOT (s2_op[2]!) not_op2,
    Gate.mkNOT (s2_op[1]!) not_op1,
    Gate.mkNOT (s2_op[0]!) not_op0,
    -- op=1: MULH (!op3 & !op2 & !op1 & op0)
    Gate.mkAND not_op3 not_op2 (Wire.mk "sc64_top0"),
    Gate.mkAND (Wire.mk "sc64_top0") not_op1 (Wire.mk "sc64_top1"),
    Gate.mkAND (Wire.mk "sc64_top1") (s2_op[0]!) is_mulh,
    -- op=2: MULHSU (!op3 & !op2 & op1 & !op0)
    Gate.mkAND (Wire.mk "sc64_top0") (s2_op[1]!) (Wire.mk "sc64_top2"),
    Gate.mkAND (Wire.mk "sc64_top2") not_op0 is_mulhsu,
    -- needs_sub_b = (is_mulh | is_mulhsu) & a[63]
    Gate.mkOR is_mulh is_mulhsu needs_sub_b_pre,
    Gate.mkAND needs_sub_b_pre (s2_a[63]!) needs_sub_b,
    -- needs_sub_a = is_mulh & b[63]
    Gate.mkAND is_mulh (s2_b[63]!) needs_sub_a
  ]

  let sub_b := makeIndexedWires "sc64_sub_b" 64
  let sub_b_gates := (List.range 64).map fun i =>
    Gate.mkAND (s2_b[i]!) needs_sub_b (sub_b[i]!)

  let sub_a := makeIndexedWires "sc64_sub_a" 64
  let sub_a_gates := (List.range 64).map fun i =>
    Gate.mkAND (s2_a[i]!) needs_sub_a (sub_a[i]!)

  let corr1 := makeIndexedWires "sc64_corr1" 64
  let sub1_inst : CircuitInstance := {
    moduleName := "Subtractor64"
    instName := "u_sign_sub1"
    portMap :=
      (high_product.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (sub_b.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("one", one)] ++
      (corr1.enum.map (fun ⟨i, w⟩ => (s!"diff_{i}", w))) ++
      [("borrow", Wire.mk "sc64_borrow1")]
  }

  let corr2 := makeIndexedWires "sc64_corr2" 64
  let sub2_inst : CircuitInstance := {
    moduleName := "Subtractor64"
    instName := "u_sign_sub2"
    portMap :=
      (corr1.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (sub_a.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("one", one)] ++
      (corr2.enum.map (fun ⟨i, w⟩ => (s!"diff_{i}", w))) ++
      [("borrow", Wire.mk "sc64_borrow2")]
  }

  -- Output selection:
  -- is_word = op[3] (MULW=8)
  -- is_high = op[0] | op[1] (MULH=1, MULHSU=2, MULHU=3)
  let is_word_op := s2_op[3]!
  let is_high_op := Wire.mk "m64_is_high"
  let sel_ctrl_gates := [
    Gate.mkOR (s2_op[0]!) (s2_op[1]!) is_high_op
  ]

  let mux_lo_w := makeIndexedWires "m64_mux_lo_w" 64
  let out_mux_gates := (List.range 64).flatMap fun i => [
    Gate.mkMUX (low_product[i]!) (mulw_res[i]!) is_word_op (mux_lo_w[i]!),
    Gate.mkMUX (mux_lo_w[i]!) (corr2[i]!) is_high_op (result[i]!)
  ]

  let tag_passthrough := List.zipWith (fun src dst => Gate.mkBUF src dst) s2_tag tag_out
  let valid_passthrough := [Gate.mkBUF s2_valid valid_out]

  let all_gates :=
    s1_reg_gates ++
    s2_reg_gates ++
    mulw_gates ++
    c_mid1_gates ++
    c_low_gates ++
    sc_ctrl_gates ++
    sub_b_gates ++
    sub_a_gates ++
    sel_ctrl_gates ++
    out_mux_gates ++
    tag_passthrough ++
    valid_passthrough

  { name := "PipelinedMultiplier64"
    inputs := a ++ b ++ op ++ dest_tag ++ [valid_in, clock, reset, zero, one]
    outputs := result ++ tag_out ++ [valid_out]
    gates := all_gates
    instances := mul_instances ++ [ksa_mid, ksa_low, ksa_high, sub1_inst, sub2_inst]
    keepHierarchy := true
    signalGroups := [
      { name := "a", width := 64, wires := a },
      { name := "b", width := 64, wires := b },
      { name := "op", width := 4, wires := op },
      { name := "dest_tag", width := 6, wires := dest_tag },
      { name := "result", width := 64, wires := result },
      { name := "tag_out", width := 6, wires := tag_out }
    ]
  }

/-- Convenience alias for 64-bit pipelined multiplier. -/
def pipelinedMultiplier64 : Circuit := mkPipelinedMultiplier64

end Shoumei.Circuits.Combinational
