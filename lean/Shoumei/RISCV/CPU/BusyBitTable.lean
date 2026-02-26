import Shoumei.DSL
import Shoumei.RISCV.Config
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Sequential.Register

namespace Shoumei.RISCV.CPU

open Shoumei
open Shoumei.Circuits.Combinational
open Shoumei.Circuits.Sequential

/--
Single-port Busy Bit Table (W=1).
Tracks 64 physical registers.
- Sets bit for 1 newly renamed instruction.
- Clears bit for 1 completing instruction.
- Reads readiness for 2 source operands.
-/
def mkBusyBitTable1
    (clock global_reset : Wire) (flush_groups : List Wire) (zero one : Wire)
    (set_tag : List Wire) (set_en : Wire)
    (clear_tag : List Wire) (clear_en : Wire)
    (read1_tag : List Wire) (read2_tag : List Wire)
    (use_imm : Wire)
    (src1_ready src2_ready src2_ready_reg : Wire)
    (pfx : String := "busy")
    : (List Gate × List CircuitInstance) :=
  let mkW := fun (s : String) => Wire.mk s
  -- Decoder instances for set and clear paths
  let set_decode := (List.range 64).map fun i => mkW s!"{pfx}_set_dec_{i}"
  let clear_decode := (List.range 64).map fun i => mkW s!"{pfx}_clr_dec_{i}"

  let set_dec_inst : CircuitInstance := {
    moduleName := "Decoder6"
    instName := s!"u_{pfx}_set_dec"
    portMap :=
      (set_tag.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (set_decode.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }
  let clear_dec_inst : CircuitInstance := {
    moduleName := "Decoder6"
    instName := s!"u_{pfx}_clr_dec"
    portMap :=
      (clear_tag.enum.map (fun ⟨i, w⟩ => (s!"in_{i}", w))) ++
      (clear_decode.enum.map (fun ⟨i, w⟩ => (s!"out_{i}", w)))
  }

  -- 64 busy bits: DFF + next-state logic
  let busy_cur := (List.range 64).map fun i => mkW s!"{pfx}_q_{i}"
  let busy_next := (List.range 64).map fun i => mkW s!"{pfx}_d_{i}"

  -- Replicated reset OR gates: 8 groups × 8 DFFs each.
  let numGroups := 8
  let groupSize := 8
  let resetGroupWires := (List.range numGroups).map fun g => mkW s!"{pfx}_reset_g{g}"
  let resetGroupGates := (List.range numGroups).map fun g =>
    Gate.mkOR global_reset flush_groups[g]! resetGroupWires[g]!

  -- Per-bit logic:
  let perBitGates := (List.range 64).map fun i =>
    let set_i := mkW s!"{pfx}_set_{i}"
    let clr_i := mkW s!"{pfx}_clr_{i}"
    let mux1 := mkW s!"{pfx}_mux1_{i}"
    [
      Gate.mkAND set_en set_decode[i]! set_i,
      Gate.mkAND clear_en clear_decode[i]! clr_i,
      Gate.mkMUX busy_cur[i]! zero clr_i mux1,
      Gate.mkMUX mux1 one set_i busy_next[i]!
    ]

  let perBitInstances := (List.range 64).map fun i =>
    let g := i / groupSize
    ({ moduleName := "DFlipFlop", instName := s!"u_{pfx}_bit_{i}",
       portMap := [("d", busy_next[i]!), ("q", busy_cur[i]!),
                   ("clock", clock), ("reset", resetGroupWires[g]!)] } : CircuitInstance)

  let mkMux64to1 (inputs : List Wire) (sel : List Wire) (portName : String) (output : Wire) : List Gate :=
    let l0 := (List.range 32).map fun i =>
      let o := mkW s!"{portName}_l0_{i}"
      (Gate.mkMUX inputs[2*i]! inputs[2*i+1]! sel[0]! o, o)
    let l0_outs := l0.map Prod.snd
    let l1 := (List.range 16).map fun i =>
      let o := mkW s!"{portName}_l1_{i}"
      (Gate.mkMUX l0_outs[2*i]! l0_outs[2*i+1]! sel[1]! o, o)
    let l1_outs := l1.map Prod.snd
    let l2 := (List.range 8).map fun i =>
      let o := mkW s!"{portName}_l2_{i}"
      (Gate.mkMUX l1_outs[2*i]! l1_outs[2*i+1]! sel[2]! o, o)
    let l2_outs := l2.map Prod.snd
    let l3 := (List.range 4).map fun i =>
      let o := mkW s!"{portName}_l3_{i}"
      (Gate.mkMUX l2_outs[2*i]! l2_outs[2*i+1]! sel[3]! o, o)
    let l3_outs := l3.map Prod.snd
    let l4 := (List.range 2).map fun i =>
      let o := mkW s!"{portName}_l4_{i}"
      (Gate.mkMUX l3_outs[2*i]! l3_outs[2*i+1]! sel[4]! o, o)
    let l4_outs := l4.map Prod.snd
    let l5 := Gate.mkMUX l4_outs[0]! l4_outs[1]! sel[5]! output
    (l0.map Prod.fst) ++ (l1.map Prod.fst) ++ (l2.map Prod.fst) ++
      (l3.map Prod.fst) ++ (l4.map Prod.fst) ++ [l5]

  let busy_rs1 := mkW s!"{pfx}_rs1_raw"
  let busy_rs2 := mkW s!"{pfx}_rs2_raw"
  let mux1_gates := mkMux64to1 busy_cur read1_tag s!"{pfx}mux1" busy_rs1
  let mux2_gates := mkMux64to1 busy_cur read2_tag s!"{pfx}mux2" busy_rs2

  let not_busy_rs2 := mkW s!"not_{pfx}_rs2"
  let readyGates := [
    Gate.mkNOT busy_rs1 src1_ready,
    Gate.mkNOT busy_rs2 not_busy_rs2,
    Gate.mkOR use_imm not_busy_rs2 src2_ready,
    Gate.mkBUF not_busy_rs2 src2_ready_reg
  ]

  let allGates := resetGroupGates ++ perBitGates.flatten ++ mux1_gates ++ mux2_gates ++ readyGates
  let allInstances := [set_dec_inst, clear_dec_inst] ++ perBitInstances
  (allGates, allInstances)

/--
Dual-port Busy Bit Table (W=2).
Tracks 64 physical registers.
- Sets bits for up to 2 newly renamed instructions (dual-issue).
- Clears bits for up to 2 completing instructions (CDB broadcast).
- Reads readiness for 4 source operands (2 per issue slot).
-/
def mkBusyBitTable2
    (clock global_reset : Wire) (flush_groups : List Wire) (zero one : Wire)
    (set_tag_0 set_tag_1 : List Wire) (set_en_0 set_en_1 : Wire)
    (clear_tag_0 clear_tag_1 : List Wire) (clear_en_0 clear_en_1 : Wire)
    (read1_tag_0 read2_tag_0 : List Wire) (read1_tag_1 read2_tag_1 : List Wire)
    (use_imm_0 use_imm_1 : Wire)
    (src1_ready_0 src2_ready_0 src2_ready0_reg : Wire)
    (src1_ready_1 src2_ready_1 src2_ready1_reg : Wire)
    (pfx : String := "busy")
    : (List Gate × List CircuitInstance) :=
  let mkW := fun (s : String) => Wire.mk s

  -- Decoders for sets
  let set_dec0 := (List.range 64).map fun i => mkW s!"{pfx}_set0_dec_{i}"
  let set_dec1 := (List.range 64).map fun i => mkW s!"{pfx}_set1_dec_{i}"
  let set_dec0_inst : CircuitInstance := {
    moduleName := "Decoder6", instName := s!"u_{pfx}_s0_dec",
    portMap := (set_tag_0.enum.map (fun ⟨i,w⟩ => (s!"in_{i}", w))) ++
               (set_dec0.enum.map (fun ⟨i,w⟩ => (s!"out_{i}", w)))
  }
  let set_dec1_inst : CircuitInstance := {
    moduleName := "Decoder6", instName := s!"u_{pfx}_s1_dec",
    portMap := (set_tag_1.enum.map (fun ⟨i,w⟩ => (s!"in_{i}", w))) ++
               (set_dec1.enum.map (fun ⟨i,w⟩ => (s!"out_{i}", w)))
  }

  -- Decoders for clears
  let clr_dec0 := (List.range 64).map fun i => mkW s!"{pfx}_clr0_dec_{i}"
  let clr_dec1 := (List.range 64).map fun i => mkW s!"{pfx}_clr1_dec_{i}"
  let clr_dec0_inst : CircuitInstance := {
    moduleName := "Decoder6", instName := s!"u_{pfx}_c0_dec",
    portMap := (clear_tag_0.enum.map (fun ⟨i,w⟩ => (s!"in_{i}", w))) ++
               (clr_dec0.enum.map (fun ⟨i,w⟩ => (s!"out_{i}", w)))
  }
  let clr_dec1_inst : CircuitInstance := {
    moduleName := "Decoder6", instName := s!"u_{pfx}_c1_dec",
    portMap := (clear_tag_1.enum.map (fun ⟨i,w⟩ => (s!"in_{i}", w))) ++
               (clr_dec1.enum.map (fun ⟨i,w⟩ => (s!"out_{i}", w)))
  }

  -- State
  let busy_cur  := (List.range 64).map fun i => mkW s!"{pfx}_q_{i}"
  let busy_next := (List.range 64).map fun i => mkW s!"{pfx}_d_{i}"

  -- Reset tree
  let resetGroupWires := (List.range 8).map fun g => mkW s!"{pfx}_reset_g{g}"
  let resetGroupGates := (List.range 8).map fun g =>
    Gate.mkOR global_reset (flush_groups[g]!) (resetGroupWires[g]!)

  -- Per-bit logic
  let perBitGates := (List.range 64).map (fun i =>
    let s0 := mkW s!"{pfx}_s0_{i}"; let s1 := mkW s!"{pfx}_s1_{i}"; let sa := mkW s!"{pfx}_sa_{i}"
    let c0 := mkW s!"{pfx}_c0_{i}"; let c1 := mkW s!"{pfx}_c1_{i}"; let ca := mkW s!"{pfx}_ca_{i}"
    let m1 := mkW s!"{pfx}_m1_{i}"
    [Gate.mkAND set_en_0 (set_dec0[i]!) s0,
     Gate.mkAND set_en_1 (set_dec1[i]!) s1,
     Gate.mkOR s0 s1 sa,
     Gate.mkAND clear_en_0 (clr_dec0[i]!) c0,
     Gate.mkAND clear_en_1 (clr_dec1[i]!) c1,
     Gate.mkOR c0 c1 ca,
     Gate.mkMUX (busy_cur[i]!) zero ca m1,
     Gate.mkMUX m1 one sa (busy_next[i]!)]
  ) |>.flatten

  let perBitInstances := (List.range 64).map fun i =>
    { moduleName := "DFlipFlop", instName := s!"u_{pfx}_bit_{i}",
      portMap := [("d", busy_next[i]!), ("q", busy_cur[i]!),
                  ("clock", clock), ("reset", resetGroupWires[i/8]!)] }

  -- Read ports (4× 64:1 mux)
  let mkMuxTree64 (inputs : List Wire) (sel : List Wire) (output : Wire) (pfx2 : String) : List Gate :=
    let l0 := (List.range 32).map (fun i =>
      let o := mkW s!"{pfx2}_l0_{i}"
      (Gate.mkMUX inputs[2*i]! inputs[2*i+1]! sel[0]! o, o))
    let l1 := (List.range 16).map (fun i =>
      let o := mkW s!"{pfx2}_l1_{i}"
      (Gate.mkMUX (l0.map (·.2))[2*i]! (l0.map (·.2))[2*i+1]! sel[1]! o, o))
    let l2 := (List.range 8).map (fun i =>
      let o := mkW s!"{pfx2}_l2_{i}"
      (Gate.mkMUX (l1.map (·.2))[2*i]! (l1.map (·.2))[2*i+1]! sel[2]! o, o))
    let l3 := (List.range 4).map (fun i =>
      let o := mkW s!"{pfx2}_l3_{i}"
      (Gate.mkMUX (l2.map (·.2))[2*i]! (l2.map (·.2))[2*i+1]! sel[3]! o, o))
    let l4 := (List.range 2).map (fun i =>
      let o := mkW s!"{pfx2}_l4_{i}"
      (Gate.mkMUX (l3.map (·.2))[2*i]! (l3.map (·.2))[2*i+1]! sel[4]! o, o))
    (l0.map (·.1)) ++ (l1.map (·.1)) ++ (l2.map (·.1)) ++ (l3.map (·.1)) ++ (l4.map (·.1)) ++
    [Gate.mkMUX (l4.map (·.2))[0]! (l4.map (·.2))[1]! sel[5]! output]

  let b_s1_0 := mkW s!"{pfx}_rs1_0_raw"; let b_s2_0 := mkW s!"{pfx}_rs2_0_raw"
  let b_s1_1 := mkW s!"{pfx}_rs1_1_raw"; let b_s2_1 := mkW s!"{pfx}_rs2_1_raw"

  let muxGates := [
    mkMuxTree64 busy_cur read1_tag_0 b_s1_0 s!"{pfx}_m1_0",
    mkMuxTree64 busy_cur read2_tag_0 b_s2_0 s!"{pfx}_m2_0",
    mkMuxTree64 busy_cur read1_tag_1 b_s1_1 s!"{pfx}_m1_1",
    mkMuxTree64 busy_cur read2_tag_1 b_s2_1 s!"{pfx}_m2_1"
  ].flatten

  let not_b_s2_0 := mkW s!"not_{pfx}_rs2_0"
  let not_b_s2_1 := mkW s!"not_{pfx}_rs2_1"
  -- Intra-group RAW hazard: if slot 0 sets the same tag slot 1 reads,
  -- slot 1 must see "not ready" (busy_cur hasn't updated yet)
  let tagWidth := 6
  let s0_eq_r1_1 := mkW s!"{pfx}_s0_eq_r1_1"  -- set_tag_0 == read1_tag_1
  let s0_eq_r2_1 := mkW s!"{pfx}_s0_eq_r2_1"  -- set_tag_0 == read2_tag_1
  let mkTagEq (pfx2 : String) (a b : List Wire) (out : Wire) : List Gate :=
    let xns := (List.range tagWidth).map fun i =>
      let x := mkW s!"{pfx2}_x{i}"; let xn := mkW s!"{pfx2}_xn{i}"
      [Gate.mkXOR a[i]! b[i]! x, Gate.mkNOT x xn]
    let ands := [
      Gate.mkAND (mkW s!"{pfx2}_xn0") (mkW s!"{pfx2}_xn1") (mkW s!"{pfx2}_a01"),
      Gate.mkAND (mkW s!"{pfx2}_xn2") (mkW s!"{pfx2}_xn3") (mkW s!"{pfx2}_a23"),
      Gate.mkAND (mkW s!"{pfx2}_xn4") (mkW s!"{pfx2}_xn5") (mkW s!"{pfx2}_a45"),
      Gate.mkAND (mkW s!"{pfx2}_a01") (mkW s!"{pfx2}_a23") (mkW s!"{pfx2}_a0123"),
      Gate.mkAND (mkW s!"{pfx2}_a0123") (mkW s!"{pfx2}_a45") out]
    xns.flatten ++ ands
  let s0_eq_r1_1_gates := mkTagEq s!"{pfx}_raw_s1" set_tag_0 read1_tag_1 s0_eq_r1_1
  let s0_eq_r2_1_gates := mkTagEq s!"{pfx}_raw_s2" set_tag_0 read2_tag_1 s0_eq_r2_1
  -- slot 1 hazard: set_en_0 AND tag match → force not-ready
  let raw_s1_hit := mkW s!"{pfx}_raw_s1_hit"; let raw_s2_hit := mkW s!"{pfx}_raw_s2_hit"
  let not_raw_s1 := mkW s!"{pfx}_not_raw_s1"; let not_raw_s2 := mkW s!"{pfx}_not_raw_s2"
  let raw_gates := [
    Gate.mkAND set_en_0 s0_eq_r1_1 raw_s1_hit,
    Gate.mkAND set_en_0 s0_eq_r2_1 raw_s2_hit,
    Gate.mkNOT raw_s1_hit not_raw_s1,
    Gate.mkNOT raw_s2_hit not_raw_s2]
  let s1_ready_1_pre := mkW s!"{pfx}_s1_1_pre"
  let s2_ready_1_pre := mkW s!"{pfx}_s2_1_pre"
  let readyGates := [
    Gate.mkNOT b_s1_0 src1_ready_0,
    Gate.mkNOT b_s2_0 not_b_s2_0,
    Gate.mkOR use_imm_0 not_b_s2_0 src2_ready_0,
    Gate.mkBUF not_b_s2_0 src2_ready0_reg,
    -- Slot 1: AND with NOT(intra-group hazard)
    Gate.mkNOT b_s1_1 s1_ready_1_pre,
    Gate.mkAND s1_ready_1_pre not_raw_s1 src1_ready_1,
    Gate.mkNOT b_s2_1 not_b_s2_1,
    Gate.mkAND not_b_s2_1 not_raw_s2 s2_ready_1_pre,
    Gate.mkOR use_imm_1 s2_ready_1_pre src2_ready_1,
    Gate.mkBUF s2_ready_1_pre src2_ready1_reg
  ]

  (resetGroupGates ++ perBitGates ++ muxGates ++ s0_eq_r1_1_gates ++ s0_eq_r2_1_gates ++ raw_gates ++ readyGates,
   [set_dec0_inst, set_dec1_inst, clr_dec0_inst, clr_dec1_inst] ++ perBitInstances)

end Shoumei.RISCV.CPU
