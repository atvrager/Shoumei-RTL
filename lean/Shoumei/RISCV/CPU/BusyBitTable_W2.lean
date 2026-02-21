import Shoumei.DSL
import Shoumei.RISCV.Config
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Sequential.Register

namespace Shoumei.RISCV.CPU

open Shoumei
open Shoumei.Circuits.Combinational
open Shoumei.Circuits.Sequential

/--
Dual-port Busy Bit Table.
Tracks 64 physical registers.
- Sets bits for 2 newly renamed instructions.
- Clears bits for 2 completing instructions (CDB).
- Reads readiness for 4 source operands.
-/
def mkBusyBitTable_W2
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
    moduleName := "Decoder6",
    instName := s!"u_{pfx}_s0_dec", 
    portMap := (set_tag_0.enum.map (fun ⟨i,w⟩ => (s!"in_{i}", w))) ++ (set_dec0.enum.map (fun ⟨i,w⟩ => (s!"out_{i}", w)))
  }
  let set_dec1_inst : CircuitInstance := {
    moduleName := "Decoder6",
    instName := s!"u_{pfx}_s1_dec", 
    portMap := (set_tag_1.enum.map (fun ⟨i,w⟩ => (s!"in_{i}", w))) ++ (set_dec1.enum.map (fun ⟨i,w⟩ => (s!"out_{i}", w)))
  }

  -- Decoders for clears
  let clr_dec0 := (List.range 64).map fun i => mkW s!"{pfx}_clr0_dec_{i}"
  let clr_dec1 := (List.range 64).map fun i => mkW s!"{pfx}_clr1_dec_{i}"
  let clr_dec0_inst : CircuitInstance := {
    moduleName := "Decoder6",
    instName := s!"u_{pfx}_c0_dec", 
    portMap := (clear_tag_0.enum.map (fun ⟨i,w⟩ => (s!"in_{i}", w))) ++ (clr_dec0.enum.map (fun ⟨i,w⟩ => (s!"out_{i}", w)))
  }
  let clr_dec1_inst : CircuitInstance := {
    moduleName := "Decoder6",
    instName := s!"u_{pfx}_c1_dec", 
    portMap := (clear_tag_1.enum.map (fun ⟨i,w⟩ => (s!"in_{i}", w))) ++ (clr_dec1.enum.map (fun ⟨i,w⟩ => (s!"out_{i}", w)))
  }

  -- 64 busy bits
  let busy_cur := (List.range 64).map fun i => mkW s!"{pfx}_q_{i}"
  let busy_next := (List.range 64).map fun i => mkW s!"{pfx}_d_{i}"

  -- Reset tree (8 groups)
  let resetGroupWires := (List.range 8).map fun g => mkW s!"{pfx}_reset_g{g}"
  let resetGroupGates := (List.range 8).map fun g => Gate.mkOR global_reset (flush_groups[g]!) (resetGroupWires[g]!)

  -- Per-bit logic:
  -- clr_any_i = (clr_en0 & clr0_dec[i]) | (clr_en1 & clr1_dec[i])
  -- set_any_i = (set_en0 & set0_dec[i]) | (set_en1 & set1_dec[i])
  -- next[i] = clr_any_i ? 0 : (set_any_i ? 1 : cur[i])
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
     Gate.mkMUX (busy_cur[i]!) one sa m1,
     Gate.mkMUX m1 zero ca (busy_next[i]!)]
  ) |>.flatten

  let perBitInstances := (List.range 64).map fun i =>
    { moduleName := "DFlipFlop", instName := s!"u_{pfx}_bit_{i}",
      portMap := [("d", busy_next[i]!), ("q", busy_cur[i]!), ("clock", clock), ("reset", resetGroupWires[i/8]!)] }

  -- Read ports (4x 64:1 mux)
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
    (mkMuxTree64 busy_cur read1_tag_0 b_s1_0 s!"{pfx}_m1_0"),
    (mkMuxTree64 busy_cur read2_tag_0 b_s2_0 s!"{pfx}_m2_0"),
    (mkMuxTree64 busy_cur read1_tag_1 b_s1_1 s!"{pfx}_m1_1"),
    (mkMuxTree64 busy_cur read2_tag_1 b_s2_1 s!"{pfx}_m2_1")
  ].flatten

  let not_b_s2_0 := mkW s!"not_{pfx}_rs2_0"; let not_b_s2_1 := mkW s!"not_{pfx}_rs2_1"
  let readyGates := [
    Gate.mkNOT b_s1_0 src1_ready_0, Gate.mkNOT b_s2_0 not_b_s2_0, Gate.mkOR use_imm_0 not_b_s2_0 src2_ready_0, Gate.mkBUF not_b_s2_0 src2_ready0_reg,
    Gate.mkNOT b_s1_1 src1_ready_1, Gate.mkNOT b_s2_1 not_b_s2_1, Gate.mkOR use_imm_1 not_b_s2_1 src2_ready_1, Gate.mkBUF not_b_s2_1 src2_ready1_reg
  ]

  (resetGroupGates ++ perBitGates ++ muxGates ++ readyGates, [set_dec0_inst, set_dec1_inst, clr_dec0_inst, clr_dec1_inst] ++ perBitInstances)

end Shoumei.RISCV.CPU
