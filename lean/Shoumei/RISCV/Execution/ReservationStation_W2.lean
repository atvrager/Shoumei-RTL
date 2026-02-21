import Shoumei.RISCV.ISA
import Shoumei.RISCV.Config
import Shoumei.RISCV.Renaming.RenameStage
import Shoumei.RISCV.Renaming.PhysRegFile
import Shoumei.DSL
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Combinational.Arbiter

namespace Shoumei.RISCV.Execution

open Shoumei
open Shoumei.Circuits.Combinational

/-- Helper: Create indexed wires -/
private def makeIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}_{i}")

-- Disable unused variables warning for work-in-progress circuit declaration
set_option linter.unusedVariables false

/-- 
Dual-Issue Reservation Station (W=2) -> Banked Architecture.

Total 4 entries divided into 2 banks (Bank 0: entries 0,1; Bank 1: entries 2,3).
- issue_0 targets Bank 0 (using a 1-bit alloc pointer)
- issue_1 targets Bank 1 (using a 1-bit alloc pointer)
- BOTH banks snoop cdb_0 and cdb_1
- Bank 0 arbitrates entries 0,1 -> dispatch_0
- Bank 1 arbitrates entries 2,3 -> dispatch_1
-/
def mkReservationStation4_W2 (enableStoreLoadOrdering : Bool := false) : Circuit :=
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  let opcodeWidth := 6
  let tagWidth := 6
  let dataWidth := 32
  let entryWidth := 1 + opcodeWidth + tagWidth + 1 + tagWidth + dataWidth + 1 + tagWidth + dataWidth

  -- Issue interface (W=2)
  let issue_en_0 := Wire.mk "issue_en_0"
  let issue_en_1 := Wire.mk "issue_en_1"
  let issue_is_store_0 := Wire.mk "issue_is_store_0"
  let issue_is_store_1 := Wire.mk "issue_is_store_1"
  let issue_opcode_0 := makeIndexedWires "issue_opcode_0" opcodeWidth
  let issue_dest_tag_0 := makeIndexedWires "issue_dest_tag_0" tagWidth
  let issue_src1_ready_0 := Wire.mk "issue_src1_ready_0"
  let issue_src1_tag_0 := makeIndexedWires "issue_src1_tag_0" tagWidth
  let issue_src1_data_0 := makeIndexedWires "issue_src1_data_0" dataWidth
  let issue_src2_ready_0 := Wire.mk "issue_src2_ready_0"
  let issue_src2_tag_0 := makeIndexedWires "issue_src2_tag_0" tagWidth
  let issue_src2_data_0 := makeIndexedWires "issue_src2_data_0" dataWidth
  
  let issue_opcode_1 := makeIndexedWires "issue_opcode_1" opcodeWidth
  let issue_dest_tag_1 := makeIndexedWires "issue_dest_tag_1" tagWidth
  let issue_src1_ready_1 := Wire.mk "issue_src1_ready_1"
  let issue_src1_tag_1 := makeIndexedWires "issue_src1_tag_1" tagWidth
  let issue_src1_data_1 := makeIndexedWires "issue_src1_data_1" dataWidth
  let issue_src2_ready_1 := Wire.mk "issue_src2_ready_1"
  let issue_src2_tag_1 := makeIndexedWires "issue_src2_tag_1" tagWidth
  let issue_src2_data_1 := makeIndexedWires "issue_src2_data_1" dataWidth

  let alloc_avail_0 := Wire.mk "alloc_avail_0"
  let alloc_avail_1 := Wire.mk "alloc_avail_1"

  -- CDB interface (W=2)
  let cdb_valid_0 := Wire.mk "cdb_valid_0"
  let cdb_tag_0 := makeIndexedWires "cdb_tag_0" tagWidth
  let cdb_data_0 := makeIndexedWires "cdb_data_0" dataWidth
  let cdb_valid_1 := Wire.mk "cdb_valid_1"
  let cdb_tag_1 := makeIndexedWires "cdb_tag_1" tagWidth
  let cdb_data_1 := makeIndexedWires "cdb_data_1" dataWidth

  -- Dispatch interface (W=2)
  let dispatch_en_0 := Wire.mk "dispatch_en_0"
  let dispatch_valid_0 := Wire.mk "dispatch_valid_0"
  let dispatch_opcode_0 := makeIndexedWires "dispatch_opcode_0" opcodeWidth
  let dispatch_src1_data_0 := makeIndexedWires "dispatch_src1_data_0" dataWidth
  let dispatch_src2_data_0 := makeIndexedWires "dispatch_src2_data_0" dataWidth
  let dispatch_dest_tag_0 := makeIndexedWires "dispatch_dest_tag_0" tagWidth
  
  let dispatch_en_1 := Wire.mk "dispatch_en_1"
  let dispatch_valid_1 := Wire.mk "dispatch_valid_1"
  let dispatch_opcode_1 := makeIndexedWires "dispatch_opcode_1" opcodeWidth
  let dispatch_src1_data_1 := makeIndexedWires "dispatch_src1_data_1" dataWidth
  let dispatch_src2_data_1 := makeIndexedWires "dispatch_src2_data_1" dataWidth
  let dispatch_dest_tag_1 := makeIndexedWires "dispatch_dest_tag_1" tagWidth

  -- 1-bit allocation pointers for each bank
  let alloc_ptr_0 := Wire.mk "alloc_ptr_0"
  let alloc_ptr_next_0 := Wire.mk "alloc_ptr_next_0"
  let alloc_ptr_1 := Wire.mk "alloc_ptr_1"
  let alloc_ptr_next_1 := Wire.mk "alloc_ptr_next_1"
  
  let ptr_gates := [
    Gate.mkNOT alloc_ptr_0 alloc_ptr_next_0,
    Gate.mkNOT alloc_ptr_1 alloc_ptr_next_1
  ]
  let ptr_inst_0 : CircuitInstance := {
    moduleName := "Register1", instName := "u_alloc_ptr_0",
    portMap := [("d_0", alloc_ptr_next_0), ("clock", clock), ("reset", reset), ("q_0", alloc_ptr_0)]
  }
  let ptr_inst_1 : CircuitInstance := {
    moduleName := "Register1", instName := "u_alloc_ptr_1",
    portMap := [("d_0", alloc_ptr_next_1), ("clock", clock), ("reset", reset), ("q_0", alloc_ptr_1)]
  }
  
  -- Def issue routing details per bank
  let issue_we_0_0 := Wire.mk "issue_we_0_0"
  let issue_we_0_1 := Wire.mk "issue_we_0_1"
  let not_ptr_0 := Wire.mk "not_ptr_0"
  let base_issue_gates_0 := [
    Gate.mkNOT alloc_ptr_0 not_ptr_0,
    Gate.mkAND issue_en_0 not_ptr_0 issue_we_0_0,
    Gate.mkAND issue_en_0 alloc_ptr_0 issue_we_0_1
  ]

  let issue_we_1_0 := Wire.mk "issue_we_1_0"
  let issue_we_1_1 := Wire.mk "issue_we_1_1"
  let not_ptr_1 := Wire.mk "not_ptr_1"
  let base_issue_gates_1 := [
    Gate.mkNOT alloc_ptr_1 not_ptr_1,
    Gate.mkAND issue_en_1 not_ptr_1 issue_we_1_0,
    Gate.mkAND issue_en_1 alloc_ptr_1 issue_we_1_1
  ]

  -- Helper to construct a single entry (0-3)
  -- returns (gates, instances, valid, ready)
  let buildEntry (idx : Nat) : List Gate × List CircuitInstance × Wire × Wire :=
    let bank := idx / 2
    let subIdx := idx % 2
    
    let e_cur := makeIndexedWires s!"e{idx}" entryWidth
    let e_next := makeIndexedWires s!"e{idx}_next" entryWidth
    let valid := e_cur[0]!
    let src1_ready := e_cur[13]!
    let src1_tag := e_cur.drop 14 |>.take tagWidth
    let src1_data := e_cur.drop 20 |>.take dataWidth
    let src2_ready := e_cur[52]!
    let src2_tag := e_cur.drop 53 |>.take tagWidth
    let src2_data := e_cur.drop 59 |>.take dataWidth
    
    let issue_we_this :=
      if bank == 0 then (if subIdx == 0 then issue_we_0_0 else issue_we_0_1)
      else (if subIdx == 0 then issue_we_1_0 else issue_we_1_1)
      
    -- Issue Inputs
    let (issue_opcode, issue_dest, issue_s1r, issue_s1t, issue_s1d, issue_s2r, issue_s2t, issue_s2d) :=
      if bank == 0 then
        (issue_opcode_0, issue_dest_tag_0, issue_src1_ready_0, issue_src1_tag_0, issue_src1_data_0, issue_src2_ready_0, issue_src2_tag_0, issue_src2_data_0)
      else
        (issue_opcode_1, issue_dest_tag_1, issue_src1_ready_1, issue_src1_tag_1, issue_src1_data_1, issue_src2_ready_1, issue_src2_tag_1, issue_src2_data_1)
        
    -- CDB Match Logic (dual port)
    -- src1 cdb 0
    let m1_0_xors := (List.range tagWidth).map fun i => Gate.mkXOR src1_tag[i]! cdb_tag_0[i]! (Wire.mk s!"e{idx}_m1_0_x{i}")
    let m1_0_xnors := (List.range tagWidth).map fun i => Gate.mkNOT (Wire.mk s!"e{idx}_m1_0_x{i}") (Wire.mk s!"e{idx}_m1_0_xn{i}")
    let m1_0_eq := Wire.mk s!"e{idx}_m1_0_eq"
    let m1_0_and := [
      Gate.mkAND (Wire.mk s!"e{idx}_m1_0_xn0") (Wire.mk s!"e{idx}_m1_0_xn1") (Wire.mk s!"e{idx}_m1_0_a1"),
      Gate.mkAND (Wire.mk s!"e{idx}_m1_0_xn2") (Wire.mk s!"e{idx}_m1_0_xn3") (Wire.mk s!"e{idx}_m1_0_a2"),
      Gate.mkAND (Wire.mk s!"e{idx}_m1_0_xn4") (Wire.mk s!"e{idx}_m1_0_xn5") (Wire.mk s!"e{idx}_m1_0_a3"),
      Gate.mkAND (Wire.mk s!"e{idx}_m1_0_a1") (Wire.mk s!"e{idx}_m1_0_a2") (Wire.mk s!"e{idx}_m1_0_a4"),
      Gate.mkAND (Wire.mk s!"e{idx}_m1_0_a4") (Wire.mk s!"e{idx}_m1_0_a3") m1_0_eq
    ]
    let m1_0_match := Wire.mk s!"e{idx}_m1_0"
    let m1_0_gate := Gate.mkAND m1_0_eq cdb_valid_0 m1_0_match
    
    -- src1 cdb 1
    let m1_1_xors := (List.range tagWidth).map fun i => Gate.mkXOR src1_tag[i]! cdb_tag_1[i]! (Wire.mk s!"e{idx}_m1_1_x{i}")
    let m1_1_xnors := (List.range tagWidth).map fun i => Gate.mkNOT (Wire.mk s!"e{idx}_m1_1_x{i}") (Wire.mk s!"e{idx}_m1_1_xn{i}")
    let m1_1_eq := Wire.mk s!"e{idx}_m1_1_eq"
    let m1_1_and := [
      Gate.mkAND (Wire.mk s!"e{idx}_m1_1_xn0") (Wire.mk s!"e{idx}_m1_1_xn1") (Wire.mk s!"e{idx}_m1_1_a1"),
      Gate.mkAND (Wire.mk s!"e{idx}_m1_1_xn2") (Wire.mk s!"e{idx}_m1_1_xn3") (Wire.mk s!"e{idx}_m1_1_a2"),
      Gate.mkAND (Wire.mk s!"e{idx}_m1_1_xn4") (Wire.mk s!"e{idx}_m1_1_xn5") (Wire.mk s!"e{idx}_m1_1_a3"),
      Gate.mkAND (Wire.mk s!"e{idx}_m1_1_a1") (Wire.mk s!"e{idx}_m1_1_a2") (Wire.mk s!"e{idx}_m1_1_a4"),
      Gate.mkAND (Wire.mk s!"e{idx}_m1_1_a4") (Wire.mk s!"e{idx}_m1_1_a3") m1_1_eq
    ]
    let m1_1_match := Wire.mk s!"e{idx}_m1_1"
    let m1_1_gate := Gate.mkAND m1_1_eq cdb_valid_1 m1_1_match
    
    -- src2 cdb 0
    let m2_0_xors := (List.range tagWidth).map fun i => Gate.mkXOR src2_tag[i]! cdb_tag_0[i]! (Wire.mk s!"e{idx}_m2_0_x{i}")
    let m2_0_xnors := (List.range tagWidth).map fun i => Gate.mkNOT (Wire.mk s!"e{idx}_m2_0_x{i}") (Wire.mk s!"e{idx}_m2_0_xn{i}")
    let m2_0_eq := Wire.mk s!"e{idx}_m2_0_eq"
    let m2_0_and := [
      Gate.mkAND (Wire.mk s!"e{idx}_m2_0_xn0") (Wire.mk s!"e{idx}_m2_0_xn1") (Wire.mk s!"e{idx}_m2_0_a1"),
      Gate.mkAND (Wire.mk s!"e{idx}_m2_0_xn2") (Wire.mk s!"e{idx}_m2_0_xn3") (Wire.mk s!"e{idx}_m2_0_a2"),
      Gate.mkAND (Wire.mk s!"e{idx}_m2_0_xn4") (Wire.mk s!"e{idx}_m2_0_xn5") (Wire.mk s!"e{idx}_m2_0_a3"),
      Gate.mkAND (Wire.mk s!"e{idx}_m2_0_a1") (Wire.mk s!"e{idx}_m2_0_a2") (Wire.mk s!"e{idx}_m2_0_a4"),
      Gate.mkAND (Wire.mk s!"e{idx}_m2_0_a4") (Wire.mk s!"e{idx}_m2_0_a3") m2_0_eq
    ]
    let m2_0_match := Wire.mk s!"e{idx}_m2_0"
    let m2_0_gate := Gate.mkAND m2_0_eq cdb_valid_0 m2_0_match
    
    -- src2 cdb 1
    let m2_1_xors := (List.range tagWidth).map fun i => Gate.mkXOR src2_tag[i]! cdb_tag_1[i]! (Wire.mk s!"e{idx}_m2_1_x{i}")
    let m2_1_xnors := (List.range tagWidth).map fun i => Gate.mkNOT (Wire.mk s!"e{idx}_m2_1_x{i}") (Wire.mk s!"e{idx}_m2_1_xn{i}")
    let m2_1_eq := Wire.mk s!"e{idx}_m2_1_eq"
    let m2_1_and := [
      Gate.mkAND (Wire.mk s!"e{idx}_m2_1_xn0") (Wire.mk s!"e{idx}_m2_1_xn1") (Wire.mk s!"e{idx}_m2_1_a1"),
      Gate.mkAND (Wire.mk s!"e{idx}_m2_1_xn2") (Wire.mk s!"e{idx}_m2_1_xn3") (Wire.mk s!"e{idx}_m2_1_a2"),
      Gate.mkAND (Wire.mk s!"e{idx}_m2_1_xn4") (Wire.mk s!"e{idx}_m2_1_xn5") (Wire.mk s!"e{idx}_m2_1_a3"),
      Gate.mkAND (Wire.mk s!"e{idx}_m2_1_a1") (Wire.mk s!"e{idx}_m2_1_a2") (Wire.mk s!"e{idx}_m2_1_a4"),
      Gate.mkAND (Wire.mk s!"e{idx}_m2_1_a4") (Wire.mk s!"e{idx}_m2_1_a3") m2_1_eq
    ]
    let m2_1_match := Wire.mk s!"e{idx}_m2_1"
    let m2_1_gate := Gate.mkAND m2_1_eq cdb_valid_1 m2_1_match

    -- Wakeup state calc
    let tmp_r1 := Wire.mk s!"e{idx}_tmp_r1"
    let s1_match_any := Wire.mk s!"e{idx}_m1_any"
    let r1_m1 := Wire.mk s!"e{idx}_r1_m1"
    let wakeup1_gates := [
      Gate.mkOR m1_0_match m1_1_match s1_match_any,
      Gate.mkOR src1_ready s1_match_any r1_m1,     
      Gate.mkMUX r1_m1 issue_s1r issue_we_this e_next[13]!
    ]
    
    let w1d_tmp := (List.range dataWidth).map fun i => Wire.mk s!"e{idx}_w1d_t1_{i}"
    let w1d_m01 := (List.range dataWidth).map fun i => Wire.mk s!"e{idx}_w1d_m01_{i}"
    let wakeup1_data_gates := (List.range dataWidth).map fun i => Gate.mkMUX src1_data[i]! cdb_data_1[i]! m1_1_match w1d_tmp[i]!
    let wakeup1_data_gates_2 := (List.range dataWidth).map fun i => Gate.mkMUX w1d_tmp[i]! cdb_data_0[i]! m1_0_match w1d_m01[i]!
    let wakeup1_data_gates_we := (List.range 32).map fun i => Gate.mkMUX w1d_m01[i]! issue_s1d[i]! issue_we_this e_next[20+i]!

    let tmp_r2 := Wire.mk s!"e{idx}_tmp_r2"
    let s2_match_any := Wire.mk s!"e{idx}_m2_any"
    let r2_m2 := Wire.mk s!"e{idx}_r2_m2"
    let wakeup2_gates := [
      Gate.mkOR m2_0_match m2_1_match s2_match_any,
      Gate.mkOR src2_ready s2_match_any r2_m2,     
      Gate.mkMUX r2_m2 issue_s2r issue_we_this e_next[52]!
    ]
    
    let w2d_tmp := (List.range dataWidth).map fun i => Wire.mk s!"e{idx}_w2d_t1_{i}"
    let w2d_m01 := (List.range dataWidth).map fun i => Wire.mk s!"e{idx}_w2d_m01_{i}"
    let wakeup2_data_gates := (List.range dataWidth).map fun i => Gate.mkMUX src2_data[i]! cdb_data_1[i]! m2_1_match w2d_tmp[i]!
    let wakeup2_data_gates_2 := (List.range dataWidth).map fun i => Gate.mkMUX w2d_tmp[i]! cdb_data_0[i]! m2_0_match w2d_m01[i]!
    let wakeup2_data_gates_we := (List.range 32).map fun i => Gate.mkMUX w2d_m01[i]! issue_s2d[i]! issue_we_this e_next[59+i]!

    -- Dispatch integration
    let dispatch_en_this := if bank == 0 then dispatch_en_0 else dispatch_en_1
    let dispatch_grant := Wire.mk s!"dispatch_grant_{idx}"
    let dispatch := Wire.mk s!"e{idx}_dispatch"
    let dispatch_gate := Gate.mkAND dispatch_en_this dispatch_grant dispatch
    
    -- valid bit
    let v_keep := Wire.mk s!"e{idx}_v_keep"
    let not_dispatch := Wire.mk s!"e{idx}_not_dispatch"
    let valid_we := [
      Gate.mkNOT dispatch not_dispatch,
      Gate.mkAND valid not_dispatch v_keep,
      Gate.mkOR v_keep issue_we_this e_next[0]!
    ]
    
    -- opcode, tags pass through mux
    let opcode_gates := (List.range opcodeWidth).map fun i => Gate.mkMUX e_cur[1+i]! issue_opcode[i]! issue_we_this e_next[1+i]!
    let dest_tag_gates := (List.range tagWidth).map fun i => Gate.mkMUX e_cur[7+i]! issue_dest[i]! issue_we_this e_next[7+i]!
    let src1_tag_gates := (List.range tagWidth).map fun i => Gate.mkMUX e_cur[14+i]! issue_s1t[i]! issue_we_this e_next[14+i]!
    let src2_tag_gates := (List.range tagWidth).map fun i => Gate.mkMUX e_cur[53+i]! issue_s2t[i]! issue_we_this e_next[53+i]!
    
    let e_gates := m1_0_xors ++ m1_0_xnors ++ m1_0_and ++ [m1_0_gate] ++
                   m1_1_xors ++ m1_1_xnors ++ m1_1_and ++ [m1_1_gate] ++
                   m2_0_xors ++ m2_0_xnors ++ m2_0_and ++ [m2_0_gate] ++
                   m2_1_xors ++ m2_1_xnors ++ m2_1_and ++ [m2_1_gate] ++
                   wakeup1_gates ++ wakeup1_data_gates ++ wakeup1_data_gates_2 ++ wakeup1_data_gates_we ++
                   wakeup2_gates ++ wakeup2_data_gates ++ wakeup2_data_gates_2 ++ wakeup2_data_gates_we ++
                   [dispatch_gate] ++ valid_we ++ opcode_gates ++ dest_tag_gates ++ src1_tag_gates ++ src2_tag_gates
                   
    let e_inst : CircuitInstance := {
      moduleName := "Register91", instName := s!"u_e{idx}",
      portMap := (e_next.enum.map fun ⟨i, w⟩ => (s!"d_{i}", w)) ++ [("clock", clock), ("reset", reset)] ++ (e_cur.enum.map fun ⟨i, w⟩ => (s!"q_{i}", w))
    }
    
    let is_ready := Wire.mk s!"e{idx}_ready"
    let and_ready := Gate.mkAND r1_m1 r2_m2 (Wire.mk s!"e{idx}_r12")
    let and_r_val := Gate.mkAND valid (Wire.mk s!"e{idx}_r12") is_ready
    
    (e_gates ++ [and_ready, and_r_val], [e_inst], valid, is_ready)
  
  -- Apply for 0 -> 3
  let (eg0, ei0, ev0, er0) := buildEntry 0
  let (eg1, ei1, ev1, er1) := buildEntry 1
  let (eg2, ei2, ev2, er2) := buildEntry 2
  let (eg3, ei3, ev3, er3) := buildEntry 3
  
  -- Bank 0 alloc logic: full when valid 0 and valid 1 are 1? No, just valid of alloc_ptr.
  let v_01_mux := Wire.mk "v_01_mux"
  let alloc_avail_g_0 := [
    Gate.mkMUX ev0 ev1 alloc_ptr_0 v_01_mux,
    Gate.mkNOT v_01_mux alloc_avail_0
  ]
  
  -- Bank 1 alloc
  let v_23_mux := Wire.mk "v_23_mux"
  let alloc_avail_g_1 := [
    Gate.mkMUX ev2 ev3 alloc_ptr_1 v_23_mux,
    Gate.mkNOT v_23_mux alloc_avail_1
  ]

  -- Bank 0 Arbiter (PriorityArbiter2)
  let arb0_in0 := er0; let arb0_in1 := er1
  let arb0_gr0 := Wire.mk "dispatch_grant_0"
  let arb0_gr1 := Wire.mk "dispatch_grant_1"
  let arb0_valid := dispatch_valid_0
  let arb0_inst : CircuitInstance := {
    moduleName := "PriorityArbiter2", instName := "u_arb0",
    portMap := [("req_0", arb0_in0), ("req_1", arb0_in1), 
                ("grant_0", arb0_gr0), ("grant_1", arb0_gr1), 
                ("valid", dispatch_valid_0)]
  }
  
  -- Bank 1 Arbiter (PriorityArbiter2)
  let arb1_in0 := er2; let arb1_in1 := er3
  let arb1_gr0 := Wire.mk "dispatch_grant_2"
  let arb1_gr1 := Wire.mk "dispatch_grant_3"
  let arb1_valid := dispatch_valid_1
  let arb1_inst : CircuitInstance := {
    moduleName := "PriorityArbiter2", instName := "u_arb1",
    portMap := [("req_0", arb1_in0), ("req_1", arb1_in1), 
                ("grant_0", arb1_gr0), ("grant_1", arb1_gr1), 
                ("valid", dispatch_valid_1)]
  }

  -- Bank 0 Muxes (Mux2xN for opcode, src1, src2, dest)
  -- Since we just have 2 elements, we can build custom MUX2 trees or just instances.
  -- The Shoumei.Circuits library has Mux2x8. But we need 32 etc. We can just generate multiplexing logic!
  let mkMux2Array (name: String) (width: Nat) (in0 in1 out_wires: List Wire) (sel: Wire) : List Gate :=
    (List.range width).map fun i => Gate.mkMUX in0[i]! in1[i]! sel out_wires[i]!
    
  let e0 := makeIndexedWires "e0" entryWidth
  let e1 := makeIndexedWires "e1" entryWidth
  let b0_mux_opcode := mkMux2Array "b0_m_op" opcodeWidth (e0.drop 1) (e1.drop 1) dispatch_opcode_0 arb0_gr1
  let b0_mux_dst := mkMux2Array "b0_m_dst" tagWidth (e0.drop 7) (e1.drop 7) dispatch_dest_tag_0 arb0_gr1
  let b0_mux_s1d := mkMux2Array "b0_m_s1d" dataWidth (e0.drop 20) (e1.drop 20) dispatch_src1_data_0 arb0_gr1
  let b0_mux_s2d := mkMux2Array "b0_m_s2d" dataWidth (e0.drop 59) (e1.drop 59) dispatch_src2_data_0 arb0_gr1

  let e2 := makeIndexedWires "e2" entryWidth
  let e3 := makeIndexedWires "e3" entryWidth
  let b1_mux_opcode := mkMux2Array "b1_m_op" opcodeWidth (e2.drop 1) (e3.drop 1) dispatch_opcode_1 arb1_gr1
  let b1_mux_dst := mkMux2Array "b1_m_dst" tagWidth (e2.drop 7) (e3.drop 7) dispatch_dest_tag_1 arb1_gr1
  let b1_mux_s1d := mkMux2Array "b1_m_s1d" dataWidth (e2.drop 20) (e3.drop 20) dispatch_src1_data_1 arb1_gr1
  let b1_mux_s2d := mkMux2Array "b1_m_s2d" dataWidth (e2.drop 59) (e3.drop 59) dispatch_src2_data_1 arb1_gr1

  { name := "ReservationStation4_W2"
    inputs := [clock, reset, zero, one, 
               issue_en_0, issue_en_1] ++
              (if enableStoreLoadOrdering then [issue_is_store_0, issue_is_store_1] else []) ++
              issue_opcode_0 ++ issue_dest_tag_0 ++ [issue_src1_ready_0] ++ issue_src1_tag_0 ++ issue_src1_data_0 ++
              [issue_src2_ready_0] ++ issue_src2_tag_0 ++ issue_src2_data_0 ++
              issue_opcode_1 ++ issue_dest_tag_1 ++ [issue_src1_ready_1] ++ issue_src1_tag_1 ++ issue_src1_data_1 ++
              [issue_src2_ready_1] ++ issue_src2_tag_1 ++ issue_src2_data_1 ++
              [cdb_valid_0] ++ cdb_tag_0 ++ cdb_data_0 ++
              [cdb_valid_1] ++ cdb_tag_1 ++ cdb_data_1 ++
              [dispatch_en_0, dispatch_en_1]
    outputs := [alloc_avail_0, alloc_avail_1, dispatch_valid_0, dispatch_valid_1] ++
               dispatch_opcode_0 ++ dispatch_src1_data_0 ++
               dispatch_src2_data_0 ++ dispatch_dest_tag_0 ++
               dispatch_opcode_1 ++ dispatch_src1_data_1 ++
               dispatch_src2_data_1 ++ dispatch_dest_tag_1
    gates := ptr_gates ++ base_issue_gates_0 ++ base_issue_gates_1 ++
             eg0 ++ eg1 ++ eg2 ++ eg3 ++
             alloc_avail_g_0 ++ alloc_avail_g_1 ++
             b0_mux_opcode ++ b0_mux_dst ++ b0_mux_s1d ++ b0_mux_s2d ++
             b1_mux_opcode ++ b1_mux_dst ++ b1_mux_s1d ++ b1_mux_s2d
    instances := [ptr_inst_0, ptr_inst_1, arb0_inst, arb1_inst] ++
                 ei0 ++ ei1 ++ ei2 ++ ei3 }

end Shoumei.RISCV.Execution
