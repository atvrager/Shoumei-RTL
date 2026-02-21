/-
RenameStage_W2.lean — Dual-issue RenameStage structural circuit

Extends mkRenameStage to 2 rename slots per cycle.

Key design points:
- Two instruction port buses (slot 0 and slot 1), each with rs1/rs2/rs3/rd/has_rd/instr_valid
- Intra-group forwarding: slot[1]'s rs1/rs2 reads get a bypass MUX checking if
  slot[0]'s rd_addr matches — no stale RAT read for instructions in the same group
- One RAT instance with 2 write ports: slot 0 writes, then slot 1 writes sequentially
  (implemented as two RAT instances where slot 1 RAT is fed slot 0's output for restores)
  Simplification used here: SAME single-write-port RAT, slot 1 read goes through bypass MUX
- BitmapFreeList_64_W2: two dequeue ports (deq_ready_0, deq_ready_1)
- Committed RAT: N write ports (one per committing instruction)
- Stall: global stall if EITHER slot needs an alloc and FreeList is empty for that slot
-/

import Shoumei.RISCV.Renaming.RenameStage
import Shoumei.RISCV.Renaming.BitmapFreeList

namespace Shoumei.RISCV.Renaming

open Shoumei
open Shoumei.Circuits.Combinational

/--
Dual-issue RenameStage structural circuit (N=2).

Port additions vs. mkRenameStage:
Slot 0 keeps the original port names (backwards compatible with W1 test benches):
  instr_valid, has_rd, rs1_addr[4:0], rs2_addr[4:0], rs3_addr[4:0], rd_addr[4:0]
  → rs1_phys[5:0], rs2_phys[5:0], rs3_phys[5:0], rd_phys[5:0], old_rd_phys[5:0], rename_valid

Slot 1 adds a parallel set of instruction ports with suffix "_1":
  instr_valid_1, has_rd_1, rs1_addr_1[4:0], rs2_addr_1[4:0], rs3_addr_1[4:0], rd_addr_1[4:0]
  → rs1_phys_1[5:0], rs2_phys_1[5:0], rs3_phys_1[5:0], rd_phys_1[5:0], old_rd_phys_1[5:0], rename_valid_1

Commit side: two commit channels (commit_valid_0/1, commit_archRd_0/1, commit_physRd_0/1, etc.)
-/
def mkRenameStage_W2 : Circuit :=
  let tagWidth    := 6
  let archWidth   := 5
  let dataWidth   := 32

  -- === Global signals ===
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero  := Wire.mk "zero"
  let one   := Wire.mk "one"

  -- === Slot 0 instruction inputs (original names, backwards-compatible) ===
  let instr_valid_0  := Wire.mk "instr_valid"
  let has_rd_0       := Wire.mk "has_rd"
  let rs1_addr_0     := (List.range archWidth).map fun i => Wire.mk s!"rs1_addr_{i}"
  let rs2_addr_0     := (List.range archWidth).map fun i => Wire.mk s!"rs2_addr_{i}"
  let rs3_addr_0     := (List.range archWidth).map fun i => Wire.mk s!"rs3_addr_{i}"
  let rd_addr_0      := (List.range archWidth).map fun i => Wire.mk s!"rd_addr_{i}"
  let force_alloc_0  := Wire.mk "force_alloc"

  -- === Slot 1 instruction inputs ===
  let instr_valid_1  := Wire.mk "instr_valid_1"
  let has_rd_1       := Wire.mk "has_rd_1"
  let rs1_addr_1     := (List.range archWidth).map fun i => Wire.mk s!"rs1_addr_1_{i}"
  let rs2_addr_1     := (List.range archWidth).map fun i => Wire.mk s!"rs2_addr_1_{i}"
  let rs3_addr_1     := (List.range archWidth).map fun i => Wire.mk s!"rs3_addr_1_{i}"
  let rd_addr_1      := (List.range archWidth).map fun i => Wire.mk s!"rd_addr_1_{i}"
  let force_alloc_1  := Wire.mk "force_alloc_1"

  -- === Commit channel 0 ===
  let flush_en            := Wire.mk "flush_en"
  let commit_valid_0      := Wire.mk "commit_valid"
  let commit_archRd_0     := (List.range archWidth).map fun i => Wire.mk s!"commit_archRd_{i}"
  let commit_physRd_0     := (List.range tagWidth).map  fun i => Wire.mk s!"commit_physRd_{i}"
  let commit_hasPhysRd_0  := Wire.mk "commit_hasPhysRd"
  let commit_hasAllocSlot_0 := Wire.mk "commit_hasAllocSlot"

  -- === Commit channel 1 ===
  let commit_valid_1      := Wire.mk "commit_valid_1"
  let commit_archRd_1     := (List.range archWidth).map fun i => Wire.mk s!"commit_archRd_1_{i}"
  let commit_physRd_1     := (List.range tagWidth).map  fun i => Wire.mk s!"commit_physRd_1_{i}"
  let commit_hasPhysRd_1  := Wire.mk "commit_hasPhysRd_1"
  let commit_hasAllocSlot_1 := Wire.mk "commit_hasAllocSlot_1"

  -- === CDB / retire ===
  let cdb_valid  := Wire.mk "cdb_valid"
  let cdb_tag    := (List.range tagWidth).map  fun i => Wire.mk s!"cdb_tag_{i}"
  let cdb_data   := (List.range dataWidth).map fun i => Wire.mk s!"cdb_data_{i}"
  let retire_valid := Wire.mk "retire_valid"
  let retire_tag   := (List.range tagWidth).map fun i => Wire.mk s!"retire_tag_{i}"
  let rd_tag4    := (List.range tagWidth).map  fun i => Wire.mk s!"rd_tag4_{i}"
  let rd_data4   := (List.range dataWidth).map fun i => Wire.mk s!"rd_data4_{i}"

  -- === Slot 0 outputs ===
  let rs1_phys_out_0  := (List.range tagWidth).map fun i => Wire.mk s!"rs1_phys_out_{i}"
  let rs2_phys_out_0  := (List.range tagWidth).map fun i => Wire.mk s!"rs2_phys_out_{i}"
  let rs3_phys_out_0  := (List.range tagWidth).map fun i => Wire.mk s!"rs3_phys_out_{i}"
  let rd_phys_out_0   := (List.range tagWidth).map fun i => Wire.mk s!"rd_phys_out_{i}"
  let old_rd_phys_0   := (List.range tagWidth).map fun i => Wire.mk s!"old_rd_phys_out_{i}"
  let rename_valid_0  := Wire.mk "rename_valid"
  let stall_0         := Wire.mk "stall"
  let rs1_data_0      := (List.range dataWidth).map fun i => Wire.mk s!"rs1_data_{i}"
  let rs2_data_0      := (List.range dataWidth).map fun i => Wire.mk s!"rs2_data_{i}"
  let rd_data3_0      := (List.range dataWidth).map fun i => Wire.mk s!"rd_data3_{i}"

  -- === Slot 1 outputs ===
  let rs1_phys_out_1  := (List.range tagWidth).map fun i => Wire.mk s!"rs1_phys_out_1_{i}"
  let rs2_phys_out_1  := (List.range tagWidth).map fun i => Wire.mk s!"rs2_phys_out_1_{i}"
  let rs3_phys_out_1  := (List.range tagWidth).map fun i => Wire.mk s!"rs3_phys_out_1_{i}"
  let rd_phys_out_1   := (List.range tagWidth).map fun i => Wire.mk s!"rd_phys_out_1_{i}"
  let old_rd_phys_1   := (List.range tagWidth).map fun i => Wire.mk s!"old_rd_phys_out_1_{i}"
  let rename_valid_1  := Wire.mk "rename_valid_1"
  let stall_1         := Wire.mk "stall_1"

  -- === Internal: speculative RAT read/write wires ===
  -- Slot 0: reads rs1_0/rs2_0/rs3_0 → phys tags; writes rd_0 → alloc tag
  let rs1_phys_0  := (List.range tagWidth).map fun i => Wire.mk s!"rs1p0_{i}"
  let rs2_phys_0  := (List.range tagWidth).map fun i => Wire.mk s!"rs2p0_{i}"
  let rs3_phys_0  := (List.range tagWidth).map fun i => Wire.mk s!"rs3p0_{i}"
  let rd_phys_0   := (List.range tagWidth).map fun i => Wire.mk s!"rdp0_{i}"
  let old_rd_raw_0 := (List.range tagWidth).map fun i => Wire.mk s!"old_rd_raw0_{i}"

  -- Slot 1: RAT reads rs1_1/rs2_1/rs3_1 from speculative RAT
  -- (The RAT contains slot 0's rd if it wrote this cycle — handled by intra-group bypass)
  let rs1_phys_1_rat := (List.range tagWidth).map fun i => Wire.mk s!"rs1p1_rat_{i}"
  let rs2_phys_1_rat := (List.range tagWidth).map fun i => Wire.mk s!"rs2p1_rat_{i}"
  let rs3_phys_1_rat := (List.range tagWidth).map fun i => Wire.mk s!"rs3p1_rat_{i}"
  let rd_phys_1      := (List.range tagWidth).map fun i => Wire.mk s!"rdp1_{i}"
  let old_rd_raw_1   := (List.range tagWidth).map fun i => Wire.mk s!"old_rd_raw1_{i}"

  -- === x0 detection (per slot) ===
  let rd_or_0 := (List.range archWidth).map fun i => Wire.mk s!"rd_or0_{i}"
  let rd_or_1 := (List.range archWidth).map fun i => Wire.mk s!"rd_or1_{i}"
  let x0_0    := Wire.mk "x0_det_0"
  let x0_1    := Wire.mk "x0_det_1"
  let x0_gates_0 :=
    [Gate.mkOR rd_addr_0[0]! rd_addr_0[1]! rd_or_0[0]!] ++
    (List.range 3).map (fun i => Gate.mkOR rd_or_0[i]! rd_addr_0[i+2]! rd_or_0[i+1]!) ++
    [Gate.mkNOT rd_or_0[3]! x0_0]
  let x0_gates_1 :=
    [Gate.mkOR rd_addr_1[0]! rd_addr_1[1]! rd_or_1[0]!] ++
    (List.range 3).map (fun i => Gate.mkOR rd_or_1[i]! rd_addr_1[i+2]! rd_or_1[i+1]!) ++
    [Gate.mkNOT rd_or_1[3]! x0_1]

  -- needs_alloc_{k} = has_rd_{k} AND NOT(x0_{k})
  let not_x0_0     := Wire.mk "not_x0_0"; let not_x0_1 := Wire.mk "not_x0_1"
  let needs_alloc_0 := Wire.mk "needs_alloc_0"
  let needs_alloc_1 := Wire.mk "needs_alloc_1"
  let needs_alloc_gates :=
    [Gate.mkNOT x0_0 not_x0_0, Gate.mkAND has_rd_0 not_x0_0 needs_alloc_0,
     Gate.mkNOT x0_1 not_x0_1, Gate.mkAND has_rd_1 not_x0_1 needs_alloc_1]

  -- === FreeList W2 port wires ===
  let freelist_enq_ready := Wire.mk "fl_enq_ready"
  let alloc_avail_0 := Wire.mk "alloc_avail_0"
  let alloc_avail_1 := Wire.mk "alloc_avail_1"
  let fl_deq_data_0 := (List.range tagWidth).map fun i => Wire.mk s!"fl_deq0_{i}"
  let fl_deq_data_1 := (List.range tagWidth).map fun i => Wire.mk s!"fl_deq1_{i}"
  let fl_deq_ready_0 := Wire.mk "fl_deq_ready_0"
  let fl_deq_ready_1 := Wire.mk "fl_deq_ready_1"

  -- Stall per slot: stall_k = needs_alloc_k AND NOT(alloc_avail_k)
  -- Global stall: stall_any = stall_0 OR stall_1 (all-or-nothing)
  let not_avail_0 := Wire.mk "not_avail_0"; let not_avail_1 := Wire.mk "not_avail_1"
  let stall_raw0  := Wire.mk "stall_raw_0"; let stall_raw1  := Wire.mk "stall_raw_1"
  let stall_any   := Wire.mk "stall_any"
  let stall_gates :=
    [Gate.mkNOT alloc_avail_0 not_avail_0,
     Gate.mkNOT alloc_avail_1 not_avail_1,
     Gate.mkAND needs_alloc_0 not_avail_0 stall_raw0,
     Gate.mkAND needs_alloc_1 not_avail_1 stall_raw1,
     Gate.mkOR  stall_raw0 stall_raw1 stall_any,
     Gate.mkBUF stall_any stall_0,
     Gate.mkBUF stall_any stall_1]

  -- rename_valid_{k} = instr_valid_{k} AND NOT stall_any
  let not_stall   := Wire.mk "not_stall_w2"
  let rvalid_gates :=
    [Gate.mkNOT stall_any not_stall,
     Gate.mkAND instr_valid_0 not_stall rename_valid_0,
     Gate.mkAND instr_valid_1 not_stall rename_valid_1]

  -- allocate_fire_{k} = needs_alloc_{k} AND rename_valid_{k}
  let alloc_fire_0 := Wire.mk "alloc_fire_0"
  let alloc_fire_1 := Wire.mk "alloc_fire_1"
  let ff0 := Wire.mk "ff_fire_0"; let ff1 := Wire.mk "ff_fire_1"
  let cnt0 := Wire.mk "counter_advance_0"; let cnt1 := Wire.mk "counter_advance_1"
  let fire_gates :=
    [Gate.mkAND needs_alloc_0 rename_valid_0 alloc_fire_0,
     Gate.mkAND force_alloc_0 rename_valid_0 ff0,
     Gate.mkOR  alloc_fire_0 ff0 cnt0,
     Gate.mkAND needs_alloc_1 rename_valid_1 alloc_fire_1,
     Gate.mkAND force_alloc_1 rename_valid_1 ff1,
     Gate.mkOR  alloc_fire_1 ff1 cnt1,
     Gate.mkBUF cnt0 fl_deq_ready_0,
     Gate.mkBUF cnt1 fl_deq_ready_1]

  -- rat_we_{k} = alloc_fire_{k}
  let rat_we_0 := Wire.mk "rat_we_0"
  let rat_we_1 := Wire.mk "rat_we_1"
  let rat_we_gates :=
    [Gate.mkBUF alloc_fire_0 rat_we_0, Gate.mkBUF alloc_fire_1 rat_we_1]

  -- rd_phys_{k} = fl_deq_data_{k} AND cnt_{k}
  let rd_phys_0_gates := (List.range tagWidth).map fun i =>
    Gate.mkAND fl_deq_data_0[i]! cnt0 rd_phys_0[i]!
  let rd_phys_1_gates := (List.range tagWidth).map fun i =>
    Gate.mkAND fl_deq_data_1[i]! cnt1 rd_phys_1[i]!

  -- === Intra-group bypass for slot 1 ===
  -- Check rd_addr_0 == src_addr_1 (5-bit equality via XOR+NOT then AND-reduce)
  -- If match AND rat_we_0: forward rd_phys_0 to slot 1's rs1/rs2
  let mkBypass (pfx : String) (src_addr : List Wire) (rat_out : List Wire) : List Gate × List Wire :=
    -- XNOR[i] = NOT(rd_addr_0[i] XOR src_addr[i])
    let xors := (List.range archWidth).map fun i => Wire.mk s!"{pfx}_x{i}"
    let xnors := (List.range archWidth).map fun i => Wire.mk s!"{pfx}_xn{i}"
    let xor_gates := (List.range archWidth).map fun i =>
      Gate.mkXOR rd_addr_0[i]! src_addr[i]! xors[i]!
    let xnor_gates := (List.range archWidth).map fun i =>
      Gate.mkNOT xors[i]! xnors[i]!
    -- AND-reduce: eq = AND(xnors[0..4])
    let a1 := Wire.mk s!"{pfx}_a1"; let a2 := Wire.mk s!"{pfx}_a2"
    let a3 := Wire.mk s!"{pfx}_a3"; let eq := Wire.mk s!"{pfx}_eq"
    let and_gates :=
      [Gate.mkAND xnors[0]! xnors[1]! a1,
       Gate.mkAND xnors[2]! xnors[3]! a2,
       Gate.mkAND a1 a2 a3,
       Gate.mkAND a3 xnors[4]! eq]
    -- bypass_active = eq AND rat_we_0
    let bypass_active := Wire.mk s!"{pfx}_ba"
    let ba_gate := Gate.mkAND eq rat_we_0 bypass_active
    -- MUX: bypass_out[i] = MUX(rat_out[i], rd_phys_0[i], bypass_active)
    let mux_outs := (List.range tagWidth).map fun i => Wire.mk s!"{pfx}_o{i}"
    let mux_gates := (List.range tagWidth).map fun i =>
      Gate.mkMUX rat_out[i]! rd_phys_0[i]! bypass_active mux_outs[i]!
    (xor_gates ++ xnor_gates ++ and_gates ++ [ba_gate] ++ mux_gates, mux_outs)

  -- Slot 1 rs1 bypass: if rd_addr_0 == rs1_addr_1, forward rd_phys_0 instead of RAT output
  let (bypass_rs1_gates, rs1_phys_1) := mkBypass "bp_rs1" rs1_addr_1 rs1_phys_1_rat
  -- Slot 1 rs2 bypass
  let (bypass_rs2_gates, rs2_phys_1) := mkBypass "bp_rs2" rs2_addr_1 rs2_phys_1_rat

  -- === Committed RAT write-enable per channel ===
  let mkCratWe (pfx : String) (v : Wire) (arch : List Wire) (hasPR : Wire) : List Gate × Wire :=
    let or1 := Wire.mk s!"{pfx}_cor1"; let or2 := Wire.mk s!"{pfx}_cor2"
    let or3 := Wire.mk s!"{pfx}_cor3"; let or4 := Wire.mk s!"{pfx}_cor4"
    let is_x0 := Wire.mk s!"{pfx}_is_x0"; let not_x0w := Wire.mk s!"{pfx}_nx0"
    let vh := Wire.mk s!"{pfx}_vh"; let we := Wire.mk s!"{pfx}_we"
    ([Gate.mkOR arch[0]! arch[1]! or1,
      Gate.mkOR or1 arch[2]! or2, Gate.mkOR or2 arch[3]! or3,
      Gate.mkOR or3 arch[4]! or4,
      Gate.mkNOT or4 is_x0, Gate.mkNOT is_x0 not_x0w,
      Gate.mkAND v hasPR vh, Gate.mkAND vh not_x0w we], we)

  let (crat_we_gates_0, crat_we_0) := mkCratWe "c0" commit_valid_0 commit_archRd_0 commit_hasPhysRd_0
  let (crat_we_gates_1, crat_we_1) := mkCratWe "c1" commit_valid_1 commit_archRd_1 commit_hasPhysRd_1

  -- Committed RAT alloc advance per channel
  let crat_alloc_0 := Wire.mk "commit_alloc_adv_0"
  let crat_alloc_1 := Wire.mk "commit_alloc_adv_1"
  let crat_alloc_gates :=
    [Gate.mkAND commit_valid_0 commit_hasAllocSlot_0 crat_alloc_0,
     Gate.mkAND commit_valid_1 commit_hasAllocSlot_1 crat_alloc_1]

  -- Committed RAT dump wires (shared by both commit channels)
  let crat_dump := (List.range 32).map fun i =>
    (List.range tagWidth).map fun j => Wire.mk s!"crat_dump_{i}_{j}"

  -- Old rd raw per slot (from speculative RAT old_rd_data port)
  -- We use the RAT's old_rd read: it looks up current rd mapping before the write
  -- Slot 0: directly from RAT old_rd_data
  -- Slot 1: from RAT's secondary old_rd_data (or bypass from slot 0 if forwarding)

  -- === Sub-instances ===

  -- Committed RAT (single write port; W2 commit arbitrates — commit_0 wins if both fire)
  -- For dual commit: we need a 2-write-port committed RAT.
  -- Simplification for N=2: daisy-chain two RAT instances (committed RAT 0 → 1)
  -- Inst 1: commit_0 writes to crat_0; its dump feeds restore of crat_1
  -- Inst 2: commit_1 writes to crat_1; its dump = the final committed state
  -- For readout: use crat_1 dump (which sees both commits)
  let crat_mid_dump := (List.range 32).map fun i =>
    (List.range tagWidth).map fun j => Wire.mk s!"crat_mid_{i}_{j}"

  let crat_0_inst : CircuitInstance := {
    moduleName := "RAT_32x6"
    instName := "u_crat_0"
    portMap :=
      [("clock", clock), ("reset", reset), ("write_en", crat_we_0)] ++
      (commit_archRd_0.enum.map fun ⟨i,w⟩ => (s!"write_addr_{i}", w)) ++
      (commit_physRd_0.enum.map fun ⟨i,w⟩ => (s!"write_data_{i}", w)) ++
      ((List.range archWidth).map fun i => (s!"rs1_addr_{i}", zero)) ++
      ((List.range archWidth).map fun i => (s!"rs2_addr_{i}", zero)) ++
      ((List.range archWidth).map fun i => (s!"rs3_addr_{i}", zero)) ++
      ((List.range tagWidth).map fun i => (s!"rs1_data_{i}", Wire.mk s!"c0_rs1u_{i}")) ++
      ((List.range tagWidth).map fun i => (s!"rs2_data_{i}", Wire.mk s!"c0_rs2u_{i}")) ++
      ((List.range tagWidth).map fun i => (s!"rs3_data_{i}", Wire.mk s!"c0_rs3u_{i}")) ++
      ((List.range tagWidth).map fun i => (s!"old_rd_data_{i}", Wire.mk s!"c0_oldu_{i}")) ++
      [("restore_en", zero)] ++
      ((List.range 32).map fun i => (List.range tagWidth).map fun j =>
        (s!"restore_data_{i}_{j}", zero)).flatten ++
      ((List.range 32).map fun i => (List.range tagWidth).map fun j =>
        (s!"dump_data_{i}_{j}", crat_mid_dump[i]![j]!)).flatten
  }
  let crat_1_inst : CircuitInstance := {
    moduleName := "RAT_32x6"
    instName := "u_crat_1"
    portMap :=
      [("clock", clock), ("reset", reset), ("write_en", crat_we_1)] ++
      (commit_archRd_1.enum.map fun ⟨i,w⟩ => (s!"write_addr_{i}", w)) ++
      (commit_physRd_1.enum.map fun ⟨i,w⟩ => (s!"write_data_{i}", w)) ++
      ((List.range archWidth).map fun i => (s!"rs1_addr_{i}", zero)) ++
      ((List.range archWidth).map fun i => (s!"rs2_addr_{i}", zero)) ++
      ((List.range archWidth).map fun i => (s!"rs3_addr_{i}", zero)) ++
      ((List.range tagWidth).map fun i => (s!"rs1_data_{i}", Wire.mk s!"c1_rs1u_{i}")) ++
      ((List.range tagWidth).map fun i => (s!"rs2_data_{i}", Wire.mk s!"c1_rs2u_{i}")) ++
      ((List.range tagWidth).map fun i => (s!"rs3_data_{i}", Wire.mk s!"c1_rs3u_{i}")) ++
      ((List.range tagWidth).map fun i => (s!"old_rd_data_{i}", Wire.mk s!"c1_oldu_{i}")) ++
      [("restore_en", zero)] ++
      ((List.range 32).map fun i => (List.range tagWidth).map fun j =>
        (s!"restore_data_{i}_{j}", zero)).flatten ++
      ((List.range 32).map fun i => (List.range tagWidth).map fun j =>
        (s!"dump_data_{i}_{j}", crat_dump[i]![j]!)).flatten
  }

  -- Speculative RAT: 1 write port (slot 0 wins each cycle; slot 1 uses bypass for forwarding)
  -- The RAT write is from slot 0 when alloc_fire_0; slot 1 is handled by the pipeline
  -- as a second write on the same port in the NEXT cycle unless they're independent.
  -- For N=2 structural simplification: we use ONE RAT but add slot-1 write via a second
  -- RAT instance (u_rat_1) that takes slot-0's dump + slot-1's write.
  let srat_0_dump := (List.range 32).map fun i =>
    (List.range tagWidth).map fun j => Wire.mk s!"srat0_dump_{i}_{j}"

  let rat_inst_0 : CircuitInstance := {
    moduleName := "RAT_32x6"
    instName := "u_rat_0"
    portMap :=
      [("clock", clock), ("reset", reset), ("write_en", rat_we_0)] ++
      (rd_addr_0.enum.map fun ⟨i,w⟩ => (s!"write_addr_{i}", w)) ++
      (rd_phys_0.enum.map fun ⟨i,w⟩ => (s!"write_data_{i}", w)) ++
      (rs1_addr_0.enum.map fun ⟨i,w⟩ => (s!"rs1_addr_{i}", w)) ++
      (rs2_addr_0.enum.map fun ⟨i,w⟩ => (s!"rs2_addr_{i}", w)) ++
      (rs3_addr_0.enum.map fun ⟨i,w⟩ => (s!"rs3_addr_{i}", w)) ++
      (rs1_phys_0.enum.map fun ⟨i,w⟩ => (s!"rs1_data_{i}", w)) ++
      (rs2_phys_0.enum.map fun ⟨i,w⟩ => (s!"rs2_data_{i}", w)) ++
      (rs3_phys_0.enum.map fun ⟨i,w⟩ => (s!"rs3_data_{i}", w)) ++
      (old_rd_raw_0.enum.map fun ⟨i,w⟩ => (s!"old_rd_data_{i}", w)) ++
      [("restore_en", flush_en)] ++
      ((List.range 32).map fun i => (List.range tagWidth).map fun j =>
        (s!"restore_data_{i}_{j}", crat_dump[i]![j]!)).flatten ++
      ((List.range 32).map fun i => (List.range tagWidth).map fun j =>
        (s!"dump_data_{i}_{j}", srat_0_dump[i]![j]!)).flatten
  }

  -- Slot 1 RAT reads from after slot 0's write (uses slot 0's dump as "current state")
  -- For register reads by slot 1 from RAT (before bypass applies):
  let rat_inst_1 : CircuitInstance := {
    moduleName := "RAT_32x6"
    instName := "u_rat_1"
    portMap :=
      [("clock", clock), ("reset", reset), ("write_en", rat_we_1)] ++
      (rd_addr_1.enum.map fun ⟨i,w⟩ => (s!"write_addr_{i}", w)) ++
      (rd_phys_1.enum.map fun ⟨i,w⟩ => (s!"write_data_{i}", w)) ++
      (rs1_addr_1.enum.map fun ⟨i,w⟩ => (s!"rs1_addr_{i}", w)) ++
      (rs2_addr_1.enum.map fun ⟨i,w⟩ => (s!"rs2_addr_{i}", w)) ++
      (rs3_addr_1.enum.map fun ⟨i,w⟩ => (s!"rs3_addr_{i}", w)) ++
      (rs1_phys_1_rat.enum.map fun ⟨i,w⟩ => (s!"rs1_data_{i}", w)) ++
      (rs2_phys_1_rat.enum.map fun ⟨i,w⟩ => (s!"rs2_data_{i}", w)) ++
      (rs3_phys_1_rat.enum.map fun ⟨i,w⟩ => (s!"rs3_data_{i}", w)) ++
      (old_rd_raw_1.enum.map fun ⟨i,w⟩ => (s!"old_rd_data_{i}", w)) ++
      [("restore_en", flush_en)] ++
      -- Slot 1 RAT restores from slot 0's dump (which is post-slot0-write state)
      ((List.range 32).map fun i => (List.range tagWidth).map fun j =>
        (s!"restore_data_{i}_{j}", srat_0_dump[i]![j]!)).flatten ++
      ((List.range 32).map fun i => (List.range tagWidth).map fun j =>
        (s!"dump_data_{i}_{j}", Wire.mk s!"srat1_dump_{i}_{j}")).flatten
  }

  -- BitmapFreeList W2 instance
  let freelist_inst : CircuitInstance := {
    moduleName := "BitmapFreeList_64_W2"
    instName := "u_freelist"
    portMap :=
      [("clock", clock), ("reset", reset), ("zero", zero), ("one", one)] ++
      (retire_tag.enum.map fun ⟨i,w⟩ => (s!"enq_data_{i}", w)) ++
      [("enq_valid", retire_valid),
       ("deq_ready_0", fl_deq_ready_0), ("deq_ready_1", fl_deq_ready_1)] ++
      (fl_deq_data_0.enum.map fun ⟨i,w⟩ => (s!"deq_data_0_{i}", w)) ++
      [("deq_valid_0", alloc_avail_0)] ++
      (fl_deq_data_1.enum.map fun ⟨i,w⟩ => (s!"deq_data_1_{i}", w)) ++
      [("deq_valid_1", alloc_avail_1),
       ("enq_ready", freelist_enq_ready),
       ("flush_en", flush_en),
       ("commit_alloc_en", crat_alloc_0)] ++   -- slot 0 commit drives committed bitmap clear
      (commit_physRd_0.enum.map fun ⟨i,w⟩ => (s!"commit_alloc_tag_{i}", w))
  }

  -- PhysRegFile (shared, single write port from CDB)
  let physregfile_inst : CircuitInstance := {
    moduleName := "PhysRegFile_64x32"
    instName := "u_prf"
    portMap :=
      [("clock", clock), ("reset", reset), ("wr_en", cdb_valid)] ++
      (rs1_phys_0.enum.map fun ⟨i,w⟩ => (s!"rd_tag1_{i}", w)) ++
      (rs2_phys_0.enum.map fun ⟨i,w⟩ => (s!"rd_tag2_{i}", w)) ++
      (rs3_phys_0.enum.map fun ⟨i,w⟩ => (s!"rd_tag3_{i}", w)) ++
      (rd_tag4.enum.map fun ⟨i,w⟩ => (s!"rd_tag4_{i}", w)) ++
      (cdb_tag.enum.map fun ⟨i,w⟩ => (s!"wr_tag_{i}", w)) ++
      (cdb_data.enum.map fun ⟨i,w⟩ => (s!"wr_data_{i}", w)) ++
      (rs1_data_0.enum.map fun ⟨i,w⟩ => (s!"rd_data1_{i}", w)) ++
      (rs2_data_0.enum.map fun ⟨i,w⟩ => (s!"rd_data2_{i}", w)) ++
      (rd_data3_0.enum.map fun ⟨i,w⟩ => (s!"rd_data3_{i}", w)) ++
      (rd_data4.enum.map fun ⟨i,w⟩ => (s!"rd_data4_{i}", w))
  }

  -- Output buffer gates (slot 0)
  let out_gates_0 :=
    (List.range tagWidth).map (fun i => Gate.mkBUF rs1_phys_0[i]! rs1_phys_out_0[i]!) ++
    (List.range tagWidth).map (fun i => Gate.mkBUF rs2_phys_0[i]! rs2_phys_out_0[i]!) ++
    (List.range tagWidth).map (fun i => Gate.mkBUF rs3_phys_0[i]! rs3_phys_out_0[i]!) ++
    (List.range tagWidth).map (fun i => Gate.mkBUF rd_phys_0[i]!  rd_phys_out_0[i]!) ++
    (List.range tagWidth).map (fun i => Gate.mkBUF old_rd_raw_0[i]! old_rd_phys_0[i]!)

  -- Output buffer gates (slot 1) — use bypass-corrected phys tags
  let out_gates_1 :=
    (List.range tagWidth).map (fun i => Gate.mkBUF rs1_phys_1[i]! rs1_phys_out_1[i]!) ++
    (List.range tagWidth).map (fun i => Gate.mkBUF rs2_phys_1[i]! rs2_phys_out_1[i]!) ++
    (List.range tagWidth).map (fun i => Gate.mkBUF rs3_phys_1_rat[i]! rs3_phys_out_1[i]!) ++
    (List.range tagWidth).map (fun i => Gate.mkBUF rd_phys_1[i]!  rd_phys_out_1[i]!) ++
    (List.range tagWidth).map (fun i => Gate.mkBUF old_rd_raw_1[i]! old_rd_phys_1[i]!)

  -- === Assemble ===
  let all_inputs :=
    [clock, reset, zero, one,
     instr_valid_0, has_rd_0, force_alloc_0] ++
    rs1_addr_0 ++ rs2_addr_0 ++ rs3_addr_0 ++ rd_addr_0 ++
    [instr_valid_1, has_rd_1, force_alloc_1] ++
    rs1_addr_1 ++ rs2_addr_1 ++ rs3_addr_1 ++ rd_addr_1 ++
    [flush_en, commit_valid_0] ++ commit_archRd_0 ++ commit_physRd_0 ++
    [commit_hasPhysRd_0, commit_hasAllocSlot_0,
     commit_valid_1] ++ commit_archRd_1 ++ commit_physRd_1 ++
    [commit_hasPhysRd_1, commit_hasAllocSlot_1,
     cdb_valid] ++ cdb_tag ++ cdb_data ++
    [retire_valid] ++ retire_tag ++ rd_tag4

  let all_outputs :=
    [rename_valid_0, stall_0] ++ rs1_phys_out_0 ++ rs2_phys_out_0 ++ rs3_phys_out_0 ++
    rd_phys_out_0 ++ old_rd_phys_0 ++ rs1_data_0 ++ rs2_data_0 ++ rd_data3_0 ++ rd_data4 ++
    [rename_valid_1, stall_1] ++ rs1_phys_out_1 ++ rs2_phys_out_1 ++ rs3_phys_out_1 ++
    rd_phys_out_1 ++ old_rd_phys_1

  let all_gates :=
    x0_gates_0 ++ x0_gates_1 ++ needs_alloc_gates ++ stall_gates ++ rvalid_gates ++
    fire_gates ++ rat_we_gates ++ rd_phys_0_gates ++ rd_phys_1_gates ++
    bypass_rs1_gates ++ bypass_rs2_gates ++
    crat_we_gates_0 ++ crat_we_gates_1 ++ crat_alloc_gates ++
    out_gates_0 ++ out_gates_1

  let all_instances :=
    [crat_0_inst, crat_1_inst, rat_inst_0, rat_inst_1, freelist_inst, physregfile_inst]

  { name := "RenameStage_W2"
    inputs := all_inputs; outputs := all_outputs
    gates := all_gates; instances := all_instances
    signalGroups := [
      { name := "rs1_addr",   width := archWidth, wires := rs1_addr_0 },
      { name := "rs2_addr",   width := archWidth, wires := rs2_addr_0 },
      { name := "rs3_addr",   width := archWidth, wires := rs3_addr_0 },
      { name := "rd_addr",    width := archWidth, wires := rd_addr_0 },
      { name := "rs1_addr_1", width := archWidth, wires := rs1_addr_1 },
      { name := "rs2_addr_1", width := archWidth, wires := rs2_addr_1 },
      { name := "rs3_addr_1", width := archWidth, wires := rs3_addr_1 },
      { name := "rd_addr_1",  width := archWidth, wires := rd_addr_1 },
      { name := "commit_archRd",   width := archWidth, wires := commit_archRd_0 },
      { name := "commit_physRd",   width := tagWidth,  wires := commit_physRd_0 },
      { name := "commit_archRd_1", width := archWidth, wires := commit_archRd_1 },
      { name := "commit_physRd_1", width := tagWidth,  wires := commit_physRd_1 },
      { name := "cdb_tag",    width := tagWidth,  wires := cdb_tag },
      { name := "cdb_data",   width := dataWidth, wires := cdb_data },
      { name := "retire_tag", width := tagWidth,  wires := retire_tag },
      { name := "rs1_phys_out",   width := tagWidth, wires := rs1_phys_out_0 },
      { name := "rs2_phys_out",   width := tagWidth, wires := rs2_phys_out_0 },
      { name := "rs3_phys_out",   width := tagWidth, wires := rs3_phys_out_0 },
      { name := "rd_phys_out",    width := tagWidth, wires := rd_phys_out_0 },
      { name := "old_rd_phys_out",width := tagWidth, wires := old_rd_phys_0 },
      { name := "rs1_phys_out_1", width := tagWidth, wires := rs1_phys_out_1 },
      { name := "rs2_phys_out_1", width := tagWidth, wires := rs2_phys_out_1 },
      { name := "rs3_phys_out_1", width := tagWidth, wires := rs3_phys_out_1 },
      { name := "rd_phys_out_1",  width := tagWidth, wires := rd_phys_out_1 },
      { name := "old_rd_phys_out_1", width := tagWidth, wires := old_rd_phys_1 }
    ]
  }

end Shoumei.RISCV.Renaming
