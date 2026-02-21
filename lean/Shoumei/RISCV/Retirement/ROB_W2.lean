/-
ROB_W2.lean — Dual-alloc, dual-commit 16-entry ROB (N=2)

Extends ROB.lean with mkROB16_W2 and mkROBFromConfig.
Import this file everywhere you need the W2 variant.

Port additions vs. mkROB16:
- Alloc: adds alloc_en_1, alloc_physRd_1[5:0], alloc_hasPhysRd_1,
          alloc_oldPhysRd_1[5:0], alloc_hasOldPhysRd_1, alloc_archRd_1[4:0],
          alloc_isBranch_1, alloc_idx_1[3:0]
- Commit: adds commit_en_1, head_valid_1, head_complete_1,
           head_physRd_1[5:0], head_hasPhysRd_1, head_oldPhysRd_1[5:0],
           head_hasOldPhysRd_1, head_archRd_1[4:0], head_exception_1,
           head_isBranch_1, head_mispredicted_1

Commit rule: commit_en_1 is only honoured when commit_en_0 also fires
(slot 1 only retires if slot 0 does -- enforces in-order retirement).
-/

import Shoumei.RISCV.Retirement.ROB

namespace Shoumei.RISCV.Retirement

open Shoumei
open Shoumei.Circuits.Combinational
open Shoumei.Circuits.Sequential

def mkROB16_W2 : Circuit :=
  let mkWires := @makeIndexedWires
  -- === Global Signals ===
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero  := Wire.mk "zero"
  let one   := Wire.mk "one"

  -- === Alloc Slot 0 ===
  let alloc_en_0        := Wire.mk "alloc_en_0"
  let alloc_physRd_0    := mkWires "alloc_physRd_0" 6
  let alloc_hasPhysRd_0 := Wire.mk "alloc_hasPhysRd_0"
  let alloc_oldPhysRd_0 := mkWires "alloc_oldPhysRd_0" 6
  let alloc_hasOldPR_0  := Wire.mk "alloc_hasOldPhysRd_0"
  let alloc_archRd_0    := mkWires "alloc_archRd_0" 5
  let alloc_isBranch_0  := Wire.mk "alloc_isBranch_0"
  let alloc_idx_0       := mkWires "alloc_idx_0" 4

  -- === Alloc Slot 1 ===
  let alloc_en_1        := Wire.mk "alloc_en_1"
  let alloc_physRd_1    := mkWires "alloc_physRd_1" 6
  let alloc_hasPhysRd_1 := Wire.mk "alloc_hasPhysRd_1"
  let alloc_oldPhysRd_1 := mkWires "alloc_oldPhysRd_1" 6
  let alloc_hasOldPR_1  := Wire.mk "alloc_hasOldPhysRd_1"
  let alloc_archRd_1    := mkWires "alloc_archRd_1" 5
  let alloc_isBranch_1  := Wire.mk "alloc_isBranch_1"
  let alloc_idx_1       := mkWires "alloc_idx_1" 4

  -- === CDB Interface ===
  let cdb_valid     := Wire.mk "cdb_valid"
  let cdb_tag       := mkWires "cdb_tag" 6
  let cdb_exception := Wire.mk "cdb_exception"
  let cdb_mispred   := Wire.mk "cdb_mispredicted"
  let cdb_is_fp     := Wire.mk "cdb_is_fp"
  let is_fp_shadow  := (List.range 16).map (fun i => Wire.mk s!"is_fp_shadow_{i}")

  -- === Commit / Flush ===
  let commit_en_0 := Wire.mk "commit_en_0"
  let commit_en_1 := Wire.mk "commit_en_1"
  let flush_en    := Wire.mk "flush_en"

  -- === Status ===
  let full  := Wire.mk "full"
  let empty := Wire.mk "empty"

  -- === Internal Pointers ===
  let head_ptr  := mkWires "head_ptr" 4
  let tail_ptr  := mkWires "tail_ptr" 4
  -- tail + 1 mod 16 (combinational carry-ripple)
  let tail1_ptr := mkWires "tail1_ptr" 4
  -- head + 1 mod 16 (combinational carry-ripple)
  let head1_ptr := mkWires "head1_ptr" 4
  let count     := mkWires "count" 5

  -- tail1 = tail + 1 mod 16 (4-bit ripple carry with initial cin=1)
  let t1_c := (List.range 5).map (fun i => Wire.mk s!"t1c_{i}")
  let t1_s := (List.range 4).map (fun i => Wire.mk s!"t1s_{i}")
  let tail1_gates :=
    [Gate.mkBUF one t1_c[0]!] ++
    (List.range 4).map (fun i => Gate.mkXOR tail_ptr[i]! t1_c[i]! t1_s[i]!) ++
    (List.range 4).map (fun i => Gate.mkAND tail_ptr[i]! t1_c[i]! t1_c[i+1]!) ++
    (List.range 4).map (fun i => Gate.mkBUF t1_s[i]! tail1_ptr[i]!)

  -- head1 = head + 1 mod 16
  let h1_c := (List.range 5).map (fun i => Wire.mk s!"h1c_{i}")
  let h1_s := (List.range 4).map (fun i => Wire.mk s!"h1s_{i}")
  let head1_gates :=
    [Gate.mkBUF one h1_c[0]!] ++
    (List.range 4).map (fun i => Gate.mkXOR head_ptr[i]! h1_c[i]! h1_s[i]!) ++
    (List.range 4).map (fun i => Gate.mkAND head_ptr[i]! h1_c[i]! h1_c[i+1]!) ++
    (List.range 4).map (fun i => Gate.mkBUF h1_s[i]! head1_ptr[i]!)

  -- count >= 2 = OR(count[4:1])
  let cge2_t1  := Wire.mk "cge2_t1"
  let cge2_t2  := Wire.mk "cge2_t2"
  let count_ge2 := Wire.mk "count_ge2"
  let count_ge2_gates := [
    Gate.mkOR count[1]! count[2]! cge2_t1,
    Gate.mkOR count[3]! count[4]! cge2_t2,
    Gate.mkOR cge2_t1 cge2_t2 count_ge2
  ]

  -- commit_en_0_safe = commit_en_0 AND (count >= 1)
  -- commit_en_1_safe = commit_en_1 AND commit_en_0_safe AND (count >= 2)
  let not_empty_w    := Wire.mk "not_empty_w"
  let commit_en_0_safe := Wire.mk "commit_en_0_safe"
  let commit_en_1_tmp  := Wire.mk "commit_en_1_tmp"
  let commit_en_1_safe := Wire.mk "commit_en_1_safe"
  let count_safe_gates := [
    Gate.mkOR count[0]! count[1]! not_empty_w,
    Gate.mkAND commit_en_0 not_empty_w commit_en_0_safe,
    Gate.mkAND commit_en_1 commit_en_0_safe commit_en_1_tmp,
    Gate.mkAND commit_en_1_tmp count_ge2 commit_en_1_safe
  ]

  -- alloc_idx outputs: slot 0 → tail, slot 1 → tail+1
  let alloc_idx_0_gates := List.zipWith Gate.mkBUF tail_ptr  alloc_idx_0
  let alloc_idx_1_gates := List.zipWith Gate.mkBUF tail1_ptr alloc_idx_1

  -- empty / full
  let eo1 := Wire.mk "w2_eo1"; let eo2 := Wire.mk "w2_eo2"
  let eo3 := Wire.mk "w2_eo3"; let eo4 := Wire.mk "w2_eo4"
  let empty_gates := [
    Gate.mkOR count[0]! count[1]! eo1,
    Gate.mkOR eo1 count[2]! eo2,
    Gate.mkOR eo2 count[3]! eo3,
    Gate.mkOR eo3 count[4]! eo4,
    Gate.mkNOT eo4 empty,
    Gate.mkBUF count[4]! full
  ]

  -- === Alloc Decoders (Decoder4) ===
  let alloc_dec_0 := mkWires "alloc_dec_0" 16
  let alloc_dec_0_inst : CircuitInstance := {
    moduleName := "Decoder4"
    instName := "u_alloc_dec_0"
    portMap := (tail_ptr.enum.map fun ⟨i,w⟩ => (s!"in_{i}", w)) ++
               (alloc_dec_0.enum.map fun ⟨i,w⟩ => (s!"out_{i}", w))
  }
  let alloc_dec_1 := mkWires "alloc_dec_1" 16
  let alloc_dec_1_inst : CircuitInstance := {
    moduleName := "Decoder4"
    instName := "u_alloc_dec_1"
    portMap := (tail1_ptr.enum.map fun ⟨i,w⟩ => (s!"in_{i}", w)) ++
               (alloc_dec_1.enum.map fun ⟨i,w⟩ => (s!"out_{i}", w))
  }

  -- === Commit Decoders ===
  let commit_dec_0 := mkWires "commit_dec_0" 16
  let commit_dec_0_inst : CircuitInstance := {
    moduleName := "Decoder4"
    instName := "u_commit_dec_0"
    portMap := (head_ptr.enum.map fun ⟨i,w⟩ => (s!"in_{i}", w)) ++
               (commit_dec_0.enum.map fun ⟨i,w⟩ => (s!"out_{i}", w))
  }
  let commit_dec_1 := mkWires "commit_dec_1" 16
  let commit_dec_1_inst : CircuitInstance := {
    moduleName := "Decoder4"
    instName := "u_commit_dec_1"
    portMap := (head1_ptr.enum.map fun ⟨i,w⟩ => (s!"in_{i}", w)) ++
               (commit_dec_1.enum.map fun ⟨i,w⟩ => (s!"out_{i}", w))
  }

  -- === Reset buffer tree ===
  let rr := (List.range 4).map (fun i => Wire.mk s!"w2_rr_{i}")
  let rb := (List.range 16).map (fun i => Wire.mk s!"w2_rb_{i}")
  let reset_buf_gates :=
    (List.range 4).map (fun i => Gate.mkBUF reset rr[i]!) ++
    (List.range 16).map (fun i => Gate.mkBUF rr[i/4]! rb[i]!)

  -- === Per-Entry Logic (16 entries) ===
  let entryResults := (List.range 16).map fun i =>
    let e_cur  := mkWires s!"e{i}" 24
    let e_next := mkWires s!"e{i}_nx" 24

    let cur_valid    := e_cur[0]!
    let cur_complete := e_cur[1]!
    let cur_physRd   := (List.range 6).map fun j => e_cur[2+j]!
    let cur_hasPhRd  := e_cur[8]!
    let cur_oldPhRd  := (List.range 6).map fun j => e_cur[9+j]!
    let cur_hasOPR   := e_cur[15]!
    let cur_archRd   := (List.range 5).map fun j => e_cur[16+j]!
    let cur_exc      := e_cur[21]!
    let cur_isBr     := e_cur[22]!
    let cur_misp     := e_cur[23]!

    -- Alloc write-enables
    let awe0 := Wire.mk s!"e{i}_awe0"
    let awe1 := Wire.mk s!"e{i}_awe1"
    let awe  := Wire.mk s!"e{i}_awe"
    let awe_gates := [
      Gate.mkAND alloc_en_0 alloc_dec_0[i]! awe0,
      Gate.mkAND alloc_en_1 alloc_dec_1[i]! awe1,
      Gate.mkOR  awe0 awe1 awe
    ]

    -- Select alloc data: slot 1 takes priority (it's writing into slot 1's tail position,
    -- so awe1 means this entry is being written by slot 1; awe0 by slot 0)
    let sel (pfx : String) (w0 w1 : Wire) : Gate × Wire :=
      let out := Wire.mk s!"e{i}_s{pfx}"
      (Gate.mkMUX w0 w1 awe1 out, out)

    let sel6 (pfx : String) (ws0 ws1 : List Wire) : List Gate × List Wire :=
      let pairs := (List.range 6).map fun j =>
        let out := Wire.mk s!"e{i}_s{pfx}{j}"
        (Gate.mkMUX ws0[j]! ws1[j]! awe1 out, out)
      (pairs.map Prod.fst, pairs.map Prod.snd)

    let sel5 (pfx : String) (ws0 ws1 : List Wire) : List Gate × List Wire :=
      let pairs := (List.range 5).map fun j =>
        let out := Wire.mk s!"e{i}_s{pfx}{j}"
        (Gate.mkMUX ws0[j]! ws1[j]! awe1 out, out)
      (pairs.map Prod.fst, pairs.map Prod.snd)

    let (g_physRd, sel_physRd)    := sel6 "pr"  alloc_physRd_0  alloc_physRd_1
    let (g_hasPhRd, sel_hasPhRd)  := sel "hpr"  alloc_hasPhysRd_0 alloc_hasPhysRd_1
    let (g_oldPhRd, sel_oldPhRd)  := sel6 "opr" alloc_oldPhysRd_0 alloc_oldPhysRd_1
    let (g_hasOPR, sel_hasOPR)    := sel "hopr" alloc_hasOldPR_0 alloc_hasOldPR_1
    let (g_archRd, sel_archRd)    := sel5 "ar"  alloc_archRd_0  alloc_archRd_1
    let (g_isBr, sel_isBr)        := sel "ibr"  alloc_isBranch_0 alloc_isBranch_1

    let sel_gates := g_physRd ++ [g_hasPhRd] ++ g_oldPhRd ++ [g_hasOPR] ++ g_archRd ++ [g_isBr]
    let sel_hasPhRd_w := sel_hasPhRd.2
    let sel_isBr_w    := sel_isBr.2

    -- CDB match (Comparator6 instance)
    let cdb_match  := Wire.mk s!"e{i}_cm"
    let cn         := Wire.mk s!"e{i}_cn"
    let ct1 := Wire.mk s!"e{i}_ct1"; let ct2 := Wire.mk s!"e{i}_ct2"
    let ct3 := Wire.mk s!"e{i}_ct3"; let ct4 := Wire.mk s!"e{i}_ct4"
    let hpob := Wire.mk s!"e{i}_hpob"
    let dxor := Wire.mk s!"e{i}_dxor"; let dm := Wire.mk s!"e{i}_dm"
    let cwe  := Wire.mk s!"e{i}_cwe"
    let cdb_we_gates := [
      Gate.mkNOT cur_complete cn,
      Gate.mkAND cur_valid cn ct1,
      Gate.mkOR  cur_hasPhRd cur_isBr hpob,
      Gate.mkAND ct1 hpob ct2,
      Gate.mkAND ct2 cdb_match ct3,
      Gate.mkAND ct3 cdb_valid ct4,
      Gate.mkXOR cdb_is_fp is_fp_shadow[i]! dxor,
      Gate.mkNOT dxor dm,
      Gate.mkAND ct4 dm cwe
    ]
    let cmp_inst : CircuitInstance := {
      moduleName := "Comparator6"; instName := s!"u_cmp{i}"
      portMap :=
        (cdb_tag.enum.map fun ⟨j,w⟩ => (s!"a_{j}", w)) ++
        (cur_physRd.enum.map fun ⟨j,w⟩ => (s!"b_{j}", w)) ++
        [("one", one), ("eq", cdb_match),
         ("lt",  Wire.mk s!"e{i}_clt"),  ("ltu", Wire.mk s!"e{i}_cltu"),
         ("gt",  Wire.mk s!"e{i}_cgt"),  ("gtu", Wire.mk s!"e{i}_cgtu")]
    }

    -- Commit clear
    let cc0 := Wire.mk s!"e{i}_cc0"; let cc1 := Wire.mk s!"e{i}_cc1"
    let commit_clear := Wire.mk s!"e{i}_cc"
    let cc_gates := [
      Gate.mkAND commit_en_0_safe commit_dec_0[i]! cc0,
      Gate.mkAND commit_en_1_safe commit_dec_1[i]! cc1,
      Gate.mkOR  cc0 cc1 commit_clear
    ]
    let clear := Wire.mk s!"e{i}_cl"
    let clear_gate := Gate.mkOR flush_en commit_clear clear

    -- alloc_needs_cdb = sel_hasPhRd OR sel_isBr
    let anc  := Wire.mk s!"e{i}_anc"
    let aic  := Wire.mk s!"e{i}_aic"

    -- Next-state MUX chain
    let vm1 := Wire.mk s!"e{i}_vm1"
    let valid_gates := [
      Gate.mkMUX cur_valid zero clear vm1,
      Gate.mkMUX vm1 one awe e_next[0]!
    ]
    let cpm1 := Wire.mk s!"e{i}_cpm1"; let cpm2 := Wire.mk s!"e{i}_cpm2"
    let comp_gates := [
      Gate.mkOR  sel_hasPhRd_w sel_isBr_w anc,
      Gate.mkNOT anc aic,
      Gate.mkMUX cur_complete one cwe cpm1,
      Gate.mkMUX cpm1 zero clear cpm2,
      Gate.mkMUX cpm2 aic awe e_next[1]!
    ]
    let physRd_gates := (List.range 6).map fun j =>
      Gate.mkMUX cur_physRd[j]! sel_physRd[j]! awe e_next[2+j]!
    let hasPR_gate   := Gate.mkMUX cur_hasPhRd sel_hasPhRd_w awe e_next[8]!
    let oldPR_gates  := (List.range 6).map fun j =>
      Gate.mkMUX cur_oldPhRd[j]! sel_oldPhRd[j]! awe e_next[9+j]!
    let hasOPR_gate  := Gate.mkMUX cur_hasOPR sel_hasOPR.2 awe e_next[15]!
    let archRd_gates := (List.range 5).map fun j =>
      Gate.mkMUX cur_archRd[j]! sel_archRd[j]! awe e_next[16+j]!
    let em1 := Wire.mk s!"e{i}_em1"; let em2 := Wire.mk s!"e{i}_em2"
    let exc_gates := [
      Gate.mkMUX cur_exc cdb_exception cwe em1,
      Gate.mkMUX em1 zero clear em2,
      Gate.mkMUX em2 zero awe e_next[21]!
    ]
    let isBr_gate := Gate.mkMUX cur_isBr sel_isBr_w awe e_next[22]!
    let mm1 := Wire.mk s!"e{i}_mm1"; let mm2 := Wire.mk s!"e{i}_mm2"
    let misp_gates := [
      Gate.mkMUX cur_misp cdb_mispred cwe mm1,
      Gate.mkMUX mm1 zero clear mm2,
      Gate.mkMUX mm2 zero awe e_next[23]!
    ]

    let reg_inst : CircuitInstance := {
      moduleName := "Register24"; instName := s!"u_entry{i}"
      portMap :=
        (e_next.enum.map fun ⟨j,w⟩ => (s!"d_{j}", w)) ++
        [("clock", clock), ("reset", rb[i]!)] ++
        (e_cur.enum.map fun ⟨j,w⟩ => (s!"q_{j}", w))
    }

    let entry_gates :=
      awe_gates ++ sel_gates ++ cdb_we_gates ++ cc_gates ++
      [clear_gate] ++ valid_gates ++ comp_gates ++
      physRd_gates ++ [hasPR_gate] ++ oldPR_gates ++ [hasOPR_gate] ++
      archRd_gates ++ exc_gates ++ [isBr_gate] ++ misp_gates

    (entry_gates, [cmp_inst, reg_inst], e_cur)

  let all_entry_gates     := (entryResults.map (fun (g,_,_) => g)).flatten
  let all_entry_instances := (entryResults.map (fun (_,i,_) => i)).flatten
  let all_entry_cur       :=  entryResults.map (fun (_,_,c) => c)

  -- OR-tree readout helper for single-bit fields
  let mkBitReadout (pfx name : String) (dec : List Wire) (bitIdx : Nat) (out : Wire)
      : List Gate :=
    let ands := (List.range 16).map fun i =>
      let e := all_entry_cur[i]!
      let w := Wire.mk s!"{pfx}_{name}_a{i}"
      (Gate.mkAND dec[i]! e[bitIdx]! w, w)
    let l2 := (List.range 8).map fun i =>
      let w := Wire.mk s!"{pfx}_{name}_l2_{i}"
      (Gate.mkOR (ands.map Prod.snd)[2*i]! (ands.map Prod.snd)[2*i+1]! w, w)
    let l3 := (List.range 4).map fun i =>
      let w := Wire.mk s!"{pfx}_{name}_l3_{i}"
      (Gate.mkOR (l2.map Prod.snd)[2*i]! (l2.map Prod.snd)[2*i+1]! w, w)
    let l4 := (List.range 2).map fun i =>
      let w := Wire.mk s!"{pfx}_{name}_l4_{i}"
      (Gate.mkOR (l3.map Prod.snd)[2*i]! (l3.map Prod.snd)[2*i+1]! w, w)
    ands.map Prod.fst ++ l2.map Prod.fst ++ l3.map Prod.fst ++ l4.map Prod.fst ++
    [Gate.mkOR (l4.map Prod.snd)[0]! (l4.map Prod.snd)[1]! out]

  -- Mux readout helper
  let mkMuxReadout (instName modName : String) (bitStart bitCount : Nat)
      (sel_ptr : List Wire) (outs : List Wire) : CircuitInstance := {
    moduleName := modName; instName := instName
    portMap :=
      ((List.range 16).map fun i =>
        let e := all_entry_cur[i]!
        (List.range bitCount).map fun j => (s!"in{i}[{j}]", e[bitStart+j]!)
      ).flatten ++
      (sel_ptr.enum.map fun ⟨k,w⟩ => (s!"sel[{k}]", w)) ++
      (outs.enum.map fun ⟨j,w⟩ => (s!"out[{j}]", w))
  }

  -- === Commit Slot 0 Outputs ===
  let hv0 := Wire.mk "head_valid_0";    let hcmp0 := Wire.mk "head_complete_0"
  let hpr0 := mkWires "head_physRd_0" 6
  let hhpr0 := Wire.mk "head_hasPhysRd_0"
  let hopr0 := mkWires "head_oldPhysRd_0" 6
  let hhopr0 := Wire.mk "head_hasOldPhysRd_0"
  let har0  := mkWires "head_archRd_0" 5
  let hexc0 := Wire.mk "head_exception_0"
  let hibr0 := Wire.mk "head_isBranch_0"
  let hmisp0 := Wire.mk "head_mispredicted_0"

  -- === Commit Slot 1 Outputs ===
  let hv1 := Wire.mk "head_valid_1";    let hcmp1 := Wire.mk "head_complete_1"
  let hpr1 := mkWires "head_physRd_1" 6
  let hhpr1 := Wire.mk "head_hasPhysRd_1"
  let hopr1 := mkWires "head_oldPhysRd_1" 6
  let hhopr1 := Wire.mk "head_hasOldPhysRd_1"
  let har1  := mkWires "head_archRd_1" 5
  let hexc1 := Wire.mk "head_exception_1"
  let hibr1 := Wire.mk "head_isBranch_1"
  let hmisp1 := Wire.mk "head_mispredicted_1"

  let pr_mux_0  := mkMuxReadout "u_mux_pr_0"  "Mux16x6" 2  6 head_ptr  hpr0
  let opr_mux_0 := mkMuxReadout "u_mux_opr_0" "Mux16x6" 9  6 head_ptr  hopr0
  let ar_mux_0  := mkMuxReadout "u_mux_ar_0"  "Mux16x5" 16 5 head_ptr  har0
  let pr_mux_1  := mkMuxReadout "u_mux_pr_1"  "Mux16x6" 2  6 head1_ptr hpr1
  let opr_mux_1 := mkMuxReadout "u_mux_opr_1" "Mux16x6" 9  6 head1_ptr hopr1
  let ar_mux_1  := mkMuxReadout "u_mux_ar_1"  "Mux16x5" 16 5 head1_ptr har1

  let ro0 :=
    mkBitReadout "s0" "valid"    commit_dec_0 0  hv0   ++
    mkBitReadout "s0" "complete" commit_dec_0 1  hcmp0 ++
    mkBitReadout "s0" "hasPhRd"  commit_dec_0 8  hhpr0 ++
    mkBitReadout "s0" "hasOPR"   commit_dec_0 15 hhopr0 ++
    mkBitReadout "s0" "exc"      commit_dec_0 21 hexc0 ++
    mkBitReadout "s0" "isBr"     commit_dec_0 22 hibr0 ++
    mkBitReadout "s0" "misp"     commit_dec_0 23 hmisp0
  let ro1 :=
    mkBitReadout "s1" "valid"    commit_dec_1 0  hv1   ++
    mkBitReadout "s1" "complete" commit_dec_1 1  hcmp1 ++
    mkBitReadout "s1" "hasPhRd"  commit_dec_1 8  hhpr1 ++
    mkBitReadout "s1" "hasOPR"   commit_dec_1 15 hhopr1 ++
    mkBitReadout "s1" "exc"      commit_dec_1 21 hexc1 ++
    mkBitReadout "s1" "isBr"     commit_dec_1 22 hibr1 ++
    mkBitReadout "s1" "misp"     commit_dec_1 23 hmisp1

  -- === Head/Tail Pointer + Counter Instances ===
  let head_idx_0 := mkWires "head_idx_0" 4
  let head_idx_1 := mkWires "head_idx_1" 4
  let head_idx_gates :=
    List.zipWith Gate.mkBUF head_ptr  head_idx_0 ++
    List.zipWith Gate.mkBUF head1_ptr head_idx_1

  let head_inst : CircuitInstance := {
    moduleName := "QueuePointer_4"
    instName := "u_head"
    portMap := [("clock", clock), ("reset", reset), ("en", commit_en_0_safe),
                ("one", one), ("zero", zero)] ++
               (head_ptr.enum.map fun ⟨i,w⟩ => (s!"count_{i}", w))
  }
  let tail_inst_0 : CircuitInstance := {
    moduleName := "QueuePointer_4"
    instName := "u_tail_s0"
    portMap := [("clock", clock), ("reset", reset), ("en", alloc_en_0),
                ("one", one), ("zero", zero)] ++
               (mkWires "tail_mid" 4).enum.map fun ⟨i,w⟩ => (s!"count_{i}", w)
  }
  let tail_inst_1 : CircuitInstance := {
    moduleName := "QueuePointer_4"
    instName := "u_tail_s1"
    portMap := [("clock", clock), ("reset", reset), ("en", alloc_en_1),
                ("one", one), ("zero", zero)] ++
               (tail_ptr.enum.map fun ⟨i,w⟩ => (s!"count_{i}", w))
  }
  -- head slot-1 pointer: separate QueuePointer advancing on commit_en_1_safe
  -- (not used as a register; we combine head+1 combinationally via head1_ptr)
  let count_inst_0 : CircuitInstance := {
    moduleName := "QueueCounterUpDown_5"
    instName := "u_count_s0"
    portMap := [("clock", clock), ("reset", reset),
                ("inc", alloc_en_0), ("dec", commit_en_0_safe),
                ("one", one), ("zero", zero)] ++
               (mkWires "count_mid" 5).enum.map fun ⟨i,w⟩ => (s!"count_{i}", w)
  }
  let count_inst_1 : CircuitInstance := {
    moduleName := "QueueCounterUpDown_5"
    instName := "u_count_s1"
    portMap := [("clock", clock), ("reset", reset),
                ("inc", alloc_en_1), ("dec", commit_en_1_safe),
                ("one", one), ("zero", zero)] ++
               (count.enum.map fun ⟨i,w⟩ => (s!"count_{i}", w))
  }

  -- === Assemble ===
  let all_inputs :=
    [clock, reset, zero, one,
     alloc_en_0] ++ alloc_physRd_0 ++ [alloc_hasPhysRd_0] ++
    alloc_oldPhysRd_0 ++ [alloc_hasOldPR_0] ++ alloc_archRd_0 ++ [alloc_isBranch_0] ++
    [alloc_en_1] ++ alloc_physRd_1 ++ [alloc_hasPhysRd_1] ++
    alloc_oldPhysRd_1 ++ [alloc_hasOldPR_1] ++ alloc_archRd_1 ++ [alloc_isBranch_1] ++
    [cdb_valid] ++ cdb_tag ++ [cdb_exception, cdb_mispred, cdb_is_fp] ++
    is_fp_shadow ++ [commit_en_0, commit_en_1, flush_en]

  let all_outputs :=
    [full, empty] ++ alloc_idx_0 ++ alloc_idx_1 ++
    head_idx_0 ++ head_idx_1 ++
    [hv0, hcmp0] ++ hpr0 ++ [hhpr0] ++ hopr0 ++ [hhopr0] ++ har0 ++ [hexc0, hibr0, hmisp0] ++
    [hv1, hcmp1] ++ hpr1 ++ [hhpr1] ++ hopr1 ++ [hhopr1] ++ har1 ++ [hexc1, hibr1, hmisp1]

  let all_gates :=
    tail1_gates ++ head1_gates ++ count_ge2_gates ++ count_safe_gates ++
    alloc_idx_0_gates ++ alloc_idx_1_gates ++ empty_gates ++ reset_buf_gates ++
    all_entry_gates ++ ro0 ++ ro1 ++ head_idx_gates

  let all_instances :=
    [head_inst, tail_inst_0, tail_inst_1, count_inst_0, count_inst_1,
     alloc_dec_0_inst, alloc_dec_1_inst, commit_dec_0_inst, commit_dec_1_inst] ++
    all_entry_instances ++
    [pr_mux_0, opr_mux_0, ar_mux_0, pr_mux_1, opr_mux_1, ar_mux_1]

  { name := "ROB16_W2"
    inputs := all_inputs; outputs := all_outputs
    gates := all_gates; instances := all_instances
    signalGroups := [
      { name := "alloc_physRd_0",    width := 6, wires := alloc_physRd_0 },
      { name := "alloc_oldPhysRd_0", width := 6, wires := alloc_oldPhysRd_0 },
      { name := "alloc_archRd_0",    width := 5, wires := alloc_archRd_0 },
      { name := "alloc_physRd_1",    width := 6, wires := alloc_physRd_1 },
      { name := "alloc_oldPhysRd_1", width := 6, wires := alloc_oldPhysRd_1 },
      { name := "alloc_archRd_1",    width := 5, wires := alloc_archRd_1 },
      { name := "cdb_tag",           width := 6, wires := cdb_tag },
      { name := "alloc_idx_0",       width := 4, wires := alloc_idx_0 },
      { name := "alloc_idx_1",       width := 4, wires := alloc_idx_1 },
      { name := "head_idx_0",        width := 4, wires := head_idx_0 },
      { name := "head_idx_1",        width := 4, wires := head_idx_1 },
      { name := "head_physRd_0",     width := 6, wires := hpr0 },
      { name := "head_oldPhysRd_0",  width := 6, wires := hopr0 },
      { name := "head_archRd_0",     width := 5, wires := har0 },
      { name := "head_physRd_1",     width := 6, wires := hpr1 },
      { name := "head_oldPhysRd_1",  width := 6, wires := hopr1 },
      { name := "head_archRd_1",     width := 5, wires := har1 }
    ]
  }

/-- Config-driven ROB: W2 when commitWidth >= 2, else W1 -/
def mkROBFromConfig (config : Shoumei.RISCV.CPUConfig) : Circuit :=
  if config.commitWidth >= 2 then mkROB16_W2 else mkROB16

end Shoumei.RISCV.Retirement
