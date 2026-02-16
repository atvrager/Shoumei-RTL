/-
CPU Helper Functions - CSR, Load Forwarding, Memory Pipeline, Serialize

Extracted from CPU.lean to reduce file size. These 8 helpers have matching
specs in CPUHelperSpecs.lean and proofs in CPUHelperProofs.lean.
-/

import Shoumei.DSL
import Shoumei.RISCV.Config

namespace Shoumei.RISCV.CPU

open Shoumei

/-- Helper: Create indexed wires -/
def makeIndexedWiresH (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}_{i}")

/-- CSR address decode: compare csr_addr_reg[11:0] against known CSR addresses.
    Returns (gates, is_mscratch, is_mcycle_m, is_mcycleh_m, is_minstret_m, is_minstreth_m,
    is_misa, is_fflags, is_frm, is_fcsr, is_mstatus, is_mie, is_mtvec, is_mepc, is_mcause,
    is_mtval, is_mip, is_mcycle, is_mcycleh, is_minstret, is_minstreth). -/
def mkCsrAddrDecode
    (csr_addr_reg : List Wire)
    : List Gate × Wire × Wire × Wire × Wire × Wire × Wire × Wire × Wire × Wire × Wire × Wire × Wire × Wire × Wire × Wire × Wire × Wire × Wire × Wire × Wire :=
  -- Helper: generate 12-bit match using NOT + AND tree
  let mkCsrAddrMatch (expected : Nat) (pfx : String) : Wire × List Gate :=
    let matchW := Wire.mk s!"csr_is_{pfx}"
    let bitWires := (List.range 12).map fun b =>
      if Nat.testBit expected b then csr_addr_reg[b]! else Wire.mk s!"csr_{pfx}_n{b}"
    let notGates := (List.range 12).filterMap fun b =>
      if !Nat.testBit expected b then
        some (Gate.mkNOT csr_addr_reg[b]! (Wire.mk s!"csr_{pfx}_n{b}"))
      else none
    -- 12-bit AND tree: 6 pairs → 3 → 2 → 1
    let p := (List.range 6).map (fun i => Wire.mk s!"csr_{pfx}_p{i}")
    let q := (List.range 3).map (fun i => Wire.mk s!"csr_{pfx}_q{i}")
    let r := Wire.mk s!"csr_{pfx}_r0"
    let andTree :=
      (List.range 6).map (fun i => Gate.mkAND bitWires[2*i]! bitWires[2*i+1]! p[i]!) ++
      (List.range 3).map (fun i => Gate.mkAND p[2*i]! p[2*i+1]! q[i]!) ++
      [Gate.mkAND q[0]! q[1]! r,
       Gate.mkAND r q[2]! matchW]
    (matchW, notGates ++ andTree)
  -- Address matches for writable CSRs
  let (is_mscratch, mscratch_match_gates) := mkCsrAddrMatch 0x340 "mscratch"
  let (is_mcycle_m, mcycle_m_match_gates) := mkCsrAddrMatch 0xB00 "mcycle_m"
  let (is_mcycle_u, mcycle_u_match_gates) := mkCsrAddrMatch 0xC00 "mcycle_u"
  let (is_mcycleh_m, mcycleh_m_match_gates) := mkCsrAddrMatch 0xB80 "mcycleh_m"
  let (is_mcycleh_u, mcycleh_u_match_gates) := mkCsrAddrMatch 0xC80 "mcycleh_u"
  let (is_minstret_m, minstret_m_match_gates) := mkCsrAddrMatch 0xB02 "minstret_m"
  let (is_minstret_u, minstret_u_match_gates) := mkCsrAddrMatch 0xC02 "minstret_u"
  let (is_minstreth_m, minstreth_m_match_gates) := mkCsrAddrMatch 0xB82 "minstreth_m"
  let (is_minstreth_u, minstreth_u_match_gates) := mkCsrAddrMatch 0xC82 "minstreth_u"
  let (is_misa, misa_match_gates) := mkCsrAddrMatch 0x301 "misa"
  let (_is_mhartid, mhartid_match_gates) := mkCsrAddrMatch 0xF14 "mhartid"
  let (is_fflags, fflags_match_gates) := mkCsrAddrMatch 0x001 "fflags"
  let (is_frm, frm_match_gates) := mkCsrAddrMatch 0x002 "frm"
  let (is_fcsr, fcsr_match_gates) := mkCsrAddrMatch 0x003 "fcsr"
  let (is_mstatus, mstatus_match_gates) := mkCsrAddrMatch 0x300 "mstatus"
  let (is_mie, mie_match_gates) := mkCsrAddrMatch 0x304 "mie"
  let (is_mtvec, mtvec_match_gates) := mkCsrAddrMatch 0x305 "mtvec"
  let (is_mepc, mepc_match_gates) := mkCsrAddrMatch 0x341 "mepc"
  let (is_mcause, mcause_match_gates) := mkCsrAddrMatch 0x342 "mcause"
  let (is_mtval, mtval_match_gates) := mkCsrAddrMatch 0x343 "mtval"
  let (is_mip, mip_match_gates) := mkCsrAddrMatch 0x344 "mip"
  -- Combine M-mode and U-mode aliases
  let is_mcycle := Wire.mk "csr_is_mcycle"
  let is_mcycleh := Wire.mk "csr_is_mcycleh"
  let is_minstret := Wire.mk "csr_is_minstret"
  let is_minstreth := Wire.mk "csr_is_minstreth"
  let csr_alias_gates := [
    Gate.mkOR is_mcycle_m is_mcycle_u is_mcycle,
    Gate.mkOR is_mcycleh_m is_mcycleh_u is_mcycleh,
    Gate.mkOR is_minstret_m is_minstret_u is_minstret,
    Gate.mkOR is_minstreth_m is_minstreth_u is_minstreth
  ]
  let gates :=
    mscratch_match_gates ++ mcycle_m_match_gates ++ mcycle_u_match_gates ++
    mcycleh_m_match_gates ++ mcycleh_u_match_gates ++
    minstret_m_match_gates ++ minstret_u_match_gates ++
    minstreth_m_match_gates ++ minstreth_u_match_gates ++
    misa_match_gates ++ mhartid_match_gates ++
    fflags_match_gates ++ frm_match_gates ++ fcsr_match_gates ++
    mstatus_match_gates ++ mie_match_gates ++ mtvec_match_gates ++
    mepc_match_gates ++ mcause_match_gates ++ mtval_match_gates ++
    mip_match_gates ++ csr_alias_gates
  (gates, is_mscratch, is_mcycle_m, is_mcycleh_m, is_minstret_m, is_minstreth_m,
   is_misa, is_fflags, is_frm, is_fcsr, is_mstatus, is_mie, is_mtvec, is_mepc, is_mcause,
   is_mtval, is_mip, is_mcycle, is_mcycleh, is_minstret, is_minstreth)

/-- Load forwarding logic: SB forwarding size checks, cross-size stall detection,
    and dispatch gating for branch/INT RS conflict resolution. -/
def mkLoadForwarding
    (mem_size_r : List Wire) (lsu_sb_fwd_size : List Wire)
    (lsu_sb_fwd_hit lsu_sb_fwd_committed_hit lsu_sb_fwd_word_only_hit : Wire)
    (mem_valid_r is_load_r is_load : Wire)
    (rs_mem_dispatch_valid rs_int_dispatch_valid ib_fifo_enq_ready : Wire)
    (load_fwd_valid cross_size_stall not_cross_size_stall cross_size_any cross_size_uncommitted : Wire)
    (not_int_dispatching branch_dispatch_en : Wire)
    : List Gate :=
  -- SB fwd size check: only forward when store covers the full load
  let fwd_size_ok := Wire.mk "fwd_size_ok"
  let not_load_size1 := Wire.mk "not_load_size1"
  let not_load_size0 := Wire.mk "not_load_size0"
  let fwd_sz_tmp1 := Wire.mk "fwd_sz_tmp1"
  let fwd_sz_tmp2 := Wire.mk "fwd_sz_tmp2"
  let fwd_size_check_gates := [
    Gate.mkNOT mem_size_r[1]! not_load_size1,
    Gate.mkNOT mem_size_r[0]! not_load_size0,
    Gate.mkOR lsu_sb_fwd_size[0]! not_load_size0 fwd_sz_tmp1,
    Gate.mkAND not_load_size1 fwd_sz_tmp1 fwd_sz_tmp2,
    Gate.mkOR lsu_sb_fwd_size[1]! fwd_sz_tmp2 fwd_size_ok
  ]
  let load_fwd_tmp := Wire.mk "load_fwd_tmp"
  let load_fwd_tmp2 := Wire.mk "load_fwd_tmp2"
  let not_fwd_size_ok := Wire.mk "not_fwd_size_ok"
  let not_fwd_committed_hit := Wire.mk "not_fwd_committed_hit"
  let load_fwd_gates := [
    Gate.mkAND lsu_sb_fwd_hit mem_valid_r load_fwd_tmp,
    Gate.mkAND load_fwd_tmp is_load_r load_fwd_tmp2,
    Gate.mkAND load_fwd_tmp2 fwd_size_ok (Wire.mk "load_fwd_pre_overlap"),
    -- Block SB fwd when there's a partial word overlap (forwarded data incomplete)
    Gate.mkNOT lsu_sb_fwd_word_only_hit (Wire.mk "not_word_only_hit"),
    Gate.mkAND (Wire.mk "load_fwd_pre_overlap") (Wire.mk "not_word_only_hit") load_fwd_valid,
    -- Cross-size detection: SB hit but size insufficient
    Gate.mkNOT fwd_size_ok not_fwd_size_ok,
    Gate.mkAND load_fwd_tmp2 not_fwd_size_ok cross_size_any,
    -- Word overlap: SB has entry at same word but different byte offset.
    Gate.mkAND lsu_sb_fwd_word_only_hit rs_mem_dispatch_valid (Wire.mk "wovlp_tmp1"),
    Gate.mkAND (Wire.mk "wovlp_tmp1") is_load (Wire.mk "word_overlap_stall"),
    -- cross_size_stall includes both exact cross-size AND word overlap
    Gate.mkOR cross_size_any (Wire.mk "word_overlap_stall") cross_size_stall,
    Gate.mkNOT cross_size_stall not_cross_size_stall,
    -- Branch RS dispatch is suppressed when INT RS also dispatches (shared IB FIFO slot)
    Gate.mkNOT rs_int_dispatch_valid not_int_dispatching,
    Gate.mkAND not_cross_size_stall not_int_dispatching (Wire.mk "branch_dispatch_en_tmp"),
    Gate.mkAND (Wire.mk "branch_dispatch_en_tmp") ib_fifo_enq_ready branch_dispatch_en,
    -- cross_size_uncommitted: SB hit, size mismatch, but not committed
    Gate.mkNOT lsu_sb_fwd_committed_hit not_fwd_committed_hit,
    Gate.mkAND cross_size_any not_fwd_committed_hit cross_size_uncommitted
  ]
  fwd_size_check_gates ++ load_fwd_gates

/-- Memory address pipeline register: breaks the critical path between
    RS issue → address calc → SB compare → CDB with a DFF stage.
    Returns (gates, instances) for all pipeline register fields. -/
def mkMemPipeline
    (clock reset : Wire)
    (rs_mem_dispatch_valid mem_dispatch_en : Wire)
    (mem_address : List Wire) (rs_mem_dispatch_tag : List Wire)
    (is_load is_flw : Wire) (mem_size : List Wire) (sign_extend : Wire)
    (mem_addr_r : List Wire) (mem_tag_r : List Wire)
    (is_load_r : Wire) (mem_size_r : List Wire) (sign_extend_r is_flw_r mem_valid_r : Wire)
    : List Gate × List CircuitInstance :=
  -- pipe_load_en = rs_mem_dispatch_valid & mem_dispatch_en & !pipeline_flush_comb
  let pipe_load_en := Wire.mk "pipe_load_en"
  let pipe_load_en_tmp := Wire.mk "pipe_load_en_tmp"
  let pipe_load_en_gates := [
    Gate.mkAND rs_mem_dispatch_valid mem_dispatch_en pipe_load_en_tmp,
    Gate.mkAND pipe_load_en_tmp (Wire.mk "not_flush_comb") pipe_load_en
  ]
  -- Pipeline register: MUX(hold_value, new_value, enable) → DFF
  let mem_addr_next := makeIndexedWiresH "mem_addr_next" 32
  let mem_addr_pipe_gates := (List.range 32).map (fun i =>
    Gate.mkMUX mem_addr_r[i]! mem_address[i]! pipe_load_en mem_addr_next[i]!)
  let mem_addr_pipe_insts := (List.range 32).map (fun i =>
    ({ moduleName := "DFlipFlop", instName := s!"u_mem_addr_r_{i}",
       portMap := [("d", mem_addr_next[i]!), ("q", mem_addr_r[i]!),
                   ("clock", clock), ("reset", reset)] } : CircuitInstance))
  let mem_tag_next := makeIndexedWiresH "mem_tag_next" 6
  let mem_tag_pipe_gates := (List.range 6).map (fun i =>
    Gate.mkMUX mem_tag_r[i]! rs_mem_dispatch_tag[i]! pipe_load_en mem_tag_next[i]!)
  let mem_tag_pipe_insts := (List.range 6).map (fun i =>
    ({ moduleName := "DFlipFlop", instName := s!"u_mem_tag_r_{i}",
       portMap := [("d", mem_tag_next[i]!), ("q", mem_tag_r[i]!),
                   ("clock", clock), ("reset", reset)] } : CircuitInstance))
  let is_load_next := Wire.mk "is_load_next"
  let is_load_pipe_gates := [Gate.mkMUX is_load_r is_load pipe_load_en is_load_next]
  let is_load_pipe_inst : CircuitInstance :=
    { moduleName := "DFlipFlop", instName := "u_is_load_r",
      portMap := [("d", is_load_next), ("q", is_load_r),
                  ("clock", clock), ("reset", reset)] }
  let mem_size_next := makeIndexedWiresH "mem_size_next" 2
  let mem_size_pipe_gates := (List.range 2).map (fun i =>
    Gate.mkMUX mem_size_r[i]! mem_size[i]! pipe_load_en mem_size_next[i]!)
  let mem_size_pipe_insts := (List.range 2).map (fun i =>
    ({ moduleName := "DFlipFlop", instName := s!"u_mem_size_r_{i}",
       portMap := [("d", mem_size_next[i]!), ("q", mem_size_r[i]!),
                   ("clock", clock), ("reset", reset)] } : CircuitInstance))
  let sign_extend_next := Wire.mk "sign_extend_next"
  let sign_extend_pipe_gates := [Gate.mkMUX sign_extend_r sign_extend pipe_load_en sign_extend_next]
  let sign_extend_pipe_inst : CircuitInstance :=
    { moduleName := "DFlipFlop", instName := "u_sign_extend_r",
      portMap := [("d", sign_extend_next), ("q", sign_extend_r),
                  ("clock", clock), ("reset", reset)] }
  let is_flw_next := Wire.mk "is_flw_next"
  let is_flw_pipe_gates := [Gate.mkMUX is_flw_r is_flw pipe_load_en is_flw_next]
  let is_flw_pipe_inst : CircuitInstance :=
    { moduleName := "DFlipFlop", instName := "u_is_flw_r",
      portMap := [("d", is_flw_next), ("q", is_flw_r),
                  ("clock", clock), ("reset", reset)] }
  -- Pipeline valid: set on new dispatch, hold if load can't complete yet
  let mem_valid_next := Wire.mk "mem_valid_next"
  let mem_valid_pre := Wire.mk "mem_valid_pre"
  let pipe_valid_hold := Wire.mk "pipe_valid_hold"
  let pipe_valid_hold_tmp1 := Wire.mk "pipe_valid_hold_tmp1"
  let pipe_valid_hold_tmp2 := Wire.mk "pipe_valid_hold_tmp2"
  let not_load_fwd_valid := Wire.mk "not_load_fwd_valid"
  let not_load_no_fwd := Wire.mk "not_load_no_fwd"
  let mem_valid_pipe_gates := [
    Gate.mkAND mem_valid_r is_load_r pipe_valid_hold_tmp1,
    Gate.mkNOT (Wire.mk "load_fwd_valid") not_load_fwd_valid,
    Gate.mkNOT (Wire.mk "load_no_fwd") not_load_no_fwd,
    Gate.mkAND pipe_valid_hold_tmp1 not_load_fwd_valid pipe_valid_hold_tmp2,
    Gate.mkAND pipe_valid_hold_tmp2 not_load_no_fwd pipe_valid_hold,
    Gate.mkOR pipe_load_en pipe_valid_hold mem_valid_pre,
    Gate.mkAND mem_valid_pre (Wire.mk "not_flush_comb") mem_valid_next
  ]
  let mem_valid_pipe_inst : CircuitInstance :=
    { moduleName := "DFlipFlop", instName := "u_mem_valid_r",
      portMap := [("d", mem_valid_next), ("q", mem_valid_r),
                  ("clock", clock), ("reset", reset)] }
  -- Collect all pipeline register gates and instances
  let gates := pipe_load_en_gates ++
    mem_addr_pipe_gates ++ mem_tag_pipe_gates ++
    is_load_pipe_gates ++ mem_size_pipe_gates ++
    sign_extend_pipe_gates ++ is_flw_pipe_gates ++
    mem_valid_pipe_gates
  let insts := mem_addr_pipe_insts ++ mem_tag_pipe_insts ++
    [is_load_pipe_inst] ++ mem_size_pipe_insts ++
    [sign_extend_pipe_inst, is_flw_pipe_inst, mem_valid_pipe_inst]
  (gates, insts)

/-- Serialize detection and FSM gates for FENCE.I + CSR instructions.
    Generates opcode matching, detection flags, FSM state transitions,
    and register capture MUXes for the serialize pipeline. -/
def mkSerializeDetect
    (config : CPUConfig) (oi : OpType → Nat) (opcodeWidth : Nat)
    (zero one : Wire)
    (decode_optype : List Wire) (decode_valid : Wire) (decode_imm decode_rd decode_rs1 : List Wire)
    (branch_redirect_valid_reg : Wire)
    (fence_i_draining fence_i_not_draining : Wire)
    (rob_empty lsu_sb_empty : Wire)
    (pipeline_flush_comb : Wire)
    (fence_i_redir_target fence_i_pc_plus_4 : List Wire)
    (csr_flag_reg : Wire) (csr_addr_reg : List Wire) (csr_optype_reg : List Wire)
    (csr_rd_reg : List Wire) (csr_phys_reg : List Wire) (csr_rs1cap_reg : List Wire)
    (csr_zimm_reg : List Wire)
    (rd_phys : List Wire)
    (csr_match : Wire)
    (fence_i_detected csr_detected serialize_detected : Wire)
    (fence_i_start fence_i_drain_complete fence_i_draining_next fence_i_suppress : Wire)
    (csr_rename_en not_csr_rename_en : Wire)
    (csr_flag_next : Wire) (csr_addr_next csr_optype_next csr_rd_next csr_phys_next csr_rs1cap_next csr_zimm_next : List Wire)
    (fence_i_redir_next : List Wire)
    : List Gate :=
  -- Helper: generate gates to match decode_optype against an encoding value
  let mkOpcodeMatch (encVal : Nat) (pfx : String) (matchOut : Wire) : List Gate :=
    let bitWires := (List.range opcodeWidth).map fun b =>
      if Nat.testBit encVal b then decode_optype[b]! else Wire.mk s!"{pfx}_n{b}"
    let notGates := (List.range opcodeWidth).filterMap fun b =>
      if !Nat.testBit encVal b then some (Gate.mkNOT decode_optype[b]! (Wire.mk s!"{pfx}_n{b}")) else none
    let andGates := match opcodeWidth with
      | 7 =>
        let t01 := Wire.mk s!"{pfx}_t01"
        let t23 := Wire.mk s!"{pfx}_t23"
        let t45 := Wire.mk s!"{pfx}_t45"
        let t0123 := Wire.mk s!"{pfx}_t0123"
        let t456 := Wire.mk s!"{pfx}_t456"
        [Gate.mkAND bitWires[0]! bitWires[1]! t01,
         Gate.mkAND bitWires[2]! bitWires[3]! t23,
         Gate.mkAND bitWires[4]! bitWires[5]! t45,
         Gate.mkAND t01 t23 t0123,
         Gate.mkAND t45 bitWires[6]! t456,
         Gate.mkAND t0123 t456 matchOut]
      | _ =>
        let t01 := Wire.mk s!"{pfx}_t01"
        let t012 := Wire.mk s!"{pfx}_t012"
        let t0123 := Wire.mk s!"{pfx}_t0123"
        let t01234 := Wire.mk s!"{pfx}_t01234"
        [Gate.mkAND bitWires[0]! bitWires[1]! t01,
         Gate.mkAND t01 bitWires[2]! t012,
         Gate.mkAND t012 bitWires[3]! t0123,
         Gate.mkAND t0123 bitWires[4]! t01234,
         Gate.mkAND t01234 bitWires[5]! matchOut]
    notGates ++ andGates
  -- Match decode_optype against FENCE_I encoding
  let fence_i_match := Wire.mk "fence_i_match"
  let fence_i_match_gates : List Gate :=
    if config.enableZifencei then mkOpcodeMatch (oi .FENCE_I) "fencei" fence_i_match
    else [Gate.mkBUF zero fence_i_match]
  -- Match decode_optype against each CSR encoding (6 opcodes → OR → csr_match)
  let csr_match_wires := ["csrrw", "csrrs", "csrrc", "csrrwi", "csrrsi", "csrrci"].map
    (fun n => Wire.mk s!"csr_m_{n}")
  let csr_match_gates : List Gate :=
    if config.enableZicsr then
      let csrEncs := [oi .CSRRW, oi .CSRRS, oi .CSRRC, oi .CSRRWI, oi .CSRRSI, oi .CSRRCI]
      let prefixes := ["csrrw", "csrrs", "csrrc", "csrrwi", "csrrsi", "csrrci"]
      let matchGates := (csrEncs.zip (prefixes.zip csr_match_wires)).map
        (fun (e, p, w) => mkOpcodeMatch e s!"csr_{p}" w)
      let orChain :=
        let t01 := Wire.mk "csr_or01"
        let t23 := Wire.mk "csr_or23"
        let t45 := Wire.mk "csr_or45"
        let t0123 := Wire.mk "csr_or0123"
        [Gate.mkOR csr_match_wires[0]! csr_match_wires[1]! t01,
         Gate.mkOR csr_match_wires[2]! csr_match_wires[3]! t23,
         Gate.mkOR csr_match_wires[4]! csr_match_wires[5]! t45,
         Gate.mkOR t01 t23 t0123,
         Gate.mkOR t0123 t45 csr_match]
      matchGates.flatten ++ orChain
    else [Gate.mkBUF zero csr_match]
  let enableSerialize := config.enableZifencei || config.enableZicsr
  if enableSerialize then
    let dc_tmp := Wire.mk "fencei_dc_tmp"
    let dc_tmp2 := Wire.mk "fencei_dc_tmp2"
    let not_flushing_comb := Wire.mk "fencei_not_flushing_comb"
    let drain_next_tmp := Wire.mk "fencei_drain_next_tmp"
    let set_or := Wire.mk "fencei_set_or"
    let not_dc := Wire.mk "fencei_not_dc"
    let not_redir_reg := Wire.mk "not_redir_reg"
    let decode_valid_noredir := Wire.mk "dv_noredir"
    fence_i_match_gates ++ csr_match_gates ++
    [-- Gate detection by NOT(branch_redirect_valid_reg) to prevent re-detecting
     -- stale decode output on redirect cycle
     Gate.mkNOT branch_redirect_valid_reg not_redir_reg,
     Gate.mkAND decode_valid not_redir_reg decode_valid_noredir,
     -- fence_i_detected = decode_valid_noredir AND fence_i_match
     Gate.mkAND decode_valid_noredir fence_i_match fence_i_detected,
     -- csr_detected = decode_valid_noredir AND csr_match
     Gate.mkAND decode_valid_noredir csr_match csr_detected,
     -- serialize_detected = fence_i_detected OR csr_detected
     Gate.mkOR fence_i_detected csr_detected serialize_detected,
     -- FSM logic (uses serialize_detected instead of fence_i_detected)
     Gate.mkNOT fence_i_draining fence_i_not_draining,
     Gate.mkAND serialize_detected fence_i_not_draining fence_i_start,
     -- drain_complete = draining AND rob_empty AND lsu_sb_empty AND NOT(pipeline_flush_comb)
     -- The NOT(pipeline_flush_comb) suppresses spurious drain_complete when a branch
     -- misprediction flush empties the ROB while a speculative CSR serialize is pending.
     Gate.mkAND fence_i_draining rob_empty dc_tmp,
     Gate.mkAND dc_tmp lsu_sb_empty dc_tmp2,
     Gate.mkNOT pipeline_flush_comb not_flushing_comb,
     Gate.mkAND dc_tmp2 not_flushing_comb fence_i_drain_complete,
     -- draining_next = (start OR draining) AND NOT(drain_complete) AND NOT(pipeline_flush_comb)
     -- Clear draining state on pipeline flush to cancel speculative CSR serialize
     Gate.mkOR fence_i_start fence_i_draining set_or,
     Gate.mkNOT fence_i_drain_complete not_dc,
     Gate.mkAND set_or not_dc drain_next_tmp,
     Gate.mkAND drain_next_tmp not_flushing_comb fence_i_draining_next,
     -- suppress: CSR goes through rename on start cycle (not suppressed); FENCE.I and drain are suppressed
     Gate.mkAND fence_i_start csr_detected csr_rename_en,
     Gate.mkNOT csr_rename_en not_csr_rename_en,
     Gate.mkAND fence_i_start not_csr_rename_en (Wire.mk "fi_start_nocsr"),
     Gate.mkOR (Wire.mk "fi_start_nocsr") fence_i_draining fence_i_suppress] ++
    -- Redirect target capture: MUX(hold, fetch_pc+4, start)
    (List.range 32).map (fun i =>
      Gate.mkMUX fence_i_redir_target[i]! fence_i_pc_plus_4[i]! fence_i_start fence_i_redir_next[i]!) ++
    -- CSR flag capture: MUX(hold, csr_detected, start)
    [Gate.mkMUX csr_flag_reg csr_detected fence_i_start csr_flag_next] ++
    -- CSR addr capture: MUX(hold, decode_imm[0..11], start)
    (List.range 12).map (fun i =>
      Gate.mkMUX csr_addr_reg[i]! decode_imm[i]! fence_i_start csr_addr_next[i]!) ++
    -- CSR optype capture: MUX(hold, decode_optype[0..W-1], start)
    (List.range opcodeWidth).map (fun i =>
      Gate.mkMUX csr_optype_reg[i]! decode_optype[i]! fence_i_start csr_optype_next[i]!) ++
    -- CSR rd capture: MUX(hold, decode_rd[0..4], start)
    (List.range 5).map (fun i =>
      Gate.mkMUX csr_rd_reg[i]! decode_rd[i]! fence_i_start csr_rd_next[i]!) ++
    -- CSR phys tag capture: MUX(hold, rd_phys[0..5], start)
    -- Uses rd_phys (newly allocated from rename) for unique-per-CSR mapping
    (List.range 6).map (fun i =>
      Gate.mkMUX csr_phys_reg[i]! rd_phys[i]! fence_i_start csr_phys_next[i]!) ++
    -- CSR rs1 data capture: MUX(hold, fwd_src1_data[0..31], start)
    -- Uses forwarded data (with CDB bypass) since the producing instruction may
    -- be on the CDB in the same cycle as fence_i_start
    (List.range 32).map (fun i =>
      Gate.mkMUX csr_rs1cap_reg[i]! (Wire.mk s!"fwd_src1_data_{i}") fence_i_start csr_rs1cap_next[i]!) ++
    -- CSR zimm capture: MUX(hold, decode_rs1[0..4], start)
    -- The rs1 field is used as 5-bit zero-extended immediate for CSRRWI/CSRRSI/CSRRCI
    (List.range 5).map (fun i =>
      Gate.mkMUX csr_zimm_reg[i]! decode_rs1[i]! fence_i_start csr_zimm_next[i]!)
  else
    -- No serialize extensions: tie everything low
    [Gate.mkBUF zero fence_i_match,
     Gate.mkBUF zero fence_i_detected,
     Gate.mkBUF zero csr_detected,
     Gate.mkBUF zero serialize_detected,
     Gate.mkBUF zero fence_i_start,
     Gate.mkBUF zero fence_i_drain_complete,
     Gate.mkBUF zero fence_i_draining_next,
     Gate.mkBUF zero fence_i_suppress,
     Gate.mkBUF zero csr_flag_next,
     Gate.mkBUF zero csr_rename_en,
     Gate.mkBUF one not_csr_rename_en] ++
    (List.range 12).map (fun i => Gate.mkBUF zero csr_addr_next[i]!) ++
    (List.range opcodeWidth).map (fun i => Gate.mkBUF zero csr_optype_next[i]!) ++
    (List.range 5).map (fun i => Gate.mkBUF zero csr_rd_next[i]!) ++
    (List.range 6).map (fun i => Gate.mkBUF zero csr_phys_next[i]!)

/-- CSR read MUX: cascaded multiplexer selecting the appropriate CSR register
    value based on the decoded address. Returns (gates, csr_read_data, mstatus_sd_bit,
    mstatus_fs_inv0, mstatus_fs_inv1). -/
def mkCsrReadMux
    (config : CPUConfig) (enableF : Bool) (zero one : Wire)
    (misa_val : Nat)
    (is_misa is_mscratch : Wire) (is_mcycle is_mcycleh is_minstret is_minstreth : Wire)
    (is_fflags is_frm is_fcsr : Wire)
    (is_mstatus is_mie is_mtvec is_mepc is_mcause is_mtval is_mip : Wire)
    (mscratch_reg mcycle_reg mcycleh_reg minstret_reg minstreth_reg : List Wire)
    (mstatus_reg mie_reg mtvec_reg mepc_reg mcause_reg mtval_reg : List Wire)
    (fflags_reg : List Wire) (frm_reg : List Wire)
    : List Gate × List Wire × Wire × Wire × Wire :=
  let csr_read_data := (List.range 32).map (fun i => Wire.mk s!"csr_rd_e{i}")
  let mstatus_sd_bit := Wire.mk "mstatus_sd_bit"
  let mstatus_fs_inv0 := Wire.mk "mstatus_fs_inv0"
  let mstatus_fs_inv1 := Wire.mk "mstatus_fs_inv1"
  let mstatus_sd_gate :=
    if config.enableZicsr && enableF then
      [Gate.mkNOT mstatus_reg[13]! mstatus_fs_inv0,
       Gate.mkNOT mstatus_reg[14]! mstatus_fs_inv1,
       Gate.mkAND mstatus_fs_inv0 mstatus_fs_inv1 mstatus_sd_bit]
    else if config.enableZicsr then
      [Gate.mkBUF zero mstatus_fs_inv0, Gate.mkBUF zero mstatus_fs_inv1,
       Gate.mkBUF zero mstatus_sd_bit]
    else
      [Gate.mkBUF zero mstatus_fs_inv0, Gate.mkBUF zero mstatus_fs_inv1,
       Gate.mkBUF zero mstatus_sd_bit]
  let csr_read_mux_gates :=
    if config.enableZicsr then
      (List.range 32).map (fun i =>
        let misa_bit := if Nat.testBit misa_val i then one else zero
        let r_misa := Wire.mk s!"csr_rmisa_e{i}"
        let r_mscr := Wire.mk s!"csr_rmscr_e{i}"
        let r_mcyc := Wire.mk s!"csr_rmcyc_e{i}"
        let r_mcyh := Wire.mk s!"csr_rmcyh_e{i}"
        let r_mins := Wire.mk s!"csr_rmins_e{i}"
        let r_minh := Wire.mk s!"csr_rminh_e{i}"
        let r_fflags := Wire.mk s!"csr_rfflags_e{i}"
        let r_frm := Wire.mk s!"csr_rfrm_e{i}"
        let r_fcsr := Wire.mk s!"csr_rfcsr_e{i}"
        let r_mstatus := Wire.mk s!"csr_rmstatus_e{i}"
        let r_mie := Wire.mk s!"csr_rmie_e{i}"
        let r_mtvec := Wire.mk s!"csr_rmtvec_e{i}"
        let r_mepc := Wire.mk s!"csr_rmepc_e{i}"
        let r_mcause := Wire.mk s!"csr_rmcause_e{i}"
        let r_mtval := Wire.mk s!"csr_rmtval_e{i}"
        let fflags_read_bit := if enableF && i < 5 then fflags_reg[i]! else zero
        let frm_read_bit := if enableF && i < 3 then frm_reg[i]! else zero
        let fcsr_read_bit := if enableF then
                               if i < 5 then fflags_reg[i]!
                               else if i < 8 then frm_reg[i - 5]!
                               else zero
                             else zero
        let mstatus_read_bit :=
          if i == 31 then mstatus_sd_bit
          else if i == 11 || i == 12 then one
          else if enableF && (i == 13 || i == 14) then
            if i == 13 then mstatus_fs_inv0 else mstatus_fs_inv1
          else mstatus_reg[i]!
        [Gate.mkMUX zero misa_bit is_misa r_misa,
         Gate.mkMUX r_misa mscratch_reg[i]! is_mscratch r_mscr,
         Gate.mkMUX r_mscr mcycle_reg[i]! is_mcycle r_mcyc,
         Gate.mkMUX r_mcyc mcycleh_reg[i]! is_mcycleh r_mcyh,
         Gate.mkMUX r_mcyh minstret_reg[i]! is_minstret r_mins,
         Gate.mkMUX r_mins minstreth_reg[i]! is_minstreth r_minh,
         Gate.mkMUX r_minh fflags_read_bit is_fflags r_fflags,
         Gate.mkMUX r_fflags frm_read_bit is_frm r_frm,
         Gate.mkMUX r_frm fcsr_read_bit is_fcsr r_fcsr,
         Gate.mkMUX r_fcsr mstatus_read_bit is_mstatus r_mstatus,
         Gate.mkMUX r_mstatus mie_reg[i]! is_mie r_mie,
         Gate.mkMUX r_mie mtvec_reg[i]! is_mtvec r_mtvec,
         Gate.mkMUX r_mtvec mepc_reg[i]! is_mepc r_mepc,
         Gate.mkMUX r_mepc mcause_reg[i]! is_mcause r_mcause,
         Gate.mkMUX r_mcause mtval_reg[i]! is_mtval r_mtval,
         Gate.mkMUX r_mtval zero is_mip csr_read_data[i]!]) |>.flatten
    else
      (List.range 32).map (fun i => Gate.mkBUF zero csr_read_data[i]!)
  (mstatus_sd_gate ++ csr_read_mux_gates, csr_read_data, mstatus_sd_bit, mstatus_fs_inv0, mstatus_fs_inv1)

/-- CSR operation decode: match captured optype to determine RW/RS/RC/IMM,
    and select CSR source value (register vs zero-extended immediate). -/
def mkCsrOpDecode
    (config : CPUConfig) (oi : OpType → Nat) (opcodeWidth : Nat) (zero : Wire)
    (csr_optype_reg : List Wire) (csr_rs1cap_reg : List Wire) (csr_zimm_reg : List Wire)
    : List Gate × Wire × Wire × Wire × Wire × List Wire :=
  let csr_is_rw := Wire.mk "csr_is_rw"
  let csr_is_rs := Wire.mk "csr_is_rs"
  let csr_is_rc := Wire.mk "csr_is_rc"
  let csr_is_imm := Wire.mk "csr_is_imm"
  let csr_op_match_wires : List Wire :=
    ["csrrw_x", "csrrs_x", "csrrc_x", "csrrwi_x", "csrrsi_x", "csrrci_x"].map
      (fun n => Wire.mk s!"csr_xop_{n}")
  let csr_op_match_gates :=
    if config.enableZicsr then
      let csrEncs := [oi .CSRRW, oi .CSRRS, oi .CSRRC, oi .CSRRWI, oi .CSRRSI, oi .CSRRCI]
      let prefixes := ["xrw", "xrs", "xrc", "xrwi", "xrsi", "xrci"]
      let mkCsrOpMatch (encVal : Nat) (pfx : String) (matchOut : Wire) : List Gate :=
        let bitWires := (List.range opcodeWidth).map fun b =>
          if Nat.testBit encVal b then csr_optype_reg[b]! else Wire.mk s!"csr_{pfx}_n{b}"
        let notGates := (List.range opcodeWidth).filterMap fun b =>
          if !Nat.testBit encVal b then some (Gate.mkNOT csr_optype_reg[b]! (Wire.mk s!"csr_{pfx}_n{b}")) else none
        let andGates := match opcodeWidth with
          | 7 =>
            let t01 := Wire.mk s!"csr_{pfx}_t01"
            let t23 := Wire.mk s!"csr_{pfx}_t23"
            let t45 := Wire.mk s!"csr_{pfx}_t45"
            let t0123 := Wire.mk s!"csr_{pfx}_t0123"
            let t456 := Wire.mk s!"csr_{pfx}_t456"
            [Gate.mkAND bitWires[0]! bitWires[1]! t01,
             Gate.mkAND bitWires[2]! bitWires[3]! t23,
             Gate.mkAND bitWires[4]! bitWires[5]! t45,
             Gate.mkAND t01 t23 t0123,
             Gate.mkAND t45 bitWires[6]! t456,
             Gate.mkAND t0123 t456 matchOut]
          | _ =>
            let t01 := Wire.mk s!"csr_{pfx}_t01"
            let t012 := Wire.mk s!"csr_{pfx}_t012"
            let t0123 := Wire.mk s!"csr_{pfx}_t0123"
            let t01234 := Wire.mk s!"csr_{pfx}_t01234"
            [Gate.mkAND bitWires[0]! bitWires[1]! t01,
             Gate.mkAND t01 bitWires[2]! t012,
             Gate.mkAND t012 bitWires[3]! t0123,
             Gate.mkAND t0123 bitWires[4]! t01234,
             Gate.mkAND t01234 bitWires[5]! matchOut]
        notGates ++ andGates
      let matchGates := (csrEncs.zip (prefixes.zip csr_op_match_wires)).map
        (fun (e, p, w) => mkCsrOpMatch e p w)
      matchGates.flatten ++
      [Gate.mkOR csr_op_match_wires[0]! csr_op_match_wires[3]! csr_is_rw,
       Gate.mkOR csr_op_match_wires[1]! csr_op_match_wires[4]! csr_is_rs,
       Gate.mkOR csr_op_match_wires[2]! csr_op_match_wires[5]! csr_is_rc,
       Gate.mkOR csr_op_match_wires[3]! csr_op_match_wires[4]! (Wire.mk "csr_imm_tmp"),
       Gate.mkOR (Wire.mk "csr_imm_tmp") csr_op_match_wires[5]! csr_is_imm]
    else
      [Gate.mkBUF zero csr_is_rw, Gate.mkBUF zero csr_is_rs,
       Gate.mkBUF zero csr_is_rc, Gate.mkBUF zero csr_is_imm]
  let csr_src := (List.range 32).map (fun i => Wire.mk s!"csr_src_e{i}")
  let csr_src_gates :=
    if config.enableZicsr then
      (List.range 32).map (fun i =>
        let zimm_or_zero := if i < 5 then csr_zimm_reg[i]! else zero
        Gate.mkMUX csr_rs1cap_reg[i]! zimm_or_zero csr_is_imm csr_src[i]!)
    else
      (List.range 32).map (fun i => Gate.mkBUF zero csr_src[i]!)
  (csr_op_match_gates ++ csr_src_gates, csr_is_rw, csr_is_rs, csr_is_rc, csr_is_imm, csr_src)

/-- CSR write logic: compute new CSR value from operation type and generate
    per-register write enables gated by drain_complete. -/
def mkCsrWriteLogic
    (config : CPUConfig) (zero : Wire)
    (csr_read_data csr_src : List Wire)
    (csr_is_rw csr_is_rs csr_is_rc : Wire)
    (csr_drain_complete : Wire) (csr_zimm_reg : List Wire)
    (is_mscratch is_mcycle_m is_mcycleh_m is_minstret_m is_minstreth_m : Wire)
    (is_fflags is_frm is_fcsr : Wire)
    (is_mstatus is_mie is_mtvec is_mepc is_mcause is_mtval : Wire)
    : List Gate × List Wire × Wire × Wire × Wire × Wire × Wire × Wire × Wire × Wire × Wire × Wire × Wire × Wire × Wire :=
  let csr_write_val := (List.range 32).map (fun i => Wire.mk s!"csr_wv_e{i}")
  let csr_write_compute_gates :=
    if config.enableZicsr then
      (List.range 32).map (fun i =>
        let rs_val := Wire.mk s!"csr_rs_e{i}"
        let not_src := Wire.mk s!"csr_nsrc_e{i}"
        let rc_val := Wire.mk s!"csr_rc_e{i}"
        let rw_or_rs := Wire.mk s!"csr_rwrs_e{i}"
        [Gate.mkOR csr_read_data[i]! csr_src[i]! rs_val,
         Gate.mkNOT csr_src[i]! not_src,
         Gate.mkAND csr_read_data[i]! not_src rc_val,
         Gate.mkMUX csr_src[i]! rs_val csr_is_rs rw_or_rs,
         Gate.mkMUX rw_or_rs rc_val csr_is_rc csr_write_val[i]!]) |>.flatten
    else
      (List.range 32).map (fun i => Gate.mkBUF zero csr_write_val[i]!)
  let csr_actually_writes := Wire.mk "csr_actually_writes"
  let csr_src_nonzero := Wire.mk "csr_src_nonzero"
  let csr_rs_or_rc := Wire.mk "csr_rs_or_rc"
  let csr_src_nz_tmp := (List.range 3).map (fun i => Wire.mk s!"csr_snz_e{i}")
  let csr_we_mscratch := Wire.mk "csr_we_mscratch"
  let csr_we_mcycle := Wire.mk "csr_we_mcycle"
  let csr_we_mcycleh := Wire.mk "csr_we_mcycleh"
  let csr_we_minstret := Wire.mk "csr_we_minstret"
  let csr_we_minstreth := Wire.mk "csr_we_minstreth"
  let csr_we_fflags := Wire.mk "csr_we_fflags"
  let csr_we_frm := Wire.mk "csr_we_frm"
  let csr_we_fcsr := Wire.mk "csr_we_fcsr"
  let csr_we_mstatus := Wire.mk "csr_we_mstatus"
  let csr_we_mie := Wire.mk "csr_we_mie"
  let csr_we_mtvec := Wire.mk "csr_we_mtvec"
  let csr_we_mepc := Wire.mk "csr_we_mepc"
  let csr_we_mcause := Wire.mk "csr_we_mcause"
  let csr_we_mtval := Wire.mk "csr_we_mtval"
  let csr_drain_and_writes := Wire.mk "csr_drain_and_writes"
  let csr_we_gates :=
    if config.enableZicsr then
      [Gate.mkOR csr_zimm_reg[0]! csr_zimm_reg[1]! csr_src_nz_tmp[0]!,
       Gate.mkOR csr_src_nz_tmp[0]! csr_zimm_reg[2]! csr_src_nz_tmp[1]!,
       Gate.mkOR csr_src_nz_tmp[1]! csr_zimm_reg[3]! csr_src_nz_tmp[2]!,
       Gate.mkOR csr_src_nz_tmp[2]! csr_zimm_reg[4]! csr_src_nonzero,
       Gate.mkOR csr_is_rs csr_is_rc csr_rs_or_rc,
       Gate.mkAND csr_rs_or_rc csr_src_nonzero (Wire.mk "csr_rsrc_write"),
       Gate.mkOR csr_is_rw (Wire.mk "csr_rsrc_write") csr_actually_writes,
       Gate.mkAND csr_drain_complete csr_actually_writes csr_drain_and_writes,
       Gate.mkAND csr_drain_and_writes is_mscratch csr_we_mscratch,
       Gate.mkAND csr_drain_and_writes is_mcycle_m csr_we_mcycle,
       Gate.mkAND csr_drain_and_writes is_mcycleh_m csr_we_mcycleh,
       Gate.mkAND csr_drain_and_writes is_minstret_m csr_we_minstret,
       Gate.mkAND csr_drain_and_writes is_minstreth_m csr_we_minstreth,
       Gate.mkAND csr_drain_and_writes is_fflags csr_we_fflags,
       Gate.mkAND csr_drain_and_writes is_frm csr_we_frm,
       Gate.mkAND csr_drain_and_writes is_fcsr csr_we_fcsr,
       Gate.mkAND csr_drain_and_writes is_mstatus csr_we_mstatus,
       Gate.mkAND csr_drain_and_writes is_mie csr_we_mie,
       Gate.mkAND csr_drain_and_writes is_mtvec csr_we_mtvec,
       Gate.mkAND csr_drain_and_writes is_mepc csr_we_mepc,
       Gate.mkAND csr_drain_and_writes is_mcause csr_we_mcause,
       Gate.mkAND csr_drain_and_writes is_mtval csr_we_mtval]
    else
      [Gate.mkBUF zero csr_actually_writes, Gate.mkBUF zero csr_src_nonzero,
       Gate.mkBUF zero csr_rs_or_rc, Gate.mkBUF zero csr_drain_and_writes,
       Gate.mkBUF zero csr_we_mscratch, Gate.mkBUF zero csr_we_mcycle,
       Gate.mkBUF zero csr_we_mcycleh, Gate.mkBUF zero csr_we_minstret,
       Gate.mkBUF zero csr_we_minstreth,
       Gate.mkBUF zero csr_we_fflags, Gate.mkBUF zero csr_we_frm,
       Gate.mkBUF zero csr_we_fcsr,
       Gate.mkBUF zero csr_we_mstatus, Gate.mkBUF zero csr_we_mie,
       Gate.mkBUF zero csr_we_mtvec, Gate.mkBUF zero csr_we_mepc,
       Gate.mkBUF zero csr_we_mcause, Gate.mkBUF zero csr_we_mtval]
  (csr_write_compute_gates ++ csr_we_gates, csr_write_val,
   csr_we_mscratch, csr_we_mcycle, csr_we_mcycleh, csr_we_minstret, csr_we_minstreth,
   csr_we_mstatus, csr_we_mie, csr_we_mtvec, csr_we_mepc, csr_we_mcause, csr_we_mtval,
   csr_actually_writes, csr_drain_and_writes)

/-- CSR next-value logic: WARL masking, MUX(hold, write_val, we) for all CSRs,
    and 64-bit counter auto-increment with carry chains. -/
def mkCsrNextValue
    (config : CPUConfig) (enableF : Bool) (zero one : Wire)
    (csr_write_val : List Wire)
    (csr_we_mscratch csr_we_mcycle csr_we_mcycleh csr_we_minstret csr_we_minstreth : Wire)
    (csr_we_mstatus csr_we_mie csr_we_mtvec csr_we_mepc csr_we_mcause csr_we_mtval : Wire)
    (mscratch_reg mscratch_next : List Wire)
    (mstatus_reg mstatus_next : List Wire)
    (mie_reg mie_next : List Wire)
    (mtvec_reg mtvec_next : List Wire)
    (mepc_reg mepc_next : List Wire)
    (mcause_reg mcause_next : List Wire)
    (mtval_reg mtval_next : List Wire)
    (mip_next : List Wire)
    (mcycle_reg mcycle_next mcycleh_reg mcycleh_next : List Wire)
    (minstret_reg minstret_next minstreth_reg minstreth_next : List Wire)
    (commit_valid_muxed : Wire)
    : List Gate × List CircuitInstance :=
  let mscratch_next_gates :=
    if config.enableZicsr then
      (List.range 32).map (fun i =>
        Gate.mkMUX mscratch_reg[i]! csr_write_val[i]! csr_we_mscratch mscratch_next[i]!)
    else
      (List.range 32).map (fun i => Gate.mkBUF zero mscratch_next[i]!)
  -- mstatus WARL
  let mstatus_warl := (List.range 32).map (fun i => Wire.mk s!"mstatus_warl_e{i}")
  let mstatus_warl_gates :=
    if config.enableZicsr then
      (List.range 32).map (fun i =>
        if i == 11 || i == 12 then Gate.mkBUF one mstatus_warl[i]!
        else if enableF && (i == 13 || i == 14) then Gate.mkNOT csr_write_val[i]! mstatus_warl[i]!
        else if i == 3 || i == 7 then Gate.mkBUF csr_write_val[i]! mstatus_warl[i]!
        else Gate.mkBUF zero mstatus_warl[i]!)
    else
      (List.range 32).map (fun i => Gate.mkBUF zero mstatus_warl[i]!)
  let mstatus_next_gates :=
    if config.enableZicsr then
      (List.range 32).map (fun i =>
        Gate.mkMUX mstatus_reg[i]! mstatus_warl[i]! csr_we_mstatus mstatus_next[i]!)
    else
      (List.range 32).map (fun i => Gate.mkBUF zero mstatus_next[i]!)
  -- mie WARL
  let mie_warl := (List.range 32).map (fun i => Wire.mk s!"mie_warl_e{i}")
  let mie_warl_gates :=
    if config.enableZicsr then
      (List.range 32).map (fun i =>
        if i == 3 || i == 7 || i == 11 then Gate.mkBUF csr_write_val[i]! mie_warl[i]!
        else Gate.mkBUF zero mie_warl[i]!)
    else
      (List.range 32).map (fun i => Gate.mkBUF zero mie_warl[i]!)
  let mie_next_gates :=
    if config.enableZicsr then
      (List.range 32).map (fun i =>
        Gate.mkMUX mie_reg[i]! mie_warl[i]! csr_we_mie mie_next[i]!)
    else
      (List.range 32).map (fun i => Gate.mkBUF zero mie_next[i]!)
  -- mtvec WARL
  let mtvec_warl := (List.range 32).map (fun i => Wire.mk s!"mtvec_warl_e{i}")
  let mtvec_warl_gates :=
    if config.enableZicsr then
      (List.range 32).map (fun i =>
        if i == 1 then Gate.mkBUF zero mtvec_warl[i]!
        else Gate.mkBUF csr_write_val[i]! mtvec_warl[i]!)
    else
      (List.range 32).map (fun i => Gate.mkBUF zero mtvec_warl[i]!)
  let mtvec_next_gates :=
    if config.enableZicsr then
      (List.range 32).map (fun i =>
        Gate.mkMUX mtvec_reg[i]! mtvec_warl[i]! csr_we_mtvec mtvec_next[i]!)
    else
      (List.range 32).map (fun i => Gate.mkBUF zero mtvec_next[i]!)
  -- mepc WARL
  let mepc_warl := (List.range 32).map (fun i => Wire.mk s!"mepc_warl_e{i}")
  let mepc_warl_gates :=
    if config.enableZicsr then
      (List.range 32).map (fun i =>
        if i < 2 then Gate.mkBUF zero mepc_warl[i]!
        else Gate.mkBUF csr_write_val[i]! mepc_warl[i]!)
    else
      (List.range 32).map (fun i => Gate.mkBUF zero mepc_warl[i]!)
  let mepc_next_gates :=
    if config.enableZicsr then
      (List.range 32).map (fun i =>
        Gate.mkMUX mepc_reg[i]! mepc_warl[i]! csr_we_mepc mepc_next[i]!)
    else
      (List.range 32).map (fun i => Gate.mkBUF zero mepc_next[i]!)
  -- mcause: all 32 bits writable
  let mcause_next_gates :=
    if config.enableZicsr then
      (List.range 32).map (fun i =>
        Gate.mkMUX mcause_reg[i]! csr_write_val[i]! csr_we_mcause mcause_next[i]!)
    else
      (List.range 32).map (fun i => Gate.mkBUF zero mcause_next[i]!)
  -- mtval: all 32 bits writable
  let mtval_next_gates :=
    if config.enableZicsr then
      (List.range 32).map (fun i =>
        Gate.mkMUX mtval_reg[i]! csr_write_val[i]! csr_we_mtval mtval_next[i]!)
    else
      (List.range 32).map (fun i => Gate.mkBUF zero mtval_next[i]!)
  -- mip: WARL to 0
  let mip_next_gates :=
    (List.range 32).map (fun i => Gate.mkBUF zero mip_next[i]!)
  -- Counter auto-increment
  let mcycle_plus_1 := makeIndexedWiresH "mcycle_p1" 32
  let mcycle_adder_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32"
    instName := "u_mcycle_adder"
    portMap :=
      (mcycle_reg.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      ((List.range 32).map (fun i => (s!"b_{i}", if i == 0 then one else zero))) ++
      [("cin", zero)] ++
      (mcycle_plus_1.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }
  let mcycle_carry := Wire.mk "mcycle_carry"
  let mcycleh_plus_c := makeIndexedWiresH "mcycleh_pc" 32
  let mcycleh_adder_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32"
    instName := "u_mcycleh_adder"
    portMap :=
      (mcycleh_reg.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      ((List.range 32).map (fun i => (s!"b_{i}", zero))) ++
      [("cin", mcycle_carry)] ++
      (mcycleh_plus_c.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }
  let minstret_plus_1 := makeIndexedWiresH "minstret_p1" 32
  let minstret_adder_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32"
    instName := "u_minstret_adder"
    portMap :=
      (minstret_reg.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      ((List.range 32).map (fun i => (s!"b_{i}", zero))) ++
      [("cin", commit_valid_muxed)] ++
      (minstret_plus_1.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }
  let minstret_carry := Wire.mk "minstret_carry"
  let minstreth_plus_c := makeIndexedWiresH "minstreth_pc" 32
  let minstreth_adder_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32"
    instName := "u_minstreth_adder"
    portMap :=
      (minstreth_reg.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      ((List.range 32).map (fun i => (s!"b_{i}", zero))) ++
      [("cin", minstret_carry)] ++
      (minstreth_plus_c.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }
  let csr_counter_instances : List CircuitInstance :=
    if config.enableZicsr then
      [mcycle_adder_inst, mcycleh_adder_inst, minstret_adder_inst, minstreth_adder_inst]
    else []
  -- Carry computation
  let mcycle_carry_tmp := (List.range 31).map (fun i => Wire.mk s!"mcyc_ct_e{i}")
  let mcycle_carry_gates :=
    if config.enableZicsr then
      [Gate.mkAND mcycle_reg[0]! mcycle_reg[1]! mcycle_carry_tmp[0]!] ++
      (List.range 30).map (fun i =>
        Gate.mkAND mcycle_carry_tmp[i]! mcycle_reg[i+2]! (if i < 29 then mcycle_carry_tmp[i+1]! else mcycle_carry))
    else [Gate.mkBUF zero mcycle_carry]
  let minstret_carry_tmp := (List.range 31).map (fun i => Wire.mk s!"mins_ct_e{i}")
  let minstret_carry_pre := Wire.mk "minstret_carry_pre"
  let minstret_carry_gates :=
    if config.enableZicsr then
      [Gate.mkAND minstret_reg[0]! minstret_reg[1]! minstret_carry_tmp[0]!] ++
      (List.range 30).map (fun i =>
        Gate.mkAND minstret_carry_tmp[i]! minstret_reg[i+2]! (if i < 29 then minstret_carry_tmp[i+1]! else minstret_carry_pre)) ++
      [Gate.mkAND minstret_carry_pre commit_valid_muxed minstret_carry]
    else [Gate.mkBUF zero minstret_carry]
  let counter_next_gates :=
    if config.enableZicsr then
      mcycle_carry_gates ++ minstret_carry_gates ++
      (List.range 32).map (fun i =>
        Gate.mkMUX mcycle_plus_1[i]! csr_write_val[i]! csr_we_mcycle mcycle_next[i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkMUX mcycleh_plus_c[i]! csr_write_val[i]! csr_we_mcycleh mcycleh_next[i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkMUX minstret_plus_1[i]! csr_write_val[i]! csr_we_minstret minstret_next[i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkMUX minstreth_plus_c[i]! csr_write_val[i]! csr_we_minstreth minstreth_next[i]!)
    else
      (List.range 32).map (fun i => Gate.mkBUF zero mcycle_next[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF zero mcycleh_next[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF zero minstret_next[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF zero minstreth_next[i]!)
  let all_next_gates := mscratch_next_gates ++ mstatus_warl_gates ++ mstatus_next_gates ++
    mie_warl_gates ++ mie_next_gates ++ mtvec_warl_gates ++ mtvec_next_gates ++
    mepc_warl_gates ++ mepc_next_gates ++ mcause_next_gates ++ mtval_next_gates ++
    mip_next_gates ++ counter_next_gates
  (all_next_gates, csr_counter_instances)

end Shoumei.RISCV.CPU
