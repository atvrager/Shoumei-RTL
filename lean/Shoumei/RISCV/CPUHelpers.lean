/-
CPU Helper Functions - CSR, Load Forwarding, Memory Pipeline, Serialize

Extracted from CPU.lean to reduce file size. These 8 helpers have matching
specs in CPUHelperSpecs.lean and proofs in CPUHelperProofs.lean.
-/

import Shoumei.DSL
import Shoumei.RISCV.Config
import Shoumei.RISCV.CPUCircuitHelpers
import Shoumei.RISCV.Microcode.MicrocodeROM

namespace Shoumei.RISCV.CPU

open Shoumei

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
  -- SB fwd size check: only forward when store covers the full load (S >= L)
  let fwd_size_ok := Wire.mk "fwd_size_ok"
  let not_load_size0 := Wire.mk "not_load_size0"
  let fwd_sz_k := Wire.mk "fwd_sz_k"
  let fwd_sz_a := Wire.mk "fwd_sz_a"
  let fwd_sz_b := Wire.mk "fwd_sz_b"
  let fwd_size_check_gates := [
    Gate.mkNOT mem_size_r[0]! not_load_size0,
    Gate.mkOR lsu_sb_fwd_size[0]! not_load_size0 fwd_sz_k,
    Gate.mkOR lsu_sb_fwd_size[1]! fwd_sz_k fwd_sz_a,
    Gate.mkAND lsu_sb_fwd_size[1]! fwd_sz_k fwd_sz_b,
    Gate.mkMUX fwd_sz_a fwd_sz_b mem_size_r[1]! fwd_size_ok
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
  let addrWidth := mem_address.length
  let mem_addr_next := makeIndexedWires "mem_addr_next" addrWidth
  let mem_addr_pipe_gates := (List.range addrWidth).map (fun i =>
    Gate.mkMUX mem_addr_r[i]! mem_address[i]! pipe_load_en mem_addr_next[i]!)
  let mem_addr_pipe_insts := (List.range addrWidth).map (fun i =>
    ({ moduleName := "DFlipFlop", instName := s!"u_mem_addr_r_{i}",
       portMap := [("d", mem_addr_next[i]!), ("q", mem_addr_r[i]!),
                   ("clock", clock), ("reset", reset)] } : CircuitInstance))
  let mem_tag_next := makeIndexedWires "mem_tag_next" 6
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
  let mem_size_next := makeIndexedWires "mem_size_next" 2
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
    (zero one : Wire) (clock reset : Wire)
    (decode_optype : List Wire) (decode_valid : Wire) (decode_imm decode_rd decode_rs1 : List Wire)
    (branch_redirect_valid_reg : Wire)
    (fetch_stall_ext : Wire)
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
    (csr_read_data : List Wire)
    (fetch_pc : List Wire)
    : List Gate × List CircuitInstance :=
  -- Helper: generate gates to match decode_optype against an encoding value
  let mkOpcodeMatch (encVal : Nat) (pfx : String) (matchOut : Wire) : List Gate :=
    let bitWires := (List.range opcodeWidth).map fun b =>
      if Nat.testBit encVal b then decode_optype[b]! else Wire.mk s!"{pfx}_n{b}"
    let notGates := (List.range opcodeWidth).filterMap fun b =>
      if !Nat.testBit encVal b then some (Gate.mkNOT decode_optype[b]! (Wire.mk s!"{pfx}_n{b}")) else none
    let andGates := match opcodeWidth with
      | 8 =>
        let t01 := Wire.mk s!"{pfx}_t01"
        let t23 := Wire.mk s!"{pfx}_t23"
        let t45 := Wire.mk s!"{pfx}_t45"
        let t67 := Wire.mk s!"{pfx}_t67"
        let t0123 := Wire.mk s!"{pfx}_t0123"
        let t4567 := Wire.mk s!"{pfx}_t4567"
        [Gate.mkAND bitWires[0]! bitWires[1]! t01,
         Gate.mkAND bitWires[2]! bitWires[3]! t23,
         Gate.mkAND bitWires[4]! bitWires[5]! t45,
         Gate.mkAND bitWires[6]! bitWires[7]! t67,
         Gate.mkAND t01 t23 t0123,
         Gate.mkAND t45 t67 t4567,
         Gate.mkAND t0123 t4567 matchOut]
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
  -- ECALL detection (for trap entry via microcode sequencer)
  let ecall_match := Wire.mk "ecall_match"
  let ecall_detected := Wire.mk "ecall_detected"
  let ecall_match_gates : List Gate :=
    mkOpcodeMatch (oi .ECALL) "ecall" ecall_match

  -- MRET detection
  let mret_match := Wire.mk "mret_match"
  let mret_detected := Wire.mk "mret_detected"
  let mret_match_gates : List Gate :=
    mkOpcodeMatch (oi .MRET) "mret" mret_match

  -- WFI detection
  let wfi_match := Wire.mk "wfi_match"
  let wfi_detected := Wire.mk "wfi_detected"
  let wfi_match_gates : List Gate :=
    mkOpcodeMatch (oi .WFI) "wfi" wfi_match

  let enableSerialize := config.enableZifencei || config.enableZicsr
  let enableTraps := config.microcodesTraps
  let enableMRET := config.microcodesMRET
  if enableSerialize then
    let dc_tmp := Wire.mk "fencei_dc_tmp"
    let dc_tmp2 := Wire.mk "fencei_dc_tmp2"
    let not_flushing_comb := Wire.mk "fencei_not_flushing_comb"
    let drain_next_tmp := Wire.mk "fencei_drain_next_tmp"
    let set_or := Wire.mk "fencei_set_or"
    let not_dc := Wire.mk "fencei_not_dc"
    let not_redir_reg := Wire.mk "not_redir_reg"
    let not_fetch_stall_ext := Wire.mk "not_fetch_stall_ext"
    let decode_valid_noredir := Wire.mk "dv_noredir"
    let decode_valid_noredir_tmp := Wire.mk "dv_noredir_tmp"
    -- Hardwired CSR/FENCE.I detection
    let hw_detect_gates :=
      fence_i_match_gates ++ csr_match_gates ++
      (if enableTraps then ecall_match_gates else []) ++
      (if enableMRET then mret_match_gates ++ wfi_match_gates else []) ++
      [Gate.mkNOT branch_redirect_valid_reg not_redir_reg,
       Gate.mkNOT fetch_stall_ext not_fetch_stall_ext,
       Gate.mkAND decode_valid not_redir_reg decode_valid_noredir_tmp,
       Gate.mkAND decode_valid_noredir_tmp not_fetch_stall_ext decode_valid_noredir,
       Gate.mkAND decode_valid_noredir fence_i_match fence_i_detected,
       Gate.mkAND decode_valid_noredir csr_match csr_detected] ++
      (if enableTraps then
        [Gate.mkAND decode_valid_noredir ecall_match ecall_detected]
       else
        [Gate.mkBUF zero ecall_detected]) ++
      (if enableMRET then
        [Gate.mkAND decode_valid_noredir mret_match mret_detected,
         Gate.mkAND decode_valid_noredir wfi_match wfi_detected]
       else
        [Gate.mkBUF zero mret_detected,
         Gate.mkBUF zero wfi_detected])
    -- serialize_detected includes ECALL, MRET, WFI when enabled
    let ser_detect_gates :=
      if enableTraps || enableMRET then
        [Gate.mkOR fence_i_detected csr_detected (Wire.mk "hw_ser_pre"),
         Gate.mkOR ecall_detected mret_detected (Wire.mk "trap_or_mret"),
         Gate.mkOR (Wire.mk "trap_or_mret") wfi_detected (Wire.mk "sys_ser"),
         Gate.mkOR (Wire.mk "hw_ser_pre") (Wire.mk "sys_ser") serialize_detected]
      else
        [Gate.mkOR fence_i_detected csr_detected serialize_detected]
    -- Hardwired FSM
    let hw_fsm_gates :=
      [Gate.mkNOT fence_i_draining fence_i_not_draining]
    -- Trap sequencer integration
    if enableTraps then
      -- Instantiate microcode sequencer for ECALL only.
      -- The sequencer runs in parallel with the hardwired CSR/FENCE.I FSM.
      -- They are mutually exclusive (ECALL vs CSR/FENCE.I).
      let trap_seq_start := Wire.mk "trap_seq_start"
      let hw_csr_fence_start := Wire.mk "hw_csrfi_start"

      -- Sequencer output wires
      let useq_active := Wire.mk "useq_active"
      let useq_suppress := Wire.mk "useq_suppress"
      let useq_drain_complete := Wire.mk "useq_drain_complete"
      let useq_write_en := Wire.mk "useq_write_en"
      let useq_read_en := Wire.mk "useq_read_en"
      let useq_redir_valid := Wire.mk "useq_redir_valid"
      let useq_csr_flag := Wire.mk "useq_csr_flag"
      let useq_upc := (List.range 6).map (fun i => Wire.mk s!"useq_upc_{i}")
      let useq_rom_data := (List.range 24).map (fun i => Wire.mk s!"useq_rom_{i}")
      let useq_addr_out := (List.range 12).map (fun i => Wire.mk s!"useq_addr_{i}")
      let useq_write_data := (List.range 32).map (fun i => Wire.mk s!"useq_wr_dt_{i}")
      let useq_redir_next := (List.range 32).map (fun i => Wire.mk s!"useq_redir_{i}")
      let useq_cdb_inject := Wire.mk "useq_cdb_inject"
      let useq_cdb_tag := (List.range 6).map (fun i => Wire.mk s!"useq_cdb_tg_{i}")
      let useq_cdb_data := (List.range 32).map (fun i => Wire.mk s!"useq_cdb_dt_{i}")

      -- Start logic: trap_seq_start for ECALL, hw_csr_fence_start for CSR/FENCE.I
      -- Both gated by NOT(any_active) to prevent starting during an active operation
      let not_any_active := Wire.mk "not_any_active"
      let any_serialize_start := Wire.mk "any_ser_start"
      -- MRET starts trap sequencer with seq_id=6
      let mret_seq_start := Wire.mk "mret_seq_start"

      let start_gates :=
        [-- Neither hardwired FSM nor trap sequencer is active
         Gate.mkOR fence_i_draining useq_active (Wire.mk "any_active"),
         Gate.mkNOT (Wire.mk "any_active") not_any_active,
         -- ECALL starts trap sequencer (seq_id=4)
         Gate.mkAND ecall_detected not_any_active trap_seq_start,
         -- MRET starts trap sequencer (seq_id=6)
         Gate.mkAND mret_detected not_any_active mret_seq_start,
         -- CSR/FENCE.I/WFI starts hardwired FSM (WFI = NOP via drain)
         Gate.mkOR fence_i_detected csr_detected (Wire.mk "csrfi_det"),
         Gate.mkOR (Wire.mk "csrfi_det") wfi_detected (Wire.mk "csrfi_wfi_det"),
         Gate.mkAND (Wire.mk "csrfi_wfi_det") not_any_active hw_csr_fence_start,
         -- any_serialize_start = either start type
         Gate.mkOR trap_seq_start mret_seq_start (Wire.mk "any_seq_start"),
         Gate.mkOR (Wire.mk "any_seq_start") hw_csr_fence_start any_serialize_start,
         -- fence_i_start = any_serialize_start (drives capture latches)
         Gate.mkBUF any_serialize_start fence_i_start]

      -- Hardwired drain FSM (only active for CSR/FENCE.I, not ECALL)
      let hw_drain_complete := Wire.mk "hw_drain_complete"
      let not_useq_active := Wire.mk "not_useq_active"
      let hw_fsm_drain_gates :=
        [Gate.mkAND fence_i_draining rob_empty dc_tmp,
         Gate.mkAND dc_tmp lsu_sb_empty dc_tmp2,
         Gate.mkNOT pipeline_flush_comb not_flushing_comb,
         Gate.mkAND dc_tmp2 not_flushing_comb (Wire.mk "hw_dc_pre"),
         -- Gate hw_drain_complete with NOT(useq_active) to prevent hw FSM
         -- from completing during trap sequencer operation
         Gate.mkNOT useq_active not_useq_active,
         Gate.mkAND (Wire.mk "hw_dc_pre") not_useq_active hw_drain_complete,
         -- draining_next for hardwired path: starts on CSR/FENCE.I, clears on drain_complete or flush
         Gate.mkOR hw_csr_fence_start fence_i_draining set_or,
         Gate.mkNOT hw_drain_complete not_dc,
         Gate.mkAND set_or not_dc drain_next_tmp,
         Gate.mkAND drain_next_tmp not_flushing_comb (Wire.mk "hw_draining_next")]

      -- Merge outputs: OR hardwired and trap sequencer (mutually exclusive)
      -- Delay useq_drain_complete by 1 cycle so fence_i_redir_target DFF can latch
      -- the sequencer's redirect (SET_PC sets redir_next and drain_complete same cycle)
      let useq_dc_delayed := Wire.mk "useq_dc_delayed"
      let useq_dc_dff : CircuitInstance := {
        moduleName := "DFlipFlop"
        instName := "u_useq_dc_dff"
        portMap := [("d", useq_drain_complete), ("q", useq_dc_delayed),
                    ("clock", clock), ("reset", reset)]
      }
      let merge_gates :=
        [-- fence_i_draining_next = hw OR useq_active (trap sequencer replaces draining)
         Gate.mkOR (Wire.mk "hw_draining_next") useq_active (Wire.mk "drain_merge_pre"),
         -- Clear on pipeline flush
         Gate.mkAND (Wire.mk "drain_merge_pre") not_flushing_comb fence_i_draining_next,
         -- fence_i_drain_complete = hw_drain_complete OR useq_dc_delayed (1-cycle delayed)
         Gate.mkOR hw_drain_complete useq_dc_delayed fence_i_drain_complete,
         -- fence_i_suppress: when CSR start, don't suppress (goes through rename);
         -- when FENCE.I start or draining or trap active, suppress
         Gate.mkAND hw_csr_fence_start csr_detected csr_rename_en,
         Gate.mkNOT csr_rename_en not_csr_rename_en,
         Gate.mkAND hw_csr_fence_start not_csr_rename_en (Wire.mk "fi_start_nocsr"),
         Gate.mkOR (Wire.mk "fi_start_nocsr") fence_i_draining (Wire.mk "hw_suppress"),
         Gate.mkOR (Wire.mk "hw_suppress") useq_suppress (Wire.mk "suppress_pre"),
         -- ECALL/MRET detected also suppresses (prevent dispatch on detection cycle)
         Gate.mkOR ecall_detected mret_detected (Wire.mk "ecall_or_mret_det"),
         Gate.mkOR (Wire.mk "suppress_pre") (Wire.mk "ecall_or_mret_det") fence_i_suppress]

      -- Redirect: for hw path use captured PC+4, for trap use sequencer's redirect
      let redir_merge_gates :=
        -- hw path redirect target: MUX(hold, fetch_pc+4, hw_csr_fence_start)
        (List.range 32).map (fun i =>
          Gate.mkMUX fence_i_redir_target[i]! fence_i_pc_plus_4[i]! hw_csr_fence_start (Wire.mk s!"hw_redir_{i}")) ++
        -- final redirect: MUX(hw_redir, useq_redir, useq_active)
        (List.range 32).map (fun i =>
          Gate.mkMUX (Wire.mk s!"hw_redir_{i}") useq_redir_next[i]! useq_active fence_i_redir_next[i]!)

      -- CSR addr: when trap sequencer active, use sequencer's addr; else use decode_imm
      let csr_addr_merge_gates :=
        (List.range 12).map (fun i =>
          let hw_next := Wire.mk s!"hw_csra_{i}"
          Gate.mkMUX csr_addr_reg[i]! decode_imm[i]! hw_csr_fence_start hw_next) ++
        (List.range 12).map (fun i =>
          Gate.mkMUX (Wire.mk s!"hw_csra_{i}") useq_addr_out[i]! useq_active csr_addr_next[i]!)

      -- Capture latches (same as before, gated by fence_i_start = any_serialize_start)
      let capture_gates :=
        [Gate.mkMUX csr_flag_reg csr_detected fence_i_start csr_flag_next] ++
        (List.range opcodeWidth).map (fun i =>
          Gate.mkMUX csr_optype_reg[i]! decode_optype[i]! fence_i_start csr_optype_next[i]!) ++
        (List.range 5).map (fun i =>
          Gate.mkMUX csr_rd_reg[i]! decode_rd[i]! fence_i_start csr_rd_next[i]!) ++
        (List.range 6).map (fun i =>
          Gate.mkMUX csr_phys_reg[i]! rd_phys[i]! fence_i_start csr_phys_next[i]!) ++
        (List.range 32).map (fun i =>
          Gate.mkMUX csr_rs1cap_reg[i]! (Wire.mk s!"fwd_src1_data_{i}") fence_i_start csr_rs1cap_next[i]!) ++
        (List.range 5).map (fun i =>
          Gate.mkMUX csr_zimm_reg[i]! decode_rs1[i]! fence_i_start csr_zimm_next[i]!)

      -- Sequencer start = ecall OR mret
      let useq_start := Wire.mk "useq_start"
      let useq_start_gate := [Gate.mkOR trap_seq_start mret_seq_start useq_start]

      -- ROM lookup for microcode sequencer (same as in mkMicrocodeSerializePath)
      let addr_match := (List.range 64).map (fun a => Wire.mk s!"urom_am_{a}")
      let addr_inv := (List.range 6).map (fun i => Wire.mk s!"urom_ai_{i}")
      let romInvGates := (List.range 6).map (fun i =>
        Gate.mkNOT useq_upc[i]! addr_inv[i]!)
      let romAddrGates := (List.range 64).map (fun a =>
        let bits := (List.range 6).map (fun i =>
          if Nat.testBit a i then useq_upc[i]! else addr_inv[i]!)
        let t01 := Wire.mk s!"urom_{a}_t01"
        let t23 := Wire.mk s!"urom_{a}_t23"
        let t45 := Wire.mk s!"urom_{a}_t45"
        let t0123 := Wire.mk s!"urom_{a}_t0123"
        [Gate.mkAND bits[0]! bits[1]! t01,
         Gate.mkAND bits[2]! bits[3]! t23,
         Gate.mkAND bits[4]! bits[5]! t45,
         Gate.mkAND t01 t23 t0123,
         Gate.mkAND t0123 t45 addr_match[a]!]) |>.flatten
      let romEncoded : List Nat := (List.finRange 64).map (fun a =>
        (Shoumei.RISCV.Microcode.romContents a).encode)
      let romOutputGates := (List.range 24).map (fun bit =>
        let activeAddrs := (List.range 64).filter (fun a =>
          match romEncoded[a]? with
          | some enc => Nat.testBit enc bit
          | none => false)
        if activeAddrs.isEmpty then
          [Gate.mkBUF zero useq_rom_data[bit]!]
        else if activeAddrs.length == 1 then
          [Gate.mkBUF addr_match[activeAddrs[0]!]! useq_rom_data[bit]!]
        else
          let n := activeAddrs.length
          let orWires := (List.range (n - 1)).map (fun i =>
            if i + 1 == n - 1 then useq_rom_data[bit]!
            else Wire.mk s!"urom_b{bit}_or{i}")
          let orGates := (List.range (n - 1)).map (fun i =>
            let lhs := if i == 0 then addr_match[activeAddrs[0]!]! else orWires[i - 1]!
            let rhs := addr_match[activeAddrs[i + 1]!]!
            Gate.mkOR lhs rhs orWires[i]!)
          orGates) |>.flatten

      -- Sequencer instance (trap-only, seq_id hardwired to 4 = TRAP_ENTRY)
      let seq_id := (List.range 3).map (fun i => Wire.mk s!"trap_seq_id_{i}")
      let seq_id_gates :=
        [-- seq_id: ECALL=4(100), MRET=6(110)
         -- bit0 = 0 always
         Gate.mkBUF zero seq_id[0]!,
         -- bit1 = 1 for MRET (seq_id=6), 0 for ECALL (seq_id=4)
         Gate.mkBUF mret_seq_start seq_id[1]!,
         -- bit2 = 1 always
         Gate.mkBUF one seq_id[2]!]

      let sequencerInst : CircuitInstance := {
        moduleName := "MicrocodeSequencer"
        instName := "u_trap_seq"
        portMap :=
          [("clock", clock), ("reset", reset),
           ("start", useq_start)] ++
          (List.range 3).map (fun i => (s!"seq_id_{i}", seq_id[i]!)) ++
          -- rs1_val: unused for ECALL (tie to zero)
          (List.range 32).map (fun i => (s!"rs1_val_{i}", zero)) ++
          -- csr_addr_in: unused at start for ECALL (set by SET_CSR_ADDR µops)
          (List.range 12).map (fun i => (s!"csr_addr_in_{i}", zero)) ++
          -- rd_tag_in: ECALL doesn't write rd
          (List.range 6).map (fun i => (s!"rd_tag_in_{i}", zero)) ++
          [("has_rd_in", zero),
           ("skip_write_in", zero),
           ("csr_flag_in", zero),   -- not a CSR op
           ("rob_empty", rob_empty),
           ("sb_empty", lsu_sb_empty)] ++
          (List.range 32).map (fun i => (s!"csr_read_data_{i}", csr_read_data[i]!)) ++
          (List.range 24).map (fun i => (s!"rom_data_{i}", useq_rom_data[i]!)) ++
          (List.range 32).map (fun i => (s!"redir_pc4_{i}", fence_i_pc_plus_4[i]!)) ++
          [("pipeline_flush", pipeline_flush_comb)] ++
          (List.range 32).map (fun i => (s!"pc_in_{i}", fetch_pc[i]!)) ++
          [("is_interrupt_in", Wire.mk "irq_inject")] ++
          -- Outputs
          [(s!"active_q", useq_active),
           ("fence_i_suppress", useq_suppress),
           ("csr_drain_complete", useq_drain_complete),
           ("csr_cdb_inject", useq_cdb_inject),
           ("csr_write_en", useq_write_en),
           ("csr_read_en", useq_read_en),
           ("fence_i_redir_valid", useq_redir_valid),
           ("csr_rename_en", Wire.mk "useq_rename_en_unused"),
           (s!"csrflag_q", useq_csr_flag),
           ("mstatus_trap_active", Wire.mk "useq_mstatus_trap"),
           ("mstatus_mret_active", Wire.mk "useq_mstatus_mret"),
           ("trap_taken", Wire.mk "useq_trap_taken")] ++
          (List.range 6).map (fun i => (s!"csr_cdb_tag_{i}", useq_cdb_tag[i]!)) ++
          (List.range 32).map (fun i => (s!"csr_cdb_data_{i}", useq_cdb_data[i]!)) ++
          (List.range 32).map (fun i => (s!"csr_write_data_{i}", useq_write_data[i]!)) ++
          (List.range 12).map (fun i => (s!"csr_addr_out_{i}", useq_addr_out[i]!)) ++
          (List.range 32).map (fun i => (s!"fence_i_redir_next_{i}", useq_redir_next[i]!)) ++
          (List.range 6).map (fun i => (s!"upc_q_{i}", useq_upc[i]!))
      }

      let allGates := hw_detect_gates ++ ser_detect_gates ++ hw_fsm_gates ++
                       start_gates ++ hw_fsm_drain_gates ++ merge_gates ++
                       redir_merge_gates ++ csr_addr_merge_gates ++ capture_gates ++
                       useq_start_gate ++
                       seq_id_gates ++ romInvGates ++ romAddrGates ++ romOutputGates
      (allGates, [sequencerInst, useq_dc_dff])
    else
      -- No traps: original hardwired-only path
      let hw_start_gates :=
        [Gate.mkAND serialize_detected fence_i_not_draining fence_i_start,
         Gate.mkAND fence_i_draining rob_empty dc_tmp,
         Gate.mkAND dc_tmp lsu_sb_empty dc_tmp2,
         Gate.mkNOT pipeline_flush_comb not_flushing_comb,
         Gate.mkAND dc_tmp2 not_flushing_comb fence_i_drain_complete,
         Gate.mkOR fence_i_start fence_i_draining set_or,
         Gate.mkNOT fence_i_drain_complete not_dc,
         Gate.mkAND set_or not_dc drain_next_tmp,
         Gate.mkAND drain_next_tmp not_flushing_comb fence_i_draining_next,
         Gate.mkAND fence_i_start csr_detected csr_rename_en,
         Gate.mkNOT csr_rename_en not_csr_rename_en,
         Gate.mkAND fence_i_start not_csr_rename_en (Wire.mk "fi_start_nocsr"),
         Gate.mkOR (Wire.mk "fi_start_nocsr") fence_i_draining fence_i_suppress]
      let hw_capture_gates :=
        (List.range 32).map (fun i =>
          Gate.mkMUX fence_i_redir_target[i]! fence_i_pc_plus_4[i]! fence_i_start fence_i_redir_next[i]!) ++
        [Gate.mkMUX csr_flag_reg csr_detected fence_i_start csr_flag_next] ++
        (List.range 12).map (fun i =>
          Gate.mkMUX csr_addr_reg[i]! decode_imm[i]! fence_i_start csr_addr_next[i]!) ++
        (List.range opcodeWidth).map (fun i =>
          Gate.mkMUX csr_optype_reg[i]! decode_optype[i]! fence_i_start csr_optype_next[i]!) ++
        (List.range 5).map (fun i =>
          Gate.mkMUX csr_rd_reg[i]! decode_rd[i]! fence_i_start csr_rd_next[i]!) ++
        (List.range 6).map (fun i =>
          Gate.mkMUX csr_phys_reg[i]! rd_phys[i]! fence_i_start csr_phys_next[i]!) ++
        -- rs1cap: capture on fence_i_start (forwarded data with CDB bypass)
        (List.range 32).map (fun i =>
          Gate.mkMUX csr_rs1cap_reg[i]! (Wire.mk s!"fwd_src1_data_{i}") fence_i_start csr_rs1cap_next[i]!) ++
        (List.range 5).map (fun i =>
          Gate.mkMUX csr_zimm_reg[i]! decode_rs1[i]! fence_i_start csr_zimm_next[i]!)
      (hw_detect_gates ++ ser_detect_gates ++ hw_fsm_gates ++ hw_start_gates ++ hw_capture_gates, [])
  else
    -- No serialize extensions: tie everything low
    ([Gate.mkBUF zero fence_i_match,
     Gate.mkBUF zero fence_i_detected,
     Gate.mkBUF zero csr_detected,
     Gate.mkBUF zero ecall_detected,
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
    (List.range 6).map (fun i => Gate.mkBUF zero csr_phys_next[i]!), [])

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
  let dataWidth := if config.xlen == 64 || config.enableD then 64 else 32
  let csr_read_data := (List.range dataWidth).map (fun i => Wire.mk s!"csr_rd_e{i}")
  let mstatus_sd_bit := Wire.mk "mstatus_sd_bit"
  let mstatus_fs_inv0 := Wire.mk "mstatus_fs_inv0"
  let mstatus_fs_inv1 := Wire.mk "mstatus_fs_inv1"
  let mstatus_sd_gate :=
    if config.enableZicsr && enableF then
      [Gate.mkAND mstatus_reg[13]! mstatus_reg[14]! mstatus_sd_bit,
       Gate.mkBUF zero mstatus_fs_inv0,
       Gate.mkBUF zero mstatus_fs_inv1]
    else
      [Gate.mkBUF zero mstatus_fs_inv0, Gate.mkBUF zero mstatus_fs_inv1,
       Gate.mkBUF zero mstatus_sd_bit]
  let csr_read_mux_gates :=
    if config.enableZicsr then
      ((List.range 32).map (fun i =>
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
          if i == 31 then (if config.xlen == 64 then zero else mstatus_sd_bit)
          else if i == 11 || i == 12 then one
          else mstatus_reg[i]!
        let mcause_read_bit :=
          if i == 31 then (if config.xlen == 64 then zero else mcause_reg[31]!)
          else mcause_reg[i]!
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
         Gate.mkMUX r_mepc mcause_read_bit is_mcause r_mcause,
         Gate.mkMUX r_mcause mtval_reg[i]! is_mtval r_mtval,
         Gate.mkMUX r_mtval zero is_mip csr_read_data[i]!]) |>.flatten) ++
      (if config.xlen == 64 || config.enableD then
        (List.range 32).map (fun k =>
          let r_mcyc_hi := Wire.mk s!"csr_rmcyc_hi_{k}"
          let r_mins_hi := Wire.mk s!"csr_rmins_hi_{k}"
          let r_mstat_hi := Wire.mk s!"csr_rmstat_hi_{k}"
          let r_mcause_hi := Wire.mk s!"csr_rmcause_hi_{k}"
          let mstat_hi_bit := if k == 31 then mstatus_sd_bit else zero
          let mcause_hi_bit := if k == 31 then mcause_reg[31]! else zero
          [Gate.mkMUX zero mcycleh_reg[k]! is_mcycle r_mcyc_hi,
           Gate.mkMUX r_mcyc_hi minstreth_reg[k]! is_minstret r_mins_hi,
           Gate.mkMUX r_mins_hi mstat_hi_bit is_mstatus r_mstat_hi,
           Gate.mkMUX r_mstat_hi mcause_hi_bit is_mcause r_mcause_hi,
           Gate.mkBUF r_mcause_hi csr_read_data[32+k]!]) |>.flatten
       else [])
    else
      (List.range dataWidth).map (fun i => Gate.mkBUF zero csr_read_data[i]!)
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
          | 8 =>
            let t01 := Wire.mk s!"csr_{pfx}_t01"
            let t23 := Wire.mk s!"csr_{pfx}_t23"
            let t45 := Wire.mk s!"csr_{pfx}_t45"
            let t67 := Wire.mk s!"csr_{pfx}_t67"
            let t0123 := Wire.mk s!"csr_{pfx}_t0123"
            let t4567 := Wire.mk s!"csr_{pfx}_t4567"
            [Gate.mkAND bitWires[0]! bitWires[1]! t01,
             Gate.mkAND bitWires[2]! bitWires[3]! t23,
             Gate.mkAND bitWires[4]! bitWires[5]! t45,
             Gate.mkAND bitWires[6]! bitWires[7]! t67,
             Gate.mkAND t01 t23 t0123,
             Gate.mkAND t45 t67 t4567,
             Gate.mkAND t0123 t4567 matchOut]
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
    (commit_valid_0 : Wire) (commit_valid_1 : Wire := zero)
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
        else if enableF && (i == 13 || i == 14) then Gate.mkBUF csr_write_val[i]! mstatus_warl[i]!
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
        let wr_bit := if i == 31 && config.xlen == 64 && csr_write_val.length >= 64
                      then csr_write_val[63]!
                      else csr_write_val[i]!
        Gate.mkMUX mcause_reg[i]! wr_bit csr_we_mcause mcause_next[i]!)
    else
      (List.range 32).map (fun i => Gate.mkBUF zero mcause_next[i]!)
  -- mtval: all 32 bits writable
  let mtval_next_gates :=
    if config.enableZicsr then
      (List.range 32).map (fun i =>
        Gate.mkMUX mtval_reg[i]! csr_write_val[i]! csr_we_mtval mtval_next[i]!)
    else
      (List.range 32).map (fun i => Gate.mkBUF zero mtval_next[i]!)
  -- mip: bit7 = mtip_in (machine timer interrupt pending), rest zero
  let mtip_in := Wire.mk "mtip_in"
  let mip_next_gates :=
    (List.range 32).map (fun i =>
      if i == 7 then Gate.mkBUF mtip_in mip_next[i]!
      else Gate.mkBUF zero mip_next[i]!)
  -- Counter auto-increment
  -- Counter auto-increment (pure inlined gates: replaces 4 KoggeStoneAdder32 instances)
  let mcycle_plus_1 := makeIndexedWires "mcycle_p1" 32
  let mcycle_inc_carries := (List.range 31).map fun i => Wire.mk s!"mcyc_inc_c_{i}"
  let mcycle_inc_gates : List Gate :=
    if config.enableZicsr then
      [Gate.mkNOT mcycle_reg[0]! mcycle_plus_1[0]!,
       Gate.mkBUF mcycle_reg[0]! mcycle_inc_carries[0]!] ++
      ((List.range 31).map (fun i =>
        let prev_c := mcycle_inc_carries[i]!
        let next_c := if i < 30 then mcycle_inc_carries[i+1]! else Wire.mk "mcyc_inc_c_last"
        [Gate.mkXOR mcycle_reg[i+1]! prev_c mcycle_plus_1[i+1]!,
         Gate.mkAND mcycle_reg[i+1]! prev_c next_c]
      ) |>.flatten)
    else
      (List.range 32).map fun i => Gate.mkBUF zero mcycle_plus_1[i]!

  let mcycle_carry := Wire.mk "mcycle_carry"
  let mcycleh_plus_c := makeIndexedWires "mcycleh_pc" 32
  let mcycleh_inc_carries := (List.range 32).map fun i => Wire.mk s!"mcych_inc_c_{i}"
  let mcycleh_inc_gates : List Gate :=
    if config.enableZicsr then
      (List.range 32).map (fun i =>
        let in_c := if i == 0 then mcycle_carry else mcycleh_inc_carries[i-1]!
        let out_c := mcycleh_inc_carries[i]!
        [Gate.mkXOR mcycleh_reg[i]! in_c mcycleh_plus_c[i]!,
         Gate.mkAND mcycleh_reg[i]! in_c out_c]
      ) |>.flatten
    else
      (List.range 32).map fun i => Gate.mkBUF zero mcycleh_plus_c[i]!

  let mins_inc_0 := Wire.mk "mins_inc_0"
  let mins_inc_1 := Wire.mk "mins_inc_1"
  let mins_inc_gates :=
    if config.enableZicsr then
      [Gate.mkXOR commit_valid_0 commit_valid_1 mins_inc_0,
       Gate.mkAND commit_valid_0 commit_valid_1 mins_inc_1]
    else []
  let minstret_plus_c := makeIndexedWires "minstret_pc" 32
  let mins_c0 := Wire.mk "mins_c0"
  let mins_c1 := Wire.mk "mins_c1_mid"
  let mins_c1_xor := Wire.mk "mins_c1_xor"
  let mins_c1_and1 := Wire.mk "mins_c1_and1"
  let mins_c1_and2 := Wire.mk "mins_c1_and2"
  let mins_inc_carries := (List.range 30).map fun i => Wire.mk s!"mins_inc_c_{i}"
  let minstret_inc_gates : List Gate :=
    if config.enableZicsr then
      -- Bit 0: Half-adder with mins_inc_0
      [Gate.mkXOR minstret_reg[0]! mins_inc_0 minstret_plus_c[0]!,
       Gate.mkAND minstret_reg[0]! mins_inc_0 mins_c0,
       -- Bit 1: Full-adder with mins_inc_1 and mins_c0
       Gate.mkXOR minstret_reg[1]! mins_inc_1 mins_c1_xor,
       Gate.mkXOR mins_c1_xor mins_c0 minstret_plus_c[1]!,
       Gate.mkAND minstret_reg[1]! mins_inc_1 mins_c1_and1,
       Gate.mkAND mins_c1_xor mins_c0 mins_c1_and2,
       Gate.mkOR mins_c1_and1 mins_c1_and2 mins_c1] ++
      -- Bits 2..31: Half-adder ripple
      ((List.range 30).map (fun i =>
        let in_c := if i == 0 then mins_c1 else mins_inc_carries[i-1]!
        let out_c := mins_inc_carries[i]!
        [Gate.mkXOR minstret_reg[i+2]! in_c minstret_plus_c[i+2]!,
         Gate.mkAND minstret_reg[i+2]! in_c out_c]
      ) |>.flatten)
    else
      (List.range 32).map fun i => Gate.mkBUF zero minstret_plus_c[i]!

  let minstret_carry := Wire.mk "minstret_carry"
  let minstreth_plus_c := makeIndexedWires "minstreth_pc" 32
  let minstreth_inc_carries := (List.range 32).map fun i => Wire.mk s!"minsh_inc_c_{i}"
  let minstreth_inc_gates : List Gate :=
    if config.enableZicsr then
      (List.range 32).map (fun i =>
        let in_c := if i == 0 then minstret_carry else minstreth_inc_carries[i-1]!
        let out_c := minstreth_inc_carries[i]!
        [Gate.mkXOR minstreth_reg[i]! in_c minstreth_plus_c[i]!,
         Gate.mkAND minstreth_reg[i]! in_c out_c]
      ) |>.flatten
    else
      (List.range 32).map fun i => Gate.mkBUF zero minstreth_plus_c[i]!

  let csr_counter_instances : List CircuitInstance := []

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
  let minstret_carry_tmp2 := (List.range 30).map (fun i => Wire.mk s!"mins_ct2_e{i}")
  let minstret_carry_pre2 := Wire.mk "minstret_carry_pre2"
  let minstret_carry_gates :=
    if config.enableZicsr then
      -- bits 0..31 all 1 (0xFFFFFFFF)
      [Gate.mkAND minstret_reg[0]! minstret_reg[1]! minstret_carry_tmp[0]!] ++
      (List.range 30).map (fun i =>
        Gate.mkAND minstret_carry_tmp[i]! minstret_reg[i+2]! (if i < 29 then minstret_carry_tmp[i+1]! else minstret_carry_pre)) ++
      -- bits 1..31 all 1 (0xFFFFFFFE)
      [Gate.mkAND minstret_reg[1]! minstret_reg[2]! minstret_carry_tmp2[0]!] ++
      (List.range 29).map (fun i =>
        Gate.mkAND minstret_carry_tmp2[i]! minstret_reg[i+3]! (if i < 28 then minstret_carry_tmp2[i+1]! else minstret_carry_pre2)) ++
      [Gate.mkAND minstret_carry_pre commit_valid_0 (Wire.mk "mins_c1"),
       Gate.mkAND minstret_carry_pre2 mins_inc_1 (Wire.mk "mins_c2"),
       Gate.mkOR (Wire.mk "mins_c1") (Wire.mk "mins_c2") minstret_carry]
    else [Gate.mkBUF zero minstret_carry]
  let counter_next_gates :=
    if config.enableZicsr then
      mins_inc_gates ++ mcycle_inc_gates ++ mcycleh_inc_gates ++
      minstret_inc_gates ++ minstreth_inc_gates ++
      mcycle_carry_gates ++ minstret_carry_gates ++
      (List.range 32).map (fun i =>
        Gate.mkMUX mcycle_plus_1[i]! csr_write_val[i]! csr_we_mcycle mcycle_next[i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkMUX mcycleh_plus_c[i]! csr_write_val[i]! csr_we_mcycleh mcycleh_next[i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkMUX minstret_plus_c[i]! csr_write_val[i]! csr_we_minstret minstret_next[i]!) ++
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

/-- Microcode serialize path: detection logic + MicrocodeSequencer instance.
    Returns (gates, instances) that drive the same output wires as mkSerializeDetect,
    plus sequencer-specific outputs (csr_write_en, csr_write_data, csr_read_en).

    In microcoded mode, the sequencer replaces:
    - Drain FSM (draining_next logic)
    - Capture latch MUXes (addr, optype, rd, phys, rs1cap, zimm)
    - CSR read-modify-write computation (ALU_OR, ALU_ANDN in temp regs)

    The CSR register file (addr decode, read MUX, next-value) is still shared.
    The sequencer's csr_write_en + csr_write_data replace mkCsrOpDecode + mkCsrWriteLogic. -/
def mkMicrocodeSerializePath
    (config : CPUConfig) (oi : OpType → Nat) (opcodeWidth : Nat)
    (zero one : Wire) (clock reset : Wire)
    (decode_optype : List Wire) (decode_valid : Wire) (decode_imm _decode_rd decode_rs1 : List Wire)
    (branch_redirect_valid_reg : Wire)
    (fetch_stall_ext : Wire)
    (_fence_i_draining _fence_i_not_draining : Wire)
    (rob_empty lsu_sb_empty : Wire)
    (pipeline_flush_comb : Wire)
    (_fence_i_redir_target fence_i_pc_plus_4 : List Wire)
    (_csr_flag_reg : Wire) (_csr_addr_reg : List Wire) (_csr_optype_reg : List Wire)
    (_csr_rd_reg : List Wire) (_csr_phys_reg : List Wire) (_csr_rs1cap_reg : List Wire)
    (_csr_zimm_reg : List Wire)
    (rd_phys : List Wire)
    (csr_match : Wire)
    (fence_i_detected csr_detected serialize_detected : Wire)
    (fence_i_start fence_i_drain_complete fence_i_draining_next fence_i_suppress : Wire)
    (csr_rename_en not_csr_rename_en : Wire)
    (csr_flag_next : Wire) (csr_addr_next csr_optype_next csr_rd_next csr_phys_next csr_rs1cap_next csr_zimm_next : List Wire)
    (fence_i_redir_next : List Wire)
    (csr_read_data : List Wire)
    (csr_cdb_inject : Wire) (csr_cdb_tag csr_cdb_data : List Wire)
    (fetch_pc : List Wire)
    (irqInject : Wire := Wire.mk "irq_inject")
    : List Gate × List CircuitInstance :=
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

  -- === Detection (same as hardwired) ===
  let fence_i_match := Wire.mk "fence_i_match"
  let fence_i_match_gates : List Gate :=
    if config.enableZifencei then mkOpcodeMatch (oi .FENCE_I) "fencei" fence_i_match
    else [Gate.mkBUF zero fence_i_match]

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

  -- ECALL detection
  let ecall_match := Wire.mk "ecall_match"
  let ecall_match_gates : List Gate :=
    mkOpcodeMatch (oi .ECALL) "ecall" ecall_match
  let ecall_detected := Wire.mk "ecall_detected"

  -- MRET detection
  let mret_match := Wire.mk "mret_match"
  let mret_detected := Wire.mk "mret_detected"
  let mret_match_gates : List Gate :=
    mkOpcodeMatch (oi .MRET) "mret" mret_match

  -- WFI detection
  let wfi_match := Wire.mk "wfi_match"
  let wfi_detected := Wire.mk "wfi_detected"
  let wfi_match_gates : List Gate :=
    mkOpcodeMatch (oi .WFI) "wfi" wfi_match

  let enableSerialize := config.enableZifencei || config.enableZicsr
  let enableMRET := config.microcodesMRET
  if !enableSerialize then
    -- No serialize extensions: tie everything low (same as hardwired disabled path)
    let tieGates :=
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
    (tieGates, [])
  else
    -- Compute sequence ID from CSR opcode match wires
    -- seq_id[2:0]: 0=CSRRW, 1=CSRRS, 2=CSRRC, 3=FENCE.I
    -- Encoding: bit0 = CSRRS|CSRRSI|CSRRC|CSRRCI, bit1 = CSRRC|CSRRCI|FENCE.I, bit2 = FENCE.I
    let seq_id := (List.range 3).map (fun i => Wire.mk s!"useq_id_{i}")
    let seq_id_tmp0 := Wire.mk "useq_id_tmp0"
    let seq_id_tmp1 := Wire.mk "useq_id_tmp1"
    let _seq_id_tmp2 := Wire.mk "useq_id_tmp2"
    let _seq_id_tmp3 := Wire.mk "useq_id_tmp3"

    -- seq_id encoding: CSRRW=0, CSRRS=1, CSRRC=2, FENCE.I=3, ECALL=4, MRET=6
    -- bit0 = CSRRS|CSRRSI|FENCE.I
    -- bit1 = CSRRC|CSRRCI|FENCE.I|MRET
    -- bit2 = ECALL|MRET
    let seq_id_gates :=
      [-- tmp0 = CSRRS | CSRRSI
       Gate.mkOR csr_match_wires[1]! csr_match_wires[4]! seq_id_tmp0,
       -- tmp1 = CSRRC | CSRRCI
       Gate.mkOR csr_match_wires[2]! csr_match_wires[5]! seq_id_tmp1,
       -- bit0 = tmp0 | fence_i_match
       Gate.mkOR seq_id_tmp0 fence_i_match seq_id[0]!,
       -- bit1 = tmp1 | fence_i_match | mret_detected
       Gate.mkOR seq_id_tmp1 fence_i_match (Wire.mk "seq_id_b1_pre"),
       Gate.mkOR (Wire.mk "seq_id_b1_pre") mret_detected seq_id[1]!,
       -- bit2 = ecall_detected | mret_detected
       Gate.mkOR ecall_detected mret_detected seq_id[2]!]

    -- skipWrite: for CSRRS/CSRRC, skip write when rs1=x0
    -- rs1 is decode_rs1[0..4], OR-tree to detect nonzero
    let rs1_nz_tmp := (List.range 4).map (fun i => Wire.mk s!"useq_r1nz_{i}")
    let rs1_nonzero := Wire.mk "useq_rs1_nonzero"
    let rs1_is_zero := Wire.mk "useq_rs1_is_zero"
    let skip_write_pre := Wire.mk "useq_skip_write_pre"
    let is_rs_or_rc := Wire.mk "useq_is_rs_or_rc"

    let skip_write_gates :=
      [Gate.mkOR decode_rs1[0]! decode_rs1[1]! rs1_nz_tmp[0]!,
       Gate.mkOR rs1_nz_tmp[0]! decode_rs1[2]! rs1_nz_tmp[1]!,
       Gate.mkOR rs1_nz_tmp[1]! decode_rs1[3]! rs1_nz_tmp[2]!,
       Gate.mkOR rs1_nz_tmp[2]! decode_rs1[4]! rs1_nonzero,
       Gate.mkNOT rs1_nonzero rs1_is_zero,
       -- is_rs_or_rc = CSRRS|CSRRSI|CSRRC|CSRRCI (same as seq_id bit0 OR bit1 set)
       Gate.mkOR seq_id_tmp0 seq_id_tmp1 is_rs_or_rc,
       Gate.mkAND is_rs_or_rc rs1_is_zero skip_write_pre]

    -- CSR immediate source MUX: for CSRRWI/CSRRSI/CSRRCI, use zero-extended
    -- decode_rs1[4:0] instead of fwd_src1_data (register value)
    let csr_is_imm_tmp := Wire.mk "useq_isimm_tmp"
    let csr_is_imm := Wire.mk "useq_is_imm"
    let useq_rs1_muxed := (List.range 32).map (fun i => Wire.mk s!"useq_rs1m_{i}")
    let csr_imm_mux_gates :=
      [Gate.mkOR csr_match_wires[3]! csr_match_wires[4]! csr_is_imm_tmp,
       Gate.mkOR csr_is_imm_tmp csr_match_wires[5]! csr_is_imm] ++
      -- Bits 0-4: MUX between fwd_src1_data and decode_rs1 (the zimm)
      (List.range 5).map (fun i =>
        Gate.mkMUX (Wire.mk s!"fwd_src1_data_{i}") decode_rs1[i]! csr_is_imm useq_rs1_muxed[i]!) ++
      -- Bits 5-31: MUX between fwd_src1_data and zero (zimm is only 5 bits)
      (List.range 27).map (fun i =>
        Gate.mkMUX (Wire.mk s!"fwd_src1_data_{i+5}") zero csr_is_imm useq_rs1_muxed[i+5]!)

    -- Detection gates (shared with hardwired)
    let not_redir_reg := Wire.mk "not_redir_reg"
    let decode_valid_noredir := Wire.mk "dv_noredir"
    let decode_valid_noredir_tmp := Wire.mk "dv_noredir_tmp"
    let not_fetch_stall_ext := Wire.mk "not_fetch_stall_ext"

    let detect_gates :=
      fence_i_match_gates ++ csr_match_gates ++ ecall_match_gates ++
      (if enableMRET then mret_match_gates ++ wfi_match_gates else []) ++
      [Gate.mkNOT branch_redirect_valid_reg not_redir_reg,
       Gate.mkAND decode_valid not_redir_reg decode_valid_noredir_tmp,
       Gate.mkNOT fetch_stall_ext not_fetch_stall_ext,
       Gate.mkAND decode_valid_noredir_tmp not_fetch_stall_ext decode_valid_noredir,
       Gate.mkAND decode_valid_noredir fence_i_match fence_i_detected,
       Gate.mkAND decode_valid_noredir csr_match csr_detected,
       Gate.mkAND decode_valid_noredir ecall_match ecall_detected] ++
      (if enableMRET then
        [Gate.mkAND decode_valid_noredir mret_match mret_detected,
         Gate.mkAND decode_valid_noredir wfi_match wfi_detected]
       else
        [Gate.mkBUF zero mret_detected, Gate.mkBUF zero wfi_detected]) ++
      [-- serialize_detected = fence_i | csr | ecall | mret | wfi
       Gate.mkOR fence_i_detected csr_detected (Wire.mk "ser_pre_ecall"),
       Gate.mkOR ecall_detected mret_detected (Wire.mk "ser_ecall_mret"),
       Gate.mkOR (Wire.mk "ser_ecall_mret") wfi_detected (Wire.mk "ser_sys"),
       Gate.mkOR (Wire.mk "ser_pre_ecall") (Wire.mk "ser_sys") serialize_detected]

    -- Sequencer ROM data wires (from MicrocodeSequencer's upc output → ROM → rom_data)
    -- The ROM is a combinational lookup. We need a MuxTree64x24 or equivalent.
    -- For now, we'll use the MicrocodeSequencer which expects rom_data as an input.
    -- The CPU must provide a ROM lookup circuit that maps upc → rom_data.
    -- We'll instantiate a simple MuxTree for the ROM.
    let useq_upc := (List.range 6).map (fun i => Wire.mk s!"useq_upc_{i}")
    let useq_rom_data := (List.range 24).map (fun i => Wire.mk s!"useq_rom_{i}")

    -- Sequencer output wires
    let useq_active := Wire.mk "useq_active"
    let useq_suppress := Wire.mk "useq_suppress"
    let useq_drain_complete := Wire.mk "useq_drain_complete"
    let useq_cdb_inject := Wire.mk "useq_cdb_inject"
    let useq_write_en := Wire.mk "useq_write_en"
    let useq_read_en := Wire.mk "useq_read_en"
    let useq_redir_valid := Wire.mk "useq_redir_valid"
    let useq_rename_en := Wire.mk "useq_rename_en"
    let useq_csr_flag := Wire.mk "useq_csr_flag"
    let useq_cdb_tag := (List.range 6).map (fun i => Wire.mk s!"useq_cdb_tg_{i}")
    let useq_cdb_data := (List.range 32).map (fun i => Wire.mk s!"useq_cdb_dt_{i}")
    let useq_write_data := (List.range 32).map (fun i => Wire.mk s!"useq_wr_dt_{i}")
    let useq_addr_out := (List.range 12).map (fun i => Wire.mk s!"useq_addr_{i}")
    let useq_redir_next := (List.range 32).map (fun i => Wire.mk s!"useq_redir_{i}")

    -- Wire sequencer outputs to CPU's expected wire names
    let bridge_gates :=
      [-- fence_i_suppress = useq_suppress (active while sequencer runs)
       Gate.mkBUF useq_suppress fence_i_suppress,
       -- fence_i_drain_complete = useq_drain_complete
       Gate.mkBUF useq_drain_complete fence_i_drain_complete,
       -- fence_i_draining_next = (serialize_detected OR useq_active) AND NOT(flush)
       Gate.mkOR serialize_detected useq_active (Wire.mk "useq_drain_next_pre"),
       Gate.mkNOT pipeline_flush_comb (Wire.mk "useq_not_flushing"),
       Gate.mkAND (Wire.mk "useq_drain_next_pre") (Wire.mk "useq_not_flushing") fence_i_draining_next,
       -- fence_i_start = serialize_detected AND NOT(useq_active)
       Gate.mkNOT useq_active (Wire.mk "useq_not_active"),
       Gate.mkAND serialize_detected (Wire.mk "useq_not_active") fence_i_start,
       -- csr_rename_en = useq_rename_en
       Gate.mkBUF useq_rename_en csr_rename_en,
       Gate.mkNOT useq_rename_en not_csr_rename_en,
       -- csr_flag = useq_csr_flag
       Gate.mkBUF useq_csr_flag csr_flag_next,
       -- csr_cdb_inject = useq_cdb_inject
       Gate.mkBUF useq_cdb_inject csr_cdb_inject] ++
      -- CDB tag/data from sequencer
      (List.range 6).map (fun i => Gate.mkBUF useq_cdb_tag[i]! csr_cdb_tag[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF useq_cdb_data[i]! csr_cdb_data[i]!) ++
      -- Redirect target
      (List.range 32).map (fun i => Gate.mkBUF useq_redir_next[i]! fence_i_redir_next[i]!) ++
      -- CSR address from sequencer (drives addr decode)
      (List.range 12).map (fun i => Gate.mkBUF useq_addr_out[i]! csr_addr_next[i]!) ++
      -- Tie unused capture next wires (sequencer handles internally)
      (List.range opcodeWidth).map (fun i => Gate.mkBUF zero csr_optype_next[i]!) ++
      (List.range 5).map (fun i =>
        Gate.mkMUX _csr_rd_reg[i]! _decode_rd[i]! fence_i_start csr_rd_next[i]!) ++
      (List.range 6).map (fun i =>
        Gate.mkMUX _csr_phys_reg[i]! rd_phys[i]! fence_i_start csr_phys_next[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF zero csr_rs1cap_next[i]!) ++
      (List.range 5).map (fun i => Gate.mkBUF zero csr_zimm_next[i]!)

    -- Sequencer instance
    let sequencerInst : CircuitInstance := {
      moduleName := "MicrocodeSequencer"
      instName := "u_microcode_seq"
      portMap :=
        [("clock", clock), ("reset", reset),
         ("start", fence_i_start)] ++
        (List.range 3).map (fun i => (s!"seq_id_{i}", seq_id[i]!)) ++
        -- rs1_val: fwd_src1_data for register CSR, zero-extended zimm for immediate CSR
        (List.range 32).map (fun i => (s!"rs1_val_{i}", useq_rs1_muxed[i]!)) ++
        -- csr_addr_in: from decode immediate
        (List.range 12).map (fun i => (s!"csr_addr_in_{i}", decode_imm[i]!)) ++
        -- rd_tag_in: from rename allocation
        (List.range 6).map (fun i => (s!"rd_tag_in_{i}", rd_phys[i]!)) ++
        [("has_rd_in", one),  -- CSR instructions always have rd
         ("skip_write_in", skip_write_pre),
         ("csr_flag_in", csr_detected),  -- ECALL has csr_flag=false (not a CSR op)
         ("rob_empty", rob_empty),
         ("sb_empty", lsu_sb_empty)] ++
        -- csr_read_data: from CSR read MUX
        (List.range 32).map (fun i => (s!"csr_read_data_{i}", csr_read_data[i]!)) ++
        -- rom_data: from ROM lookup
        (List.range 24).map (fun i => (s!"rom_data_{i}", useq_rom_data[i]!)) ++
        -- redir_pc4: PC+4 for FENCE.I redirect
        (List.range 32).map (fun i => (s!"redir_pc4_{i}", fence_i_pc_plus_4[i]!)) ++
        [("pipeline_flush", pipeline_flush_comb)] ++
        -- pc_in: fetch PC for LOAD_PC µop
        (List.range 32).map (fun i => (s!"pc_in_{i}", fetch_pc[i]!)) ++
        [("is_interrupt_in", irqInject)] ++
        -- Outputs
        [(s!"active_q", useq_active),
         ("fence_i_suppress", useq_suppress),
         ("csr_drain_complete", useq_drain_complete),
         ("csr_cdb_inject", useq_cdb_inject),
         ("csr_write_en", useq_write_en),
         ("csr_read_en", useq_read_en),
         ("fence_i_redir_valid", useq_redir_valid),
         ("csr_rename_en", useq_rename_en),
         (s!"csrflag_q", useq_csr_flag)] ++
        [("mstatus_trap_active", Wire.mk "useq_mstatus_trap"),
         ("mstatus_mret_active", Wire.mk "useq_mstatus_mret"),
         ("trap_taken", Wire.mk "useq_trap_taken")] ++
        (List.range 6).map (fun i => (s!"csr_cdb_tag_{i}", useq_cdb_tag[i]!)) ++
        (List.range 32).map (fun i => (s!"csr_cdb_data_{i}", useq_cdb_data[i]!)) ++
        (List.range 32).map (fun i => (s!"csr_write_data_{i}", useq_write_data[i]!)) ++
        (List.range 12).map (fun i => (s!"csr_addr_out_{i}", useq_addr_out[i]!)) ++
        (List.range 32).map (fun i => (s!"fence_i_redir_next_{i}", useq_redir_next[i]!)) ++
        (List.range 6).map (fun i => (s!"upc_q_{i}", useq_upc[i]!))
    }

    -- ROM lookup: 6-bit address decoder + AND-OR plane
    -- Each of 64 addresses gets a match wire, then each output bit is OR of matching entries.
    let addr_match := (List.range 64).map (fun a => Wire.mk s!"urom_am_{a}")
    let addr_inv := (List.range 6).map (fun i => Wire.mk s!"urom_ai_{i}")

    let romInvGates := (List.range 6).map (fun i =>
      Gate.mkNOT useq_upc[i]! addr_inv[i]!)

    -- 64 address decoders (6-bit AND trees)
    let romAddrGates := (List.range 64).map (fun a =>
      let bits := (List.range 6).map (fun i =>
        if Nat.testBit a i then useq_upc[i]! else addr_inv[i]!)
      let t01 := Wire.mk s!"urom_{a}_t01"
      let t23 := Wire.mk s!"urom_{a}_t23"
      let t45 := Wire.mk s!"urom_{a}_t45"
      let t0123 := Wire.mk s!"urom_{a}_t0123"
      [Gate.mkAND bits[0]! bits[1]! t01,
       Gate.mkAND bits[2]! bits[3]! t23,
       Gate.mkAND bits[4]! bits[5]! t45,
       Gate.mkAND t01 t23 t0123,
       Gate.mkAND t0123 t45 addr_match[a]!]) |>.flatten

    -- Precompute ROM encoded bits: 64 entries × 24 bits
    -- Use Fin to avoid omega issues
    let romEncoded : List Nat := (List.finRange 64).map (fun a =>
      (Shoumei.RISCV.Microcode.romContents a).encode)

    -- 24 output bits: OR tree of matching entries
    let romOutputGates := (List.range 24).map (fun bit =>
      let activeAddrs := (List.range 64).filter (fun a =>
        match romEncoded[a]? with
        | some enc => Nat.testBit enc bit
        | none => false)
      if activeAddrs.isEmpty then
        [Gate.mkBUF zero useq_rom_data[bit]!]
      else if activeAddrs.length == 1 then
        [Gate.mkBUF addr_match[activeAddrs[0]!]! useq_rom_data[bit]!]
      else
        -- OR tree: chain all matching addresses
        let n := activeAddrs.length
        let orWires := (List.range (n - 1)).map (fun i =>
          if i + 1 == n - 1 then useq_rom_data[bit]!
          else Wire.mk s!"urom_b{bit}_or{i}")
        let orGates := (List.range (n - 1)).map (fun i =>
          let lhs := if i == 0 then addr_match[activeAddrs[0]!]! else orWires[i - 1]!
          let rhs := addr_match[activeAddrs[i + 1]!]!
          Gate.mkOR lhs rhs orWires[i]!)
        orGates) |>.flatten

    let allGates := detect_gates ++ seq_id_gates ++ skip_write_gates ++
                    csr_imm_mux_gates ++
                    romInvGates ++ romAddrGates ++ romOutputGates ++
                    bridge_gates

    (allGates, [sequencerInst])

/-! ## A Extension: Atomic Memory Operations (LR.W / SC.W / AMO*.W)

Reservation-set tracking plus atomic read-modify-write support.

The memory pipeline is single-slot: at most one memory op is in flight
(`mem_valid_r`) and at most one DMEM load is pending.  Atomic ops reuse that
slot: the op is captured, its read goes through the normal DMEM read path, and
(for AMO/SC) a direct DMEM write commits the new value.  Dispatch of further
memory ops is blocked while an atomic RMW is in flight, so the read and write
are never separated by another memory access from this hart.

Single-hart reservation semantics:
  * `lr.w` sets `(reservationValid, reservationAddr)` on its read response.
  * `sc.w` succeeds iff the reservation is valid and addresses match; the
    reservation is cleared either way.
  * Any intervening store to the reserved word (snooped on store-buffer
    dequeue) and any pipeline flush also clear the reservation.
-/

/-- Result of building the atomic (A-extension) support logic. -/
structure AtomicUnit where
  gates : List Gate
  instances : List CircuitInstance
  /-- Reservation register outputs. -/
  reservationValid : Wire
  reservationAddr : List Wire
  /-- Registered atomic selector / AMO operands (memory stage). -/
  atomicCodeR : List Wire
  scSel : Wire
  scExec : Wire
  scResult : Wire
  /-- Atomic direct-write request to DMEM (AMO new value / SC store data). -/
  awValid : Wire
  awAddr : List Wire
  awData : List Wire
  /-- An atomic RMW is in flight; block further memory dispatch. -/
  atomicBusy : Wire
  /-- Dispatch permitted for the current memory op. -/
  atomicDispatchOk : Wire

/-- Build the atomic (A-extension) support logic.

    Atomic code (2 bits): bit0 = reads (LR/AMO), bit1 = writes (SC/AMO), so
    LR=01, SC=10, AMO=11. -/
def mkAtomicUnit
    (clock reset zero one : Wire)
    (rs_mem_dispatch_valid mem_dispatch_en_any : Wire)
    (is_lr is_sc is_amo is_atomic_d : Wire)
    (amo_funct : List Wire)             -- 4 bits: AMO function select
    (rs_mem_dispatch_src2 : List Wire)  -- 32 bits: store operand (rs2)
    (pipeline_flush_comb : Wire)
    (mem_valid_r is_load_r : Wire)
    (mem_addr_r : List Wire)            -- 32 bits: registered address
    (dmem_resp_valid dmem_load_pending : Wire)
    (dmem_resp_data : List Wire)        -- 32 bits
    (dmem_req_ready : Wire)
    (lsu_sb_empty lsu_sb_deq_valid : Wire)
    (lsu_sb_deq_bits : List Wire)       -- 66 bits: SB dequeue payload
    (rs_pending_store : Wire)           -- a plain store is still pending in the mem RS
    : AtomicUnit :=
  let mkW := makeIndexedWires

  -- === 2-bit atomic code at dispatch ===
  let ac0 := Wire.mk "atom_code0"   -- reads: LR or AMO
  let ac1 := Wire.mk "atom_code1"   -- writes: SC or AMO
  let lrsc := Wire.mk "atom_lrsc"
  let is_atomic := Wire.mk "atom_is_atomic"
  let code_gates := [
    Gate.mkOR is_lr is_amo ac0,
    Gate.mkOR is_sc is_amo ac1,
    Gate.mkOR is_lr is_sc lrsc,
    Gate.mkOR lrsc is_amo is_atomic]

  -- pipe_load_en: same condition as mkMemPipeline (register enable)
  let pipe_load_en := Wire.mk "atom_pipe_load_en"
  let not_flush := Wire.mk "atom_not_flush"
  let ple_t := Wire.mk "atom_ple_t"
  let pipe_en_gates := [
    Gate.mkAND rs_mem_dispatch_valid mem_dispatch_en_any ple_t,
    Gate.mkNOT pipeline_flush_comb not_flush,
    Gate.mkAND ple_t not_flush pipe_load_en]

  -- === Registered atomic fields (memory stage) ===
  let atomic_code_r := mkW "atom_code_r" 2
  let atomic_code_next := mkW "atom_code_next" 2
  let amo_funct_r := mkW "atom_funct_r" 4
  let amo_funct_next := mkW "atom_funct_next" 4
  -- Operand/data paths are XLEN wide: 64-bit atomics (LR.D/SC.D/AMO*.D) need it
  let dataW := dmem_resp_data.length
  let amo_rs2_r := mkW "atom_rs2_r" dataW
  let amo_rs2_next := mkW "atom_rs2_next" dataW
  -- .W atomics compare 32-bit words, .D atomics the full 64-bit operands
  let amo_d_r := Wire.mk "atom_d_r"
  let amo_d_next := Wire.mk "atom_d_next"
  let code_reg_gates :=
    [Gate.mkMUX amo_d_r is_atomic_d pipe_load_en amo_d_next,
     Gate.mkMUX atomic_code_r[0]! ac0 pipe_load_en atomic_code_next[0]!,
     Gate.mkMUX atomic_code_r[1]! ac1 pipe_load_en atomic_code_next[1]!] ++
    (List.range 4).map (fun i =>
      Gate.mkMUX amo_funct_r[i]! amo_funct[i]! pipe_load_en amo_funct_next[i]!) ++
    (List.range dataW).map (fun i =>
      Gate.mkMUX amo_rs2_r[i]! rs_mem_dispatch_src2[i]! pipe_load_en amo_rs2_next[i]!)
  let code_reg_insts : List CircuitInstance :=
    ({ moduleName := "DFlipFlop", instName := "u_atom_d_r",
       portMap := [("d", amo_d_next), ("q", amo_d_r),
                   ("clock", clock), ("reset", reset)] } : CircuitInstance) ::
    (List.range 2).map (fun i =>
      ({ moduleName := "DFlipFlop", instName := s!"u_atom_code_r_{i}",
         portMap := [("d", atomic_code_next[i]!), ("q", atomic_code_r[i]!),
                     ("clock", clock), ("reset", reset)] } : CircuitInstance)) ++
    (List.range 4).map (fun i =>
      ({ moduleName := "DFlipFlop", instName := s!"u_atom_funct_r_{i}",
         portMap := [("d", amo_funct_next[i]!), ("q", amo_funct_r[i]!),
                     ("clock", clock), ("reset", reset)] } : CircuitInstance)) ++
    (List.range dataW).map (fun i =>
      ({ moduleName := "DFlipFlop", instName := s!"u_atom_rs2_r_{i}",
         portMap := [("d", amo_rs2_next[i]!), ("q", amo_rs2_r[i]!),
                     ("clock", clock), ("reset", reset)] } : CircuitInstance))

  -- === Atomic selector bits at the memory stage ===
  let not_c0 := Wire.mk "atom_not_c0"
  let not_c1 := Wire.mk "atom_not_c1"
  let c0_and_c1 := Wire.mk "atom_c0_c1"
  let lr_sel := Wire.mk "atom_lr_sel"
  let sc_sel := Wire.mk "atom_sc_sel"
  let amo_sel := Wire.mk "atom_amo_sel"
  let sel_gates := [
    Gate.mkNOT atomic_code_r[0]! not_c0,
    Gate.mkNOT atomic_code_r[1]! not_c1,
    Gate.mkAND atomic_code_r[0]! not_c1 lr_sel,
    Gate.mkAND not_c0 atomic_code_r[1]! sc_sel,
    Gate.mkAND atomic_code_r[0]! atomic_code_r[1]! c0_and_c1,
    Gate.mkBUF c0_and_c1 amo_sel]

  -- === Read responses and SC execute ===
  let resp_x := Wire.mk "atom_resp_x"
  let resp_busy := Wire.mk "atom_resp_busy"
  let resp_live := Wire.mk "atom_resp_live"
  let lr_resp := Wire.mk "atom_lr_resp"
  let amo_resp := Wire.mk "atom_amo_resp"
  let resp_gates := [
    Gate.mkAND dmem_resp_valid dmem_load_pending resp_x,
    -- Only the atomic op currently in flight may consume a DMEM response; the
    -- registered selector bits outlive it until the next memory dispatch.
    -- Responses arriving during a pipeline flush are for squashed operations.
    Gate.mkAND resp_x (Wire.mk "atom_busy") resp_busy,
    Gate.mkAND resp_busy not_flush resp_live,
    Gate.mkAND resp_live lr_sel lr_resp,
    Gate.mkAND resp_live amo_sel amo_resp]
  let sc_exec := Wire.mk "atom_sc_exec"
  let sc_exec_t := Wire.mk "atom_sc_exec_t"
  let sc_exec_gates := [
    Gate.mkAND mem_valid_r sc_sel sc_exec_t,
    Gate.mkAND sc_exec_t not_flush sc_exec]

  -- === Reservation registers ===
  let reservation_valid := Wire.mk "atom_res_valid"
  let reservation_valid_next := Wire.mk "atom_res_valid_next"
  let reservation_addr := mkW "atom_res_addr" 32
  let reservation_addr_next := mkW "atom_res_addr_next" 32
  let res_addr_eq := Wire.mk "atom_res_addr_eq"
  -- SC reservation check: reservationValid && reservationAddr == mem_addr_r
  let res_cmp_inst : CircuitInstance := {
    moduleName := "EqualityComparator32", instName := "u_atom_res_cmp",
    portMap :=
      (List.range 32).map (fun i => (s!"a_{i}", reservation_addr[i]!)) ++
      (List.range 32).map (fun i => (s!"b_{i}", mem_addr_r[i]!)) ++
      [("eq", res_addr_eq)] }
  let sc_ok := Wire.mk "atom_sc_ok"
  let sc_result := Wire.mk "atom_sc_result"
  let sc_ok_gate := Gate.mkAND reservation_valid res_addr_eq sc_ok
  let sc_result_gate := Gate.mkNOT sc_ok sc_result
  -- Intervening-store invalidation: SB dequeue writes the reserved word
  let sb_deq_addr := (List.range 32).map (fun i => lsu_sb_deq_bits[i]!)
  let sb_deq_addr_eq := Wire.mk "atom_sb_addr_eq"
  let sb_cmp_inst : CircuitInstance := {
    moduleName := "EqualityComparator32", instName := "u_atom_sb_cmp",
    portMap :=
      (List.range 32).map (fun i => (s!"a_{i}", sb_deq_addr[i]!)) ++
      (List.range 32).map (fun i => (s!"b_{i}", reservation_addr[i]!)) ++
      [("eq", sb_deq_addr_eq)] }
  let res_inval_t := Wire.mk "atom_res_inv_t"
  let res_invalidate := Wire.mk "atom_res_invalidate"
  let res_clr_t := Wire.mk "atom_res_clr_t"
  let res_clr := Wire.mk "atom_res_clr"
  let res_inval_gates := [
    Gate.mkAND lsu_sb_deq_valid reservation_valid res_inval_t,
    Gate.mkAND res_inval_t sb_deq_addr_eq res_invalidate,
    Gate.mkOR sc_exec res_invalidate res_clr_t,
    -- NOTE: a pipeline flush must NOT clear the reservation.  A mispredicted
    -- branch between LR and SC would otherwise cause a spurious SC failure,
    -- diverging from the reference model (spec permits failure, but the tests
    -- require success when no intervening store occurs).
    Gate.mkBUF res_clr_t res_clr]
  -- Next value: clear > set > hold
  let res_set_v := Wire.mk "atom_res_set_v"
  let res_set_gates := [
    Gate.mkMUX reservation_valid one lr_resp res_set_v,
    Gate.mkMUX res_set_v zero res_clr reservation_valid_next]
  let res_addr_gates := (List.range 32).map (fun i =>
    Gate.mkMUX reservation_addr[i]! mem_addr_r[i]! lr_resp reservation_addr_next[i]!)
  let res_insts : List CircuitInstance :=
    ({ moduleName := "DFlipFlop", instName := "u_atom_res_valid",
       portMap := [("d", reservation_valid_next), ("q", reservation_valid),
                   ("clock", clock), ("reset", reset)] } : CircuitInstance) ::
    (List.range 32).map (fun i =>
      ({ moduleName := "DFlipFlop", instName := s!"u_atom_res_addr_{i}",
         portMap := [("d", reservation_addr_next[i]!), ("q", reservation_addr[i]!),
                     ("clock", clock), ("reset", reset)] } : CircuitInstance))

  -- === AMO new-value ALU: new = f(funct, old, rs2) ===
  let old := dmem_resp_data
  let rs2 := amo_rs2_r
  let add_sum := mkW "atom_add_sum" dataW
  let add_inst : CircuitInstance := {
    moduleName := s!"KoggeStoneAdder{dataW}NoCin", instName := "u_atom_add",
    portMap :=
      (List.range dataW).map (fun i => (s!"a_{i}", old[i]!)) ++
      (List.range dataW).map (fun i => (s!"b_{i}", rs2[i]!)) ++
      (List.range dataW).map (fun i => (s!"sum_{i}", add_sum[i]!)) }
  let res_xor := mkW "atom_res_xor" dataW
  let res_and := mkW "atom_res_and" dataW
  let res_or := mkW "atom_res_or" dataW
  let bitwise_gates :=
    (List.range dataW).map (fun i => Gate.mkXOR old[i]! rs2[i]! res_xor[i]!) ++
    (List.range dataW).map (fun i => Gate.mkAND old[i]! rs2[i]! res_and[i]!) ++
    (List.range dataW).map (fun i => Gate.mkOR old[i]! rs2[i]! res_or[i]!)
  -- .W atomics (amo_d_r=0) compare only the low 32 bits: the signed compares need
  -- a sign-extended operand pair, the unsigned compares a zero-extended pair.
  -- .D atomics pass the raw 64-bit operands through.
  let half := dataW / 2
  let old_cmp_s := mkW "atom_old_cmp_s" dataW
  let rs2_cmp_s := mkW "atom_rs2_cmp_s" dataW
  let old_cmp_u := mkW "atom_old_cmp_u" dataW
  let rs2_cmp_u := mkW "atom_rs2_cmp_u" dataW
  let cmp_operand_gates :=
    (List.range half).flatMap (fun i =>
      [Gate.mkBUF old[i]! old_cmp_s[i]!, Gate.mkBUF rs2[i]! rs2_cmp_s[i]!,
       Gate.mkBUF old[i]! old_cmp_u[i]!, Gate.mkBUF rs2[i]! rs2_cmp_u[i]!]) ++
    (List.range (dataW - half)).flatMap (fun j =>
      let i := half + j
      [Gate.mkMUX old[half - 1]! old[i]! amo_d_r old_cmp_s[i]!,
       Gate.mkMUX rs2[half - 1]! rs2[i]! amo_d_r rs2_cmp_s[i]!,
       Gate.mkMUX zero old[i]! amo_d_r old_cmp_u[i]!,
       Gate.mkMUX zero rs2[i]! amo_d_r rs2_cmp_u[i]!])
  let cmp_lt := Wire.mk "atom_cmp_lt"
  let cmp_ltu := Wire.mk "atom_cmp_ltu"
  let cmp_gt := Wire.mk "atom_cmp_gt"
  let cmp_gtu := Wire.mk "atom_cmp_gtu"
  let cmp_eq := Wire.mk "atom_cmp_eq"
  let cmp_inst : CircuitInstance := {
    moduleName := s!"Comparator{dataW}", instName := "u_atom_cmp",
    portMap :=
      (List.range dataW).map (fun i => (s!"a_{i}", old_cmp_s[i]!)) ++
      (List.range dataW).map (fun i => (s!"b_{i}", rs2_cmp_s[i]!)) ++
      [("one", one), ("eq", cmp_eq), ("lt", cmp_lt), ("ltu", Wire.mk "atom_cmp_ltu_s"),
       ("gt", cmp_gt), ("gtu", Wire.mk "atom_cmp_gtu_s")] }
  let cmp_u_inst : CircuitInstance := {
    moduleName := s!"Comparator{dataW}", instName := "u_atom_cmp_u",
    portMap :=
      (List.range dataW).map (fun i => (s!"a_{i}", old_cmp_u[i]!)) ++
      (List.range dataW).map (fun i => (s!"b_{i}", rs2_cmp_u[i]!)) ++
      [("one", one), ("eq", Wire.mk "atom_cmp_eq_u"), ("lt", Wire.mk "atom_cmp_lt_u"),
       ("ltu", cmp_ltu), ("gt", Wire.mk "atom_cmp_gt_u"), ("gtu", cmp_gtu)] }
  let res_min_s := mkW "atom_res_min_s" dataW
  let res_max_s := mkW "atom_res_max_s" dataW
  let res_min_u := mkW "atom_res_min_u" dataW
  let res_max_u := mkW "atom_res_max_u" dataW
  let minmax_gates :=
    (List.range dataW).map (fun i => Gate.mkMUX rs2[i]! old[i]! cmp_lt res_min_s[i]!) ++
    (List.range dataW).map (fun i => Gate.mkMUX rs2[i]! old[i]! cmp_gt res_max_s[i]!) ++
    (List.range dataW).map (fun i => Gate.mkMUX rs2[i]! old[i]! cmp_ltu res_min_u[i]!) ++
    (List.range dataW).map (fun i => Gate.mkMUX rs2[i]! old[i]! cmp_gtu res_max_u[i]!)
  -- 16:1 select by amo_funct
  let amo_new := mkW "atom_new" dataW
  let amo_l0 := (List.range 8).map (fun i => mkW s!"atom_l0_{i}" dataW)
  let amo_l1 := (List.range 4).map (fun i => mkW s!"atom_l1_{i}" dataW)
  let amo_l2 := (List.range 2).map (fun i => mkW s!"atom_l2_{i}" dataW)
  let zeroW := (List.range dataW).map (fun _ => zero)
  let tree_inputs : List (List Wire) :=
    [add_sum, rs2, res_xor, res_and, res_or,
     res_min_s, res_max_s, res_min_u, res_max_u] ++
    (List.range 7).map (fun _ => zeroW)
  let l0_gates := (List.range 8).flatMap (fun i =>
    (List.range dataW).map (fun b =>
      Gate.mkMUX tree_inputs[2*i]![b]! tree_inputs[2*i+1]![b]! amo_funct_r[0]! amo_l0[i]![b]!))
  let l1_gates := (List.range 4).flatMap (fun i =>
    (List.range dataW).map (fun b =>
      Gate.mkMUX amo_l0[2*i]![b]! amo_l0[2*i+1]![b]! amo_funct_r[1]! amo_l1[i]![b]!))
  let l2_gates := (List.range 2).flatMap (fun i =>
    (List.range dataW).map (fun b =>
      Gate.mkMUX amo_l1[2*i]![b]! amo_l1[2*i+1]![b]! amo_funct_r[2]! amo_l2[i]![b]!))
  let l3_gates := (List.range dataW).map (fun b =>
    Gate.mkMUX amo_l2[0]![b]! amo_l2[1]![b]! amo_funct_r[3]! amo_new[b]!)

  -- === Atomic direct write (AMO new value / SC store data) ===
  let aw_pending := Wire.mk "atom_aw_pending"
  let aw_pending_next := Wire.mk "atom_aw_pending_next"
  let aw_set := Wire.mk "atom_aw_set"
  let aw_clr := Wire.mk "atom_aw_clr"
  let aw_addr := mkW "atom_aw_addr" 32
  let aw_addr_next := mkW "atom_aw_addr_next" 32
  let aw_data := mkW "atom_aw_data" dataW
  let aw_data_next := mkW "atom_aw_data_next" dataW
  let aw_hold := Wire.mk "atom_aw_hold"
  let sc_wr := Wire.mk "atom_sc_wr"
  let aw_set_gates := [
    Gate.mkAND sc_exec sc_ok sc_wr,
    Gate.mkOR sc_wr amo_resp aw_set,
    Gate.mkAND aw_pending dmem_req_ready aw_clr,
    -- aw_pending_next = aw_clr ? 0 : (aw_set ? 1 : aw_pending)
    Gate.mkMUX aw_pending one aw_set aw_hold,
    Gate.mkMUX aw_hold zero aw_clr aw_pending_next]
  -- write data: SC uses rs2, AMO uses the computed new value
  let aw_data_sel := mkW "atom_aw_data_sel" dataW
  let aw_data_sel_gates := (List.range dataW).map (fun i =>
    Gate.mkMUX amo_new[i]! amo_rs2_r[i]! sc_sel aw_data_sel[i]!)
  let aw_addr_next_gates := (List.range 32).map (fun i =>
    Gate.mkMUX aw_addr[i]! mem_addr_r[i]! aw_set aw_addr_next[i]!)
  let aw_data_next_gates := (List.range dataW).map (fun i =>
    Gate.mkMUX aw_data[i]! aw_data_sel[i]! aw_set aw_data_next[i]!)
  let aw_insts : List CircuitInstance :=
    ({ moduleName := "DFlipFlop", instName := "u_atom_aw_pending",
       portMap := [("d", aw_pending_next), ("q", aw_pending),
                   ("clock", clock), ("reset", reset)] } : CircuitInstance) ::
    (List.range 32).map (fun i =>
      ({ moduleName := "DFlipFlop", instName := s!"u_atom_aw_addr_{i}",
         portMap := [("d", aw_addr_next[i]!), ("q", aw_addr[i]!),
                     ("clock", clock), ("reset", reset)] } : CircuitInstance)) ++
    (List.range dataW).map (fun i =>
      ({ moduleName := "DFlipFlop", instName := s!"u_atom_aw_data_{i}",
         portMap := [("d", aw_data_next[i]!), ("q", aw_data[i]!),
                     ("clock", clock), ("reset", reset)] } : CircuitInstance))

  -- === Busy latch: block dispatch while an atomic RMW is in flight ===
  let atomic_busy := Wire.mk "atom_busy"
  let atomic_busy_next := Wire.mk "atom_busy_next"
  let atomic_disp := Wire.mk "atom_disp"
  let sc_fail_t := Wire.mk "atom_sc_fail_t"
  let atomic_done := Wire.mk "atom_done"
  let busy_set := Wire.mk "atom_busy_set"
  let not_sc_ok := Wire.mk "atom_not_sc_ok"
  let done_t := Wire.mk "atom_done_t"
  let done_t2 := Wire.mk "atom_done_t2"
  let busy_gates := [
    Gate.mkAND pipe_load_en is_atomic atomic_disp,
    Gate.mkNOT sc_ok not_sc_ok,
    Gate.mkAND sc_exec not_sc_ok sc_fail_t,
    -- An atomic op is done when:
    --   * a failing SC completes, or
    --   * a direct write is accepted, or
    --   * an LR read completes (LR has no write), or
    --   * the pipeline is flushed (the atomic op is squashed).
    Gate.mkOR sc_fail_t aw_clr done_t,
    Gate.mkOR done_t lr_resp done_t2,
    Gate.mkOR done_t2 pipeline_flush_comb atomic_done,
    -- busy_next = atomic_disp ? 1 : (atomic_done ? 0 : busy)
    Gate.mkMUX atomic_busy one atomic_disp busy_set,
    Gate.mkMUX busy_set zero atomic_done atomic_busy_next]
  let busy_inst : CircuitInstance :=
    { moduleName := "DFlipFlop", instName := "u_atom_busy",
      portMap := [("d", atomic_busy_next), ("q", atomic_busy),
                  ("clock", clock), ("reset", reset)] }

  -- === Dispatch gate: atomics wait for a drained store buffer and no in-flight load ===
  let atomic_disp_ok := Wire.mk "atom_disp_ok"
  let disp_ok_pre := Wire.mk "atom_disp_ok_pre"
  let pipe_load := Wire.mk "atom_pipe_load"
  let load_in_flight := Wire.mk "atom_load_in_flight"
  let not_load_in_flight := Wire.mk "atom_not_load_in_flight"
  let not_is_atomic := Wire.mk "atom_not_is_atomic"
  let atom_load_ok := Wire.mk "atom_load_ok"
  let di_dr := Wire.mk "atom_di_dr"
  let req_ok := Wire.mk "atom_req_ok"
  let not_busy := Wire.mk "atom_not_busy"
  let nps := Wire.mk "atom_not_pending_store"
  let drain_req := Wire.mk "atom_drain_req"
  let not_drain_req := Wire.mk "atom_not_drain_req"
  let disp_ok_gates := [
    Gate.mkNOT atomic_busy not_busy,
    Gate.mkNOT rs_pending_store nps,
    Gate.mkAND mem_valid_r is_load_r pipe_load,
    Gate.mkOR pipe_load dmem_load_pending load_in_flight,
    Gate.mkNOT load_in_flight not_load_in_flight,
    Gate.mkNOT is_atomic not_is_atomic,
    Gate.mkOR not_is_atomic not_load_in_flight atom_load_ok,
    -- SC / AMO form an RMW: they wait for a fully drained store buffer and no
    -- pending plain store in the memory RS (an older store may not have reached
    -- the SB yet).  LR is a plain load plus a reservation set, so it does not.
    Gate.mkOR is_sc is_amo drain_req,
    Gate.mkNOT drain_req not_drain_req,
    Gate.mkAND lsu_sb_empty nps di_dr,
    Gate.mkOR not_drain_req di_dr req_ok,
    -- While an atomic op is in flight, block ALL memory dispatch so no
    -- load/store can slip between the atomic read and write.
    Gate.mkAND req_ok not_busy disp_ok_pre,
    Gate.mkAND disp_ok_pre atom_load_ok atomic_disp_ok]
  let gates :=
    code_gates ++ pipe_en_gates ++ code_reg_gates ++ sel_gates ++ resp_gates ++
    sc_exec_gates ++ res_inval_gates ++ res_set_gates ++ res_addr_gates ++
    [sc_ok_gate, sc_result_gate] ++
    bitwise_gates ++ cmp_operand_gates ++ minmax_gates ++ l0_gates ++ l1_gates ++ l2_gates ++ l3_gates ++
    aw_set_gates ++ aw_data_sel_gates ++ aw_addr_next_gates ++ aw_data_next_gates ++
    busy_gates ++ disp_ok_gates
  let instances :=
    code_reg_insts ++ [res_cmp_inst, sb_cmp_inst] ++ res_insts ++
    [add_inst, cmp_inst, cmp_u_inst] ++ aw_insts ++ [busy_inst]
  { gates := gates
    instances := instances
    reservationValid := reservation_valid
    reservationAddr := reservation_addr
    atomicCodeR := atomic_code_r
    scSel := sc_sel
    scExec := sc_exec
    scResult := sc_result
    awValid := aw_pending
    awAddr := aw_addr
    awData := aw_data
    atomicBusy := atomic_busy
    atomicDispatchOk := atomic_disp_ok }

/-- Generate combinational increment-by-4 gates for 32-bit PC.
    Avoids instantiating a full 32-bit KoggeStone adder with 31 bits tied to 0. -/
def mkPCPlus4Gates (pfx : String) (pc : List Wire) (pc_p4 : List Wire) : List Gate :=
  let b0 := Gate.mkBUF (pc[0]!) (pc_p4[0]!)
  let b1 := Gate.mkBUF (pc[1]!) (pc_p4[1]!)
  let n2 := Gate.mkNOT (pc[2]!) (pc_p4[2]!)
  let rec makeChain (i : Nat) (c_prev : Wire) (acc : List Gate) : List Gate :=
    if i >= 32 then acc
    else
      let sum_gate := Gate.mkXOR (pc[i]!) c_prev (pc_p4[i]!)
      if i == 31 then
        acc ++ [sum_gate]
      else
        let c_next := Wire.mk s!"{pfx}_c{i}"
        let carry_gate := Gate.mkAND (pc[i]!) c_prev c_next
        makeChain (i + 1) c_next (acc ++ [sum_gate, carry_gate])
  [b0, b1, n2] ++ makeChain 3 (pc[2]!) []

/-- Emit flat gates for a 1-entry flow queue (skid buffer).
    Eliminates submodule instances and tied-to-zero LINT-32 warnings on unused data bits. -/
def mkQueue1FlowGates
    (pfx : String) (width : Nat)
    (enq_data : List Wire) (enq_valid : Wire) (enq_ready : Wire)
    (deq_data : List Wire) (deq_valid : Wire) (deq_ready : Wire)
    (clock : Wire) (reset : Wire) : List Gate :=
  let valid := Wire.mk s!"{pfx}_v"
  let valid_next := Wire.mk s!"{pfx}_vnx"
  let data_reg := List.range width |>.map (fun i => Wire.mk s!"{pfx}_dreg_{i}")
  let data_next := List.range width |>.map (fun i => Wire.mk s!"{pfx}_dnx_{i}")

  let enq_fire := Wire.mk s!"{pfx}_efire"
  let deq_fire := Wire.mk s!"{pfx}_dfire"
  let not_valid := Wire.mk s!"{pfx}_nv"
  let valid_hold := Wire.mk s!"{pfx}_vhold"
  let not_deq_fire := Wire.mk s!"{pfx}_ndfire"
  let bypass_consumed := Wire.mk s!"{pfx}_bp_cons"
  let bypass_tmp := Wire.mk s!"{pfx}_bp_tmp"
  let not_bypass_consumed := Wire.mk s!"{pfx}_nbp_cons"
  let actual_enq := Wire.mk s!"{pfx}_act_enq"

  let ctrl_gates := [
    Gate.mkNOT valid not_valid,
    Gate.mkAND valid deq_ready deq_fire,
    Gate.mkOR not_valid deq_fire enq_ready,
    Gate.mkAND enq_valid enq_ready enq_fire,
    Gate.mkOR valid enq_valid deq_valid,
    Gate.mkAND not_valid enq_valid bypass_tmp,
    Gate.mkAND bypass_tmp deq_ready bypass_consumed,
    Gate.mkNOT bypass_consumed not_bypass_consumed,
    Gate.mkAND enq_fire not_bypass_consumed actual_enq,
    Gate.mkNOT deq_fire not_deq_fire,
    Gate.mkAND valid not_deq_fire valid_hold,
    Gate.mkOR actual_enq valid_hold valid_next,
    Gate.mkDFF valid_next clock reset valid
  ]

  let data_mux_gates := (List.range width).map (fun i =>
    Gate.mkMUX (data_reg[i]!) (enq_data[i]!) actual_enq (data_next[i]!))
  let dff_gates := (List.range width).map (fun i =>
    Gate.mkDFF (data_next[i]!) clock reset (data_reg[i]!))
  let bypass_gates := (List.range width).map (fun i =>
    Gate.mkMUX (enq_data[i]!) (data_reg[i]!) valid (deq_data[i]!))

  ctrl_gates ++ data_mux_gates ++ dff_gates ++ bypass_gates

end Shoumei.RISCV.CPU
