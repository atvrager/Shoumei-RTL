/-
Top-Level CPU Integration - RV32 W=2 Dual-Issue Tomasulo Processor
-/

import Shoumei.RISCV.Config
import Shoumei.RISCV.CPUBehavioral
import Shoumei.RISCV.CPUCircuitHelpers
import Shoumei.RISCV.CPUHelpers
import Shoumei.RISCV.CPU.BusyBitTable
import Shoumei.DSL
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Sequential.Register
import Shoumei.RISCV.CSRFile
import Shoumei.RISCV.Microcode.TrapSequencer

namespace Shoumei.RISCV.CPU_W2

open Shoumei.RISCV
open Shoumei
open Shoumei.Circuits.Combinational
open Shoumei.Circuits.Sequential
open Shoumei.RISCV.CPU

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
/-- Dual-Issue Top-Level CPU Integration (W=2).
Extends mkCPU to 2 instructions per cycle throughout the pipeline. -/
def mkCPU_W2 (config : CPUConfig) : Circuit :=
  let enableM := config.enableM
  let enableF := config.enableF
  let enableD := config.enableD
  let enableA := config.enableA
  let oi := config.opcodeIndex
  let opcodeWidth := config.opcodeWidth

  -- Global signals
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- === EXTERNAL INTERFACES ===
  let fetch_stall_ext := Wire.mk "fetch_stall_ext"
  let ifetch_last_word := Wire.mk "ifetch_last_word"  -- high when PC is at last word of cache line
  let dmem_stall_ext := Wire.mk "dmem_stall_ext"
  let imem_resp_data_0 := CPU.makeIndexedWires "imem_resp_data_0" 32
  let imem_resp_data_1 := CPU.makeIndexedWires "imem_resp_data_1" 32
  let dmem_req_ready := Wire.mk "dmem_req_ready"
  let dmem_resp_valid := Wire.mk "dmem_resp_valid"
  let dmem_resp_data := CPU.makeIndexedWires "dmem_resp_data" (if config.xlen == 64 || config.enableD then 64 else 32)

  -- === PIPELINE FLUSH ===
  let branch_redirect_valid_reg := Wire.mk "branch_redirect_valid_reg"
  let pipeline_flush_comb := Wire.mk "pipeline_flush_comb"
  let pipeline_flush := Wire.mk "pipeline_flush"
  -- Per-subsystem flush registers
  let flush_rs_int := Wire.mk "flush_rs_int"
  let flush_rs_mem := Wire.mk "flush_rs_mem"
  let flush_rs_br := Wire.mk "flush_rs_br"
  let flush_rs_muldiv := Wire.mk "flush_rs_muldiv"
  let flush_rob := Wire.mk "flush_rob"
  let flush_busy_groups := (List.range 8).map fun g => Wire.mk s!"flush_busy_g{g}"
  let flush_misc := Wire.mk "flush_misc"
  let pipeline_reset_rs_int := Wire.mk "pipeline_reset_rs_int"
  let pipeline_reset_rs_mem := Wire.mk "pipeline_reset_rs_mem"
  let pipeline_reset_rs_br := Wire.mk "pipeline_reset_rs_br"
  let pipeline_reset_rs_muldiv := Wire.mk "pipeline_reset_rs_muldiv"
  let pipeline_reset_rob := Wire.mk "pipeline_reset_rob"
  let pipeline_reset_busy := Wire.mk "pipeline_reset_busy"
  let pipeline_reset_misc := Wire.mk "pipeline_reset_misc"

  -- flush_comb = reset OR branch_redirect_valid_reg
  let flush_gate :=
    [Gate.mkOR reset branch_redirect_valid_reg pipeline_flush_comb,
     -- Per-subsystem reset OR gates
     Gate.mkOR reset flush_rs_int pipeline_reset_rs_int,
     Gate.mkOR reset flush_rs_mem pipeline_reset_rs_mem,
     Gate.mkOR reset flush_rs_br pipeline_reset_rs_br] ++
    (if enableM then [Gate.mkOR reset flush_rs_muldiv pipeline_reset_rs_muldiv] else []) ++
    [Gate.mkOR reset flush_rob pipeline_reset_rob,
     Gate.mkOR reset flush_busy_groups[0]! pipeline_reset_busy,
     Gate.mkOR reset flush_misc pipeline_reset_misc]

  let flush_dff_dispatch : CircuitInstance := {
    moduleName := "DFlipFlop"
    instName := "u_flush_dff_dispatch"
    portMap := [("d", pipeline_flush_comb), ("q", pipeline_flush),
                ("clock", clock), ("reset", reset)]
  }
  let flush_rs_fp := Wire.mk "flush_rs_fp"
  let pipeline_reset_rs_fp := Wire.mk "pipeline_reset_rs_fp"
  let fp_flush_reset_gates :=
    if enableF then [Gate.mkOR reset flush_rs_fp pipeline_reset_rs_fp] else []

  let flush_tags :=
    ["rs_int", "rs_mem", "rs_br"] ++
    (if enableM then ["rs_muldiv"] else []) ++
    (if enableF then ["rs_fp"] else []) ++
    ["rob", "misc"]
  let flush_dff_insts : List CircuitInstance := flush_tags.map (fun tag => {
    moduleName := "DFlipFlop"
    instName := s!"u_flush_dff_{tag}"
    portMap := [("d", pipeline_flush_comb), ("q", Wire.mk s!"flush_{tag}"),
                ("clock", clock), ("reset", reset)]
  })
  let flush_busy_dff_insts : List CircuitInstance := (List.range 8).map (fun g => {
    moduleName := "DFlipFlop"
    instName := s!"u_flush_dff_busy_g{g}"
    portMap := [("d", pipeline_flush_comb), ("q", flush_busy_groups[g]!),
                ("clock", clock), ("reset", reset)]
  })

  -- Redirect valid DFF
  let rob_redirect_valid := Wire.mk "rob_redirect_valid"
  let redirect_valid_dff_inst : CircuitInstance := {
    moduleName := "DFlipFlop"
    instName := "u_redirect_valid_dff"
    portMap := [("d", rob_redirect_valid), ("q", branch_redirect_valid_reg),
                ("clock", clock), ("reset", reset)]
  }
  let branch_redirect_target := CPU.makeIndexedWires "branch_redirect_target" 32
  let branch_redirect_target_reg := CPU.makeIndexedWires "branch_redirect_target_reg" 32
  let redirect_target_dff_insts : List CircuitInstance := [{
    moduleName := "Register32"
    instName := "u_redirect_target_reg"
    portMap := (branch_redirect_target.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
               [("clock", clock), ("reset", reset)] ++
               (branch_redirect_target_reg.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w)))
  }]

  -- === FETCH STAGE (W2) ===
  let fetch_pc_0 := CPU.makeIndexedWires "fetch_pc_0" 32
  let fetch_pc_1 := CPU.makeIndexedWires "fetch_pc_1" 32
  let global_stall := Wire.mk "global_stall"
  let fetch_stall := Wire.mk "fetch_stall"
  let fetch_stalled := Wire.mk "fetch_stalled"

  -- Forward declarations for decode/rename signals used by serialize FSM
  -- Names must match what mkDecoder/rename actually produce
  let d0_op := CPU.makeIndexedWires "dec0_optype" opcodeWidth
  let d1_op := CPU.makeIndexedWires "dec1_optype" opcodeWidth
  let _d0_valid := Wire.mk "dec0_valid"
  let _d1_valid := Wire.mk "dec1_valid"
  let d0_imm := CPU.makeIndexedWires "dec0_imm" 32
  let d1_imm := CPU.makeIndexedWires "dec1_imm" 32
  let d0_rd := CPU.makeIndexedWires "dec0_rd" 5
  let d1_rd := CPU.makeIndexedWires "dec1_rd" 5
  let d0_rs1 := CPU.makeIndexedWires "dec0_rs1" 5
  let d1_rs1 := CPU.makeIndexedWires "dec1_rs1" 5
  let rd_phys_0 := CPU.makeIndexedWires "rd_phys_0" 6
  let rd_phys_1 := CPU.makeIndexedWires "rd_phys_1" 6
  let rob_empty := Wire.mk "rob_empty"

  -- === SERIALIZE FSM (FENCE.I + CSR, W=2) ===
  -- State DFFs
  let fence_i_draining := Wire.mk "fence_i_draining"
  let fence_i_draining_next := Wire.mk "fence_i_draining_next"
  let fence_i_not_draining := Wire.mk "fence_i_not_draining"
  let fence_i_start := Wire.mk "fence_i_start"
  let fence_i_drain_complete := Wire.mk "fence_i_drain_complete"
  let fence_i_suppress := Wire.mk "fence_i_suppress"
  let fence_i_detected_0 := Wire.mk "fi_det_s0"
  let fence_i_detected_1 := Wire.mk "fi_det_s1"
  let fence_i_detected := Wire.mk "fence_i_detected"
  let csr_detected_0 := Wire.mk "csr_det_s0"
  let csr_detected_1 := Wire.mk "csr_det_s1"
  let csr_detected := Wire.mk "csr_detected"
  let serialize_detected := Wire.mk "serialize_detected"
  let csr_rename_en := Wire.mk "csr_rename_en"
  let not_csr_rename_en := Wire.mk "not_csr_rename_en"
  let ser_slot_sel := Wire.mk "ser_slot_sel" -- 0=slot 0, 1=slot 1

  -- CSR flag register (discriminates CSR vs FENCE.I drain)
  let csr_flag_reg := Wire.mk "csr_flag_reg"
  let csr_flag_next := Wire.mk "csr_flag_next"

  -- CSR capture registers
  let csr_addr_reg := CPU.makeIndexedWires "csr_addr_e" 12
  let csr_addr_next := CPU.makeIndexedWires "csr_anxt_e" 12
  let csr_optype_reg := CPU.makeIndexedWires "csr_opty_e" opcodeWidth
  let csr_optype_next := CPU.makeIndexedWires "csr_onxt_e" opcodeWidth
  let csr_rd_reg := CPU.makeIndexedWires "csr_rdcap_e" 5
  let csr_rd_next := CPU.makeIndexedWires "csr_rdnx_e" 5
  let csr_phys_reg := CPU.makeIndexedWires "csr_phcap_e" 6
  let csr_phys_next := CPU.makeIndexedWires "csr_phnxt_e" 6
  -- Old phys reg capture (for freelist return at CSR commit)
  let csr_old_phys_reg := CPU.makeIndexedWires "csr_ophcap_e" 6
  let csr_old_phys_next := CPU.makeIndexedWires "csr_ophnxt_e" 6
  let csr_rs1cap_reg := CPU.makeIndexedWires "csr_r1c_e" (if config.xlen == 64 then 64 else 32)
  let csr_rs1cap_next := CPU.makeIndexedWires "csr_r1n_e" (if config.xlen == 64 then 64 else 32)
  -- RS1 physical tag capture (for CDB snooping during drain)
  let csr_rs1tag_reg := CPU.makeIndexedWires "csr_r1t_e" 6
  let csr_rs1tag_next := CPU.makeIndexedWires "csr_r1tn_e" 6
  let csr_zimm_reg := CPU.makeIndexedWires "csr_zmc_e" 5
  let csr_zimm_next := CPU.makeIndexedWires "csr_zmn_e" 5

  -- CSR PC and instruction capture (for RVVI trace of CSR retires)
  let csr_pc_reg := CPU.makeIndexedWires "csr_pc_e" 32
  let csr_pc_next := CPU.makeIndexedWires "csr_pcn_e" 32
  let csr_insn_reg := CPU.makeIndexedWires "csr_isn_e" 32
  let csr_insn_next := CPU.makeIndexedWires "csr_isnn_e" 32

  -- Redirect target capture (PC+4 of serializing instruction)
  let fence_i_redir_target := CPU.makeIndexedWires "fencei_redir_e" 32
  let fence_i_redir_next := CPU.makeIndexedWires "fencei_rnxt_e" 32
  -- PC+4 for slot 0 (already have fetch_pc_0+4 from FetchStage), use fetch_pc_1 for slot 1
  let ser_pc_plus_4 := CPU.makeIndexedWires "ser_pc_plus_4" 32

  -- CDB injection wires
  let csr_cdb_inject := Wire.mk "csr_cdb_inject"
  let csr_flush_suppress := Wire.mk "csr_flush_suppress"

  -- ECALL detection wires (for trap entry via microcode sequencer)
  let ecall_detected_0 := Wire.mk "ecall_det_s0"
  let ecall_detected_1 := Wire.mk "ecall_det_s1"
  let ecall_detected := Wire.mk "ecall_detected"

  -- Trap sequencer wires (when config.microcodesTraps)
  let trap_seq_start := Wire.mk "trap_seq_start"
  let hw_csr_fence_start := Wire.mk "hw_csrfi_start"
  let useq_active := Wire.mk "useq_active"
  let useq_drain_complete := Wire.mk "useq_drain_complete"
  let useq_write_en := Wire.mk "useq_write_en"
  let useq_csr_sel := (List.range 2).map (fun i => Wire.mk s!"useq_csr_sel_{i}")
  let useq_write_data := (List.range 32).map (fun i => Wire.mk s!"useq_wr_dt_{i}")
  let useq_redir_next := (List.range 32).map (fun i => Wire.mk s!"useq_redir_{i}")
  let useq_mstatus_trap := Wire.mk "useq_mstatus_trap"
  let useq_mstatus_mret := Wire.mk "useq_mstatus_mret"

  -- Detection: match FENCE.I and CSR opcodes in both slots
  -- When opcodeWidth=8 (RV64G) or opcodeWidth=7 (F extension), use full-width matching to avoid collisions
  let mkMatch := if opcodeWidth == 8
    then fun pfx enc op result => mkOpcodeMatch8 pfx enc op result
    else if opcodeWidth == 7
    then fun pfx enc op result => mkOpcodeMatch7 pfx enc op result
    else fun pfx enc op result => mkOpcodeMatch6 pfx enc (op.take 6) result
  let mkMatchAny := if opcodeWidth == 8
    then fun pfx encs op result => mkOpcodeMatchAny8 pfx encs op result
    else fun pfx encs op result => mkOpcodeMatchAny7 pfx encs op result
  let fi_match_0 := mkMatch "fi_m0" (oi .FENCE_I) d0_op fence_i_detected_0
  let fi_match_1 := mkMatch "fi_m1" (oi .FENCE_I) d1_op fence_i_detected_1
  -- CSR opcode matches (CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI)
  let csrrw_m0 := mkMatch "csrrw_m0" (oi .CSRRW) d0_op (Wire.mk "csrrw_0")
  let csrrs_m0 := mkMatch "csrrs_m0" (oi .CSRRS) d0_op (Wire.mk "csrrs_0")
  let csrrc_m0 := mkMatch "csrrc_m0" (oi .CSRRC) d0_op (Wire.mk "csrrc_0")
  let csrrwi_m0 := mkMatch "csrrwi_m0" (oi .CSRRWI) d0_op (Wire.mk "csrrwi_0")
  let csrrsi_m0 := mkMatch "csrrsi_m0" (oi .CSRRSI) d0_op (Wire.mk "csrrsi_0")
  let csrrci_m0 := mkMatch "csrrci_m0" (oi .CSRRCI) d0_op (Wire.mk "csrrci_0")
  let csrrw_m1 := mkMatch "csrrw_m1" (oi .CSRRW) d1_op (Wire.mk "csrrw_1")
  let csrrs_m1 := mkMatch "csrrs_m1" (oi .CSRRS) d1_op (Wire.mk "csrrs_1")
  let csrrc_m1 := mkMatch "csrrc_m1" (oi .CSRRC) d1_op (Wire.mk "csrrc_1")
  let csrrwi_m1 := mkMatch "csrrwi_m1" (oi .CSRRWI) d1_op (Wire.mk "csrrwi_1")
  let csrrsi_m1 := mkMatch "csrrsi_m1" (oi .CSRRSI) d1_op (Wire.mk "csrrsi_1")
  let csrrci_m1 := mkMatch "csrrci_m1" (oi .CSRRCI) d1_op (Wire.mk "csrrci_1")

  -- ECALL opcode match in both slots
  let ecall_m0 := mkMatch "ecall_m0" (oi .ECALL) d0_op (Wire.mk "ecall_match_0")
  let ecall_m1 := mkMatch "ecall_m1" (oi .ECALL) d1_op (Wire.mk "ecall_match_1")

  -- MRET opcode match in both slots
  let enableMRET := config.microcodesMRET
  let mret_m0 := mkMatch "mret_m0" (oi .MRET) d0_op (Wire.mk "mret_match_0")
  let mret_m1 := mkMatch "mret_m1" (oi .MRET) d1_op (Wire.mk "mret_match_1")
  -- WFI opcode match in both slots (routes to hw drain FSM as NOP)
  let wfi_m0 := mkMatch "wfi_m0" (oi .WFI) d0_op (Wire.mk "wfi_match_0")
  let wfi_m1 := mkMatch "wfi_m1" (oi .WFI) d1_op (Wire.mk "wfi_match_1")
  let mret_detected_0 := Wire.mk "mret_det_0"
  let mret_detected_1 := Wire.mk "mret_det_1"
  let mret_detected := Wire.mk "mret_detected"
  let wfi_detected_0 := Wire.mk "wfi_det_0"
  let wfi_detected_1 := Wire.mk "wfi_det_1"
  let wfi_detected := Wire.mk "wfi_detected"

  let csr_detect_gates :=
    if config.enableZicsr then
      [Gate.mkOR (Wire.mk "csrrw_0") (Wire.mk "csrrs_0") (Wire.mk "csr_or0_0"),
       Gate.mkOR (Wire.mk "csr_or0_0") (Wire.mk "csrrc_0") (Wire.mk "csr_or1_0"),
       Gate.mkOR (Wire.mk "csr_or1_0") (Wire.mk "csrrwi_0") (Wire.mk "csr_or2_0"),
       Gate.mkOR (Wire.mk "csr_or2_0") (Wire.mk "csrrsi_0") (Wire.mk "csr_or3_0"),
       Gate.mkOR (Wire.mk "csr_or3_0") (Wire.mk "csrrci_0") (Wire.mk "csr_match_0"),
       Gate.mkOR (Wire.mk "csrrw_1") (Wire.mk "csrrs_1") (Wire.mk "csr_or0_1"),
       Gate.mkOR (Wire.mk "csr_or0_1") (Wire.mk "csrrc_1") (Wire.mk "csr_or1_1"),
       Gate.mkOR (Wire.mk "csr_or1_1") (Wire.mk "csrrwi_1") (Wire.mk "csr_or2_1"),
       Gate.mkOR (Wire.mk "csr_or2_1") (Wire.mk "csrrsi_1") (Wire.mk "csr_or3_1"),
       Gate.mkOR (Wire.mk "csr_or3_1") (Wire.mk "csrrci_1") (Wire.mk "csr_match_1")]
    else
      [Gate.mkBUF zero (Wire.mk "csr_match_0"), Gate.mkBUF zero (Wire.mk "csr_match_1")]

  -- Gate by decode_valid and not redirect/stall
  let enableTraps := config.microcodesTraps
  let ser_detect_gates :=
    [Gate.mkNOT branch_redirect_valid_reg (Wire.mk "ser_not_redir"),
     Gate.mkNOT fetch_stall_ext (Wire.mk "ser_not_fse"),
     -- Also gate by NOT(pipeline_flush) — pipeline_flush is DFF of pipeline_flush_comb,
     -- so it's high the cycle AFTER a redirect. Instructions arriving during pipeline_flush
     -- are stale (fetched before the redirect) and must not trigger serialize.
     Gate.mkNOT pipeline_flush (Wire.mk "ser_not_pflush"),
     Gate.mkAND (Wire.mk "ser_not_redir") (Wire.mk "ser_not_pflush") (Wire.mk "ser_not_redir_flush"),
     -- Gate by NOT(global_stall): if pipeline is stalled, slot 0 cannot dispatch.
     -- Starting serialize while stalled would cause slot 0's instruction to be permanently
     -- lost (fence_i_draining suppresses all future dispatch before it ever fires).
     Gate.mkNOT global_stall (Wire.mk "ser_not_stall"),
     -- Use gated decode-valid (after fetch_valid masking) to avoid triggering
     -- serialize on invalid slot 1 instructions (e.g. cache line boundary)
     Gate.mkAND (Wire.mk "d0_valid_gated") (Wire.mk "ser_not_redir_flush") (Wire.mk "ser_dv0_nr"),
     Gate.mkAND (Wire.mk "ser_dv0_nr") (Wire.mk "ser_not_fse") (Wire.mk "ser_dv0_pre"),
     Gate.mkAND (Wire.mk "ser_dv0_pre") (Wire.mk "ser_not_stall") (Wire.mk "ser_dv0"),
     Gate.mkAND (Wire.mk "d1_valid_gated") (Wire.mk "ser_not_redir_flush") (Wire.mk "ser_dv1_nr"),
     Gate.mkAND (Wire.mk "ser_dv1_nr") (Wire.mk "ser_not_fse") (Wire.mk "ser_dv1_pre"),
     Gate.mkAND (Wire.mk "ser_dv1_pre") (Wire.mk "ser_not_stall") (Wire.mk "ser_dv1")] ++
    (if config.enableZifencei then
      [Gate.mkAND (Wire.mk "ser_dv0") fence_i_detected_0 (Wire.mk "fi_det_0_gated"),
       Gate.mkAND (Wire.mk "ser_dv1") fence_i_detected_1 (Wire.mk "fi_det_1_gated"),
       Gate.mkOR (Wire.mk "fi_det_0_gated") (Wire.mk "fi_det_1_gated") fence_i_detected]
    else [Gate.mkBUF zero fence_i_detected]) ++
    (if config.enableZicsr then
      [Gate.mkAND (Wire.mk "ser_dv0") (Wire.mk "csr_match_0") csr_detected_0,
       Gate.mkAND (Wire.mk "ser_dv1") (Wire.mk "csr_match_1") csr_detected_1,
       Gate.mkOR csr_detected_0 csr_detected_1 csr_detected]
    else [Gate.mkBUF zero csr_detected_0, Gate.mkBUF zero csr_detected_1,
          Gate.mkBUF zero csr_detected]) ++
    -- ECALL detection (gated by decode_valid)
    (if enableTraps then
      [Gate.mkAND (Wire.mk "ser_dv0") (Wire.mk "ecall_match_0") ecall_detected_0,
       Gate.mkAND (Wire.mk "ser_dv1") (Wire.mk "ecall_match_1") ecall_detected_1,
       Gate.mkOR ecall_detected_0 ecall_detected_1 ecall_detected]
    else
      [Gate.mkBUF zero ecall_detected_0, Gate.mkBUF zero ecall_detected_1,
       Gate.mkBUF zero ecall_detected]) ++
    -- MRET detection (gated by decode_valid)
    (if enableMRET then
      [Gate.mkAND (Wire.mk "ser_dv0") (Wire.mk "mret_match_0") mret_detected_0,
       Gate.mkAND (Wire.mk "ser_dv1") (Wire.mk "mret_match_1") mret_detected_1,
       Gate.mkOR mret_detected_0 mret_detected_1 mret_detected]
    else
      [Gate.mkBUF zero mret_detected_0, Gate.mkBUF zero mret_detected_1,
       Gate.mkBUF zero mret_detected]) ++
    -- WFI detection (gated by decode_valid) — routes to hw drain as NOP
    (if enableMRET then
      [Gate.mkAND (Wire.mk "ser_dv0") (Wire.mk "wfi_match_0") wfi_detected_0,
       Gate.mkAND (Wire.mk "ser_dv1") (Wire.mk "wfi_match_1") wfi_detected_1,
       Gate.mkOR wfi_detected_0 wfi_detected_1 wfi_detected]
    else
      [Gate.mkBUF zero wfi_detected_0, Gate.mkBUF zero wfi_detected_1,
       Gate.mkBUF zero wfi_detected]) ++
    -- serialize_detected includes ECALL, MRET, WFI when enabled
    [Gate.mkOR fence_i_detected csr_detected (Wire.mk "hw_ser_pre"),
     Gate.mkOR (Wire.mk "hw_ser_pre") ecall_detected (Wire.mk "hw_ser_pre2"),
     Gate.mkOR (Wire.mk "hw_ser_pre2") mret_detected (Wire.mk "hw_ser_pre3"),
     Gate.mkOR (Wire.mk "hw_ser_pre3") wfi_detected serialize_detected] ++
    [-- Slot selection: slot 0 priority. sel=0 when slot 0 has the serialize op.
     -- ser_slot_sel = NOT(slot 0 detected) AND (slot 1 detected)
     Gate.mkNOT (Wire.mk "ser_dv0_det") (Wire.mk "ser_not_s0"),
     -- Include ECALL/MRET/WFI in slot any-match
     Gate.mkOR fence_i_detected_0 (Wire.mk "csr_match_0") (Wire.mk "ser_s0_csrfi"),
     Gate.mkOR (Wire.mk "ser_s0_csrfi") (Wire.mk "ecall_match_0") (Wire.mk "ser_s0_pre"),
     Gate.mkOR (Wire.mk "ser_s0_pre") (Wire.mk "mret_match_0") (Wire.mk "ser_s0_pre2"),
     Gate.mkOR (Wire.mk "ser_s0_pre2") (Wire.mk "wfi_match_0") (Wire.mk "ser_s0_any"),
     Gate.mkAND (Wire.mk "ser_dv0") (Wire.mk "ser_s0_any") (Wire.mk "ser_dv0_det"),
     Gate.mkOR fence_i_detected_1 (Wire.mk "csr_match_1") (Wire.mk "ser_s1_csrfi"),
     Gate.mkOR (Wire.mk "ser_s1_csrfi") (Wire.mk "ecall_match_1") (Wire.mk "ser_s1_pre"),
     Gate.mkOR (Wire.mk "ser_s1_pre") (Wire.mk "mret_match_1") (Wire.mk "ser_s1_pre2"),
     Gate.mkOR (Wire.mk "ser_s1_pre2") (Wire.mk "wfi_match_1") (Wire.mk "ser_s1_any"),
     Gate.mkAND (Wire.mk "ser_dv1") (Wire.mk "ser_s1_any") (Wire.mk "ser_dv1_det"),
     Gate.mkAND (Wire.mk "ser_not_s0") (Wire.mk "ser_dv1_det") ser_slot_sel] ++
    -- Slot-selected detection: when both slots have serialize ops, only the winning
    -- slot's operation type should start. e.g., CSR in slot 0 + ECALL in slot 1 →
    -- CSR wins (ser_slot_sel=0), so ecall_selected=0.
    [Gate.mkNOT ser_slot_sel (Wire.mk "not_ser_slot"),
     -- ecall_selected = (ecall_det_s0 AND NOT(ser_slot_sel)) OR (ecall_det_s1 AND ser_slot_sel)
     Gate.mkAND ecall_detected_0 (Wire.mk "not_ser_slot") (Wire.mk "ecall_sel_s0"),
     Gate.mkAND ecall_detected_1 ser_slot_sel (Wire.mk "ecall_sel_s1"),
     Gate.mkOR (Wire.mk "ecall_sel_s0") (Wire.mk "ecall_sel_s1") (Wire.mk "ecall_selected"),
     -- mret_selected
     Gate.mkAND mret_detected_0 (Wire.mk "not_ser_slot") (Wire.mk "mret_sel_s0"),
     Gate.mkAND mret_detected_1 ser_slot_sel (Wire.mk "mret_sel_s1"),
     Gate.mkOR (Wire.mk "mret_sel_s0") (Wire.mk "mret_sel_s1") (Wire.mk "mret_selected"),
     -- csr_selected
     Gate.mkAND csr_detected_0 (Wire.mk "not_ser_slot") (Wire.mk "csr_sel_s0"),
     Gate.mkAND csr_detected_1 ser_slot_sel (Wire.mk "csr_sel_s1"),
     Gate.mkOR (Wire.mk "csr_sel_s0") (Wire.mk "csr_sel_s1") (Wire.mk "csr_selected"),
     -- fence_i_selected (use raw match signals, valid gating already in ser_dv0/1)
     Gate.mkAND fence_i_detected_0 (Wire.mk "not_ser_slot") (Wire.mk "fi_sel_s0"),
     Gate.mkAND fence_i_detected_1 ser_slot_sel (Wire.mk "fi_sel_s1"),
     Gate.mkOR (Wire.mk "fi_sel_s0") (Wire.mk "fi_sel_s1") (Wire.mk "fi_selected"),
     -- wfi_selected
     Gate.mkAND wfi_detected_0 (Wire.mk "not_ser_slot") (Wire.mk "wfi_sel_s0"),
     Gate.mkAND wfi_detected_1 ser_slot_sel (Wire.mk "wfi_sel_s1"),
     Gate.mkOR (Wire.mk "wfi_sel_s0") (Wire.mk "wfi_sel_s1") (Wire.mk "wfi_selected")]

  -- FSM transitions (with trap sequencer integration when enableTraps)
  let ser_fsm_gates :=
    [Gate.mkNOT fence_i_draining fence_i_not_draining,
     Gate.mkNOT pipeline_flush_comb (Wire.mk "ser_not_flush")] ++
    if enableTraps then
      -- Split start: ECALL → trap_seq_start, MRET → mret_seq_start, CSR/FENCE.I/WFI → hw_csr_fence_start
      let mret_seq_start := Wire.mk "mret_seq_start"
      [Gate.mkOR fence_i_draining useq_active (Wire.mk "any_active"),
       Gate.mkNOT (Wire.mk "any_active") (Wire.mk "not_any_active"),
       -- ECALL starts trap sequencer (TRAP_ENTRY) — use slot-selected signal
       Gate.mkAND (Wire.mk "ecall_selected") (Wire.mk "not_any_active") trap_seq_start,
       -- MRET starts trap sequencer (MRET sequence) — use slot-selected signal
       Gate.mkAND (Wire.mk "mret_selected") (Wire.mk "not_any_active") mret_seq_start,
       -- CSR/FENCE.I/WFI starts hardwired FSM — use slot-selected signals
       Gate.mkOR (Wire.mk "fi_selected") (Wire.mk "csr_selected") (Wire.mk "csrfi_det"),
       Gate.mkOR (Wire.mk "csrfi_det") (Wire.mk "wfi_selected") (Wire.mk "csrfiwfi_det"),
       Gate.mkAND (Wire.mk "csrfiwfi_det") (Wire.mk "not_any_active") hw_csr_fence_start,
       -- useq_start = ecall OR mret (both start the microcode sequencer)
       Gate.mkOR trap_seq_start mret_seq_start (Wire.mk "useq_start"),
       -- any_serialize_start = useq_start OR hw_start OR irq_inject
       Gate.mkOR (Wire.mk "useq_start") hw_csr_fence_start (Wire.mk "any_ser_start_pre"),
       Gate.mkOR (Wire.mk "any_ser_start_pre") (Wire.mk "irq_inject") (Wire.mk "any_ser_start"),
       -- fence_i_start = any_serialize_start (drives capture latches)
       Gate.mkBUF (Wire.mk "any_ser_start") fence_i_start,
       -- Hardwired drain FSM (only active for CSR/FENCE.I/WFI, not ECALL/MRET)
       -- Suppress drain_complete on first cycle of draining (fence_i_start_delayed)
       -- to prevent false completion when pipeline is already empty from previous op.
       Gate.mkAND fence_i_draining rob_empty (Wire.mk "ser_dc_tmp"),
       Gate.mkAND (Wire.mk "ser_dc_tmp") (Wire.mk "lsu_sb_empty") (Wire.mk "ser_dc_tmp2"),
       Gate.mkAND (Wire.mk "ser_dc_tmp2") (Wire.mk "ser_not_flush") (Wire.mk "hw_dc_pre"),
       -- Gate hw_drain_complete with NOT(useq_active) AND NOT(fence_i_start_delayed)
       Gate.mkNOT useq_active (Wire.mk "not_useq_active"),
       Gate.mkNOT (Wire.mk "fence_start_delayed") (Wire.mk "not_fsd"),
       Gate.mkAND (Wire.mk "hw_dc_pre") (Wire.mk "not_useq_active") (Wire.mk "hw_dc_pre2"),
       Gate.mkAND (Wire.mk "hw_dc_pre2") (Wire.mk "not_fsd") (Wire.mk "hw_drain_complete"),
       -- draining_next for hw path
       Gate.mkOR hw_csr_fence_start fence_i_draining (Wire.mk "hw_set_or"),
       Gate.mkNOT (Wire.mk "hw_drain_complete") (Wire.mk "hw_not_dc"),
       Gate.mkAND (Wire.mk "hw_set_or") (Wire.mk "hw_not_dc") (Wire.mk "hw_drain_next_tmp"),
       Gate.mkAND (Wire.mk "hw_drain_next_tmp") (Wire.mk "ser_not_flush") (Wire.mk "hw_draining_next"),
       -- Merge: fence_i_draining_next = hw OR useq_active
       Gate.mkOR (Wire.mk "hw_draining_next") useq_active (Wire.mk "drain_merge_pre"),
       Gate.mkAND (Wire.mk "drain_merge_pre") (Wire.mk "ser_not_flush") fence_i_draining_next,
       -- fence_i_drain_complete = hw_drain_complete OR useq_dc_delayed (1-cycle delay)
       Gate.mkOR (Wire.mk "hw_drain_complete") (Wire.mk "useq_dc_delayed") fence_i_drain_complete,
       -- NOT(drain_complete) for csr_flag hold logic
       Gate.mkNOT fence_i_drain_complete (Wire.mk "ser_not_dc"),
       -- Suppress: CSR start allows rename; FENCE.I/ECALL/MRET/WFI/drain suppress
       Gate.mkAND hw_csr_fence_start (Wire.mk "csr_selected") csr_rename_en,
       Gate.mkNOT csr_rename_en not_csr_rename_en,
       Gate.mkAND hw_csr_fence_start not_csr_rename_en (Wire.mk "fi_start_nocsr"),
       Gate.mkOR (Wire.mk "fi_start_nocsr") fence_i_draining (Wire.mk "hw_suppress"),
       Gate.mkOR (Wire.mk "hw_suppress") useq_active (Wire.mk "suppress_pre"),
       -- ECALL/MRET detected (slot-selected) also suppress
       Gate.mkOR (Wire.mk "ecall_selected") (Wire.mk "mret_selected") (Wire.mk "ecall_or_mret_det"),
       Gate.mkOR (Wire.mk "suppress_pre") (Wire.mk "ecall_or_mret_det") fence_i_suppress]
    else
      -- Original hardwired-only path (no traps)
      [Gate.mkAND serialize_detected fence_i_not_draining fence_i_start,
       -- Drain complete: draining AND rob_empty AND sb_empty AND NOT flushing
       Gate.mkAND fence_i_draining rob_empty (Wire.mk "ser_dc_tmp"),
       Gate.mkAND (Wire.mk "ser_dc_tmp") (Wire.mk "lsu_sb_empty") (Wire.mk "ser_dc_tmp2"),
       Gate.mkAND (Wire.mk "ser_dc_tmp2") (Wire.mk "ser_not_flush") fence_i_drain_complete,
       -- Next state
       Gate.mkOR fence_i_start fence_i_draining (Wire.mk "ser_set_or"),
       Gate.mkNOT fence_i_drain_complete (Wire.mk "ser_not_dc"),
       Gate.mkAND (Wire.mk "ser_set_or") (Wire.mk "ser_not_dc") (Wire.mk "ser_drain_tmp"),
       Gate.mkAND (Wire.mk "ser_drain_tmp") (Wire.mk "ser_not_flush") fence_i_draining_next,
       -- Suppress: gate dispatch during drain
       Gate.mkAND fence_i_start csr_detected csr_rename_en,
       Gate.mkNOT csr_rename_en not_csr_rename_en,
       Gate.mkAND fence_i_start not_csr_rename_en (Wire.mk "fi_start_nocsr"),
       Gate.mkOR (Wire.mk "fi_start_nocsr") fence_i_draining fence_i_suppress,
       -- Stub trap wires
       Gate.mkBUF zero trap_seq_start,
       Gate.mkBUF zero hw_csr_fence_start,
       Gate.mkBUF zero useq_active,
       Gate.mkBUF zero useq_drain_complete,
       Gate.mkBUF zero useq_write_en,
       Gate.mkBUF zero useq_mstatus_trap,
       Gate.mkBUF zero useq_mstatus_mret,
       Gate.mkBUF zero (Wire.mk "irq_inject")]

  -- PC+4 of serializing instruction (MUX between slot 0 PC and slot 1 PC, then add 4)
  let ser_pc_muxed := CPU.makeIndexedWires "ser_pc_muxed" 32
  let ser_pc_mux_gates :=
    (List.range 32).map (fun i =>
      Gate.mkMUX fetch_pc_0[i]! fetch_pc_1[i]! ser_slot_sel ser_pc_muxed[i]!)
  let ser_pc_adder_inst : CircuitInstance := {
    moduleName := "PCIncrementer4"
    instName := "u_ser_pc_plus_4"
    portMap := (ser_pc_muxed.enum.map (fun ⟨i, w⟩ => (s!"pc_{i}", w))) ++
               (ser_pc_plus_4.enum.map (fun ⟨i, w⟩ => (s!"pc_next_{i}", w))) }

  -- Capture MUXes (gated by fence_i_start, select from slot ser_slot_sel)
  -- When trap sequencer active, redirect comes from sequencer; else from hw path (PC+4)
  let ser_capture_gates :=
    -- Redirect target: hw path captures PC+4; merge with trap sequencer redirect
    (if enableTraps then
      -- hw redir = MUX(hold, pc+4, hw_csr_fence_start)
      (List.range 32).map (fun i =>
        Gate.mkMUX fence_i_redir_target[i]! ser_pc_plus_4[i]! hw_csr_fence_start (Wire.mk s!"hw_redir_{i}")) ++
      -- final redir = MUX(hw_redir, useq_redir, useq_active)
      (List.range 32).map (fun i =>
        Gate.mkMUX (Wire.mk s!"hw_redir_{i}") useq_redir_next[i]! useq_active fence_i_redir_next[i]!)
    else
      (List.range 32).map (fun i =>
        Gate.mkMUX fence_i_redir_target[i]! ser_pc_plus_4[i]! fence_i_start fence_i_redir_next[i]!)) ++
    -- CSR flag: 1=CSR, 0=FENCE.I
    -- Clear csr_flag on drain_complete (CSR done, redirect fires)
    [Gate.mkAND csr_flag_reg (Wire.mk "ser_not_dc") (Wire.mk "csr_flag_hold"),
     Gate.mkMUX (Wire.mk "csr_flag_hold") csr_detected fence_i_start csr_flag_next] ++
    -- CSR address: decode_imm captured on hw_csr_fence_start / fence_i_start
    (if config.enableZicsr then
      ((List.range 12).map (fun i =>
        let muxed := Wire.mk s!"ser_imm_{i}"
        let start_sig := if enableTraps then hw_csr_fence_start else fence_i_start
        [Gate.mkMUX d0_imm[i]! d1_imm[i]! ser_slot_sel muxed,
         Gate.mkMUX csr_addr_reg[i]! muxed start_sig csr_addr_next[i]!])).flatten ++
      -- CSR optype from selected slot
      ((List.range opcodeWidth).map (fun i =>
        let muxed := Wire.mk s!"ser_op_{i}"
        [Gate.mkMUX (d0_op.take opcodeWidth)[i]! (d1_op.take opcodeWidth)[i]! ser_slot_sel muxed,
         Gate.mkMUX csr_optype_reg[i]! muxed fence_i_start csr_optype_next[i]!])).flatten ++
      -- CSR rd from selected slot
      ((List.range 5).map (fun i =>
        let muxed := Wire.mk s!"ser_rd_{i}"
        [Gate.mkMUX d0_rd[i]! d1_rd[i]! ser_slot_sel muxed,
         Gate.mkMUX csr_rd_reg[i]! muxed fence_i_start csr_rd_next[i]!])).flatten ++
      -- CSR phys rd from selected slot
      ((List.range 6).map (fun i =>
        let muxed := Wire.mk s!"ser_phrd_{i}"
        [Gate.mkMUX rd_phys_0[i]! rd_phys_1[i]! ser_slot_sel muxed,
         Gate.mkMUX csr_phys_reg[i]! muxed fence_i_start csr_phys_next[i]!])).flatten ++
      -- CSR old phys rd from selected slot (for freelist return at commit)
      ((List.range 6).map (fun i =>
        let muxed := Wire.mk s!"ser_ophrd_{i}"
        [Gate.mkMUX (Wire.mk s!"old_physRd_0_{i}") (Wire.mk s!"old_physRd_1_{i}") ser_slot_sel muxed,
         Gate.mkMUX csr_old_phys_reg[i]! muxed fence_i_start csr_old_phys_next[i]!])).flatten ++
      -- CSR rs1 phys tag capture (for CDB snoop during drain)
      ((List.range 6).map (fun i =>
        let muxed := Wire.mk s!"ser_r1t_{i}"
        [Gate.mkMUX (Wire.mk s!"rs1_phys_0_{i}") (Wire.mk s!"rs1_phys_1_{i}") ser_slot_sel muxed,
         Gate.mkMUX csr_rs1tag_reg[i]! muxed fence_i_start csr_rs1tag_next[i]!])).flatten ++
      -- CSR rs1 data: slot-mux raw data (ser_r1) used by snoop_data MUX defined later
      ((List.range (if config.xlen == 64 then 64 else 32)).map (fun i =>
        Gate.mkMUX (Wire.mk s!"rs1_data_0_{i}") (Wire.mk s!"rs1_data_1_{i}") ser_slot_sel (Wire.mk s!"ser_r1_{i}"))) ++
      -- Final capture: MUX(hold, snoop_data, update_en)
      ((List.range (if config.xlen == 64 then 64 else 32)).map (fun i =>
        Gate.mkMUX csr_rs1cap_reg[i]! (Wire.mk s!"csr_snoop_data_{i}") (Wire.mk "rs1cap_update_en") csr_rs1cap_next[i]!)) ++
      -- CSR zimm (rs1 field from instruction)
      ((List.range 5).map (fun i =>
        let muxed := Wire.mk s!"ser_zm_{i}"
        [Gate.mkMUX d0_rs1[i]! d1_rs1[i]! ser_slot_sel muxed,
         Gate.mkMUX csr_zimm_reg[i]! muxed fence_i_start csr_zimm_next[i]!])).flatten ++
      -- CSR PC capture (for RVVI trace): ser_pc_muxed is computed above
      ((List.range 32).map (fun i =>
        Gate.mkMUX csr_pc_reg[i]! ser_pc_muxed[i]! fence_i_start csr_pc_next[i]!)) ++
      -- CSR instruction capture (for RVVI trace)
      ((List.range 32).map (fun i =>
        let muxed := Wire.mk s!"ser_insn_{i}"
        [Gate.mkMUX imem_resp_data_0[i]! imem_resp_data_1[i]! ser_slot_sel muxed,
         Gate.mkMUX csr_insn_reg[i]! muxed fence_i_start csr_insn_next[i]!])).flatten
    else
      -- No CSR: just hold capture registers
      (List.range 12).map (fun i => Gate.mkBUF csr_addr_reg[i]! csr_addr_next[i]!) ++
      (List.range opcodeWidth).map (fun i => Gate.mkBUF csr_optype_reg[i]! csr_optype_next[i]!) ++
      (List.range 5).map (fun i => Gate.mkBUF csr_rd_reg[i]! csr_rd_next[i]!) ++
      (List.range 6).map (fun i => Gate.mkBUF csr_phys_reg[i]! csr_phys_next[i]!) ++
      (List.range 6).map (fun i => Gate.mkBUF csr_old_phys_reg[i]! csr_old_phys_next[i]!) ++
      (List.range (if config.xlen == 64 then 64 else 32)).map (fun i => Gate.mkBUF csr_rs1cap_reg[i]! csr_rs1cap_next[i]!) ++
      (List.range 5).map (fun i => Gate.mkBUF csr_zimm_reg[i]! csr_zimm_next[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF csr_pc_reg[i]! csr_pc_next[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF csr_insn_reg[i]! csr_insn_next[i]!))

  -- Serialize FSM DFFs (use reset, survive pipeline flushes)
  let ser_dff_insts : List CircuitInstance :=
    [{ moduleName := "DFlipFlop", instName := "u_fence_i_draining_dff",
       portMap := [("d", fence_i_draining_next), ("q", fence_i_draining),
                   ("clock", clock), ("reset", reset)] },
     { moduleName := "DFlipFlop", instName := "u_csr_flag_dff",
       portMap := [("d", csr_flag_next), ("q", csr_flag_reg),
                   ("clock", clock), ("reset", reset)] },
     -- fence_start_delayed: suppress hw_drain_complete on first cycle of draining
     { moduleName := "DFlipFlop", instName := "u_fence_start_dly_dff",
       portMap := [("d", fence_i_start), ("q", Wire.mk "fence_start_delayed"),
                   ("clock", clock), ("reset", reset)] }] ++
    [{ moduleName := "Register32", instName := "u_fencei_redir_reg",
       portMap := (fence_i_redir_next.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
                  [("clock", clock), ("reset", reset)] ++
                  (fence_i_redir_target.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w))) }] ++
    (if config.enableZicsr then
      (List.range 12).map (fun i =>
        { moduleName := "DFlipFlop", instName := s!"u_csr_addr_dff_{i}",
          portMap := [("d", csr_addr_next[i]!), ("q", csr_addr_reg[i]!),
                      ("clock", clock), ("reset", reset)] }) ++
      (List.range opcodeWidth).map (fun i =>
        { moduleName := "DFlipFlop", instName := s!"u_csr_optype_dff_{i}",
          portMap := [("d", csr_optype_next[i]!), ("q", csr_optype_reg[i]!),
                      ("clock", clock), ("reset", reset)] }) ++
      (List.range 5).map (fun i =>
        { moduleName := "DFlipFlop", instName := s!"u_csr_rd_dff_{i}",
          portMap := [("d", csr_rd_next[i]!), ("q", csr_rd_reg[i]!),
                      ("clock", clock), ("reset", reset)] }) ++
      (List.range 6).map (fun i =>
        { moduleName := "DFlipFlop", instName := s!"u_csr_phys_dff_{i}",
          portMap := [("d", csr_phys_next[i]!), ("q", csr_phys_reg[i]!),
                      ("clock", clock), ("reset", reset)] }) ++
      (List.range 6).map (fun i =>
        { moduleName := "DFlipFlop", instName := s!"u_csr_ophys_dff_{i}",
          portMap := [("d", csr_old_phys_next[i]!), ("q", csr_old_phys_reg[i]!),
                      ("clock", clock), ("reset", reset)] }) ++
      (if config.xlen == 64 then
        [{ moduleName := "Register64", instName := "u_csr_rs1cap_reg",
           portMap := (csr_rs1cap_next.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
                      [("clock", clock), ("reset", reset)] ++
                      (csr_rs1cap_reg.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w))) }]
       else
        [{ moduleName := "Register32", instName := "u_csr_rs1cap_reg",
           portMap := (csr_rs1cap_next.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
                      [("clock", clock), ("reset", reset)] ++
                      (csr_rs1cap_reg.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w))) }]) ++
      (List.range 6).map (fun i =>
        { moduleName := "DFlipFlop", instName := s!"u_csr_rs1tag_dff_{i}",
          portMap := [("d", csr_rs1tag_next[i]!), ("q", csr_rs1tag_reg[i]!),
                      ("clock", clock), ("reset", reset)] }) ++
      (List.range 5).map (fun i =>
        { moduleName := "DFlipFlop", instName := s!"u_csr_zimm_dff_{i}",
          portMap := [("d", csr_zimm_next[i]!), ("q", csr_zimm_reg[i]!),
                      ("clock", clock), ("reset", reset)] }) ++
      [{ moduleName := "Register32", instName := "u_csr_pc_reg",
         portMap := (csr_pc_next.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
                    [("clock", clock), ("reset", reset)] ++
                    (csr_pc_reg.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w))) },
       { moduleName := "Register32", instName := "u_csr_insn_reg",
         portMap := (csr_insn_next.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
                    [("clock", clock), ("reset", reset)] ++
                    (csr_insn_reg.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w))) }] ++
      [{ moduleName := "DFlipFlop", instName := "u_csr_flush_sup",
         portMap := [("d", csr_cdb_inject), ("q", csr_flush_suppress),
                     ("clock", clock), ("reset", reset)] }]
    else [])

  -- TrapSequencer instance (trap entry & mret)
  let (trap_rom_gates, trap_seq_insts) : (List Gate × List CircuitInstance) :=
    if enableTraps then
      let mret_seq_start_w := Wire.mk "mret_seq_start"
      -- IRQ injection: irq_pending = mip[7] AND mie[7] AND mstatus[3] (MIE bit)
      -- irq_inject = irq_pending AND NOT(any_active) → starts TRAP_ENTRY sequence
      let irq_inject := Wire.mk "irq_inject"
      let irq_gates :=
        [Gate.mkAND (Wire.mk "irq_pending") (Wire.mk "not_any_active") irq_inject,
         -- IRQ inject also starts the sequencer (OR into useq_start)
         Gate.mkOR (Wire.mk "useq_start") irq_inject (Wire.mk "useq_start_irq")]
      -- PC from selected slot (for trap sequencer's pc_in)
      let ser_pc_for_trap := CPU.makeIndexedWires "ser_pc_trap" 32
      let ser_pc_trap_gates := (List.range 32).map (fun i =>
        Gate.mkMUX fetch_pc_0[i]! fetch_pc_1[i]! ser_slot_sel ser_pc_for_trap[i]!)
      -- Sequencer instance
      let sequencerInst : CircuitInstance := {
        moduleName := "TrapSequencer"
        instName := "u_trap_seq"
        portMap :=
          [("clock", clock), ("reset", reset),
           ("start", Wire.mk "useq_start_irq"),
           ("is_interrupt", Wire.mk "irq_inject"),
           ("is_mret", mret_seq_start_w),
           ("rob_empty", rob_empty),
           ("sb_empty", Wire.mk "lsu_sb_empty")] ++
          (List.range 32).map (fun i => (s!"csr_read_data_{i}", Wire.mk s!"csr_cdb_dt_e{i}")) ++
          [("pipeline_flush", pipeline_flush_comb)] ++
          (List.range 32).map (fun i => (s!"pc_in_{i}", ser_pc_for_trap[i]!)) ++
          [("active", useq_active),
           ("drain_complete", useq_drain_complete),
           ("write_en", useq_write_en)] ++
          (List.range 32).map (fun i => (s!"write_data_{i}", useq_write_data[i]!)) ++
          [("csr_sel_0", useq_csr_sel[0]!),
           ("csr_sel_1", useq_csr_sel[1]!)] ++
          (List.range 32).map (fun i => (s!"redir_next_{i}", useq_redir_next[i]!)) ++
          [("mstatus_trap_active", useq_mstatus_trap),
           ("mstatus_mret_active", useq_mstatus_mret)]
      }
      -- DFF to delay useq_drain_complete by 1 cycle
      let useq_dc_dff : CircuitInstance := {
        moduleName := "DFlipFlop"
        instName := "u_useq_dc_dff"
        portMap := [("d", useq_drain_complete), ("q", Wire.mk "useq_dc_delayed"),
                    ("clock", clock), ("reset", reset)]
      }
      (irq_gates ++ ser_pc_trap_gates,
       [sequencerInst, useq_dc_dff])
    else
      (useq_csr_sel.map (fun w => Gate.mkBUF zero w), [])

  -- fetch_stall = global_stall OR pipeline_flush OR fence_i_draining_next OR fetch_stall_ext
  let fetch_stall_gates :=
    [Gate.mkOR global_stall pipeline_flush (Wire.mk "fetch_stall_tmp"),
     Gate.mkOR (Wire.mk "fetch_stall_tmp") fence_i_draining_next (Wire.mk "fetch_stall_tmp2"),
     Gate.mkOR (Wire.mk "fetch_stall_tmp2") fetch_stall_ext fetch_stall]

  let fetch_inst : CircuitInstance := {
    moduleName := "FetchStage_W2"
    instName := "u_fetch"
    portMap := [("clock", clock), ("reset", reset), ("stall", fetch_stall),
                ("half_step", Wire.mk "any_dual_stall"),
                ("branch_valid", branch_redirect_valid_reg)] ++
               bundledPorts "branch_target" branch_redirect_target_reg ++
               bundledPorts "instr_0" imem_resp_data_0 ++
               bundledPorts "instr_1" imem_resp_data_1 ++
               bundledPorts "pc_0" fetch_pc_0 ++
               bundledPorts "pc_1" fetch_pc_1 ++
               [("valid_0", Wire.mk "fetch_valid_0"), ("valid_1", Wire.mk "fetch_valid_1"),
                ("pt_0", Wire.mk "fetch_pt_0"), ("pt_1", Wire.mk "fetch_pt_1"),
                ("stalled_reg", fetch_stalled)]
  }

  -- === DECODE STAGE (W2) ===
  let decoderModuleName :=
    if config.xlen == 64 then
      if enableD && enableM then "RV64GDecoder"
      else if enableF && enableM then "RV64IMFDecoder"
      else if enableF then "RV64IFDecoder"
      else if enableM then "RV64IMDecoder"
      else "RV64IDecoder"
    else
      if enableD && enableM then "RV32GDecoder"
      else if enableF && enableM then "RV32IMFDecoder"
      else if enableF then "RV32IFDecoder"
      else if enableM then "RV32IMDecoder"
      else "RV32IDecoder"

  -- Extended decoder helper that returns more output wires
  let mkDecoder (idx : Nat) (instr : List Wire) :=
    let pfx := s!"dec{idx}"
    let optype := CPU.makeIndexedWires s!"{pfx}_optype" opcodeWidth
    let rd := CPU.makeIndexedWires s!"{pfx}_rd" 5
    let rs1 := CPU.makeIndexedWires s!"{pfx}_rs1" 5
    let rs2 := CPU.makeIndexedWires s!"{pfx}_rs2" 5
    let imm := CPU.makeIndexedWires s!"{pfx}_imm" 32
    let valid := Wire.mk s!"{pfx}_valid"
    let has_rd := Wire.mk s!"{pfx}_has_rd"
    let is_int := Wire.mk s!"{pfx}_is_int"
    let is_mem := Wire.mk s!"{pfx}_is_mem"
    let is_br := Wire.mk s!"{pfx}_is_br"
    let is_st := Wire.mk s!"{pfx}_is_st"
    let is_atomic := Wire.mk s!"{pfx}_is_atomic"
    let use_imm := Wire.mk s!"{pfx}_use_imm"
    let is_muldiv := Wire.mk s!"{pfx}_is_muldiv"
    -- FP decoder outputs
    let is_fp := Wire.mk s!"{pfx}_is_fp"
    let has_fp_rd := Wire.mk s!"{pfx}_has_fp_rd"
    let fp_rs1_read := Wire.mk s!"{pfx}_fp_rs1_read"
    let fp_rs2_read := Wire.mk s!"{pfx}_fp_rs2_read"
    let fp_rs3_used := Wire.mk s!"{pfx}_fp_rs3_used"
    let is_fp_load := Wire.mk s!"{pfx}_is_fp_load"
    let is_fp_store := Wire.mk s!"{pfx}_is_fp_store"
    let rs3 := CPU.makeIndexedWires s!"{pfx}_rs3" 5
    let rm := CPU.makeIndexedWires s!"{pfx}_rm" 3
    let inst : CircuitInstance := {
      moduleName := decoderModuleName, instName := s!"u_decoder_{idx}",
      portMap := bundledPorts "io_instr" instr ++ bundledPorts "io_optype" optype ++
                 bundledPorts "io_rd" rd ++ bundledPorts "io_rs1" rs1 ++ bundledPorts "io_rs2" rs2 ++ bundledPorts "io_imm" imm ++
                 [("io_valid", valid), ("io_has_rd", has_rd),
                  ("io_is_integer", is_int), ("io_is_memory", is_mem),
                  ("io_is_branch", is_br), ("io_is_store", is_st),
                  ("io_is_atomic", is_atomic),
                  ("io_use_imm", use_imm)] ++
                 (if enableM then [("io_is_muldiv", is_muldiv)] else []) ++
                 (if enableF then
                   [("io_is_fp", is_fp), ("io_has_fp_rd", has_fp_rd),
                    ("io_fp_rs1_read", fp_rs1_read), ("io_fp_rs2_read", fp_rs2_read),
                    ("io_fp_rs3_used", fp_rs3_used),
                    ("io_is_fp_load", is_fp_load), ("io_is_fp_store", is_fp_store)] ++
                   bundledPorts "io_rs3" rs3 ++ bundledPorts "io_rm" rm
                  else [])
    }
    (inst, optype, rd, rs1, rs2, imm, valid, has_rd, is_int, is_mem, is_br, is_st, is_atomic, use_imm, is_muldiv,
     is_fp, has_fp_rd, fp_rs1_read, fp_rs2_read, fp_rs3_used, is_fp_load, is_fp_store, rs3, rm)

  let (dec0_inst, d0_op, d0_rd, d0_rs1, d0_rs2, d0_imm, d0_valid_raw, d0_has_rd, d0_is_int, d0_is_mem, d0_is_br, d0_is_st, d0_is_atomic, d0_use_imm, d0_is_muldiv,
       d0_is_fp, d0_has_fp_rd, d0_fp_rs1_read, d0_fp_rs2_read, d0_fp_rs3_used, d0_is_fp_load, d0_is_fp_store, d0_rs3, d0_rm) := mkDecoder 0 imem_resp_data_0
  let (dec1_inst, d1_op, d1_rd, d1_rs1, d1_rs2, d1_imm, d1_valid_raw, d1_has_rd, d1_is_int, d1_is_mem, d1_is_br, d1_is_st, d1_is_atomic, d1_use_imm, d1_is_muldiv,
       d1_is_fp, d1_has_fp_rd, d1_fp_rs1_read, d1_fp_rs2_read, d1_fp_rs3_used, d1_is_fp_load, d1_is_fp_store, d1_rs3, d1_rm) := mkDecoder 1 imem_resp_data_1

  -- Gate decoder valid by fetch valid (e.g. fetch invalidates slot 1 when slot 0 is taken)
  let fetch_valid_0 := Wire.mk "fetch_valid_0"
  let fetch_valid_1 := Wire.mk "fetch_valid_1"
  let d0_valid := Wire.mk "d0_valid_gated"
  let d1_valid := Wire.mk "d1_valid_gated"
  -- Gate slot 1 by NOT(ifetch_last_word): when PC is at last word of cache line,
  -- slot 1 data wraps around (invalid). Force slot 1 invalid so next cycle refetches.
  let fetch_valid_1_masked := Wire.mk "fetch_valid_1_masked"
  let fetch_valid_gates :=
    [Gate.mkAND d0_valid_raw fetch_valid_0 d0_valid,
     Gate.mkNOT ifetch_last_word (Wire.mk "not_last_word"),
     Gate.mkAND fetch_valid_1 (Wire.mk "not_last_word") fetch_valid_1_masked,
     Gate.mkAND d1_valid_raw fetch_valid_1_masked d1_valid]

  -- === PIPELINE CONTROL ===
  let rob_full := Wire.mk "rob_full"
  let rob_empty := Wire.mk "rob_empty"
  let rob_nearly_full := Wire.mk "rob_nearly_full"
  let rob_alloc_idx_0 := CPU.makeIndexedWires "rob_alloc_idx_0" 4
  let rob_alloc_idx_1 := CPU.makeIndexedWires "rob_alloc_idx_1" 4
  let rob_head_idx_0 := CPU.makeIndexedWires "rob_head_idx_0" 4
  let rob_head_idx_1 := CPU.makeIndexedWires "rob_head_idx_1" 4
  let commit_archRd_0 := CPU.makeIndexedWires "head_archRd_0" 5
  let commit_physRd_0 := CPU.makeIndexedWires "head_physRd_0" 6
  let commit_archRd_1 := CPU.makeIndexedWires "head_archRd_1" 5
  let commit_physRd_1 := CPU.makeIndexedWires "head_physRd_1" 6
  let rob_head_oldPhysRd_0 := CPU.makeIndexedWires "head_oldPhysRd_0" 6
  let rob_head_oldPhysRd_1 := CPU.makeIndexedWires "head_oldPhysRd_1" 6
  let rob_head_valid_0 := Wire.mk "head_valid_0"
  let rob_head_complete_0 := Wire.mk "head_complete_0"
  let rob_head_hasPhysRd_0 := Wire.mk "head_hasPhysRd_0"
  let rob_head_hasOldPhysRd_0 := Wire.mk "head_hasOldPhysRd_0"
  let rob_head_exception_0 := Wire.mk "head_exception_0"
  let rob_head_isBranch_0 := Wire.mk "head_isBranch_0"
  let rob_head_mispredicted_0 := Wire.mk "head_mispredicted_0"
  let rob_head_valid_1 := Wire.mk "head_valid_1"
  let rob_head_complete_1 := Wire.mk "head_complete_1"
  let rob_head_hasPhysRd_1 := Wire.mk "head_hasPhysRd_1"
  let rob_head_hasOldPhysRd_1 := Wire.mk "head_hasOldPhysRd_1"
  let rob_head_exception_1 := Wire.mk "head_exception_1"
  let rob_head_isBranch_1 := Wire.mk "head_isBranch_1"
  let rob_head_mispredicted_1 := Wire.mk "head_mispredicted_1"
  let retire_valid_0 := Wire.mk "commit_en_0"
  let retire_valid_1 := Wire.mk "commit_en_1"

  -- Branch tracking wires (defined early for RenameStage wiring; gates added later)
  let branch_tracking_0 := Wire.mk "branch_tracking_0"
  let branch_tracking_1 := Wire.mk "branch_tracking_1"
  let retire_any_old_0 := Wire.mk "retire_any_old_0"
  let retire_any_old_1 := Wire.mk "retire_any_old_1"
  let retire_tag_bt_0 := CPU.makeIndexedWires "retire_tag_bt_0" 6
  let retire_tag_bt_1 := CPU.makeIndexedWires "retire_tag_bt_1" 6

  -- === DISPATCH QUALIFICATION ===
  -- Gate decode_valid during redirect/flush
  let not_stall := Wire.mk "not_stall"
  let not_redirecting := Wire.mk "not_redirecting"
  let redirect_or := Wire.mk "redirect_or"
  let redirect_or_flush := Wire.mk "redirect_or_flush"
  let dispatch_base_valid_0 := Wire.mk "dispatch_base_valid_0"
  let dispatch_base_valid_1 := Wire.mk "dispatch_base_valid_1"
  let dispatch_int_0 := Wire.mk "dispatch_int_0"
  let dispatch_int_1 := Wire.mk "dispatch_int_1"
  let dispatch_mem_0 := Wire.mk "dispatch_mem_0"
  let dispatch_mem_1 := Wire.mk "dispatch_mem_1"
  let dispatch_br_0 := Wire.mk "dispatch_br_0"
  let dispatch_br_1 := Wire.mk "dispatch_br_1"
  let dispatch_muldiv_0 := Wire.mk "dispatch_muldiv_0"
  let dispatch_muldiv_1 := Wire.mk "dispatch_muldiv_1"
  let dispatch_fp_0 := Wire.mk "dispatch_fp_0"
  let dispatch_fp_1 := Wire.mk "dispatch_fp_1"
  let rename_valid_0 := Wire.mk "rename_valid_0"
  let rename_valid_1 := Wire.mk "rename_valid_1"

  let not_fence_i_suppress := Wire.mk "not_fence_i_suppress"
  let dispatch_gates :=
    [Gate.mkOR global_stall fetch_stall_ext (Wire.mk "dispatch_stall"),
     Gate.mkNOT (Wire.mk "dispatch_stall") not_stall,
     Gate.mkOR rob_redirect_valid branch_redirect_valid_reg redirect_or,
     Gate.mkOR redirect_or pipeline_flush redirect_or_flush,
     -- rename_ext_stall = dispatch_stall OR redirect_or_flush (suppress rename during redirect/flush)
     Gate.mkOR (Wire.mk "dispatch_stall") redirect_or_flush (Wire.mk "rename_ext_stall"),
     Gate.mkNOT redirect_or_flush not_redirecting,
     Gate.mkNOT fence_i_suppress not_fence_i_suppress,
     -- Slot 0 base valid (gated by fence_i_suppress)
     Gate.mkAND d0_valid not_redirecting (Wire.mk "d0_no_redir"),
     Gate.mkAND (Wire.mk "d0_no_redir") not_fence_i_suppress (Wire.mk "d0_no_ser"),
     Gate.mkAND (Wire.mk "d0_no_ser") not_stall (Wire.mk "d0_base_tmp"),
     Gate.mkAND (Wire.mk "d0_base_tmp") rename_valid_0 (Wire.mk "d0_base_pre"),
     -- Gate dispatch on CSR rename cycle: CSR goes through rename but NOT to ROB
     -- Per-slot CSR suppress: only suppress the slot that HAS the CSR (and later slots)
     -- ser_slot_sel=0 → CSR at slot 0 → suppress both; ser_slot_sel=1 → CSR at slot 1 → suppress only slot 1
     Gate.mkNOT ser_slot_sel (Wire.mk "not_ser_slot_sel"),
     Gate.mkAND csr_rename_en (Wire.mk "not_ser_slot_sel") (Wire.mk "d0_csr_suppress"),
     Gate.mkNOT (Wire.mk "d0_csr_suppress") (Wire.mk "d0_not_csr_sup"),
     Gate.mkAND (Wire.mk "d0_base_pre") (Wire.mk "d0_not_csr_sup") dispatch_base_valid_0,
     -- Slot 1 base valid
     Gate.mkAND d1_valid not_redirecting (Wire.mk "d1_no_redir"),
     Gate.mkAND (Wire.mk "d1_no_redir") not_fence_i_suppress (Wire.mk "d1_no_ser"),
     Gate.mkAND (Wire.mk "d1_no_ser") not_stall (Wire.mk "d1_base_tmp"),
     Gate.mkAND (Wire.mk "d1_base_tmp") rename_valid_1 (Wire.mk "d1_base_pre"),
     Gate.mkAND (Wire.mk "d1_base_pre") not_csr_rename_en (Wire.mk "d1_base_pre2"),
     Gate.mkAND (Wire.mk "d1_base_pre2") (Wire.mk "not_dual_stall") dispatch_base_valid_1,
     -- Per-type qualification for each slot
     Gate.mkAND dispatch_base_valid_0 d0_is_int dispatch_int_0,
     Gate.mkAND dispatch_base_valid_1 d1_is_int dispatch_int_1,
     Gate.mkAND dispatch_base_valid_0 d0_is_mem dispatch_mem_0,
     Gate.mkAND dispatch_base_valid_1 d1_is_mem dispatch_mem_1,
     Gate.mkAND dispatch_base_valid_0 d0_is_br dispatch_br_0,
     Gate.mkAND dispatch_base_valid_1 d1_is_br dispatch_br_1] ++
    (if enableM then
      [Gate.mkAND dispatch_base_valid_0 d0_is_muldiv dispatch_muldiv_0,
       Gate.mkAND dispatch_base_valid_1 d1_is_muldiv dispatch_muldiv_1]
    else
      [Gate.mkBUF zero dispatch_muldiv_0, Gate.mkBUF zero dispatch_muldiv_1]) ++
    -- FP dispatch qualification
    (if enableF then
      [Gate.mkAND dispatch_base_valid_0 d0_is_fp dispatch_fp_0,
       Gate.mkAND dispatch_base_valid_1 d1_is_fp dispatch_fp_1]
    else
      [Gate.mkBUF zero dispatch_fp_0, Gate.mkBUF zero dispatch_fp_1])

  -- === has_rd_int: filter out FP-dest instructions from INT rename ===
  let d0_has_rd_int := Wire.mk "d0_has_rd_int"
  let d1_has_rd_int := Wire.mk "d1_has_rd_int"
  let has_rd_int_gates :=
    if enableF then
      [Gate.mkNOT d0_has_fp_rd (Wire.mk "d0_not_has_fp_rd"),
       Gate.mkAND d0_has_rd (Wire.mk "d0_not_has_fp_rd") d0_has_rd_int,
       Gate.mkNOT d1_has_fp_rd (Wire.mk "d1_not_has_fp_rd"),
       Gate.mkAND d1_has_rd (Wire.mk "d1_not_has_fp_rd") d1_has_rd_int]
    else
      [Gate.mkBUF d0_has_rd d0_has_rd_int,
       Gate.mkBUF d1_has_rd d1_has_rd_int]

  -- === has_rd_nox0 for busy-table guard (don't set busy[p0]) ===
  let d0_rd_nonzero := Wire.mk "d0_rd_nonzero"
  let d1_rd_nonzero := Wire.mk "d1_rd_nonzero"
  let d0_has_rd_nox0 := Wire.mk "d0_has_rd_nox0"
  let d1_has_rd_nox0 := Wire.mk "d1_has_rd_nox0"
  let busy_set_en_0 := Wire.mk "busy_set_en_0"
  let busy_set_en_1 := Wire.mk "busy_set_en_1"
  let rd_nox0_gates :=
    [Gate.mkOR d0_rd[0]! d0_rd[1]! (Wire.mk "d0_rd_or01"),
     Gate.mkOR (Wire.mk "d0_rd_or01") d0_rd[2]! (Wire.mk "d0_rd_or012"),
     Gate.mkOR (Wire.mk "d0_rd_or012") d0_rd[3]! (Wire.mk "d0_rd_or0123"),
     Gate.mkOR (Wire.mk "d0_rd_or0123") d0_rd[4]! d0_rd_nonzero,
     Gate.mkAND d0_has_rd_int d0_rd_nonzero d0_has_rd_nox0,
     Gate.mkAND dispatch_base_valid_0 d0_has_rd_nox0 busy_set_en_0,
     Gate.mkOR d1_rd[0]! d1_rd[1]! (Wire.mk "d1_rd_or01"),
     Gate.mkOR (Wire.mk "d1_rd_or01") d1_rd[2]! (Wire.mk "d1_rd_or012"),
     Gate.mkOR (Wire.mk "d1_rd_or012") d1_rd[3]! (Wire.mk "d1_rd_or0123"),
     Gate.mkOR (Wire.mk "d1_rd_or0123") d1_rd[4]! d1_rd_nonzero,
     Gate.mkAND d1_has_rd_int d1_rd_nonzero d1_has_rd_nox0,
     Gate.mkAND dispatch_base_valid_1 d1_has_rd_nox0 busy_set_en_1]

  -- Masked dest tags: zero out physRd when rd=x0 (prevent CDB from writing garbage to PRF)
  let int_dest_tag_masked_0 := CPU.makeIndexedWires "int_dtm_0" 6
  let int_dest_tag_masked_1 := CPU.makeIndexedWires "int_dtm_1" 6
  let dest_tag_mask_gates :=
    (List.range 6).map (fun i => Gate.mkAND rd_phys_0[i]! d0_has_rd_nox0 int_dest_tag_masked_0[i]!) ++
    (List.range 6).map (fun i => Gate.mkAND rd_phys_1[i]! d1_has_rd_nox0 int_dest_tag_masked_1[i]!)

  -- ROB alloc_hasPhysRd must include branches (force_alloc allocates a tag for them)
  -- Also includes FP rd (FLW etc.) — these need hasPhysRd for ROB commit to free the old tag
  let rob_alloc_hasPhysRd_0 := Wire.mk "rob_alloc_hasPhysRd_0"
  let rob_alloc_hasPhysRd_1 := Wire.mk "rob_alloc_hasPhysRd_1"
  let rob_hasPhysRd_gates :=
    if enableF then
      [Gate.mkOR d0_has_rd_nox0 d0_has_fp_rd (Wire.mk "d0_has_any_rd_nox0"),
       Gate.mkOR d0_is_br (Wire.mk "d0_has_any_rd_nox0") rob_alloc_hasPhysRd_0,
       Gate.mkOR d1_has_rd_nox0 d1_has_fp_rd (Wire.mk "d1_has_any_rd_nox0"),
       Gate.mkOR d1_is_br (Wire.mk "d1_has_any_rd_nox0") rob_alloc_hasPhysRd_1]
    else
      [Gate.mkOR d0_is_br d0_has_rd_nox0 rob_alloc_hasPhysRd_0,
       Gate.mkOR d1_is_br d1_has_rd_nox0 rob_alloc_hasPhysRd_1]

  -- === DISPATCH ROUTING ===
  -- Integer RS gets both slots directly (W=2 RS has dual issue ports).
  -- Single-unit RS (branch, mem, muldiv): MUX between slot 0 and slot 1.
  -- If both slots have the same type, route slot 0 and stall (dual_stall).

  -- Dual-stall detection: computed from pre-stall signals to avoid combinational cycle.
  -- "Both slots want the same single-unit resource" is known from decode classification
  -- before stall gating. Pre-stall valid = d{k}_no_ser AND rename_valid_{k}.
  let pre_valid_0 := Wire.mk "pre_valid_0"
  let pre_valid_1 := Wire.mk "pre_valid_1"
  let br_dual_stall := Wire.mk "br_dual_stall"
  let mem_dual_stall := Wire.mk "mem_dual_stall"
  let muldiv_dual_stall := Wire.mk "muldiv_dual_stall"
  let fp_dual_stall := Wire.mk "fp_dual_stall"
  let dual_stall_gates :=
    [Gate.mkAND (Wire.mk "d0_no_ser") rename_valid_0 pre_valid_0,
     Gate.mkAND (Wire.mk "d1_no_ser") rename_valid_1 pre_valid_1,
     -- Branch dual stall: both slots are branch AND both decoder-valid (raw, not fetch-gated)
     -- Uses d0/d1_valid_raw to avoid combinational loop through fetch valid_1 / half_step
     Gate.mkAND d0_valid_raw d0_is_br (Wire.mk "pre_br_0"),
     Gate.mkAND d1_valid_raw d1_is_br (Wire.mk "pre_br_1"),
     Gate.mkAND (Wire.mk "pre_br_0") (Wire.mk "pre_br_1") br_dual_stall,
     -- Memory dual stall: only 1 memory RS issue port, stall if both slots are memory
     Gate.mkAND d0_valid_raw d0_is_mem (Wire.mk "pre_mem_0"),
     Gate.mkAND d1_valid_raw d1_is_mem (Wire.mk "pre_mem_1"),
     Gate.mkAND (Wire.mk "pre_mem_0") (Wire.mk "pre_mem_1") mem_dual_stall] ++
    (if enableM then
      [Gate.mkAND d0_valid_raw d0_is_muldiv (Wire.mk "pre_md_0"),
       Gate.mkAND d1_valid_raw d1_is_muldiv (Wire.mk "pre_md_1"),
       Gate.mkAND (Wire.mk "pre_md_0") (Wire.mk "pre_md_1") muldiv_dual_stall]
    else [Gate.mkBUF zero muldiv_dual_stall]) ++
    (if enableF then
      let d0_fp_res := Wire.mk "d0_fp_res"
      let d1_fp_res := Wire.mk "d1_fp_res"
      let d0_needs_fp := Wire.mk "d0_needs_fp_ren_pre"
      let d1_needs_fp := Wire.mk "d1_needs_fp_ren_pre"
      [-- Stall when both slots need FP resources (is_fp OR has_fp_rd OR is_fp_store covers FP exec + FLW + FSW)
       Gate.mkOR d0_is_fp d0_has_fp_rd d0_fp_res,
       Gate.mkOR d0_fp_res d0_is_fp_store d0_needs_fp,
       Gate.mkAND d0_valid_raw d0_needs_fp (Wire.mk "pre_fp_0"),
       Gate.mkOR d1_is_fp d1_has_fp_rd d1_fp_res,
       Gate.mkOR d1_fp_res d1_is_fp_store d1_needs_fp,
       Gate.mkAND d1_valid_raw d1_needs_fp (Wire.mk "pre_fp_1"),
       Gate.mkAND (Wire.mk "pre_fp_0") (Wire.mk "pre_fp_1") fp_dual_stall]
    else [Gate.mkBUF zero fp_dual_stall])

  -- Branch routing MUX: slot 0 has priority
  let br_route_sel := Wire.mk "br_route_sel"  -- 1 = use slot 1
  let br_not_s0 := Wire.mk "br_not_s0"
  let br_dispatch_valid := Wire.mk "br_dispatch_valid"
  let br_route_gates :=
    [Gate.mkNOT dispatch_br_0 br_not_s0,
     Gate.mkAND br_not_s0 dispatch_br_1 br_route_sel,
     Gate.mkOR dispatch_br_0 dispatch_br_1 br_dispatch_valid]

  -- Forward-declare FP wires needed by memory and ROB sections
  let fp_issue_dest_tag := CPU.makeIndexedWires "fp_issue_dest_tag" 6
  let rob_head_is_fp_0 := Wire.mk "rob_head_is_fp_0"
  let rob_head_is_fp_1 := Wire.mk "rob_head_is_fp_1"

  -- Memory routing MUX
  let mem_route_sel := Wire.mk "mem_route_sel"
  let mem_not_s0 := Wire.mk "mem_not_s0"
  let mem_dispatch_valid := Wire.mk "mem_dispatch_valid"
  let mem_route_gates :=
    [Gate.mkNOT dispatch_mem_0 mem_not_s0,
     Gate.mkAND mem_not_s0 dispatch_mem_1 mem_route_sel,
     Gate.mkOR dispatch_mem_0 dispatch_mem_1 mem_dispatch_valid]

  -- MulDiv routing MUX
  let muldiv_route_sel := Wire.mk "muldiv_route_sel"
  let muldiv_not_s0 := Wire.mk "muldiv_not_s0"
  let muldiv_dispatch_valid := Wire.mk "muldiv_dispatch_valid_pre"
  let muldiv_route_gates :=
    if enableM then
      [Gate.mkNOT dispatch_muldiv_0 muldiv_not_s0,
       Gate.mkAND muldiv_not_s0 dispatch_muldiv_1 muldiv_route_sel,
       Gate.mkOR dispatch_muldiv_0 dispatch_muldiv_1 muldiv_dispatch_valid]
    else
      [Gate.mkBUF zero muldiv_route_sel, Gate.mkBUF zero muldiv_dispatch_valid]

  -- FP routing MUX (for FP RS dispatch: only is_fp instructions)
  let fp_route_sel := Wire.mk "fp_route_sel"
  let fp_not_s0 := Wire.mk "fp_not_s0"
  let fp_dispatch_valid := Wire.mk "fp_dispatch_valid_pre"
  -- FP rename routing: broader signal including FP loads (has_fp_rd but not is_fp)
  let fp_rename_route_sel := Wire.mk "fp_rename_route_sel"
  let fp_rs2_route_sel := Wire.mk "fp_rs2_route_sel"
  let fp_rename_dispatch_valid := Wire.mk "fp_rename_dispatch_valid"
  let dispatch_fp_rename_0 := Wire.mk "dispatch_fp_rename_0"
  let dispatch_fp_rename_1 := Wire.mk "dispatch_fp_rename_1"
  let fp_route_gates :=
    if enableF then
      [Gate.mkNOT dispatch_fp_0 fp_not_s0,
       Gate.mkAND fp_not_s0 dispatch_fp_1 fp_route_sel,
       Gate.mkOR dispatch_fp_0 dispatch_fp_1 fp_dispatch_valid,
       -- FP rename valid includes is_fp OR has_fp_rd (for FLW dest tag)
       Gate.mkOR d0_is_fp d0_has_fp_rd (Wire.mk "d0_needs_fp_rename"),
       Gate.mkAND dispatch_base_valid_0 (Wire.mk "d0_needs_fp_rename") dispatch_fp_rename_0,
       Gate.mkOR d1_is_fp d1_has_fp_rd (Wire.mk "d1_needs_fp_rename"),
       Gate.mkAND dispatch_base_valid_1 (Wire.mk "d1_needs_fp_rename") dispatch_fp_rename_1,
       Gate.mkNOT dispatch_fp_rename_0 (Wire.mk "fp_ren_not_s0"),
       Gate.mkAND (Wire.mk "fp_ren_not_s0") dispatch_fp_rename_1 fp_rename_route_sel,
       Gate.mkOR dispatch_fp_rename_0 dispatch_fp_rename_1 fp_rename_dispatch_valid,
       -- FP rs2 route select: FP RS gets priority for rs2 port; else FSW uses mem_route_sel
       Gate.mkMUX mem_route_sel fp_route_sel fp_dispatch_valid fp_rs2_route_sel]
    else
      [Gate.mkBUF zero fp_route_sel, Gate.mkBUF zero fp_dispatch_valid,
       Gate.mkBUF zero fp_rename_route_sel, Gate.mkBUF zero fp_rename_dispatch_valid,
       Gate.mkBUF zero dispatch_fp_rename_0, Gate.mkBUF zero dispatch_fp_rename_1,
       Gate.mkBUF zero fp_rs2_route_sel]

  -- === RENAME STAGE (W2) ===
  let rs1_phys_0 := CPU.makeIndexedWires "rs1_phys_0" 6
  let rs2_phys_0 := CPU.makeIndexedWires "rs2_phys_0" 6
  let rd_phys_0  := CPU.makeIndexedWires "rd_phys_0" 6
  let rs1_data_0 := CPU.makeIndexedWires "rs1_data_0" (if config.xlen == 64 then 64 else 32)
  let rs2_data_0 := CPU.makeIndexedWires "rs2_data_0" (if config.xlen == 64 then 64 else 32)
  let old_physRd_0 := CPU.makeIndexedWires "old_physRd_0" 6

  let rs1_phys_1 := CPU.makeIndexedWires "rs1_phys_1" 6
  let rs2_phys_1 := CPU.makeIndexedWires "rs2_phys_1" 6
  let rd_phys_1  := CPU.makeIndexedWires "rd_phys_1" 6
  let rs1_data_1 := CPU.makeIndexedWires "rs1_data_1" (if config.xlen == 64 then 64 else 32)
  let rs2_data_1 := CPU.makeIndexedWires "rs2_data_1" (if config.xlen == 64 then 64 else 32)
  let old_physRd_1 := CPU.makeIndexedWires "old_physRd_1" 6

  -- RVVI PRF readback data (from PRF read ports 5/6)
  let prf_rvvi_data_0 := CPU.makeIndexedWires "prf_rvvi_data_0" (if config.xlen == 64 then 64 else 32)
  let prf_rvvi_data_1 := CPU.makeIndexedWires "prf_rvvi_data_1" (if config.xlen == 64 then 64 else 32)

  let cdb_valid_0 := Wire.mk "cdb_valid_0"; let cdb_tag_0 := CPU.makeIndexedWires "cdb_tag_0" 6
  let cdb_data_0 := CPU.makeIndexedWires "cdb_data_0" (if config.xlen == 64 || config.enableD then 64 else 32)
  let cdb_data32_0 := cdb_data_0.take (if config.xlen == 64 then 64 else 32)
  let cdb_valid_1 := Wire.mk "cdb_valid_1"; let cdb_tag_1 := CPU.makeIndexedWires "cdb_tag_1" 6; let cdb_data_1 := CPU.makeIndexedWires "cdb_data_1" (if config.xlen == 64 || config.enableD then 64 else 32)
  let cdb_data32_1 := cdb_data_1.take (if config.xlen == 64 then 64 else 32)

  -- CDB snoop for CSR rs1 capture: during drain, compare captured rs1 tag against CDB
  -- If match, capture CDB data into csr_rs1cap_reg. Also capture initial value on fence_i_start.
  let (cdb_fwd_rs1_gates, cdb_fwd_rs1_insts) : (List Gate × List CircuitInstance) :=
    if config.enableZicsr then
      let pfx := "csr_snoop"
      let match0 := Wire.mk s!"{pfx}_m0"
      let match0_v := Wire.mk s!"{pfx}_m0v"
      let match1 := Wire.mk s!"{pfx}_m1"
      let match1_v := Wire.mk s!"{pfx}_m1v"
      let cdb_snoop_hit := Wire.mk "cdb_snoop_hit"
      -- Compare captured rs1 tag against CDB tags
      let cmp0_inst : CircuitInstance := {
        moduleName := "EqualityComparator6"
        instName := s!"u_{pfx}_cmp0"
        portMap := [("eq", match0)] ++
                   (cdb_tag_0.enum.map fun ⟨i, w⟩ => (s!"a_{i}", w)) ++
                   (csr_rs1tag_reg.enum.map fun ⟨i, w⟩ => (s!"b_{i}", w)) }
      let cmp1_inst : CircuitInstance := {
        moduleName := "EqualityComparator6"
        instName := s!"u_{pfx}_cmp1"
        portMap := [("eq", match1)] ++
                   (cdb_tag_1.enum.map fun ⟨i, w⟩ => (s!"a_{i}", w)) ++
                   (csr_rs1tag_reg.enum.map fun ⟨i, w⟩ => (s!"b_{i}", w)) }
      -- Gate with valid AND fence_i_draining (only snoop during drain)
      let m0_drain := Wire.mk s!"{pfx}_m0d"
      let m1_drain := Wire.mk s!"{pfx}_m1d"
      let gates :=
        [Gate.mkAND match0 cdb_valid_0 match0_v,
         Gate.mkAND match1 cdb_valid_1 match1_v,
         Gate.mkAND match0_v fence_i_draining m0_drain,
         Gate.mkAND match1_v fence_i_draining m1_drain,
         Gate.mkOR m0_drain m1_drain cdb_snoop_hit,
         -- rs1cap_update_en = fence_i_start OR cdb_snoop_hit
         Gate.mkOR fence_i_start cdb_snoop_hit (Wire.mk "rs1cap_update_en")]
      -- Snoop data MUX: CDB0 has priority over CDB1 (if both match, use CDB0)
      let snoop_data := CPU.makeIndexedWires "csr_snoop_data" (if config.xlen == 64 then 64 else 32)
      let snoop_data_gates := (List.range (if config.xlen == 64 then 64 else 32)).map fun i =>
        let tmp := Wire.mk s!"csr_snoop_tmp_{i}"
        [Gate.mkMUX cdb_data_1[i]! cdb_data_0[i]! m0_drain tmp,
         -- On fence_i_start: use slot-muxed rs1_data (initial capture)
         -- During drain snoop: use snoop data from CDB
         -- ser_r1 wires from capture section hold slot-muxed value
         Gate.mkMUX (Wire.mk s!"ser_r1_{i}") tmp cdb_snoop_hit snoop_data[i]!]
      -- The snoop_data feeds csr_rs1cap_next through rs1cap_update_en
      -- But wait - the capture MUX in ser_capture_gates uses ser_r1 → csr_rs1cap_next
      -- We need snoop_data to override. Redefine: csr_rs1cap_next MUX uses snoop_data
      (gates ++ snoop_data_gates.flatten, [cmp0_inst, cmp1_inst])
    else ([], [])

  let cdb_mispredicted_reg_1 := Wire.mk "cdb_mispredicted_reg_1"

  let src1_ready_0 := Wire.mk "src1_ready_0"; let src2_ready_0 := Wire.mk "src2_ready_0"
  let src1_ready_1 := Wire.mk "src1_ready_1"; let src2_ready_1 := Wire.mk "src2_ready_1"

  -- MUX data for single-unit RS (branch): select between slot 0 and slot 1 data
  let br_mux_opcode := CPU.makeIndexedWires "br_mux_opcode" opcodeWidth
  let br_mux_rs1_phys := CPU.makeIndexedWires "br_mux_rs1_phys" 6
  let br_mux_rs2_phys := CPU.makeIndexedWires "br_mux_rs2_phys" 6
  let br_mux_rs1_data := CPU.makeIndexedWires "br_mux_rs1_data" (if config.xlen == 64 then 64 else 32)
  let br_mux_rs2_data := CPU.makeIndexedWires "br_mux_rs2_data" (if config.xlen == 64 then 64 else 32)
  let br_mux_rd_phys := CPU.makeIndexedWires "br_mux_rd_phys" 6
  let br_mux_src1_ready := Wire.mk "br_mux_src1_ready"
  let br_mux_src2_ready := Wire.mk "br_mux_src2_ready"
  let br_mux_imm := CPU.makeIndexedWires "br_mux_imm" 32
  let br_mux_pc := CPU.makeIndexedWires "br_mux_pc" 32
  let br_mux_data_gates :=
    (List.range opcodeWidth).map (fun i =>
      Gate.mkMUX (d0_op.take opcodeWidth)[i]! (d1_op.take opcodeWidth)[i]! br_route_sel br_mux_opcode[i]!) ++
    (List.range 6).map (fun i =>
      Gate.mkMUX rs1_phys_0[i]! rs1_phys_1[i]! br_route_sel br_mux_rs1_phys[i]!) ++
    (List.range 6).map (fun i =>
      Gate.mkMUX rs2_phys_0[i]! rs2_phys_1[i]! br_route_sel br_mux_rs2_phys[i]!) ++
    (List.range (if config.xlen == 64 then 64 else 32)).map (fun i =>
      Gate.mkMUX rs1_data_0[i]! rs1_data_1[i]! br_route_sel br_mux_rs1_data[i]!) ++
    (List.range (if config.xlen == 64 then 64 else 32)).map (fun i =>
      Gate.mkMUX rs2_data_0[i]! rs2_data_1[i]! br_route_sel br_mux_rs2_data[i]!) ++
    (List.range 6).map (fun i =>
      Gate.mkMUX rd_phys_0[i]! rd_phys_1[i]! br_route_sel br_mux_rd_phys[i]!) ++
    [Gate.mkMUX src1_ready_0 src1_ready_1 br_route_sel br_mux_src1_ready,
     Gate.mkMUX src2_ready_0 src2_ready_1 br_route_sel br_mux_src2_ready] ++
    (List.range 32).map (fun i =>
      Gate.mkMUX d0_imm[i]! d1_imm[i]! br_route_sel br_mux_imm[i]!) ++
    (List.range 32).map (fun i =>
      Gate.mkMUX fetch_pc_0[i]! fetch_pc_1[i]! br_route_sel br_mux_pc[i]!)

  -- MUX data for memory RS
  let mem_mux_opcode := CPU.makeIndexedWires "mem_mux_opcode" opcodeWidth
  let mem_mux_rs1_phys := CPU.makeIndexedWires "mem_mux_rs1_phys" 6
  let mem_mux_rs2_phys := CPU.makeIndexedWires "mem_mux_rs2_phys" 6
  let mem_mux_rs1_data := CPU.makeIndexedWires "mem_mux_rs1_data" (if config.xlen == 64 then 64 else 32)
  let mem_mux_rs2_data := CPU.makeIndexedWires "mem_mux_rs2_data" (if config.xlen == 64 || config.enableD then 64 else 32)
  let mem_mux_rd_phys := CPU.makeIndexedWires "mem_mux_rd_phys" 6
  -- Forward-declare FP rename wires needed for FSW/FSD src2 override in mem RS
  let mem_fp_rs2_phys := CPU.makeIndexedWires "fp_rs2_phys" 6
  let mem_fp_rs2_data := CPU.makeIndexedWires "fp_issue_src2_data" (if config.enableD then 64 else 32)
  let mem_fp_issue_src2_ready := Wire.mk "fp_issue_src2_ready"
  let mem_mux_src1_ready := Wire.mk "mem_mux_src1_ready"
  let mem_mux_src2_ready := Wire.mk "mem_mux_src2_ready"
  let mem_mux_imm := CPU.makeIndexedWires "mem_mux_imm" 32
  let mem_mux_is_store := Wire.mk "mem_mux_is_store"
  let mem_mux_data_gates :=
    (List.range opcodeWidth).map (fun i =>
      Gate.mkMUX (d0_op.take opcodeWidth)[i]! (d1_op.take opcodeWidth)[i]! mem_route_sel mem_mux_opcode[i]!) ++
    (List.range 6).map (fun i =>
      Gate.mkMUX rs1_phys_0[i]! rs1_phys_1[i]! mem_route_sel mem_mux_rs1_phys[i]!) ++
    -- FSW/FSD: src2 tag/data from FP rename instead of INT rename
    (if enableF then
      let mem_mux_int_rs2_phys := CPU.makeIndexedWires "mem_mux_int_rs2_phys" 6
      let mem_mux_is_fp_store := Wire.mk "mem_mux_is_fp_store"
      let mem_mux_int_rs2_data := CPU.makeIndexedWires "mem_mux_int_rs2_data" (if config.xlen == 64 then 64 else 32)
      let mem_mux_int_src2_ready := Wire.mk "mem_mux_int_src2_ready"
      [Gate.mkMUX d0_is_fp_store d1_is_fp_store mem_route_sel mem_mux_is_fp_store] ++
      (List.range 6).map (fun i =>
        Gate.mkMUX rs2_phys_0[i]! rs2_phys_1[i]! mem_route_sel mem_mux_int_rs2_phys[i]!) ++
      (List.range 6).map (fun i =>
        Gate.mkMUX mem_mux_int_rs2_phys[i]! mem_fp_rs2_phys[i]! mem_mux_is_fp_store mem_mux_rs2_phys[i]!) ++
      (List.range (if config.xlen == 64 then 64 else 32)).map (fun i =>
        Gate.mkMUX rs1_data_0[i]! rs1_data_1[i]! mem_route_sel mem_mux_rs1_data[i]!) ++
      (List.range (if config.xlen == 64 then 64 else 32)).map (fun i =>
        Gate.mkMUX rs2_data_0[i]! rs2_data_1[i]! mem_route_sel mem_mux_int_rs2_data[i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkMUX mem_mux_int_rs2_data[i]! mem_fp_rs2_data[i]! mem_mux_is_fp_store mem_mux_rs2_data[i]!) ++
      (if config.xlen == 64 || config.enableD then
        (List.range 32).map (fun i =>
          Gate.mkMUX (if config.xlen == 64 then mem_mux_int_rs2_data[32+i]! else zero) mem_fp_rs2_data[32+i]! mem_mux_is_fp_store mem_mux_rs2_data[32+i]!)
       else []) ++
      -- src2_ready override: FSW/FSD uses FP busy table ready
      [Gate.mkMUX (Wire.mk "src2_ready0_reg") (Wire.mk "src2_ready1_reg") mem_route_sel mem_mux_int_src2_ready] ++
      []
    else
      (List.range 6).map (fun i =>
        Gate.mkMUX rs2_phys_0[i]! rs2_phys_1[i]! mem_route_sel mem_mux_rs2_phys[i]!) ++
      (List.range (if config.xlen == 64 then 64 else 32)).map (fun i =>
        Gate.mkMUX rs1_data_0[i]! rs1_data_1[i]! mem_route_sel mem_mux_rs1_data[i]!) ++
      (List.range (if config.xlen == 64 || config.enableD then 64 else 32)).map (fun i =>
        Gate.mkMUX rs2_data_0[i]! rs2_data_1[i]! mem_route_sel mem_mux_rs2_data[i]!) ++
      []) ++
    -- For FP loads: use FP rename dest tag instead of INT rename dest tag
    (if enableF then
      let mem_mux_int_rd := CPU.makeIndexedWires "mem_mux_int_rd" 6
      let mem_mux_is_fp_load := Wire.mk "mem_mux_is_fp_load"
      (List.range 6).map (fun i =>
        Gate.mkMUX int_dest_tag_masked_0[i]! int_dest_tag_masked_1[i]! mem_route_sel mem_mux_int_rd[i]!) ++
      [Gate.mkMUX d0_is_fp_load d1_is_fp_load mem_route_sel mem_mux_is_fp_load] ++
      (List.range 6).map (fun i =>
        Gate.mkMUX mem_mux_int_rd[i]! fp_issue_dest_tag[i]! mem_mux_is_fp_load mem_mux_rd_phys[i]!)
    else
      (List.range 6).map (fun i =>
        Gate.mkMUX int_dest_tag_masked_0[i]! int_dest_tag_masked_1[i]! mem_route_sel mem_mux_rd_phys[i]!)) ++
    [Gate.mkMUX src1_ready_0 src1_ready_1 mem_route_sel mem_mux_src1_ready] ++
    (if enableF then
      [Gate.mkMUX (Wire.mk "mem_mux_int_src2_ready") mem_fp_issue_src2_ready (Wire.mk "mem_mux_is_fp_store") mem_mux_src2_ready]
    else
      [Gate.mkMUX (Wire.mk "src2_ready0_reg") (Wire.mk "src2_ready1_reg") mem_route_sel mem_mux_src2_ready]) ++
    [Gate.mkMUX d0_is_st d1_is_st mem_route_sel mem_mux_is_store,
   Gate.mkMUX d0_is_atomic d1_is_atomic mem_route_sel (Wire.mk "mem_mux_is_atomic"),
   Gate.mkOR mem_mux_is_store (Wire.mk "mem_mux_is_atomic") (Wire.mk "mem_mux_is_store_or_atomic")] ++
    (List.range 32).map (fun i =>
      Gate.mkMUX d0_imm[i]! d1_imm[i]! mem_route_sel mem_mux_imm[i]!)

  -- MUX data for muldiv RS
  let md_mux_opcode := CPU.makeIndexedWires "md_mux_opcode" opcodeWidth
  let md_mux_rs1_phys := CPU.makeIndexedWires "md_mux_rs1_phys" 6
  let md_mux_rs2_phys := CPU.makeIndexedWires "md_mux_rs2_phys" 6
  let md_mux_rs1_data := CPU.makeIndexedWires "md_mux_rs1_data" (if config.xlen == 64 then 64 else 32)
  let md_mux_rs2_data := CPU.makeIndexedWires "md_mux_rs2_data" (if config.xlen == 64 then 64 else 32)
  let md_mux_rd_phys := CPU.makeIndexedWires "md_mux_rd_phys" 6
  let md_mux_src1_ready := Wire.mk "md_mux_src1_ready"
  let md_mux_src2_ready := Wire.mk "md_mux_src2_ready"
  let md_mux_data_gates :=
    if enableM then
      (List.range opcodeWidth).map (fun i =>
        Gate.mkMUX (d0_op.take opcodeWidth)[i]! (d1_op.take opcodeWidth)[i]! muldiv_route_sel md_mux_opcode[i]!) ++
      (List.range 6).map (fun i =>
        Gate.mkMUX rs1_phys_0[i]! rs1_phys_1[i]! muldiv_route_sel md_mux_rs1_phys[i]!) ++
      (List.range 6).map (fun i =>
        Gate.mkMUX rs2_phys_0[i]! rs2_phys_1[i]! muldiv_route_sel md_mux_rs2_phys[i]!) ++
      (List.range (if config.xlen == 64 then 64 else 32)).map (fun i =>
        Gate.mkMUX rs1_data_0[i]! rs1_data_1[i]! muldiv_route_sel md_mux_rs1_data[i]!) ++
      (List.range (if config.xlen == 64 then 64 else 32)).map (fun i =>
        Gate.mkMUX rs2_data_0[i]! rs2_data_1[i]! muldiv_route_sel md_mux_rs2_data[i]!) ++
      (List.range 6).map (fun i =>
        Gate.mkMUX int_dest_tag_masked_0[i]! int_dest_tag_masked_1[i]! muldiv_route_sel md_mux_rd_phys[i]!) ++
      [Gate.mkMUX src1_ready_0 src1_ready_1 muldiv_route_sel md_mux_src1_ready,
       Gate.mkMUX src2_ready_0 src2_ready_1 muldiv_route_sel md_mux_src2_ready]
    else []

  -- FP MUX data: route slot 0 or slot 1 operands to single-issue FP port
  -- FP uses FP rename outputs for tags/data (cross-domain), so we MUX *after* cross-domain routing
  -- The fp_mux wires here are for the INT-side decode signals (opcode, imm, has_fp_rd, etc.)
  let fp_mux_has_fp_rd := Wire.mk "fp_mux_has_fp_rd"
  let fp_mux_fp_rs1_read := Wire.mk "fp_mux_fp_rs1_read"
  let fp_mux_fp_rs2_read := Wire.mk "fp_mux_fp_rs2_read"
  let fp_mux_fp_rs3_used := Wire.mk "fp_mux_fp_rs3_used"
  let fp_mux_rd := CPU.makeIndexedWires "fp_mux_rd" 5
  let fp_mux_rs1 := CPU.makeIndexedWires "fp_mux_rs1" 5
  let fp_mux_rs2 := CPU.makeIndexedWires "fp_mux_rs2" 5
  let fp_mux_rs3 := CPU.makeIndexedWires "fp_mux_rs3" 5
  let fp_mux_imm := CPU.makeIndexedWires "fp_mux_imm" 32
  let fp_mux_opcode := CPU.makeIndexedWires "fp_mux_opcode" opcodeWidth
  let fp_mux_decode_rm := CPU.makeIndexedWires "fp_mux_decode_rm" 3
  let fp_mux_data_gates :=
    if enableF then
      -- Use fp_rename_route_sel for has_fp_rd and rd_addr (needed for FLW FP rename)
      [Gate.mkMUX d0_has_fp_rd d1_has_fp_rd fp_rename_route_sel fp_mux_has_fp_rd,
       Gate.mkMUX d0_fp_rs1_read d1_fp_rs1_read fp_route_sel fp_mux_fp_rs1_read,
       Gate.mkMUX d0_fp_rs2_read d1_fp_rs2_read fp_rs2_route_sel fp_mux_fp_rs2_read,
       Gate.mkMUX d0_fp_rs3_used d1_fp_rs3_used fp_route_sel fp_mux_fp_rs3_used] ++
      (List.range 5).map (fun i =>
        Gate.mkMUX d0_rd[i]! d1_rd[i]! fp_rename_route_sel fp_mux_rd[i]!) ++
      (List.range 5).map (fun i =>
        Gate.mkMUX d0_rs1[i]! d1_rs1[i]! fp_route_sel fp_mux_rs1[i]!) ++
      (List.range 5).map (fun i =>
        Gate.mkMUX d0_rs2[i]! d1_rs2[i]! fp_rs2_route_sel fp_mux_rs2[i]!) ++
      (List.range 5).map (fun i =>
        Gate.mkMUX (d0_rs3.getD i zero) (d1_rs3.getD i zero) fp_route_sel fp_mux_rs3[i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkMUX d0_imm[i]! d1_imm[i]! fp_route_sel fp_mux_imm[i]!) ++
      (List.range opcodeWidth).map (fun i =>
        Gate.mkMUX d0_op[i]! d1_op[i]! fp_route_sel fp_mux_opcode[i]!) ++
      (List.range 3).map (fun i =>
        Gate.mkMUX (d0_rm.getD i zero) (d1_rm.getD i zero) fp_route_sel fp_mux_decode_rm[i]!)
    else []

  -- Forward-declare INT-domain commit gating wires (gates defined after branch_tracking)
  let int_hasOldPhysRd_0 := Wire.mk "int_hasOldPhysRd_0"
  let int_hasOldPhysRd_1 := Wire.mk "int_hasOldPhysRd_1"
  let int_hasPhysRd_0 := Wire.mk "int_hasPhysRd_0"
  let int_hasPhysRd_1 := Wire.mk "int_hasPhysRd_1"
  let int_retire_any_old_0 := Wire.mk "int_retire_any_old_0"
  let int_retire_any_old_1 := Wire.mk "int_retire_any_old_1"

  -- === RENAME INSTANCE ===
  let rename_inst : CircuitInstance := {
    moduleName := if config.xlen == 64 then "IntRenameStage_W2_64" else "IntRenameStage_W2"
    instName := "u_rename"
    portMap := [("clock", clock), ("reset", reset), ("zero", zero), ("one", one),
                ("instr_valid", d0_valid), ("has_rd", d0_has_rd_int), ("force_alloc", d0_is_br),
                ("instr_valid_1", d1_valid), ("has_rd_1", d1_has_rd_int), ("force_alloc_1", d1_is_br),
                ("flush_en", pipeline_flush)] ++
               -- commit_valid for slot 0 is muxed with CSR inject (defined in CSR block below)
               [("commit_valid", Wire.mk "csr_commit_valid_0"), ("commit_valid_1", retire_valid_1)] ++
               bundledPorts "rs1_addr" d0_rs1 ++ bundledPorts "rs2_addr" d0_rs2 ++ bundledPorts "rd_addr" d0_rd ++
               bundledPorts "rs1_addr_1" d1_rs1 ++ bundledPorts "rs2_addr_1" d1_rs2 ++ bundledPorts "rd_addr_1" d1_rd ++
               bundledPorts "commit_archRd" (CPU.makeIndexedWires "cmt_archRd_mux_0" 5) ++
               bundledPorts "commit_physRd" (CPU.makeIndexedWires "cmt_physRd_mux_0" 6) ++
               bundledPorts "commit_archRd_1" commit_archRd_1 ++ bundledPorts "commit_physRd_1" commit_physRd_1 ++
               [("cdb_valid", Wire.mk "cdb_valid_int_0"), ("cdb_valid_1", Wire.mk "cdb_valid_int_1")] ++
               bundledPorts "cdb_tag_0" cdb_tag_0 ++ bundledPorts "cdb_data_0" (cdb_data_0.take (if config.xlen == 64 then 64 else 32)) ++
               bundledPorts "cdb_tag_1" cdb_tag_1 ++ bundledPorts "cdb_data_1" cdb_data32_1 ++
               [("rename_valid", rename_valid_0), ("stall", Wire.mk "rename_stall_0"),
                ("rename_valid_1", rename_valid_1)] ++
               bundledPorts "rs1_phys_out" rs1_phys_0 ++ bundledPorts "rs2_phys_out" rs2_phys_0 ++ bundledPorts "rd_phys_out" rd_phys_0 ++
               bundledPorts "old_rd_phys_out" old_physRd_0 ++
               bundledPorts "rs1_data" rs1_data_0 ++ bundledPorts "rs2_data" rs2_data_0 ++
               bundledPorts "rs1_phys_out_1" rs1_phys_1 ++ bundledPorts "rs2_phys_out_1" rs2_phys_1 ++ bundledPorts "rd_phys_out_1" rd_phys_1 ++
               bundledPorts "old_rd_phys_out_1" old_physRd_1 ++
               bundledPorts "rs1_data_1" rs1_data_1 ++ bundledPorts "rs2_data_1" rs2_data_1 ++
               bundledPorts "retire_tag" (CPU.makeIndexedWires "cmt_retag_mux_0" 6) ++
               bundledPorts "retire_tag_1" retire_tag_bt_1 ++
               -- Commit hasPhysRd/hasAllocSlot: slot 0 muxed with CSR inject
               -- commit_hasPhysRd: controls CRAT write (branches excluded to prevent RAT corruption)
               -- retire_hasPhysRd: controls free list enqueue (branches included for physRd reclaim)
               [("commit_hasPhysRd", Wire.mk "csr_commit_hasPhysRd_0"),
                ("commit_hasAllocSlot", Wire.mk "csr_commit_hasAllocSlot_0"),
                ("commit_hasPhysRd_1", int_hasOldPhysRd_1),
                ("commit_hasAllocSlot_1", int_hasPhysRd_1)] ++
               -- RVVI readback data outputs from PRF
               bundledPorts "rd_data5" prf_rvvi_data_0 ++
               bundledPorts "rd_data6" prf_rvvi_data_1 ++
               [("ext_stall", Wire.mk "rename_ext_stall"),
                ("ext_stall_1", Wire.mk "any_dual_stall"),
                ("retire_hasPhysRd", Wire.mk "csr_retire_hasPhysRd_0"),
                ("retire_hasPhysRd_1", int_retire_any_old_1)]
  }

  -- === BUSY TABLE (W2) ===
  let busy_raw_s1_hit := Wire.mk "busy_raw_s1_hit"
  let busy_raw_s2_hit := Wire.mk "busy_raw_s2_hit"
  let busy_inst : CircuitInstance := {
    moduleName := "BusyTable_W2",
    instName := "u_busy_table",
    portMap := [
      ("clock", clock),
      ("reset", reset),
      ("zero", zero),
      ("one", one)
    ] ++
    (flush_busy_groups.enum.map fun ⟨i, w⟩ => (s!"flush_groups_{i}", w)) ++
    (rd_phys_0.enum.map fun ⟨i, w⟩ => (s!"set_tag_0_{i}", w)) ++
    (rd_phys_1.enum.map fun ⟨i, w⟩ => (s!"set_tag_1_{i}", w)) ++
    [("set_en_0", busy_set_en_0), ("set_en_1", busy_set_en_1)] ++
    (cdb_tag_0.enum.map fun ⟨i, w⟩ => (s!"clear_tag_0_{i}", w)) ++
    (cdb_tag_1.enum.map fun ⟨i, w⟩ => (s!"clear_tag_1_{i}", w)) ++
    [("clear_en_0", if enableF then Wire.mk "cdb_valid_int_0" else cdb_valid_0),
     ("clear_en_1", if enableF then Wire.mk "cdb_valid_int_1" else cdb_valid_1)] ++
    (rs1_phys_0.enum.map fun ⟨i, w⟩ => (s!"read1_tag_0_{i}", w)) ++
    (rs2_phys_0.enum.map fun ⟨i, w⟩ => (s!"read2_tag_0_{i}", w)) ++
    (rs1_phys_1.enum.map fun ⟨i, w⟩ => (s!"read1_tag_1_{i}", w)) ++
    (rs2_phys_1.enum.map fun ⟨i, w⟩ => (s!"read2_tag_1_{i}", w)) ++
    [("use_imm_0", d0_use_imm), ("use_imm_1", d1_use_imm),
     ("src1_ready_0", src1_ready_0),
     ("src2_ready_0", src2_ready_0),
     ("src2_ready0_reg", Wire.mk "src2_ready0_reg"),
     ("src1_ready_1", src1_ready_1),
     ("src2_ready_1", src2_ready_1),
     ("src2_ready1_reg", Wire.mk "src2_ready1_reg"),
     ("busy_raw_s1_hit", busy_raw_s1_hit),
     ("busy_raw_s2_hit", busy_raw_s2_hit)]
  }

  -- === REORDER BUFFER (W2) ===
  -- Forward-declare FP wires (defined later in FP pipeline block)
  let cdb_is_fp_0 := Wire.mk "cdb_is_fp_0"
  let cdb_is_fp_1 := Wire.mk "cdb_is_fp_1"

  -- FP dest tag MUX for ROB: when an FP instruction dispatches, the ROB must store
  -- the FP issue dest tag (from FP rename) instead of the INT rename tag, so CDB
  -- completion matching works correctly across domains.
  let rob_alloc_physRd_0 := CPU.makeIndexedWires "rob_alloc_physRd_0" 6
  let rob_alloc_physRd_1 := CPU.makeIndexedWires "rob_alloc_physRd_1" 6
  let rob_physRd_mux_gates :=
    if enableF then
      (List.range 6).map (fun i =>
        Gate.mkMUX rd_phys_0[i]! fp_issue_dest_tag[i]! d0_has_fp_rd rob_alloc_physRd_0[i]!) ++
      (List.range 6).map (fun i =>
        Gate.mkMUX rd_phys_1[i]! fp_issue_dest_tag[i]! d1_has_fp_rd rob_alloc_physRd_1[i]!)
    else
      (List.range 6).map (fun i =>
        Gate.mkBUF rd_phys_0[i]! rob_alloc_physRd_0[i]!) ++
      (List.range 6).map (fun i =>
        Gate.mkBUF rd_phys_1[i]! rob_alloc_physRd_1[i]!)

  -- ROB old_rd_phys MUX: at dispatch, select FP or INT old_rd_phys for ROB storage
  -- For W=2, FP rename is single-issue: dispatch_fp_rename_0/1 selects which slot
  -- Forward-declare fp_old_rd_phys wires (connected later to FP rename output)
  let fp_old_rd_phys := CPU.makeIndexedWires "fp_old_rd_phys" 6
  let rob_old_phys_muxed_0 := CPU.makeIndexedWires "rob_old_phys_muxed_0" 6
  let rob_old_phys_muxed_1 := CPU.makeIndexedWires "rob_old_phys_muxed_1" 6
  let rob_old_phys_mux_gates :=
    if enableF then
      (List.range 6).map (fun i =>
        Gate.mkMUX old_physRd_0[i]! fp_old_rd_phys[i]! d0_has_fp_rd rob_old_phys_muxed_0[i]!) ++
      (List.range 6).map (fun i =>
        Gate.mkMUX old_physRd_1[i]! fp_old_rd_phys[i]! d1_has_fp_rd rob_old_phys_muxed_1[i]!)
    else
      (List.range 6).map (fun i => Gate.mkBUF old_physRd_0[i]! rob_old_phys_muxed_0[i]!) ++
      (List.range 6).map (fun i => Gate.mkBUF old_physRd_1[i]! rob_old_phys_muxed_1[i]!)

  let rob_inst : CircuitInstance := {
    moduleName := "ROB16_W2"
    instName := "u_rob"
    portMap := [("clock", clock), ("reset", pipeline_reset_rob), ("zero", zero), ("one", one),
                ("alloc_en_0", dispatch_base_valid_0), ("alloc_en_1", dispatch_base_valid_1),
                ("alloc_hasPhysRd_0", rob_alloc_hasPhysRd_0), ("alloc_hasPhysRd_1", rob_alloc_hasPhysRd_1),
                ("alloc_hasOldPhysRd_0", if enableF then Wire.mk "d0_has_any_rd_nox0" else d0_has_rd_nox0),
                ("alloc_hasOldPhysRd_1", if enableF then Wire.mk "d1_has_any_rd_nox0" else d1_has_rd_nox0),
                ("alloc_isBranch_0", d0_is_br), ("alloc_is_fp_0", if enableF then d0_has_fp_rd else zero),
                ("alloc_isBranch_1", d1_is_br), ("alloc_is_fp_1", if enableF then d1_has_fp_rd else zero),
                ("cdb_valid", cdb_valid_0), ("cdb_valid_1", cdb_valid_1),
                ("cdb_mispredicted_1", cdb_mispredicted_reg_1),
                ("cdb_is_fp", if enableF then cdb_is_fp_0 else zero),
                ("cdb_is_fp_1", if enableF then cdb_is_fp_1 else zero),
                ("flush_en", branch_redirect_valid_reg),
                ("commit_en_0", retire_valid_0), ("commit_en_1", retire_valid_1)] ++
               bundledPorts "alloc_physRd_0" rob_alloc_physRd_0 ++ bundledPorts "alloc_oldPhysRd_0" rob_old_phys_muxed_0 ++ bundledPorts "alloc_archRd_0" d0_rd ++
               bundledPorts "alloc_physRd_1" rob_alloc_physRd_1 ++ bundledPorts "alloc_oldPhysRd_1" rob_old_phys_muxed_1 ++ bundledPorts "alloc_archRd_1" d1_rd ++
               bundledPorts "cdb_tag" cdb_tag_0 ++ bundledPorts "cdb_tag_1" cdb_tag_1 ++
               -- Outputs
               [("full", rob_full), ("empty", rob_empty), ("nearly_full", rob_nearly_full)] ++
               bundledPorts "alloc_idx_0" rob_alloc_idx_0 ++ bundledPorts "alloc_idx_1" rob_alloc_idx_1 ++
               bundledPorts "head_idx_0" rob_head_idx_0 ++ bundledPorts "head_idx_1" rob_head_idx_1 ++
               [("head_valid_0", rob_head_valid_0), ("head_complete_0", rob_head_complete_0)] ++
               bundledPorts "head_physRd_0" commit_physRd_0 ++ [("head_hasPhysRd_0", rob_head_hasPhysRd_0)] ++
               bundledPorts "head_oldPhysRd_0" rob_head_oldPhysRd_0 ++ [("head_hasOldPhysRd_0", rob_head_hasOldPhysRd_0)] ++
               bundledPorts "head_archRd_0" commit_archRd_0 ++
               [("head_exception_0", rob_head_exception_0), ("head_isBranch_0", rob_head_isBranch_0),
                ("head_mispredicted_0", rob_head_mispredicted_0)] ++
               [("head_valid_1", rob_head_valid_1), ("head_complete_1", rob_head_complete_1)] ++
               bundledPorts "head_physRd_1" commit_physRd_1 ++ [("head_hasPhysRd_1", rob_head_hasPhysRd_1)] ++
               bundledPorts "head_oldPhysRd_1" rob_head_oldPhysRd_1 ++ [("head_hasOldPhysRd_1", rob_head_hasOldPhysRd_1)] ++
               bundledPorts "head_archRd_1" commit_archRd_1 ++
               [("head_exception_1", rob_head_exception_1), ("head_isBranch_1", rob_head_isBranch_1),
                ("head_mispredicted_1", rob_head_mispredicted_1),
                ("head_is_fp_0", rob_head_is_fp_0), ("head_is_fp_1", rob_head_is_fp_1)]
  }

  -- === COMMIT CONTROL (W2) ===
  -- commit_en_0 = head_valid_0 AND head_complete_0 AND NOT redirect
  -- commit_en_1 = head_valid_1 AND head_complete_1 AND commit_en_0
  let fp_commit_buf_stall := Wire.mk "fp_commit_buf_stall"
  let not_fp_commit_buf_stall := Wire.mk "not_fp_commit_buf_stall"
  let fp_buf_stall_gates :=
    if enableF then
      [Gate.mkAND (Wire.mk "fp_commit_buf_valid_reg") rob_head_is_fp_0 fp_commit_buf_stall,
       Gate.mkNOT fp_commit_buf_stall not_fp_commit_buf_stall]
    else
      [Gate.mkBUF zero fp_commit_buf_stall, Gate.mkBUF one not_fp_commit_buf_stall]
  let commit_gates :=
    fp_buf_stall_gates ++
    [Gate.mkNOT branch_redirect_valid_reg (Wire.mk "not_redirect_for_commit"),
     Gate.mkAND rob_head_valid_0 rob_head_complete_0 (Wire.mk "commit_ready_0"),
     Gate.mkAND (Wire.mk "commit_ready_0") not_fp_commit_buf_stall (Wire.mk "commit_ready_0_gated"),
     Gate.mkAND (Wire.mk "commit_ready_0_gated") (Wire.mk "not_redirect_for_commit") retire_valid_0,
     Gate.mkAND rob_head_valid_1 rob_head_complete_1 (Wire.mk "commit_ready_1"),
     -- Slot 1 must not commit if slot 0 triggers a redirect (mispredicted branch)
     Gate.mkAND retire_valid_0 rob_head_isBranch_0 (Wire.mk "s0_is_committing_branch"),
     Gate.mkAND (Wire.mk "s0_is_committing_branch") rob_head_mispredicted_0 (Wire.mk "s0_redirect"),
     Gate.mkNOT (Wire.mk "s0_redirect") (Wire.mk "not_s0_redirect"),
     Gate.mkAND (Wire.mk "commit_ready_1") retire_valid_0 (Wire.mk "commit_ready_1_pre"),
     Gate.mkAND (Wire.mk "commit_ready_1_pre") (Wire.mk "not_s0_redirect") retire_valid_1]

  -- === BRANCH TRACKING (W2) ===
  -- Branches force-allocate a physRd but have no archRd (hasOldPhysRd=0).
  -- At commit, we must free the branch's OWN physRd (not garbage oldPhysRd).
  -- branch_tracking_s = isBranch_s AND NOT(hasOldPhysRd_s) AND hasPhysRd_s
  -- retire_any_old_s = hasOldPhysRd_s OR branch_tracking_s
  -- retire_tag_s = branch_tracking_s ? physRd_s : oldPhysRd_s
  let branch_tracking_gates :=
    [Gate.mkNOT rob_head_hasOldPhysRd_0 (Wire.mk "not_hasOldPhysRd_0"),
     Gate.mkAND rob_head_isBranch_0 (Wire.mk "not_hasOldPhysRd_0") (Wire.mk "bt_tmp_0"),
     Gate.mkAND (Wire.mk "bt_tmp_0") rob_head_hasPhysRd_0 branch_tracking_0,
     Gate.mkOR rob_head_hasOldPhysRd_0 branch_tracking_0 retire_any_old_0,
     Gate.mkNOT rob_head_hasOldPhysRd_1 (Wire.mk "not_hasOldPhysRd_1"),
     Gate.mkAND rob_head_isBranch_1 (Wire.mk "not_hasOldPhysRd_1") (Wire.mk "bt_tmp_1"),
     Gate.mkAND (Wire.mk "bt_tmp_1") rob_head_hasPhysRd_1 branch_tracking_1,
     Gate.mkOR rob_head_hasOldPhysRd_1 branch_tracking_1 retire_any_old_1] ++
    -- MUX retire_tag for slot 0: branch_tracking ? physRd : oldPhysRd
    (List.range 6).map (fun i =>
      Gate.mkMUX rob_head_oldPhysRd_0[i]! commit_physRd_0[i]! branch_tracking_0 retire_tag_bt_0[i]!) ++
    -- MUX retire_tag for slot 1: branch_tracking ? physRd : oldPhysRd
    (List.range 6).map (fun i =>
      Gate.mkMUX rob_head_oldPhysRd_1[i]! commit_physRd_1[i]! branch_tracking_1 retire_tag_bt_1[i]!)

  -- INT-domain commit gating: when F extension enabled, prevent FP instruction commits
  -- from updating the INT CRAT or INT free list
  let int_commit_fp_gate :=
    if enableF then
      [Gate.mkNOT rob_head_is_fp_0 (Wire.mk "not_rob_head_is_fp_0"),
       Gate.mkNOT rob_head_is_fp_1 (Wire.mk "not_rob_head_is_fp_1"),
       -- hasOldPhysRd gated by NOT(is_fp) for CRAT write
       Gate.mkAND rob_head_hasOldPhysRd_0 (Wire.mk "not_rob_head_is_fp_0") int_hasOldPhysRd_0,
       Gate.mkAND rob_head_hasOldPhysRd_1 (Wire.mk "not_rob_head_is_fp_1") int_hasOldPhysRd_1,
       -- hasPhysRd gated by NOT(is_fp) for alloc slot
       Gate.mkAND rob_head_hasPhysRd_0 (Wire.mk "not_rob_head_is_fp_0") int_hasPhysRd_0,
       Gate.mkAND rob_head_hasPhysRd_1 (Wire.mk "not_rob_head_is_fp_1") int_hasPhysRd_1,
       -- retire_any_old gated: use int_hasOldPhysRd instead of raw
       Gate.mkOR int_hasOldPhysRd_0 branch_tracking_0 int_retire_any_old_0,
       Gate.mkOR int_hasOldPhysRd_1 branch_tracking_1 int_retire_any_old_1]
    else
      [Gate.mkBUF rob_head_hasOldPhysRd_0 int_hasOldPhysRd_0,
       Gate.mkBUF rob_head_hasOldPhysRd_1 int_hasOldPhysRd_1,
       Gate.mkBUF rob_head_hasPhysRd_0 int_hasPhysRd_0,
       Gate.mkBUF rob_head_hasPhysRd_1 int_hasPhysRd_1,
       Gate.mkBUF retire_any_old_0 int_retire_any_old_0,
       Gate.mkBUF retire_any_old_1 int_retire_any_old_1]

  -- === BRANCH RESOLVE (W2) ===
  -- Check both commit slots for mispredicted branch. Slot 0 has priority.
  -- rob_redirect_valid = (commit_en_0 AND isBranch_0 AND mispred_0)
  --                   OR (commit_en_1 AND isBranch_1 AND mispred_1)
  let redirect_0 := Wire.mk "redirect_slot_0"
  let redirect_1 := Wire.mk "redirect_slot_1"
  let branch_resolve_gates :=
    [Gate.mkAND retire_valid_0 rob_head_isBranch_0 (Wire.mk "commit_is_branch_0"),
     Gate.mkAND (Wire.mk "commit_is_branch_0") rob_head_mispredicted_0 redirect_0,
     Gate.mkAND retire_valid_1 rob_head_isBranch_1 (Wire.mk "commit_is_branch_1"),
     Gate.mkAND (Wire.mk "commit_is_branch_1") rob_head_mispredicted_1 redirect_1,
     Gate.mkOR redirect_0 redirect_1 (Wire.mk "branch_redirect_any"),
     -- fence_i_drain_complete also triggers redirect
     Gate.mkOR (Wire.mk "branch_redirect_any") fence_i_drain_complete rob_redirect_valid]
  -- Select redirect target: branch misprediction > fence_i redirect
  -- Within branch, slot 0 priority
  let redir_tgt_0 := CPU.makeIndexedWires "rob_head_redirect_target_0" 32
  let redir_tgt_1 := CPU.makeIndexedWires "rob_head_redirect_target_1" 32
  let branch_redirect_target_mux_gates :=
    (List.range 32).map (fun i =>
      -- First: MUX between slot 1 and slot 0 branch redirect (slot 0 wins)
      let br_tgt := Wire.mk s!"br_redir_tgt_{i}"
      [Gate.mkMUX redir_tgt_1[i]! redir_tgt_0[i]! redirect_0 br_tgt,
       Gate.mkMUX fence_i_redir_target[i]! br_tgt (Wire.mk "branch_redirect_any") branch_redirect_target[i]!]) |>.flatten

  -- === IMMEDIATE MUX: for I-type instructions, src2 = immediate ===
  let src2_muxed_0 := CPU.makeIndexedWires "src2_muxed_0" (if config.xlen == 64 then 64 else 32)
  let src2_muxed_1 := CPU.makeIndexedWires "src2_muxed_1" (if config.xlen == 64 then 64 else 32)
  let src2_imm_mux_gates :=
    (List.range 32).map (fun i =>
      Gate.mkMUX rs2_data_0[i]! d0_imm[i]! d0_use_imm src2_muxed_0[i]!) ++
    (List.range 32).map (fun i =>
      Gate.mkMUX rs2_data_1[i]! d1_imm[i]! d1_use_imm src2_muxed_1[i]!) ++
    (if config.xlen == 64 then
      (List.range 32).map (fun i =>
        Gate.mkMUX rs2_data_0[32+i]! d0_imm[31]! d0_use_imm src2_muxed_0[32+i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkMUX rs2_data_1[32+i]! d1_imm[31]! d1_use_imm src2_muxed_1[32+i]!)
     else [])

  -- === 7-bit CDB tags for RS domain matching ===
  -- RS now uses 7-bit tags: bits [5:0] = phys reg tag, bit [6] = is_fp domain.
  -- This prevents INT CDB broadcasts from falsely waking up FP operands (and vice versa).
  let cdb_tag7_0 := cdb_tag_0 ++ [cdb_is_fp_0]  -- 7-bit: tag[5:0] ++ is_fp
  let cdb_tag7_1 := cdb_tag_1 ++ [cdb_is_fp_1]

  -- === RESERVATION STATION (Integer, W2) ===
  -- INT lane 1 has its own IB1 FIFO. Backpressure: only dispatch when FIFO can accept.
  let int_de1_gates : List Gate := []
  let issue0_valid := Wire.mk "issue0_valid"; let issue1_valid := Wire.mk "issue1_valid"
  let dispatch_opcode_0 := CPU.makeIndexedWires "dispatch_opcode_0" opcodeWidth
  let dispatch_src1_data_0 := CPU.makeIndexedWires "dispatch_src1_0" (if config.xlen == 64 then 64 else 32)
  let dispatch_src2_data_0 := CPU.makeIndexedWires "dispatch_src2_0" (if config.xlen == 64 then 64 else 32)
  let dispatch_dest_tag_0 := CPU.makeIndexedWires "dispatch_dest_0" 6
  let dispatch_opcode_1 := CPU.makeIndexedWires "dispatch_opcode_1" opcodeWidth
  let dispatch_src1_data_1 := CPU.makeIndexedWires "dispatch_src1_1" (if config.xlen == 64 then 64 else 32)
  let dispatch_src2_data_1 := CPU.makeIndexedWires "dispatch_src2_1" (if config.xlen == 64 then 64 else 32)
  let dispatch_dest_tag_1 := CPU.makeIndexedWires "dispatch_dest_1" 6
  -- RS CDB BYPASS SUPPRESS SIGNALS
  -- When slot 0 allocates a fresh phys tag that slot 1 reads (intra-group RAW),
  -- suppress alloc-time CDB bypass to prevent capturing stale data.
  -- busy_raw_s1_hit / busy_raw_s2_hit come from BusyBitTable2's internal wires.
  let busy_raw_s1_hit := Wire.mk "busy_raw_s1_hit"
  let busy_raw_s2_hit := Wire.mk "busy_raw_s2_hit"
  -- For single-unit RSes that route slot 1 to bank 0, gate with route_sel
  let br_suppress_s1 := Wire.mk "br_suppress_s1"
  let br_suppress_s2 := Wire.mk "br_suppress_s2"
  let mem_suppress_s1 := Wire.mk "mem_suppress_s1"
  let mem_suppress_s2 := Wire.mk "mem_suppress_s2"
  let muldiv_suppress_s1 := Wire.mk "muldiv_suppress_s1"
  let muldiv_suppress_s2 := Wire.mk "muldiv_suppress_s2"
  let suppress_gates :=
    [Gate.mkAND br_route_sel busy_raw_s1_hit br_suppress_s1,
     Gate.mkAND br_route_sel busy_raw_s2_hit br_suppress_s2,
     Gate.mkAND mem_route_sel busy_raw_s1_hit mem_suppress_s1,
     Gate.mkAND mem_route_sel busy_raw_s2_hit mem_suppress_s2,
     Gate.mkAND muldiv_route_sel busy_raw_s1_hit muldiv_suppress_s1,
     Gate.mkAND muldiv_route_sel busy_raw_s2_hit muldiv_suppress_s2]

  let rs_int_issue_full := Wire.mk "rs_int_issue_full"
  let rs_int_alloc_ptr := CPU.makeIndexedWires "rs_int_alloc_ptr" 2
  let rs_int_grant := CPU.makeIndexedWires "rs_int_grant" 4

  let rs_int_inst : CircuitInstance := {
    moduleName := if config.xlen == 64 then "IntReservationStation4_W2_64" else "IntReservationStation4_W2"
    instName := "u_rs_int"
    portMap := [("clock", clock), ("reset", pipeline_reset_rs_int),
                ("issue_en_0", dispatch_int_0), ("issue_en_1", dispatch_int_1)] ++
               bundledPorts "issue_opcode_0" (d0_op.take opcodeWidth) ++
               bundledPorts "issue_dest_tag_0" int_dest_tag_masked_0 ++
               [("issue_src1_ready_0", src1_ready_0)] ++
               bundledPorts "issue_src1_tag_0" rs1_phys_0 ++
               bundledPorts "issue_src1_data_0" rs1_data_0 ++
               [("issue_src2_ready_0", src2_ready_0)] ++
               bundledPorts "issue_src2_tag_0" rs2_phys_0 ++
               bundledPorts "issue_src2_data_0" src2_muxed_0 ++
               bundledPorts "issue_opcode_1" (d1_op.take opcodeWidth) ++
               bundledPorts "issue_dest_tag_1" int_dest_tag_masked_1 ++
               [("issue_src1_ready_1", src1_ready_1)] ++
               bundledPorts "issue_src1_tag_1" rs1_phys_1 ++
               bundledPorts "issue_src1_data_1" rs1_data_1 ++
               [("issue_src2_ready_1", src2_ready_1)] ++
               bundledPorts "issue_src2_tag_1" rs2_phys_1 ++
               bundledPorts "issue_src2_data_1" src2_muxed_1 ++
               [("cdb_valid_0", cdb_valid_0), ("cdb_is_fp_0", cdb_is_fp_0)] ++
               bundledPorts "cdb_tag_0" cdb_tag_0 ++
               bundledPorts "cdb_data_0" (if config.xlen == 64 then cdb_data_0 else cdb_data32_0) ++
               [("cdb_valid_1", cdb_valid_1), ("cdb_is_fp_1", cdb_is_fp_1)] ++
               bundledPorts "cdb_tag_1" cdb_tag_1 ++
               bundledPorts "cdb_data_1" (if config.xlen == 64 then cdb_data_1 else cdb_data32_1) ++
               [("dispatch_en_1", Wire.mk "ib1_fifo_enq_ready"),
                ("suppress_cdb_s1_1", Wire.mk "busy_raw_s1_hit"),
                ("suppress_cdb_s2_1", Wire.mk "busy_raw_s2_hit"),
                ("alloc_avail_0", Wire.mk "rs_int_avail_0"),
                ("alloc_avail_1", Wire.mk "rs_int_avail_1"),
                ("dispatch_valid_0", issue0_valid),
                ("dispatch_valid_1", issue1_valid)] ++
               bundledPorts "alloc_ptr" rs_int_alloc_ptr ++
               bundledPorts "dispatch_grant" rs_int_grant ++
               bundledPorts "dispatch_opcode_0" dispatch_opcode_0 ++
               bundledPorts "dispatch_src1_data_0" dispatch_src1_data_0 ++
               bundledPorts "dispatch_src2_data_0" dispatch_src2_data_0 ++
               bundledPorts "dispatch_dest_tag_0" dispatch_dest_tag_0 ++
               bundledPorts "dispatch_opcode_1" dispatch_opcode_1 ++
               bundledPorts "dispatch_src1_data_1" dispatch_src1_data_1 ++
               bundledPorts "dispatch_src2_data_1" dispatch_src2_data_1 ++
               bundledPorts "dispatch_dest_tag_1" dispatch_dest_tag_1
  }

  -- === BRANCH RS (single-unit, W=1, 2 entries) ===
  let rs_br_issue_full := Wire.mk "rs_br_issue_full"
  let rs_br_dispatch_valid := Wire.mk "rs_br_dispatch_valid"
  let rs_br_dispatch_opcode := CPU.makeIndexedWires "rs_br_dispatch_opcode" opcodeWidth
  let rs_br_dispatch_src1 := CPU.makeIndexedWires "rs_br_dispatch_src1" (if config.xlen == 64 then 64 else 32)
  let rs_br_dispatch_src2 := CPU.makeIndexedWires "rs_br_dispatch_src2" (if config.xlen == 64 then 64 else 32)
  let rs_br_dispatch_tag := CPU.makeIndexedWires "rs_br_dispatch_tag" 6
  let rs_br_alloc_ptr := Wire.mk "rs_br_alloc_ptr"
  let rs_br_grant := CPU.makeIndexedWires "rs_br_grant" 2

  let rs_br_inst : CircuitInstance := {
    moduleName := if config.xlen == 64 then "ReservationStation2_W1_64" else "ReservationStation2_W1"
    instName := "u_rs_branch"
    portMap := [("clock", clock), ("reset", pipeline_reset_rs_br),
                ("issue_en", br_dispatch_valid)] ++
               bundledPorts "issue_opcode" br_mux_opcode ++
               bundledPorts "issue_dest_tag" br_mux_rd_phys ++
               [("issue_src1_ready", br_mux_src1_ready)] ++
               bundledPorts "issue_src1_tag" br_mux_rs1_phys ++
               bundledPorts "issue_src1_data" br_mux_rs1_data ++
               [("issue_src2_ready", br_mux_src2_ready)] ++
               bundledPorts "issue_src2_tag" br_mux_rs2_phys ++
               bundledPorts "issue_src2_data" br_mux_rs2_data ++
               [("cdb_valid_0", cdb_valid_0), ("cdb_is_fp_0", cdb_is_fp_0)] ++
               bundledPorts "cdb_tag_0" cdb_tag_0 ++
               bundledPorts "cdb_data_0" (if config.xlen == 64 then cdb_data_0 else cdb_data32_0) ++
               [("cdb_valid_1", cdb_valid_1), ("cdb_is_fp_1", cdb_is_fp_1)] ++
               bundledPorts "cdb_tag_1" cdb_tag_1 ++
               bundledPorts "cdb_data_1" (if config.xlen == 64 then cdb_data_1 else cdb_data32_1) ++
               [("dispatch_en", Wire.mk "ib_br_fifo_enq_ready"),
                ("suppress_cdb_s1", br_suppress_s1),
                ("suppress_cdb_s2", br_suppress_s2),
                ("alloc_avail", Wire.mk "rs_br_avail_0"),
                ("dispatch_valid", rs_br_dispatch_valid),
                ("alloc_ptr", rs_br_alloc_ptr),
                ("dispatch_grant_0", rs_br_grant[0]!),
                ("dispatch_grant_1", rs_br_grant[1]!)] ++
               bundledPorts "dispatch_opcode" rs_br_dispatch_opcode ++
               bundledPorts "dispatch_src1_data" rs_br_dispatch_src1 ++
               bundledPorts "dispatch_src2_data" rs_br_dispatch_src2 ++
               bundledPorts "dispatch_dest_tag" rs_br_dispatch_tag
  }

  -- === MEMORY RS (single-unit, W=1, 2 entries) ===
  let rs_mem_issue_full := Wire.mk "rs_mem_issue_full"
  let rs_mem_dispatch_valid := Wire.mk "rs_mem_dispatch_valid"
  let rs_mem_dispatch_opcode := CPU.makeIndexedWires "rs_mem_dispatch_opcode" opcodeWidth
  let rs_mem_dispatch_src1 := CPU.makeIndexedWires "rs_mem_dispatch_src1" (if config.xlen == 64 || config.enableD then 64 else 32)
  let rs_mem_dispatch_src2 := CPU.makeIndexedWires "rs_mem_dispatch_src2" (if config.xlen == 64 || config.enableD then 64 else 32)
  let rs_mem_dispatch_tag := CPU.makeIndexedWires "rs_mem_dispatch_tag" 6
  let rs_mem_alloc_ptr := Wire.mk "rs_mem_alloc_ptr"
  let rs_mem_grant := CPU.makeIndexedWires "rs_mem_grant" 2

  -- Forward-declare memory pipeline wires
  let mem_addr_r := CPU.makeIndexedWires "mem_addr_r" (if config.xlen == 64 then 64 else 32)
  let mem_valid_r := Wire.mk "mem_valid_r"
  let mem_tag_r := CPU.makeIndexedWires "mem_tag_r" 6
  let is_load_r := Wire.mk "is_load_r"
  let mem_size_r := CPU.makeIndexedWires "mem_size_r" 2
  let sign_extend_r := Wire.mk "sign_extend_r"
  let is_flw_r := Wire.mk "is_flw_r"
  let mem_dispatch_en := Wire.mk "mem_dispatch_en"

  let rsMemDataWidth := if config.xlen == 64 || config.enableD then 64 else 32
  let rs_mem_inst : CircuitInstance := {
    moduleName := if config.xlen == 64 || config.enableD then "MemoryReservationStation2_W1_64" else "MemoryReservationStation2_W1"
    instName := "u_rs_memory"
    portMap := [("clock", clock), ("reset", pipeline_reset_rs_mem),
                ("issue_en", mem_dispatch_valid),
                ("issue_is_store", Wire.mk "mem_mux_is_store_or_atomic"),
                ("issue_is_atomic", Wire.mk "mem_mux_is_atomic")] ++
               bundledPorts "issue_opcode" mem_mux_opcode ++
               bundledPorts "issue_dest_tag" mem_mux_rd_phys ++
               [("issue_src1_ready", mem_mux_src1_ready)] ++
               bundledPorts "issue_src1_tag" mem_mux_rs1_phys ++
               bundledPorts "issue_src1_data" (if config.xlen == 64 then mem_mux_rs1_data else (if config.enableD then mem_mux_rs1_data ++ (List.range 32).map fun _ => zero else mem_mux_rs1_data)) ++
               [("issue_src2_ready", mem_mux_src2_ready)] ++
               bundledPorts "issue_src2_tag" (mem_mux_rs2_phys ++ [if enableF then Wire.mk "mem_mux_is_fp_store" else zero]) ++
               bundledPorts "issue_src2_data" mem_mux_rs2_data ++
               [("cdb_valid_0", cdb_valid_0), ("cdb_is_fp_0", cdb_is_fp_0)] ++
               bundledPorts "cdb_tag_0" cdb_tag_0 ++
               bundledPorts "cdb_data_0" cdb_data_0 ++
               [("cdb_valid_1", cdb_valid_1), ("cdb_is_fp_1", cdb_is_fp_1)] ++
               bundledPorts "cdb_tag_1" cdb_tag_1 ++
               bundledPorts "cdb_data_1" cdb_data_1 ++
               [("dispatch_en", Wire.mk "mem_dispatch_en_any"),
                ("suppress_cdb_s1", mem_suppress_s1),
                ("suppress_cdb_s2", mem_suppress_s2),
                ("alloc_avail", Wire.mk "rs_mem_avail_0"),
                ("dispatch_valid", rs_mem_dispatch_valid),
                ("alloc_ptr", rs_mem_alloc_ptr),
                ("pending_store", Wire.mk "rs_mem_pending_store"),
                ("dispatch_grant_0", rs_mem_grant[0]!),
                ("dispatch_grant_1", rs_mem_grant[1]!)] ++
               bundledPorts "dispatch_opcode" rs_mem_dispatch_opcode ++
               bundledPorts "dispatch_src1_data" rs_mem_dispatch_src1 ++
               bundledPorts "dispatch_src2_data" rs_mem_dispatch_src2 ++
               bundledPorts "dispatch_dest_tag" rs_mem_dispatch_tag
  }

  -- === IMMEDIATE REGISTER FILE (Memory RS, 2 entries) ===
  let captured_imm := CPU.makeIndexedWires "captured_imm" 32
  let (imm_rf_gates, _imm_rf_entries) :=
    mkSidecarRegFile2x32 "imm_rf" clock reset rs_mem_alloc_ptr mem_dispatch_valid mem_mux_imm rs_mem_grant[1]! captured_imm

  -- Forward-declare SB tail output (used by sb_alloc_ctr flush reload)
  let lsu_sb_enq_idx := CPU.makeIndexedWires "lsu_sb_enq_idx" 3

  -- === SB INDEX PRE-ALLOCATION SIDECAR ===
  -- sb_alloc_ctr: 3-bit counter incremented at rename for each store.
  -- Ensures SB entries are allocated in program order even when stores
  -- dispatch out of order from the RS.
  let sb_alloc_ctr := CPU.makeIndexedWires "sb_alloc_ctr" 3
  let sb_alloc_ctr_next := CPU.makeIndexedWires "sb_alloc_ctr_next" 3
  let sb_alloc_inc := Wire.mk "sb_alloc_inc"
  -- Increment on store rename
  let sb_alloc_inc_gate := Gate.mkAND mem_dispatch_valid mem_mux_is_store sb_alloc_inc
  -- 3-bit incrementer: ctr + 1
  let sb_inc_xor0 := Wire.mk "sb_inc_xor0"
  let sb_inc_xor1 := Wire.mk "sb_inc_xor1"
  let sb_inc_carry1 := Wire.mk "sb_inc_carry1"
  let sb_alloc_inc_gates := [
    Gate.mkNOT sb_alloc_ctr[0]! sb_inc_xor0,
    Gate.mkAND sb_alloc_ctr[0]! sb_alloc_ctr[1]! sb_inc_carry1,
    Gate.mkXOR sb_alloc_ctr[0]! sb_alloc_ctr[1]! sb_inc_xor1
  ]
  -- MUX: flush loads from SB tail (lsu_sb_enq_idx), else increment or hold
  let sb_alloc_hold_or_inc := CPU.makeIndexedWires "sb_alloc_hoi" 3
  let sb_alloc_inc_val := [sb_inc_xor0, sb_inc_xor1, Wire.mk "sb_inc_xor2"]
  let sb_inc_xor2_gate := Gate.mkXOR sb_inc_carry1 sb_alloc_ctr[2]! (Wire.mk "sb_inc_xor2")
  let sb_alloc_mux_gates := (List.range 3).map (fun i =>
    Gate.mkMUX sb_alloc_ctr[i]! sb_alloc_inc_val[i]! sb_alloc_inc sb_alloc_hold_or_inc[i]!)
  -- On flush, reload from SB's combinational flush_tail (head + popcount(surviving))
  let lsu_sb_flush_tail := CPU.makeIndexedWires "lsu_sb_flush_tail" 3
  let sb_alloc_next_gates := (List.range 3).map (fun i =>
    Gate.mkMUX sb_alloc_hold_or_inc[i]! lsu_sb_flush_tail[i]! pipeline_flush_comb sb_alloc_ctr_next[i]!)
  -- DFFs for sb_alloc_ctr
  let sb_alloc_ctr_dffs : List CircuitInstance := (List.range 3).map (fun i => {
    moduleName := "DFlipFlop", instName := s!"u_sb_alloc_ctr_{i}",
    portMap := [("d", sb_alloc_ctr_next[i]!), ("q", sb_alloc_ctr[i]!),
                ("clock", clock), ("reset", reset)]
  })

  -- 2-entry × 3-bit sidecar: write sb_alloc_ctr at rename, read at dispatch
  let sb_sc_not_ap := Wire.mk "sb_sc_not_ap"
  let sb_sidecar_we := CPU.makeIndexedWires "sb_sc_we" 2
  let sb_sc_we_gates := [
    Gate.mkNOT rs_mem_alloc_ptr sb_sc_not_ap,
    Gate.mkAND sb_sc_not_ap mem_dispatch_valid sb_sidecar_we[0]!,
    Gate.mkAND rs_mem_alloc_ptr mem_dispatch_valid sb_sidecar_we[1]!
  ]
  let sb_sc_entries := (List.range 2).map (fun e =>
    CPU.makeIndexedWires s!"sb_sc_e{e}" 3)
  let sb_sc_rf_gates := (List.range 2).map (fun e =>
    let entry := sb_sc_entries[e]!
    (List.range 3).map (fun b =>
      let next := Wire.mk s!"sb_sc_next_e{e}_{b}"
      [ Gate.mkMUX entry[b]! sb_alloc_ctr[b]! sb_sidecar_we[e]! next,
        Gate.mkDFF next clock reset entry[b]! ]
    ) |>.flatten
  ) |>.flatten
  -- Read mux: 2:1 selected by rs_mem_grant[1]
  let sb_dispatch_idx := CPU.makeIndexedWires "sb_dispatch_idx" 3
  let sb_sc_read_gates := (List.range 3).map (fun b =>
    Gate.mkMUX sb_sc_entries[0]![b]! sb_sc_entries[1]![b]! rs_mem_grant[1]! sb_dispatch_idx[b]!)

  -- === MULDIV RS (conditional, single-unit, W=1, 2 entries) ===
  let rs_muldiv_issue_full := Wire.mk "rs_muldiv_issue_full"
  let rs_muldiv_dispatch_valid := Wire.mk "rs_muldiv_dispatch_valid"
  let rs_muldiv_dispatch_opcode := CPU.makeIndexedWires "rs_muldiv_dispatch_opcode" opcodeWidth
  let rs_muldiv_dispatch_src1 := CPU.makeIndexedWires "rs_muldiv_dispatch_src1" (if config.xlen == 64 then 64 else 32)
  let rs_muldiv_dispatch_src2 := CPU.makeIndexedWires "rs_muldiv_dispatch_src2" (if config.xlen == 64 then 64 else 32)
  let rs_muldiv_dispatch_tag := CPU.makeIndexedWires "rs_muldiv_dispatch_tag" 6
  let rs_md_alloc_ptr := Wire.mk "rs_md_alloc_ptr"
  let rs_md_grant := CPU.makeIndexedWires "rs_md_grant" 2
  let muldiv_busy := Wire.mk "muldiv_busy"
  let muldiv_dispatch_en := Wire.mk "muldiv_dispatch_en"
  let not_muldiv_busy := Wire.mk "not_muldiv_busy"
  let muldiv_dispatch_gate :=
    if enableM then
      [Gate.mkNOT muldiv_busy not_muldiv_busy,
       Gate.mkBUF not_muldiv_busy muldiv_dispatch_en]
    else [Gate.mkBUF one muldiv_dispatch_en]

  let rs_muldiv_inst : CircuitInstance := {
    moduleName := if config.xlen == 64 then "ReservationStation2_W1_64" else "ReservationStation2_W1"
    instName := "u_rs_muldiv"
    portMap := [("clock", clock), ("reset", pipeline_reset_rs_muldiv),
                ("issue_en", muldiv_dispatch_valid)] ++
               bundledPorts "issue_opcode" md_mux_opcode ++
               bundledPorts "issue_dest_tag" md_mux_rd_phys ++
               [("issue_src1_ready", md_mux_src1_ready)] ++
               bundledPorts "issue_src1_tag" md_mux_rs1_phys ++
               bundledPorts "issue_src1_data" md_mux_rs1_data ++
               [("issue_src2_ready", md_mux_src2_ready)] ++
               bundledPorts "issue_src2_tag" md_mux_rs2_phys ++
               bundledPorts "issue_src2_data" md_mux_rs2_data ++
               [("cdb_valid_0", cdb_valid_0), ("cdb_is_fp_0", cdb_is_fp_0)] ++
               bundledPorts "cdb_tag_0" cdb_tag_0 ++
               bundledPorts "cdb_data_0" (if config.xlen == 64 then cdb_data_0 else cdb_data32_0) ++
               [("cdb_valid_1", cdb_valid_1), ("cdb_is_fp_1", cdb_is_fp_1)] ++
               bundledPorts "cdb_tag_1" cdb_tag_1 ++
               bundledPorts "cdb_data_1" (if config.xlen == 64 then cdb_data_1 else cdb_data32_1) ++
               [("dispatch_en", muldiv_dispatch_en),
                ("suppress_cdb_s1", muldiv_suppress_s1),
                ("suppress_cdb_s2", muldiv_suppress_s2),
                ("alloc_avail", Wire.mk "rs_md_avail_0"),
                ("dispatch_valid", rs_muldiv_dispatch_valid),
                ("alloc_ptr", rs_md_alloc_ptr),
                ("dispatch_grant_0", rs_md_grant[0]!),
                ("dispatch_grant_1", rs_md_grant[1]!)] ++
               bundledPorts "dispatch_opcode" rs_muldiv_dispatch_opcode ++
               bundledPorts "dispatch_src1_data" rs_muldiv_dispatch_src1 ++
               bundledPorts "dispatch_src2_data" rs_muldiv_dispatch_src2 ++
               bundledPorts "dispatch_dest_tag" rs_muldiv_dispatch_tag
  }

  -- === FP PIPELINE (conditional) ===
  -- FP Rename (single-issue, W=1 RenameStage_32x64)
  let fp_rs1_phys := CPU.makeIndexedWires "fp_rs1_phys" 6
  let fp_rs2_phys := CPU.makeIndexedWires "fp_rs2_phys" 6
  let fp_rd_phys := CPU.makeIndexedWires "fp_rd_phys" 6
  let fp_old_rd_phys := CPU.makeIndexedWires "fp_old_rd_phys" 6
  let fp_rs1_data := CPU.makeIndexedWires "fp_rs1_data" config.flen
  let fp_rs2_data := CPU.makeIndexedWires "fp_rs2_data" config.flen
  let fp_rename_valid := Wire.mk "fp_rename_valid"
  let fp_rename_stall := Wire.mk "fp_rename_stall"
  let fp_rs3_data := CPU.makeIndexedWires "fp_rs3_data" config.flen
  let fp_rs3_phys := CPU.makeIndexedWires "fp_rs3_phys" 6
  let fp_rvvi_rd_data := CPU.makeIndexedWires "fp_rvvi_rd_data" config.flen

  -- CDB routing: split CDB writes between INT and FP PRFs (2-channel CDB)
  -- We register is_fp per CDB channel and use it to gate PRF writes
  let cdb_is_fp_0 := Wire.mk "cdb_is_fp_0"
  let cdb_is_fp_1 := Wire.mk "cdb_is_fp_1"
  -- FP PRF: write if CDB valid AND is_fp on either channel
  -- For FP rename CDB wakeup: use channel 0 valid for simplicity (FP ops only go through one CDB)
  -- Actually: both channels can carry FP results, so we need to handle both.
  -- The FP rename (W=1) has a single CDB input. We merge the two channels:
  -- cdb_valid_fp = (cdb_valid_0 AND cdb_is_fp_0) OR (cdb_valid_1 AND cdb_is_fp_1)
  -- Since at most one FP result per cycle (single FP exec unit), only one channel will have is_fp=1.
  let cdb_valid_fp_ch0 := Wire.mk "cdb_valid_fp_ch0"
  let cdb_valid_fp_ch1 := Wire.mk "cdb_valid_fp_ch1"
  let cdb_valid_fp_prf := Wire.mk "cdb_valid_fp_prf"
  -- Merged FP CDB tag/data: MUX between ch0 and ch1 (ch0 priority)
  let cdb_tag_fp := CPU.makeIndexedWires "cdb_tag_fp" 6
  let cdb_data_fp := CPU.makeIndexedWires "cdb_data_fp" config.flen
  let fp_cdb_merge_gates :=
    if enableF then
      [Gate.mkAND cdb_valid_0 cdb_is_fp_0 cdb_valid_fp_ch0,
       Gate.mkAND cdb_valid_1 cdb_is_fp_1 cdb_valid_fp_ch1,
       Gate.mkOR cdb_valid_fp_ch0 cdb_valid_fp_ch1 cdb_valid_fp_prf] ++
      -- MUX tag/data: if ch0 has FP, use ch0; else use ch1
      (List.range 6).map (fun i =>
        Gate.mkMUX cdb_tag_1[i]! cdb_tag_0[i]! cdb_valid_fp_ch0 cdb_tag_fp[i]!) ++
      (List.range config.flen).map (fun i =>
        Gate.mkMUX cdb_data_1[i]! cdb_data_0[i]! cdb_valid_fp_ch0 cdb_data_fp[i]!)
    else
      (List.range 6).map (fun i => Gate.mkBUF zero cdb_tag_fp[i]!) ++
      (List.range config.flen).map (fun i => Gate.mkBUF zero cdb_data_fp[i]!) ++
      [Gate.mkBUF zero cdb_valid_fp_prf]

  -- INT PRF: gate by NOT is_fp on each channel
  let cdb_valid_int_0 := Wire.mk "cdb_valid_int_0"
  let cdb_valid_int_1 := Wire.mk "cdb_valid_int_1"
  let fp_int_prf_gate :=
    if enableF then
      [Gate.mkNOT cdb_is_fp_0 (Wire.mk "not_cdb_is_fp_0"),
       Gate.mkNOT cdb_is_fp_1 (Wire.mk "not_cdb_is_fp_1"),
       Gate.mkAND cdb_valid_0 (Wire.mk "not_cdb_is_fp_0") cdb_valid_int_0,
       Gate.mkAND cdb_valid_1 (Wire.mk "not_cdb_is_fp_1") cdb_valid_int_1]
    else
      [Gate.mkBUF cdb_valid_0 cdb_valid_int_0,
       Gate.mkBUF cdb_valid_1 cdb_valid_int_1]

  -- FP rename commit signals: commit_valid when ROB head has is_fp flag (from ROB output)
  let fp_commit_valid_0 := Wire.mk "fp_commit_valid_0"
  let fp_commit_valid_1 := Wire.mk "fp_commit_valid_1"
  let fp_commit_gates :=
    if enableF then
      [Gate.mkAND retire_valid_0 rob_head_is_fp_0 fp_commit_valid_0,
       Gate.mkAND retire_valid_1 rob_head_is_fp_1 fp_commit_valid_1]
    else
      [Gate.mkBUF zero fp_commit_valid_0, Gate.mkBUF zero fp_commit_valid_1]

  -- FP redirect: use same pipeline_flush for FP rename recovery
  let redirect_valid_fp := Wire.mk "redirect_valid_fp"
  let fp_redirect_gate :=
    if enableF then [Gate.mkBUF branch_redirect_valid_reg redirect_valid_fp]
    else [Gate.mkBUF zero redirect_valid_fp]

  -- Merge FP commits from both ROB slots for single-port FP rename.
  -- When both slots retire FP instructions, slot 0 commits immediately and
  -- slot 1 is buffered in a 1-entry DFF and replayed next cycle.
  let fp_commit_merged := Wire.mk "fp_commit_merged"
  let fp_commit_sel := Wire.mk "fp_commit_sel"  -- 1 = use slot 1 (when only slot 1 is FP)
  let fp_commit_archRd := CPU.makeIndexedWires "fp_commit_archRd" 5
  let fp_commit_physRd := CPU.makeIndexedWires "fp_commit_physRd" 6
  let fp_commit_oldPhysRd := CPU.makeIndexedWires "fp_commit_oldPhysRd" 6
  let fp_commit_hasPhysRd := Wire.mk "fp_commit_hasPhysRd"
  -- Buffered (deferred) FP commit for dual-FP-retire case
  let fp_commit_buf_valid := Wire.mk "fp_commit_buf_valid"
  let fp_commit_buf_valid_reg := Wire.mk "fp_commit_buf_valid_reg"
  let fp_commit_buf_archRd := CPU.makeIndexedWires "fp_commit_buf_archRd" 5
  let fp_commit_buf_physRd := CPU.makeIndexedWires "fp_commit_buf_physRd" 6
  let fp_commit_buf_oldPhysRd := CPU.makeIndexedWires "fp_commit_buf_oldPhysRd" 6
  let both_fp_commit := Wire.mk "both_fp_commit"
  let fp_commit_merge_gates :=
    if enableF then
      -- Detect dual-FP-commit
      [Gate.mkAND fp_commit_valid_0 fp_commit_valid_1 both_fp_commit] ++
      -- Buffer valid DFF: set when both_fp_commit, clear after one drain cycle
      -- Input: both_fp_commit AND NOT flush (naturally clears next cycle since both_fp_commit is transient)
      [Gate.mkNOT redirect_valid_fp (Wire.mk "not_fp_buf_flush"),
       Gate.mkAND both_fp_commit (Wire.mk "not_fp_buf_flush") fp_commit_buf_valid,
       Gate.mkDFF fp_commit_buf_valid clock reset fp_commit_buf_valid_reg] ++
      -- Buffer slot 1's data in DFFs (always latch slot 1; data only used when buf_valid_reg=1)
      (List.range 5).map (fun i =>
        Gate.mkDFF commit_archRd_1[i]! clock reset fp_commit_buf_archRd[i]!) ++
      (List.range 6).map (fun i =>
        Gate.mkDFF commit_physRd_1[i]! clock reset fp_commit_buf_physRd[i]!) ++
      (List.range 6).map (fun i =>
        Gate.mkDFF rob_head_oldPhysRd_1[i]! clock reset fp_commit_buf_oldPhysRd[i]!) ++
      -- Merged output: buffered replay has priority over new commits
      -- When buf_valid_reg: drain buffer. When !buf_valid_reg: normal commit logic.
      [Gate.mkNOT fp_commit_valid_0 (Wire.mk "not_fp_commit_0"),
       Gate.mkAND (Wire.mk "not_fp_commit_0") fp_commit_valid_1 (Wire.mk "fp_only_slot1"),
       -- Normal merged valid (at least one FP commit this cycle)
       Gate.mkOR fp_commit_valid_0 fp_commit_valid_1 (Wire.mk "fp_commit_any"),
       -- Final merged: either buffer drain or new commit
       Gate.mkOR (Wire.mk "fp_commit_any") fp_commit_buf_valid_reg fp_commit_merged,
       -- Selection: buf_valid_reg=1 → use buffer; buf_valid_reg=0 → fp_commit_sel as before
       Gate.mkAND (Wire.mk "not_fp_commit_0") fp_commit_valid_1 fp_commit_sel] ++
      -- hasPhysRd MUX: buffer > slot0 > slot1
      [Gate.mkMUX rob_head_is_fp_0 rob_head_is_fp_1 fp_commit_sel (Wire.mk "fp_commit_hasPhysRd_new"),
       Gate.mkMUX (Wire.mk "fp_commit_hasPhysRd_new") one fp_commit_buf_valid_reg fp_commit_hasPhysRd] ++
      -- archRd MUX: buffer > slot0/slot1
      (List.range 5).map (fun i =>
        Gate.mkMUX commit_archRd_0[i]! commit_archRd_1[i]! fp_commit_sel (Wire.mk s!"fp_commit_archRd_new_{i}")) ++
      (List.range 5).map (fun i =>
        Gate.mkMUX (Wire.mk s!"fp_commit_archRd_new_{i}") fp_commit_buf_archRd[i]! fp_commit_buf_valid_reg fp_commit_archRd[i]!) ++
      -- physRd MUX: buffer > slot0/slot1
      (List.range 6).map (fun i =>
        Gate.mkMUX commit_physRd_0[i]! commit_physRd_1[i]! fp_commit_sel (Wire.mk s!"fp_commit_physRd_new_{i}")) ++
      (List.range 6).map (fun i =>
        Gate.mkMUX (Wire.mk s!"fp_commit_physRd_new_{i}") fp_commit_buf_physRd[i]! fp_commit_buf_valid_reg fp_commit_physRd[i]!) ++
      -- Old phys rd for free list: buffer > slot0/slot1
      (List.range 6).map (fun i =>
        Gate.mkMUX rob_head_oldPhysRd_0[i]! rob_head_oldPhysRd_1[i]! fp_commit_sel (Wire.mk s!"fp_commit_oldPhysRd_new_{i}")) ++
      (List.range 6).map (fun i =>
        Gate.mkMUX (Wire.mk s!"fp_commit_oldPhysRd_new_{i}") fp_commit_buf_oldPhysRd[i]! fp_commit_buf_valid_reg fp_commit_oldPhysRd[i]!)
    else
      [Gate.mkBUF zero fp_commit_merged, Gate.mkBUF zero fp_commit_sel,
       Gate.mkBUF zero fp_commit_hasPhysRd, Gate.mkBUF zero both_fp_commit,
       Gate.mkDFF zero clock reset fp_commit_buf_valid_reg,
       Gate.mkBUF zero fp_commit_buf_valid] ++
      (List.range 5).map (fun i => Gate.mkBUF zero fp_commit_archRd[i]!) ++
      (List.range 6).map (fun i => Gate.mkBUF zero fp_commit_physRd[i]!) ++
      (List.range 6).map (fun i => Gate.mkBUF zero fp_commit_oldPhysRd[i]!) ++
      (List.range 5).map (fun i => Gate.mkBUF zero fp_commit_buf_archRd[i]!) ++
      (List.range 6).map (fun i => Gate.mkBUF zero fp_commit_buf_physRd[i]!) ++
      (List.range 6).map (fun i => Gate.mkBUF zero fp_commit_buf_oldPhysRd[i]!)

  -- FP rename: use FPRenameStage_W1 (single-issue, with rs3, real f0, no slot 1)
  let fp_rename_buf_gates : List Gate := []

  let fp_rename_inst : CircuitInstance := {
    moduleName := if config.flen == 32 then "FPRenameStage_W1" else s!"FPRenameStage_W1_{config.flen}"
    instName := "u_fp_rename"
    portMap :=
      [("clock", clock), ("reset", reset), ("zero", zero), ("one", one),
       -- FP dispatch
       ("instr_valid", fp_rename_dispatch_valid),
       ("has_rd", fp_mux_has_fp_rd)] ++
      bundledPorts "rs1_addr" fp_mux_rs1 ++ bundledPorts "rs2_addr" fp_mux_rs2 ++
      bundledPorts "rs3_addr" fp_mux_rs3 ++
      bundledPorts "rd_addr" fp_mux_rd ++
      -- Flush
      [("flush_en", redirect_valid_fp)] ++
      -- Commit channel 0: merged FP commit
      [("commit_valid", fp_commit_merged),
       ("commit_hasPhysRd", fp_commit_hasPhysRd)] ++
      bundledPorts "commit_archRd" fp_commit_archRd ++
      bundledPorts "commit_physRd" fp_commit_physRd ++
      -- CDB: FP domain
      [("cdb_valid", cdb_valid_fp_prf)] ++
      bundledPorts "cdb_tag" cdb_tag_fp ++ bundledPorts "cdb_data" cdb_data_fp ++
      -- Retire (free list enqueue)
      bundledPorts "retire_tag" fp_commit_oldPhysRd ++
      -- Stall
      [("ext_stall", redirect_or_flush)] ++
      -- Outputs
      [("rename_valid", fp_rename_valid), ("stall", fp_rename_stall)] ++
      bundledPorts "rs1_phys_out" fp_rs1_phys ++ bundledPorts "rs2_phys_out" fp_rs2_phys ++
      bundledPorts "rs3_phys_out" fp_rs3_phys ++
      bundledPorts "rd_phys_out" fp_rd_phys ++
      bundledPorts "old_rd_phys_out" fp_old_rd_phys ++
      bundledPorts "rs1_data" fp_rs1_data ++ bundledPorts "rs2_data" fp_rs2_data ++
      bundledPorts "rd_data3" fp_rs3_data
  }

  -- FP dest tag: use FP rd_phys when has_fp_rd, else use INT dest_tag (for mixed ops like FMV.X.W)
  let fp_dest_tag_gates :=
    if enableF then
      -- Select INT or FP rename dest based on which domain the result goes to
      let fp_mux_int_dest := CPU.makeIndexedWires "fp_mux_int_dest" 6
      -- MUX the INT dest from the correct slot (use fp_rename_route_sel for FLW compatibility)
      (List.range 6).map (fun i =>
        Gate.mkMUX int_dest_tag_masked_0[i]! int_dest_tag_masked_1[i]! fp_rename_route_sel fp_mux_int_dest[i]!) ++
      (List.range 6).map (fun i =>
        Gate.mkMUX fp_mux_int_dest[i]! fp_rd_phys[i]! fp_mux_has_fp_rd fp_issue_dest_tag[i]!)
    else []

  -- Cross-domain source routing: FP instructions may read from INT or FP PRF
  let fp_issue_src1_tag := CPU.makeIndexedWires "fp_issue_src1_tag" 6
  let fp_issue_src2_tag := CPU.makeIndexedWires "fp_issue_src2_tag" 6
  let fp_issue_src1_data_pre := CPU.makeIndexedWires "fp_issue_src1_data_pre" (if config.enableD then 64 else 32)
  let fp_issue_src2_data_pre := CPU.makeIndexedWires "fp_issue_src2_data_pre" (if config.enableD then 64 else 32)
  let fp_issue_src1_data := CPU.makeIndexedWires "fp_issue_src1_data" (if config.enableD then 64 else 32)
  let fp_issue_src2_data := CPU.makeIndexedWires "fp_issue_src2_data" (if config.enableD then 64 else 32)
  -- MUX INT rename data from the correct slot first
  let fp_int_rs1_phys := CPU.makeIndexedWires "fp_int_rs1_phys" 6
  let fp_int_rs2_phys := CPU.makeIndexedWires "fp_int_rs2_phys" 6
  let fpIntDataWidth := if config.xlen == 64 then 64 else 32
  let fp_int_rs1_data := CPU.makeIndexedWires "fp_int_rs1_data" fpIntDataWidth
  let fp_int_rs2_data := CPU.makeIndexedWires "fp_int_rs2_data" fpIntDataWidth
  let fp_crossdomain_gates :=
    if enableF then
      -- INT side: MUX between slot 0 and slot 1 rename outputs
      (List.range 6).map (fun i =>
        Gate.mkMUX rs1_phys_0[i]! rs1_phys_1[i]! fp_route_sel fp_int_rs1_phys[i]!) ++
      (List.range 6).map (fun i =>
        Gate.mkMUX rs2_phys_0[i]! rs2_phys_1[i]! fp_route_sel fp_int_rs2_phys[i]!) ++
      (List.range fpIntDataWidth).map (fun i =>
        Gate.mkMUX rs1_data_0[i]! rs1_data_1[i]! fp_route_sel fp_int_rs1_data[i]!) ++
      (List.range fpIntDataWidth).map (fun i =>
        Gate.mkMUX rs2_data_0[i]! rs2_data_1[i]! fp_route_sel fp_int_rs2_data[i]!) ++
      -- Cross-domain MUX: fp_rs1_read → FP PRF, else INT PRF
      (List.range 6).map (fun i =>
        Gate.mkMUX fp_int_rs1_phys[i]! fp_rs1_phys[i]! fp_mux_fp_rs1_read fp_issue_src1_tag[i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkMUX fp_int_rs1_data[i]! fp_rs1_data[i]! fp_mux_fp_rs1_read fp_issue_src1_data_pre[i]!) ++
      (List.range 6).map (fun i =>
        Gate.mkMUX fp_int_rs2_phys[i]! fp_rs2_phys[i]! fp_mux_fp_rs2_read fp_issue_src2_tag[i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkMUX fp_int_rs2_data[i]! fp_rs2_data[i]! fp_mux_fp_rs2_read fp_issue_src2_data_pre[i]!) ++
      (if config.enableD then
        (List.range 32).map (fun i =>
          let int_s1_hi := if config.xlen == 64 then fp_int_rs1_data[32+i]! else zero
          Gate.mkMUX int_s1_hi fp_rs1_data[32+i]! fp_mux_fp_rs1_read fp_issue_src1_data_pre[32+i]!) ++
        (List.range 32).map (fun i =>
          let int_s2_hi := if config.xlen == 64 then fp_int_rs2_data[32+i]! else zero
          Gate.mkMUX int_s2_hi fp_rs2_data[32+i]! fp_mux_fp_rs2_read fp_issue_src2_data_pre[32+i]!)
       else [])
    else []

  -- FP Busy-Bit Table (single-set, W=1)
  let fp_busy_src1_ready := Wire.mk "fp_busy_src1_ready"
  let fp_busy_src2_ready := Wire.mk "fp_busy_src2_ready"
  let fp_src3_busy_raw := Wire.mk "fp_src3_busy_raw"
  let fp_busy_set_en := Wire.mk "fp_busy_set_en"
  let fp_busy_set_gate :=
    if enableF then Gate.mkAND fp_rename_dispatch_valid fp_mux_has_fp_rd fp_busy_set_en
    else Gate.mkBUF zero fp_busy_set_en
  let fp_busy_instances : List CircuitInstance :=
    if enableF then
      [{
        moduleName := "FPBusyTable",
        instName := "u_fp_busy_table",
        portMap := [
          ("clock", clock),
          ("reset", reset),
          ("zero", zero),
          ("one", one)
        ] ++
        (flush_busy_groups.enum.map fun ⟨i, w⟩ => (s!"flush_groups_{i}", w)) ++
        (fp_rd_phys.enum.map fun ⟨i, w⟩ => (s!"set_tag_{i}", w)) ++
        [("set_en", fp_busy_set_en)] ++
        (cdb_tag_fp.enum.map fun ⟨i, w⟩ => (s!"clear_tag_{i}", w)) ++
        [("clear_en", cdb_valid_fp_prf)] ++
        (fp_rs1_phys.enum.map fun ⟨i, w⟩ => (s!"read1_tag_{i}", w)) ++
        (fp_rs2_phys.enum.map fun ⟨i, w⟩ => (s!"read2_tag_{i}", w)) ++
        (fp_rs3_phys.enum.map fun ⟨i, w⟩ => (s!"read3_tag_{i}", w)) ++
        [("src1_ready", fp_busy_src1_ready),
         ("src2_ready", fp_busy_src2_ready),
         ("src3_busy_raw", fp_src3_busy_raw)]
      }]
    else []
  let fp_busy_stub_gates : List Gate :=
    if enableF then []
    else [Gate.mkBUF one fp_busy_src1_ready,
          Gate.mkBUF one fp_busy_src2_ready,
          Gate.mkBUF zero fp_src3_busy_raw]

  -- FP src3 ready tracking: per RS-slot DFF tracks if src3 data is valid.
  -- At alloc: ready if NOT(busy[rs3_phys]) OR NOT(fp_rs3_used).
  -- On CDB match: becomes ready.
  -- Prevents RS from issuing FMADD before src3 operand arrives.
  let fp_src3_rdy := (List.range 2).map fun slot => Wire.mk s!"fp_src3_rdy_{slot}"
  let fp_src3_busy_gates : List Gate :=
    if enableF then
      -- busy=1 means NOT ready. Invert, then OR with NOT(fp_rs3_used) for non-FMA ops.
      let fp_src3_not_busy := Wire.mk "fp_src3_not_busy"
      let fp_src3_alloc_ready := Wire.mk "fp_src3_alloc_ready"
      let not_rs3_used := Wire.mk "fp_not_rs3_used"
      let alloc_ready_gates := [
        Gate.mkNOT fp_src3_busy_raw fp_src3_not_busy,
        Gate.mkNOT fp_mux_fp_rs3_used not_rs3_used,
        Gate.mkOR fp_src3_not_busy not_rs3_used fp_src3_alloc_ready]
      -- Per-slot src3 NOT-ready DFF (reset=0 means ready, since we store inverted):
      -- not_rdy_d = MUX(hold, NOT(alloc_ready), alloc_we) then MUX(that, 0, cdb_match)
      -- ext_ready_mask = NOT(not_rdy_dff)
      let fp_src3_not_rdy := (List.range 2).map fun slot => Wire.mk s!"fp_src3_nrdy_{slot}"
      let fp_src3_alloc_not_ready := Wire.mk "fp_src3_alloc_nrdy"
      let per_slot_gates := [Gate.mkNOT fp_src3_alloc_ready fp_src3_alloc_not_ready] ++
        (List.range 2).flatMap fun slot =>
        let d_alloc := Wire.mk s!"fp_src3_nrdy_{slot}_da"
        let d_cdb := Wire.mk s!"fp_src3_nrdy_{slot}_dc"
        [Gate.mkMUX fp_src3_not_rdy[slot]! fp_src3_alloc_not_ready (Wire.mk s!"fp_src3_we_{slot}") d_alloc,
         Gate.mkMUX d_alloc zero (Wire.mk s!"fp_src3_eff_cdb_we_{slot}") d_cdb,
         Gate.mkDFF d_cdb clock reset fp_src3_not_rdy[slot]!,
         Gate.mkNOT fp_src3_not_rdy[slot]! fp_src3_rdy[slot]!]
      alloc_ready_gates ++ per_slot_gates
    else
      -- If FP is disabled, all slots always ready
      (List.range 2).map fun slot => Gate.mkBUF one fp_src3_rdy[slot]!

  -- FP busy table intra-group RAW bypass:
  -- When set_en fires (FLW/FP instruction allocates FP tag X) and the consumer instruction
  -- reads the same tag X, force "not ready" since the busy table DFF hasn't updated yet.
  let fp_raw_s1_hit := Wire.mk "fp_raw_s1_hit"
  let fp_raw_s2_hit := Wire.mk "fp_raw_s2_hit"
  let fp_busy_src1_ready_bypassed := Wire.mk "fp_busy_src1_ready_byp"
  let fp_busy_src2_ready_bypassed := Wire.mk "fp_busy_src2_ready_byp"
  let fp_raw_bypass_gates :=
    if enableF then
      let tagWidth := 6
      let mkTagEq (pfx2 : String) (a b : List Wire) (out : Wire) : List Gate :=
        let xns := (List.range tagWidth).map fun i =>
          let x := Wire.mk s!"{pfx2}_x{i}"; let xn := Wire.mk s!"{pfx2}_xn{i}"
          [Gate.mkXOR a[i]! b[i]! x, Gate.mkNOT x xn]
        let ands := [
          Gate.mkAND (Wire.mk s!"{pfx2}_xn0") (Wire.mk s!"{pfx2}_xn1") (Wire.mk s!"{pfx2}_a01"),
          Gate.mkAND (Wire.mk s!"{pfx2}_xn2") (Wire.mk s!"{pfx2}_xn3") (Wire.mk s!"{pfx2}_a23"),
          Gate.mkAND (Wire.mk s!"{pfx2}_xn4") (Wire.mk s!"{pfx2}_xn5") (Wire.mk s!"{pfx2}_a45"),
          Gate.mkAND (Wire.mk s!"{pfx2}_a01") (Wire.mk s!"{pfx2}_a23") (Wire.mk s!"{pfx2}_a0123"),
          Gate.mkAND (Wire.mk s!"{pfx2}_a0123") (Wire.mk s!"{pfx2}_a45") out]
        xns.flatten ++ ands
      let fp_set_eq_r1 := Wire.mk "fp_raw_set_eq_r1"
      let fp_set_eq_r2 := Wire.mk "fp_raw_set_eq_r2"
      let not_raw_s1 := Wire.mk "fp_raw_not_s1"
      let not_raw_s2 := Wire.mk "fp_raw_not_s2"
      mkTagEq "fp_raw_s1" fp_rd_phys fp_rs1_phys fp_set_eq_r1 ++
      mkTagEq "fp_raw_s2" fp_rd_phys fp_rs2_phys fp_set_eq_r2 ++
      [Gate.mkAND fp_busy_set_en fp_set_eq_r1 fp_raw_s1_hit,
       Gate.mkAND fp_busy_set_en fp_set_eq_r2 fp_raw_s2_hit,
       Gate.mkNOT fp_raw_s1_hit not_raw_s1,
       Gate.mkNOT fp_raw_s2_hit not_raw_s2,
       Gate.mkAND fp_busy_src1_ready not_raw_s1 fp_busy_src1_ready_bypassed,
       Gate.mkAND fp_busy_src2_ready not_raw_s2 fp_busy_src2_ready_bypassed]
    else
      [Gate.mkBUF one fp_busy_src1_ready_bypassed, Gate.mkBUF one fp_busy_src2_ready_bypassed,
       Gate.mkBUF zero fp_raw_s1_hit, Gate.mkBUF zero fp_raw_s2_hit]

  -- FP source readiness: merge busy table (pre-CDB-forwarding)
  let fp_issue_src1_ready_pre := Wire.mk "fp_issue_src1_ready_pre"
  let fp_issue_src2_ready_pre := Wire.mk "fp_issue_src2_ready_pre"
  let fp_issue_src1_ready := Wire.mk "fp_issue_src1_ready"
  let fp_issue_src2_ready := Wire.mk "fp_issue_src2_ready"
  let fp_ready_gates :=
    if enableF then
      -- When reading from INT domain, use INT busy table result (src1_ready from that slot)
      let fp_int_src1_ready := Wire.mk "fp_int_src1_ready"
      let fp_int_src2_ready := Wire.mk "fp_int_src2_ready"
      [Gate.mkMUX src1_ready_0 src1_ready_1 fp_route_sel fp_int_src1_ready,
       Gate.mkMUX src2_ready_0 src2_ready_1 fp_route_sel fp_int_src2_ready,
       -- Cross-domain: if reading FP → FP busy (with RAW bypass), if reading INT → INT busy
       Gate.mkMUX fp_int_src1_ready fp_busy_src1_ready_bypassed fp_mux_fp_rs1_read fp_issue_src1_ready_pre,
       Gate.mkMUX fp_int_src2_ready fp_busy_src2_ready_bypassed fp_mux_fp_rs2_read fp_issue_src2_ready_pre]
    else
      [Gate.mkBUF one fp_issue_src1_ready_pre, Gate.mkBUF one fp_issue_src2_ready_pre]

  -- FP CDB forwarding: when CDB broadcasts FP result in the same cycle as FP RS dispatch,
  -- forward CDB data instead of stale PRF data (PRF write takes effect next clock edge).
  let fp_cdb_fwd_match_s1 := Wire.mk "fp_cdb_fwd_match_s1"
  let fp_cdb_fwd_match_s2 := Wire.mk "fp_cdb_fwd_match_s2"
  let fp_cdb_fwd_s1 := Wire.mk "fp_cdb_fwd_s1"
  let fp_cdb_fwd_s2 := Wire.mk "fp_cdb_fwd_s2"
  let fp_cdb_fwd_cmp_s1_inst : CircuitInstance := {
    moduleName := "EqualityComparator6"
    instName := "u_fp_cdb_fwd_cmp_s1"
    portMap := [("eq", fp_cdb_fwd_match_s1)] ++
               (cdb_tag_fp.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (fp_issue_src1_tag.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  }
  let fp_cdb_fwd_cmp_s2_inst : CircuitInstance := {
    moduleName := "EqualityComparator6"
    instName := "u_fp_cdb_fwd_cmp_s2"
    portMap := [("eq", fp_cdb_fwd_match_s2)] ++
               (cdb_tag_fp.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (fp_issue_src2_tag.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w)))
  }
  let (fp_cdb_fwd_gates, fp_cdb_fwd_instances) :=
    if enableF then
      -- fwd_sX = cdb_valid_fp_prf AND tag_match AND fp_mux_fp_rsX_read
      let fp_cdb_fwd_s1_tmp := Wire.mk "fp_cdb_fwd_s1_tmp"
      let fp_cdb_fwd_s2_tmp := Wire.mk "fp_cdb_fwd_s2_tmp"
      let gates :=
        [Gate.mkAND cdb_valid_fp_prf fp_cdb_fwd_match_s1 fp_cdb_fwd_s1_tmp,
         Gate.mkAND fp_cdb_fwd_s1_tmp fp_mux_fp_rs1_read fp_cdb_fwd_s1,
         Gate.mkAND cdb_valid_fp_prf fp_cdb_fwd_match_s2 fp_cdb_fwd_s2_tmp,
         Gate.mkAND fp_cdb_fwd_s2_tmp fp_mux_fp_rs2_read fp_cdb_fwd_s2,
         -- Ready = busy_ready OR cdb_fwd
         Gate.mkOR fp_issue_src1_ready_pre fp_cdb_fwd_s1 fp_issue_src1_ready,
         Gate.mkOR fp_issue_src2_ready_pre fp_cdb_fwd_s2 fp_issue_src2_ready] ++
        -- Data MUX: if fwd, use cdb_data_fp; else use pre-fwd data
        (List.range 32).map (fun i =>
          Gate.mkMUX fp_issue_src1_data_pre[i]! cdb_data_fp[i]! fp_cdb_fwd_s1 fp_issue_src1_data[i]!) ++
        (List.range 32).map (fun i =>
          Gate.mkMUX fp_issue_src2_data_pre[i]! cdb_data_fp[i]! fp_cdb_fwd_s2 fp_issue_src2_data[i]!) ++
        (if config.enableD then
          (List.range 32).map (fun i =>
            Gate.mkMUX fp_issue_src1_data_pre[32+i]! cdb_data_fp[32+i]! fp_cdb_fwd_s1 fp_issue_src1_data[32+i]!) ++
          (List.range 32).map (fun i =>
            Gate.mkMUX fp_issue_src2_data_pre[32+i]! cdb_data_fp[32+i]! fp_cdb_fwd_s2 fp_issue_src2_data[32+i]!)
         else [])
      (gates, [fp_cdb_fwd_cmp_s1_inst, fp_cdb_fwd_cmp_s2_inst])
    else
      ([Gate.mkBUF fp_issue_src1_ready_pre fp_issue_src1_ready,
        Gate.mkBUF fp_issue_src2_ready_pre fp_issue_src2_ready] ++
       (List.range 32).map (fun i =>
         Gate.mkBUF fp_issue_src1_data_pre[i]! fp_issue_src1_data[i]!) ++
       (List.range 32).map (fun i =>
         Gate.mkBUF fp_issue_src2_data_pre[i]! fp_issue_src2_data[i]!) ++
       (if config.enableD then
         (List.range 32).map (fun i =>
           Gate.mkBUF fp_issue_src1_data_pre[32+i]! fp_issue_src1_data[32+i]!) ++
         (List.range 32).map (fun i =>
           Gate.mkBUF fp_issue_src2_data_pre[32+i]! fp_issue_src2_data[32+i]!)
        else []), [])

  -- Note: cross-domain stall not needed in W=2 because FP RS uses raw CDB
  -- (both INT and FP CDB channels) to avoid the need for domain filtering.
  let crossdomain_stall_gates : List Gate := []

  -- FP Opcode LUT: optype → 5-bit (or 6-bit) FPU opcode
  let fpuOpWidth := if config.enableD then 6 else 5
  let fpu_opcode := CPU.makeIndexedWires "fpu_opcode" fpuOpWidth
  let fpu_opcode_padded := fpu_opcode ++ (List.replicate (opcodeWidth - fpuOpWidth) zero)  -- zero-pad to opcodeWidth for RS
  let fpu_lut_gates : List Gate := []
  let fpu_lut_inst : List CircuitInstance :=
    if enableF then
      [{ moduleName := s!"FPUOpDecoder_{config.isaString}"
         instName := "u_fpu_lut"
         portMap := bundledPorts "optype" fp_mux_opcode ++
                    bundledPorts "out_op" fpu_opcode }]
    else []

  -- FP RS (single-issue, W=1, 2 entries)
  let rs_fp_alloc_ptr := Wire.mk "rs_fp_alloc_ptr"
  let rs_fp_grant := CPU.makeIndexedWires "rs_fp_grant" 2
  let rs_fp_issue_full := Wire.mk "rs_fp_issue_full"
  let rs_fp_dispatch_valid := Wire.mk "rs_fp_dispatch_valid"
  let rs_fp_dispatch_opcode := CPU.makeIndexedWires "rs_fp_dispatch_opcode" fpuOpWidth
  let rsFPDataWidth := if config.enableD then 64 else 32
  let rs_fp_dispatch_src1 := CPU.makeIndexedWires "rs_fp_dispatch_src1" rsFPDataWidth
  let rs_fp_dispatch_src2 := CPU.makeIndexedWires "rs_fp_dispatch_src2" rsFPDataWidth
  let rs_fp_dispatch_tag := CPU.makeIndexedWires "rs_fp_dispatch_tag" 6

  -- Gate FP RS dispatch: don't dispatch when FP EU is busy
  let fp_fifo_enq_ready := Wire.mk "fp_fifo_enq_ready"
  let fp_rs_dispatch_en := Wire.mk "fp_rs_dispatch_en"
  let fp_rs_dispatch_gate :=
    if enableF then
      let not_fp_eu_busy := Wire.mk "not_fp_eu_busy"
      [Gate.mkNOT (Wire.mk "fp_busy_eu") not_fp_eu_busy,
       Gate.mkBUF not_fp_eu_busy fp_rs_dispatch_en]
    else [Gate.mkBUF one fp_rs_dispatch_en]

  let fp_rs_cdb_gates : List Gate := []

  -- FP RS suppress: combine INT-domain and FP-domain RAW hazards
  let fp_supp_s1_0 := Wire.mk "fp_supp_s1_0"
  let fp_supp_s2_0 := Wire.mk "fp_supp_s2_0"
  let fp_supp_gates :=
    if enableF then
      let not_fp_rs1 := Wire.mk "fp_supp_not_fp_rs1"
      let not_fp_rs2 := Wire.mk "fp_supp_not_fp_rs2"
      let int_raw_s1 := Wire.mk "fp_supp_int_raw_s1"
      let int_raw_s2 := Wire.mk "fp_supp_int_raw_s2"
      let fp_dom_raw_s1 := Wire.mk "fp_supp_fp_dom_raw_s1"
      let fp_dom_raw_s2 := Wire.mk "fp_supp_fp_dom_raw_s2"
      let any_raw_s1 := Wire.mk "fp_supp_any_raw_s1"
      let any_raw_s2 := Wire.mk "fp_supp_any_raw_s2"
      [-- INT domain: NOT(fp_read) AND int_busy_raw
       Gate.mkNOT fp_mux_fp_rs1_read not_fp_rs1,
       Gate.mkAND not_fp_rs1 busy_raw_s1_hit int_raw_s1,
       -- FP domain: fp_read AND fp_raw_hit
       Gate.mkAND fp_mux_fp_rs1_read fp_raw_s1_hit fp_dom_raw_s1,
       -- Combined: OR(int_raw, fp_dom_raw) AND route_sel
       Gate.mkOR int_raw_s1 fp_dom_raw_s1 any_raw_s1,
       Gate.mkAND fp_route_sel any_raw_s1 fp_supp_s1_0,
       -- Same for src2
       Gate.mkNOT fp_mux_fp_rs2_read not_fp_rs2,
       Gate.mkAND not_fp_rs2 busy_raw_s2_hit int_raw_s2,
       Gate.mkAND fp_mux_fp_rs2_read fp_raw_s2_hit fp_dom_raw_s2,
       Gate.mkOR int_raw_s2 fp_dom_raw_s2 any_raw_s2,
       Gate.mkAND fp_route_sel any_raw_s2 fp_supp_s2_0]
    else
      [Gate.mkBUF zero fp_supp_s1_0, Gate.mkBUF zero fp_supp_s2_0]

  let rs_fp_inst : CircuitInstance := {
    moduleName := if config.enableD then "FPReservationStation2_W1_64" else "FPReservationStation2_W1"
    instName := "u_rs_fp"
    portMap := [("clock", clock), ("reset", pipeline_reset_rs_fp),
                ("issue_en", fp_dispatch_valid)] ++
               bundledPorts "issue_opcode" fpu_opcode ++
               bundledPorts "issue_dest_tag" fp_issue_dest_tag ++
               [("issue_src1_ready", fp_issue_src1_ready)] ++
               bundledPorts "issue_src1_tag" (fp_issue_src1_tag ++ [fp_mux_fp_rs1_read]) ++
               bundledPorts "issue_src1_data" fp_issue_src1_data ++
               [("issue_src2_ready", fp_issue_src2_ready)] ++
               bundledPorts "issue_src2_tag" (fp_issue_src2_tag ++ [fp_mux_fp_rs2_read]) ++
               bundledPorts "issue_src2_data" fp_issue_src2_data ++
               [("cdb_valid_0", cdb_valid_0), ("cdb_is_fp_0", cdb_is_fp_0)] ++
               bundledPorts "cdb_tag_0" cdb_tag_0 ++
               bundledPorts "cdb_data_0" (if config.enableD then cdb_data_0 else cdb_data32_0) ++
               [("cdb_valid_1", cdb_valid_1), ("cdb_is_fp_1", cdb_is_fp_1)] ++
               bundledPorts "cdb_tag_1" cdb_tag_1 ++
               bundledPorts "cdb_data_1" (if config.enableD then cdb_data_1 else cdb_data32_1) ++
               [("dispatch_en", fp_rs_dispatch_en),
                ("suppress_cdb_s1", fp_supp_s1_0),
                ("suppress_cdb_s2", fp_supp_s2_0),
                ("ext_ready_mask_0", fp_src3_rdy[0]!),
                ("ext_ready_mask_1", fp_src3_rdy[1]!),
                ("alloc_avail", Wire.mk "rs_fp_avail_0"),
                ("dispatch_valid", rs_fp_dispatch_valid),
                ("alloc_ptr", rs_fp_alloc_ptr),
                ("dispatch_grant_0", rs_fp_grant[0]!),
                ("dispatch_grant_1", rs_fp_grant[1]!)] ++
               bundledPorts "dispatch_opcode" rs_fp_dispatch_opcode ++
               bundledPorts "dispatch_src1_data" rs_fp_dispatch_src1 ++
               bundledPorts "dispatch_src2_data" rs_fp_dispatch_src2 ++
               bundledPorts "dispatch_dest_tag" rs_fp_dispatch_tag
  }

  -- FP SRC3 SIDECAR: 2-entry × flen-bit storage for FMA rs3 data
  let fp_src3_dispatch := CPU.makeIndexedWires "fp_src3_dispatch" config.flen
  let fp_src3_we := (List.range 2).map (fun slot => Wire.mk s!"fp_src3_we_{slot}")
  let fp_src3_alloc_decode :=
    if enableF then
      let not_ap := Wire.mk "fp_src3_not_ap"
      [Gate.mkNOT rs_fp_alloc_ptr not_ap,
       Gate.mkAND not_ap fp_dispatch_valid fp_src3_we[0]!,
       Gate.mkAND rs_fp_alloc_ptr fp_dispatch_valid fp_src3_we[1]!]
    else []
  let fp_src3_slots := (List.range 2).map (fun slot =>
    CPU.makeIndexedWires s!"fp_src3_slot{slot}" config.flen)
  let fp_src3_tags := (List.range 2).map (fun slot =>
    CPU.makeIndexedWires s!"fp_src3_tag{slot}" 6)
  let fp_src3_alloc_cdb_match := Wire.mk "fp_src3_alloc_cdb_match"
  let fp_src3_alloc_cdb_gates :=
    if enableF then
      (List.range 6).flatMap (fun bit =>
        [Gate.mkXOR fp_rs3_phys[bit]! cdb_tag_0[bit]! (Wire.mk s!"fp_src3_acdb0_xor_{bit}"),
         Gate.mkNOT (Wire.mk s!"fp_src3_acdb0_xor_{bit}") (Wire.mk s!"fp_src3_acdb0_eq_{bit}")]) ++
      [Gate.mkAND (Wire.mk "fp_src3_acdb0_eq_0") (Wire.mk "fp_src3_acdb0_eq_1") (Wire.mk "fp_src3_acdb0_and01"),
       Gate.mkAND (Wire.mk "fp_src3_acdb0_eq_2") (Wire.mk "fp_src3_acdb0_eq_3") (Wire.mk "fp_src3_acdb0_and23"),
       Gate.mkAND (Wire.mk "fp_src3_acdb0_eq_4") (Wire.mk "fp_src3_acdb0_eq_5") (Wire.mk "fp_src3_acdb0_and45"),
       Gate.mkAND (Wire.mk "fp_src3_acdb0_and01") (Wire.mk "fp_src3_acdb0_and23") (Wire.mk "fp_src3_acdb0_and0123"),
       Gate.mkAND (Wire.mk "fp_src3_acdb0_and0123") (Wire.mk "fp_src3_acdb0_and45") (Wire.mk "fp_src3_acdb0_tag_match"),
       Gate.mkAND (Wire.mk "fp_src3_acdb0_tag_match") cdb_valid_fp_ch0 (Wire.mk "fp_src3_acdb0_hit")] ++
      (List.range 6).flatMap (fun bit =>
        [Gate.mkXOR fp_rs3_phys[bit]! cdb_tag_1[bit]! (Wire.mk s!"fp_src3_acdb1_xor_{bit}"),
         Gate.mkNOT (Wire.mk s!"fp_src3_acdb1_xor_{bit}") (Wire.mk s!"fp_src3_acdb1_eq_{bit}")]) ++
      [Gate.mkAND (Wire.mk "fp_src3_acdb1_eq_0") (Wire.mk "fp_src3_acdb1_eq_1") (Wire.mk "fp_src3_acdb1_and01"),
       Gate.mkAND (Wire.mk "fp_src3_acdb1_eq_2") (Wire.mk "fp_src3_acdb1_eq_3") (Wire.mk "fp_src3_acdb1_and23"),
       Gate.mkAND (Wire.mk "fp_src3_acdb1_eq_4") (Wire.mk "fp_src3_acdb1_eq_5") (Wire.mk "fp_src3_acdb1_and45"),
       Gate.mkAND (Wire.mk "fp_src3_acdb1_and01") (Wire.mk "fp_src3_acdb1_and23") (Wire.mk "fp_src3_acdb1_and0123"),
       Gate.mkAND (Wire.mk "fp_src3_acdb1_and0123") (Wire.mk "fp_src3_acdb1_and45") (Wire.mk "fp_src3_acdb1_tag_match"),
       Gate.mkAND (Wire.mk "fp_src3_acdb1_tag_match") cdb_valid_fp_ch1 (Wire.mk "fp_src3_acdb1_hit"),
       Gate.mkOR (Wire.mk "fp_src3_acdb0_hit") (Wire.mk "fp_src3_acdb1_hit") fp_src3_alloc_cdb_match]
    else []
  let fp_src3_cdb_data := CPU.makeIndexedWires "fp_src3_cdb_data" config.flen
  let fp_src3_cdb_data_mux :=
    if enableF then
      (List.range config.flen).map (fun bit =>
        Gate.mkMUX cdb_data_1[bit]! cdb_data_0[bit]! cdb_valid_fp_ch0 fp_src3_cdb_data[bit]!)
    else []
  let fp_src3_dff_gates :=
    if enableF then
      (List.range 2).flatMap (fun slot =>
        (List.range 6).flatMap (fun bit =>
          let d := Wire.mk s!"fp_src3_tag{slot}_d_{bit}"
          [Gate.mkMUX fp_src3_tags[slot]![bit]! fp_rs3_phys[bit]! fp_src3_we[slot]! d,
           Gate.mkDFF d clock reset fp_src3_tags[slot]![bit]!]) ++
        (List.range 6).flatMap (fun bit =>
          [Gate.mkXOR fp_src3_tags[slot]![bit]! cdb_tag_0[bit]! (Wire.mk s!"fp_src3_cdb0_xor{slot}_{bit}"),
           Gate.mkNOT (Wire.mk s!"fp_src3_cdb0_xor{slot}_{bit}") (Wire.mk s!"fp_src3_cdb0_eq{slot}_{bit}")]) ++
        [Gate.mkAND (Wire.mk s!"fp_src3_cdb0_eq{slot}_0") (Wire.mk s!"fp_src3_cdb0_eq{slot}_1") (Wire.mk s!"fp_src3_cdb0_and01_{slot}"),
         Gate.mkAND (Wire.mk s!"fp_src3_cdb0_eq{slot}_2") (Wire.mk s!"fp_src3_cdb0_eq{slot}_3") (Wire.mk s!"fp_src3_cdb0_and23_{slot}"),
         Gate.mkAND (Wire.mk s!"fp_src3_cdb0_eq{slot}_4") (Wire.mk s!"fp_src3_cdb0_eq{slot}_5") (Wire.mk s!"fp_src3_cdb0_and45_{slot}"),
         Gate.mkAND (Wire.mk s!"fp_src3_cdb0_and01_{slot}") (Wire.mk s!"fp_src3_cdb0_and23_{slot}") (Wire.mk s!"fp_src3_cdb0_and0123_{slot}"),
         Gate.mkAND (Wire.mk s!"fp_src3_cdb0_and0123_{slot}") (Wire.mk s!"fp_src3_cdb0_and45_{slot}") (Wire.mk s!"fp_src3_cdb0_tag_match_{slot}"),
         Gate.mkAND (Wire.mk s!"fp_src3_cdb0_tag_match_{slot}") cdb_valid_fp_ch0 (Wire.mk s!"fp_src3_cdb0_we_{slot}")] ++
        (List.range 6).flatMap (fun bit =>
          [Gate.mkXOR fp_src3_tags[slot]![bit]! cdb_tag_1[bit]! (Wire.mk s!"fp_src3_cdb1_xor{slot}_{bit}"),
           Gate.mkNOT (Wire.mk s!"fp_src3_cdb1_xor{slot}_{bit}") (Wire.mk s!"fp_src3_cdb1_eq{slot}_{bit}")]) ++
        [Gate.mkAND (Wire.mk s!"fp_src3_cdb1_eq{slot}_0") (Wire.mk s!"fp_src3_cdb1_eq{slot}_1") (Wire.mk s!"fp_src3_cdb1_and01_{slot}"),
         Gate.mkAND (Wire.mk s!"fp_src3_cdb1_eq{slot}_2") (Wire.mk s!"fp_src3_cdb1_eq{slot}_3") (Wire.mk s!"fp_src3_cdb1_and23_{slot}"),
         Gate.mkAND (Wire.mk s!"fp_src3_cdb1_eq{slot}_4") (Wire.mk s!"fp_src3_cdb1_eq{slot}_5") (Wire.mk s!"fp_src3_cdb1_and45_{slot}"),
         Gate.mkAND (Wire.mk s!"fp_src3_cdb1_and01_{slot}") (Wire.mk s!"fp_src3_cdb1_and23_{slot}") (Wire.mk s!"fp_src3_cdb1_and0123_{slot}"),
         Gate.mkAND (Wire.mk s!"fp_src3_cdb1_and0123_{slot}") (Wire.mk s!"fp_src3_cdb1_and45_{slot}") (Wire.mk s!"fp_src3_cdb1_tag_match_{slot}"),
         Gate.mkAND (Wire.mk s!"fp_src3_cdb1_tag_match_{slot}") cdb_valid_fp_ch1 (Wire.mk s!"fp_src3_cdb1_we_{slot}"),
         Gate.mkOR (Wire.mk s!"fp_src3_cdb0_we_{slot}") (Wire.mk s!"fp_src3_cdb1_we_{slot}") (Wire.mk s!"fp_src3_cdb_we_{slot}"),
         Gate.mkAND fp_src3_we[slot]! fp_src3_alloc_cdb_match (Wire.mk s!"fp_src3_alloc_byp_{slot}"),
         Gate.mkOR (Wire.mk s!"fp_src3_cdb_we_{slot}") (Wire.mk s!"fp_src3_alloc_byp_{slot}") (Wire.mk s!"fp_src3_eff_cdb_we_{slot}")] ++
        (List.range config.flen).flatMap (fun bit =>
          let alloc_mux := Wire.mk s!"fp_src3_slot{slot}_am_{bit}"
          let d_mux := Wire.mk s!"fp_src3_slot{slot}_d_{bit}"
          [Gate.mkMUX fp_src3_slots[slot]![bit]! fp_rs3_data[bit]! fp_src3_we[slot]! alloc_mux,
           Gate.mkMUX alloc_mux fp_src3_cdb_data[bit]! (Wire.mk s!"fp_src3_eff_cdb_we_{slot}") d_mux,
           Gate.mkDFF d_mux clock reset fp_src3_slots[slot]![bit]!]))
    else []
  let fp_src3_read_gates :=
    if enableF then
      (List.range config.flen).flatMap (fun bit =>
        let byp0 := Wire.mk s!"fp_src3_byp0_{bit}"
        let byp1 := Wire.mk s!"fp_src3_byp1_{bit}"
        [Gate.mkMUX fp_src3_slots[0]![bit]! fp_src3_cdb_data[bit]! (Wire.mk "fp_src3_eff_cdb_we_0") byp0,
         Gate.mkMUX fp_src3_slots[1]![bit]! fp_src3_cdb_data[bit]! (Wire.mk "fp_src3_eff_cdb_we_1") byp1,
         Gate.mkMUX byp0 byp1 rs_fp_grant[1]! fp_src3_dispatch[bit]!])
    else []

  -- FP RM SIDECAR: 2-entry × 3-bit storage for resolved rounding mode
  let frm_reg := CPU.makeIndexedWires "frm_reg" 3
  let frm_new := CPU.makeIndexedWires "frm_new" 3
  let fp_rm_dispatch := CPU.makeIndexedWires "fp_rm_dispatch" 3
  let rm_is_dynamic := Wire.mk "rm_is_dynamic"
  let rm_resolved := CPU.makeIndexedWires "rm_resolved" 3
  let rm_resolve_gates :=
    if enableF then
      let rm_and01 := Wire.mk "rm_and01"
      [Gate.mkAND fp_mux_decode_rm[0]! fp_mux_decode_rm[1]! rm_and01,
       Gate.mkAND rm_and01 fp_mux_decode_rm[2]! rm_is_dynamic] ++
      (List.range 3).map (fun i =>
        Gate.mkMUX fp_mux_decode_rm[i]! frm_reg[i]! rm_is_dynamic rm_resolved[i]!)
    else []
  let fp_rm_we := (List.range 2).map (fun slot => Wire.mk s!"fp_rm_we_{slot}")
  let fp_rm_alloc_decode :=
    if enableF then
      let not_ap := Wire.mk "fp_rm_not_ap"
      [Gate.mkNOT rs_fp_alloc_ptr not_ap,
       Gate.mkAND not_ap fp_dispatch_valid fp_rm_we[0]!,
       Gate.mkAND rs_fp_alloc_ptr fp_dispatch_valid fp_rm_we[1]!]
    else []
  let fp_rm_slots := (List.range 2).map (fun slot =>
    CPU.makeIndexedWires s!"fp_rm_slot{slot}" 3)
  let fp_rm_dff_gates :=
    if enableF then
      (List.range 2).flatMap (fun slot =>
        (List.range 3).flatMap (fun bit =>
          let d_mux := Wire.mk s!"fp_rm_slot{slot}_d_{bit}"
          [Gate.mkMUX fp_rm_slots[slot]![bit]! rm_resolved[bit]! fp_rm_we[slot]! d_mux,
           Gate.mkDFF d_mux clock reset fp_rm_slots[slot]![bit]!]))
    else []
  let fp_rm_read_gates :=
    if enableF then
      (List.range 3).map (fun bit =>
        Gate.mkMUX fp_rm_slots[0]![bit]! fp_rm_slots[1]![bit]! rs_fp_grant[1]! fp_rm_dispatch[bit]!)
    else []

  -- FP Execution Unit
  let fp_result := CPU.makeIndexedWires "fp_result" config.flen
  let fp_tag_out := CPU.makeIndexedWires "fp_tag_out" 6
  let fp_exceptions := CPU.makeIndexedWires "fp_exceptions" 5
  let fp_valid_out := Wire.mk "fp_valid_out"
  let fp_busy_eu := Wire.mk "fp_busy_eu"
  let fp_result_is_int := Wire.mk "fp_result_is_int"
  let fp_op := CPU.makeIndexedWires "fp_op" (if config.enableD then 6 else 5)
  let fp_rm_out := CPU.makeIndexedWires "fp_rm_eu" 3
  let fp_op_gates :=
    if enableF then
      [Gate.mkAND rs_fp_dispatch_valid fp_rs_dispatch_en (Wire.mk "fp_eu_valid_in")] ++
      (List.range (if config.enableD then 6 else 5)).map (fun i =>
        Gate.mkBUF rs_fp_dispatch_opcode[i]! fp_op[i]!) ++
      (List.range 3).map (fun i =>
        Gate.mkBUF fp_rm_dispatch[i]! fp_rm_out[i]!)
    else []
  let fp_exec_inst : CircuitInstance := {
    moduleName := if config.enableD then "FPExecUnit_D" else "FPExecUnit"
    instName := "u_exec_fp"
    portMap :=
      bundledPorts "src1" rs_fp_dispatch_src1 ++
      bundledPorts "src2" rs_fp_dispatch_src2 ++
      bundledPorts "src3" fp_src3_dispatch ++
      bundledPorts "op" fp_op ++ bundledPorts "rm" fp_rm_out ++
      bundledPorts "dest_tag" (rs_fp_dispatch_tag.take 6) ++
      [("valid_in", Wire.mk "fp_eu_valid_in"),
       ("clock", clock), ("reset", reset),
       ("zero", zero), ("one", one)] ++
      bundledPorts "result" fp_result ++
      bundledPorts "tag_out" fp_tag_out ++
      bundledPorts "exceptions" fp_exceptions ++
      [("valid_out", fp_valid_out), ("busy", fp_busy_eu),
       ("result_is_int", fp_result_is_int)]
  }

  -- FP result FIFO data assembly
  let fp_fifo_width := if config.enableD then 71 else 39
  let fp_enq_is_fp := Wire.mk "fp_enq_is_fp"
  let fp_fifo_enq_data := CPU.makeIndexedWires "fp_fifo_enq_data" fp_fifo_width
  let fp_enq_is_fp_gate :=
    if enableF then [Gate.mkNOT fp_result_is_int fp_enq_is_fp]
    else [Gate.mkBUF zero fp_enq_is_fp]
  let fp_fifo_enq_assemble :=
    if enableF then
      (List.range 6).map (fun i => Gate.mkBUF fp_tag_out[i]! fp_fifo_enq_data[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF fp_result[i]! fp_fifo_enq_data[6+i]!) ++
      (if config.enableD then
        (List.range 32).map (fun i => Gate.mkBUF fp_result[32+i]! fp_fifo_enq_data[38+i]!) ++
        [Gate.mkBUF fp_enq_is_fp fp_fifo_enq_data[70]!]
       else
        [Gate.mkBUF fp_enq_is_fp fp_fifo_enq_data[38]!])
    else
      (List.range fp_fifo_width).map (fun i => Gate.mkBUF zero fp_fifo_enq_data[i]!)

  -- is_fp_shadow: now managed internally by ROB (head_is_fp_0/1 outputs)

  -- === SIDECAR REGISTER FILES ===
  -- Integer RS: captured PC and IMM for AUIPC/LUI post-processing
  -- Slot 0 uses bank 0 (rs_int_alloc_ptr[0] selects within entries 0,1)
  -- Slot 1 uses bank 1 (rs_int_alloc_ptr[1] selects within entries 2,3)
  let int_captured_pc_0 := CPU.makeIndexedWires "int_captured_pc_0" 32
  let int_captured_pc_1 := CPU.makeIndexedWires "int_captured_pc_1" 32
  let (int_pc_rf_gates, _int_pc_rf_entries) :=
    mkSidecarRegFile4x32_W2 "int_pc_rf" clock reset
      rs_int_alloc_ptr[0]! dispatch_int_0 fetch_pc_0
      rs_int_alloc_ptr[1]! dispatch_int_1 fetch_pc_1
      rs_int_grant int_captured_pc_0 int_captured_pc_1
  let int_captured_imm_0 := CPU.makeIndexedWires "int_captured_imm_0" 32
  let int_captured_imm_1 := CPU.makeIndexedWires "int_captured_imm_1" 32
  let (int_imm_rf_gates, _int_imm_rf_entries) :=
    mkSidecarRegFile4x32_W2 "int_imm_rf" clock reset
      rs_int_alloc_ptr[0]! dispatch_int_0 d0_imm
      rs_int_alloc_ptr[1]! dispatch_int_1 d1_imm
      rs_int_grant int_captured_imm_0 int_captured_imm_1

  -- Branch RS: captured PC, IMM, and predicted_taken (2 entries)
  let br_captured_pc := CPU.makeIndexedWires "br_captured_pc" 32
  let (br_pc_rf_gates, _br_pc_rf_entries) :=
    mkSidecarRegFile2x32 "br_pc_rf" clock reset rs_br_alloc_ptr br_dispatch_valid br_mux_pc rs_br_grant[1]! br_captured_pc
  let br_captured_imm := CPU.makeIndexedWires "br_captured_imm" 32
  let (br_imm_rf_gates, _br_imm_rf_entries) :=
    mkSidecarRegFile2x32 "br_imm_rf" clock reset rs_br_alloc_ptr br_dispatch_valid br_mux_imm rs_br_grant[1]! br_captured_imm

  -- Branch predicted_taken sidecar (1-bit, 2 entries)
  let br_pred_not_ap := Wire.mk "br_pred_not_ap"
  let br_pred_we := CPU.makeIndexedWires "br_pred_we" 2
  let br_pred_e := (List.range 2).map (fun e => Wire.mk s!"br_pred_e{e}")
  let fetch_predicted_taken := Wire.mk "fetch_predicted_taken_br"
  let br_pred_dec_gates :=
    [Gate.mkNOT rs_br_alloc_ptr br_pred_not_ap,
     Gate.mkAND br_pred_not_ap br_dispatch_valid br_pred_we[0]!,
     Gate.mkAND rs_br_alloc_ptr br_dispatch_valid br_pred_we[1]!]
  let fetch_pt_0_wire := Wire.mk "fetch_pt_0"
  let fetch_pt_1_wire := Wire.mk "fetch_pt_1"
  let br_pred_mux_gate := Gate.mkMUX fetch_pt_0_wire fetch_pt_1_wire br_route_sel fetch_predicted_taken
  let br_pred_rf_gates := (List.range 2).map (fun e =>
    let next := Wire.mk s!"br_pred_next_{e}"
    [Gate.mkMUX br_pred_e[e]! fetch_predicted_taken br_pred_we[e]! next,
     Gate.mkDFF next clock reset br_pred_e[e]!]) |>.flatten
  let branch_predicted_taken := Wire.mk "branch_predicted_taken"
  let br_pred_sel_gates :=
    [Gate.mkMUX br_pred_e[0]! br_pred_e[1]! rs_br_grant[1]! branch_predicted_taken]

  -- === EXECUTION UNITS ===
  -- Integer ALU (W2)
  let aluOpWidth := if config.xlen == 64 then 5 else 4
  let alu_op0 := CPU.makeIndexedWires "alu_op0" aluOpWidth
  let alu_op1 := CPU.makeIndexedWires "alu_op1" aluOpWidth
  let alu_lut_gates0 : List Gate := []
  let alu_lut_gates1 : List Gate := []
  let alu_lut_inst0 : CircuitInstance := {
    moduleName := s!"ALUOpDecoder_{config.isaString}"
    instName := "u_alu_lut0"
    portMap := bundledPorts "optype" dispatch_opcode_0 ++
               bundledPorts "out_op" alu_op0
  }
  let alu_lut_inst1 : CircuitInstance := {
    moduleName := s!"ALUOpDecoder_{config.isaString}"
    instName := "u_alu_lut1"
    portMap := bundledPorts "optype" dispatch_opcode_1 ++
               bundledPorts "out_op" alu_op1
  }

  let result0_raw := CPU.makeIndexedWires "exec_result0_raw" (if config.xlen == 64 then 64 else 32); let tag0 := CPU.makeIndexedWires "exec_tag0" 6
  let result1_raw := CPU.makeIndexedWires "exec_result1_raw" (if config.xlen == 64 then 64 else 32); let tag1 := CPU.makeIndexedWires "exec_tag1" 6

  let exec_inst : CircuitInstance := {
    moduleName := if config.xlen == 64 then "IntegerExecUnit_W2_64" else "IntegerExecUnit_W2"
    instName := "u_exec"
    portMap := bundledPorts "a0" dispatch_src1_data_0 ++ bundledPorts "b0" dispatch_src2_data_0 ++
               bundledPorts "opcode0" alu_op0 ++ bundledPorts "dest_tag0" (dispatch_dest_tag_0.take 6) ++
               bundledPorts "result0" result0_raw ++ bundledPorts "tag_out0" tag0 ++
               bundledPorts "a1" dispatch_src1_data_1 ++ bundledPorts "b1" dispatch_src2_data_1 ++
               bundledPorts "opcode1" alu_op1 ++ bundledPorts "dest_tag1" (dispatch_dest_tag_1.take 6) ++
               bundledPorts "result1" result1_raw ++ bundledPorts "tag_out1" tag1 ++
               [("zero", zero), ("one", one)]
  }

  -- AUIPC/LUI post-processing for INT lane 0
  let is_lui_0 := Wire.mk "is_lui_0"; let is_auipc_0 := Wire.mk "is_auipc_0"
  let lui_match_gates_0 := mkMatch "lui_m0" (oi .LUI) dispatch_opcode_0 is_lui_0
  let auipc_match_gates_0 := mkMatch "auipc_m0" (oi .AUIPC) dispatch_opcode_0 is_auipc_0
  let auipc_result_0 := CPU.makeIndexedWires "auipc_result_0" 32
  let auipc_adder_0_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32NoCin", instName := "u_auipc_adder_0",
    portMap := (int_captured_pc_0.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (int_captured_imm_0.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
               (auipc_result_0.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }
  let result0 := CPU.makeIndexedWires "exec_result0" (if config.xlen == 64 then 64 else 32)
  let int_auipc_muxed_0 := CPU.makeIndexedWires "int_auipc_muxed_0" (if config.xlen == 64 then 64 else 32)
  let lui_auipc_gates_0 := (List.range 32).flatMap (fun i =>
    [Gate.mkMUX result0_raw[i]! auipc_result_0[i]! is_auipc_0 int_auipc_muxed_0[i]!,
     Gate.mkMUX int_auipc_muxed_0[i]! int_captured_imm_0[i]! is_lui_0 result0[i]!]) ++
    (if config.xlen == 64 then
      (List.range 32).flatMap (fun i =>
        [Gate.mkMUX result0_raw[32+i]! auipc_result_0[31]! is_auipc_0 int_auipc_muxed_0[32+i]!,
         Gate.mkMUX int_auipc_muxed_0[32+i]! int_captured_imm_0[31]! is_lui_0 result0[32+i]!])
     else [])
  -- AUIPC/LUI post-processing for INT lane 1
  let is_lui_1 := Wire.mk "is_lui_1"; let is_auipc_1 := Wire.mk "is_auipc_1"
  let lui_match_gates_1 := mkMatch "lui_m1" (oi .LUI) dispatch_opcode_1 is_lui_1
  let auipc_match_gates_1 := mkMatch "auipc_m1" (oi .AUIPC) dispatch_opcode_1 is_auipc_1
  let auipc_result_1 := CPU.makeIndexedWires "auipc_result_1" 32
  let auipc_adder_1_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32NoCin", instName := "u_auipc_adder_1",
    portMap := (int_captured_pc_1.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (int_captured_imm_1.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
               (auipc_result_1.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }
  let result1 := CPU.makeIndexedWires "exec_result1" (if config.xlen == 64 then 64 else 32)
  let int_auipc_muxed_1 := CPU.makeIndexedWires "int_auipc_muxed_1" (if config.xlen == 64 then 64 else 32)
  let lui_auipc_gates_1 := (List.range 32).flatMap (fun i =>
    [Gate.mkMUX result1_raw[i]! auipc_result_1[i]! is_auipc_1 int_auipc_muxed_1[i]!,
     Gate.mkMUX int_auipc_muxed_1[i]! int_captured_imm_1[i]! is_lui_1 result1[i]!]) ++
    (if config.xlen == 64 then
      (List.range 32).flatMap (fun i =>
        [Gate.mkMUX result1_raw[32+i]! auipc_result_1[31]! is_auipc_1 int_auipc_muxed_1[32+i]!,
         Gate.mkMUX int_auipc_muxed_1[32+i]! int_captured_imm_1[31]! is_lui_1 result1[32+i]!])
     else [])

  -- Branch execution unit
  let branch_result := CPU.makeIndexedWires "branch_result" 32
  let branch_tag_out := CPU.makeIndexedWires "branch_tag_out" 6
  let branch_exec_inst : CircuitInstance := {
    moduleName := "BranchExecUnit"
    instName := "u_exec_branch"
    portMap :=
      bundledPorts "src1" (rs_br_dispatch_src1.take 32) ++
      bundledPorts "src2" (rs_br_dispatch_src2.take 32) ++
      bundledPorts "dest_tag" (rs_br_dispatch_tag.take 6) ++
      [("zero", zero)] ++
      bundledPorts "result" branch_result ++
      bundledPorts "tag_out" branch_tag_out
  }

  -- === BRANCH RESOLVE (W2) ===
  -- Compute misprediction and redirect target at branch dispatch time
  -- JAL/JALR detection
  let is_jal := Wire.mk "is_jal_br"; let is_jalr := Wire.mk "is_jalr_br"
  let is_jal_or_jalr := Wire.mk "is_jal_or_jalr_br"
  let jal_match_gates := mkMatch "jal_m" (oi .JAL) rs_br_dispatch_opcode is_jal
  let jalr_match_gates := mkMatch "jalr_m" (oi .JALR) rs_br_dispatch_opcode is_jalr
  let jal_jalr_gates := [Gate.mkOR is_jal is_jalr is_jal_or_jalr]
  -- PC+4 for link register (JAL/JALR result)
  let br_pc_plus_4 := CPU.makeIndexedWires "br_pc_plus_4" 32
  let br_pc_plus_4_adder : CircuitInstance := {
    moduleName := "PCIncrementer4", instName := "u_br_pc_plus_4",
    portMap := (br_captured_pc.enum.map (fun ⟨i, w⟩ => (s!"pc_{i}", w))) ++
               (br_pc_plus_4.enum.map (fun ⟨i, w⟩ => (s!"pc_next_{i}", w)))
  }
  -- Branch result final: MUX between ALU result and PC+4 for JAL/JALR
  let branch_result_final := CPU.makeIndexedWires "branch_result_final" (if config.xlen == 64 then 64 else 32)
  let branch_result_mux :=
    (List.range 32).map (fun i =>
      Gate.mkMUX branch_result[i]! br_pc_plus_4[i]! is_jal_or_jalr branch_result_final[i]!) ++
    (if config.xlen == 64 then
      (List.range 32).map (fun i =>
        Gate.mkMUX zero br_pc_plus_4[31]! is_jal_or_jalr branch_result_final[32+i]!)
     else [])
  -- Branch target: PC + IMM
  let br_final_target := CPU.makeIndexedWires "br_final_target" 32
  let br_target_adder : CircuitInstance := {
    moduleName := "KoggeStoneAdder32NoCin", instName := "u_br_target",
    portMap := (br_captured_pc.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (br_captured_imm.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
               (br_final_target.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }
  -- JALR target: src1 + IMM, bit 0 cleared
  let jalr_target_raw := CPU.makeIndexedWires "jalr_target_raw" 32
  let jalr_target := CPU.makeIndexedWires "jalr_target" 32
  let jalr_target_adder : CircuitInstance := {
    moduleName := "KoggeStoneAdder32NoCin", instName := "u_jalr_target",
    portMap := ((rs_br_dispatch_src1.take 32).enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (br_captured_imm.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
               (jalr_target_raw.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }
  let jalr_target_gates := (List.range 32).map (fun i =>
    if i == 0 then Gate.mkBUF zero jalr_target[i]!
    else Gate.mkBUF jalr_target_raw[i]! jalr_target[i]!)
  let final_branch_target := CPU.makeIndexedWires "final_branch_target" 32
  let target_sel_gates := (List.range 32).map (fun i =>
    Gate.mkMUX br_final_target[i]! jalr_target[i]! is_jalr final_branch_target[i]!)
  -- Branch condition evaluation
  let br_eq := Wire.mk "br_eq"; let br_lt := Wire.mk "br_lt"; let br_ltu := Wire.mk "br_ltu"
  let br_cmp_inst : CircuitInstance := {
    moduleName := if config.xlen == 64 then "Comparator64" else "Comparator32", instName := "u_br_cmp",
    portMap := (rs_br_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
               (rs_br_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
               [("one", one), ("eq", br_eq), ("lt", br_lt), ("ltu", br_ltu),
                ("gt", Wire.mk "br_gt"), ("gtu", Wire.mk "br_gtu")]
  }
  let is_beq := Wire.mk "is_beq"; let is_bne := Wire.mk "is_bne"
  let is_blt := Wire.mk "is_blt"; let is_bge := Wire.mk "is_bge"
  let is_bltu := Wire.mk "is_bltu"; let is_bgeu := Wire.mk "is_bgeu"
  let beq_match := mkMatch "beq_m" (oi .BEQ) rs_br_dispatch_opcode is_beq
  let bne_match := mkMatch "bne_m" (oi .BNE) rs_br_dispatch_opcode is_bne
  let blt_match := mkMatch "blt_m" (oi .BLT) rs_br_dispatch_opcode is_blt
  let bge_match := mkMatch "bge_m" (oi .BGE) rs_br_dispatch_opcode is_bge
  let bltu_match := mkMatch "bltu_m" (oi .BLTU) rs_br_dispatch_opcode is_bltu
  let bgeu_match := mkMatch "bgeu_m" (oi .BGEU) rs_br_dispatch_opcode is_bgeu
  let branch_taken := Wire.mk "branch_taken"
  let branch_cond_gates := [
    Gate.mkNOT br_eq (Wire.mk "br_not_eq"),
    Gate.mkNOT br_lt (Wire.mk "br_not_lt"),
    Gate.mkNOT br_ltu (Wire.mk "br_not_ltu"),
    Gate.mkAND is_beq br_eq (Wire.mk "beq_taken"),
    Gate.mkAND is_bne (Wire.mk "br_not_eq") (Wire.mk "bne_taken"),
    Gate.mkAND is_blt br_lt (Wire.mk "blt_taken"),
    Gate.mkAND is_bge (Wire.mk "br_not_lt") (Wire.mk "bge_taken"),
    Gate.mkAND is_bltu br_ltu (Wire.mk "bltu_taken"),
    Gate.mkAND is_bgeu (Wire.mk "br_not_ltu") (Wire.mk "bgeu_taken"),
    Gate.mkOR (Wire.mk "beq_taken") (Wire.mk "bne_taken") (Wire.mk "cond_tmp1"),
    Gate.mkOR (Wire.mk "cond_tmp1") (Wire.mk "blt_taken") (Wire.mk "cond_tmp2"),
    Gate.mkOR (Wire.mk "cond_tmp2") (Wire.mk "bge_taken") (Wire.mk "cond_tmp3"),
    Gate.mkOR (Wire.mk "cond_tmp3") (Wire.mk "bltu_taken") (Wire.mk "cond_tmp4"),
    Gate.mkOR (Wire.mk "cond_tmp4") (Wire.mk "bgeu_taken") (Wire.mk "cond_taken"),
    Gate.mkOR (Wire.mk "cond_taken") is_jal_or_jalr branch_taken
  ]
  -- Misprediction: predicted_taken XOR actual_taken, OR is_jalr (always mispredicts)
  let branch_mispredicted := Wire.mk "branch_mispredicted"
  let misprediction_gates := [
    Gate.mkXOR branch_predicted_taken branch_taken (Wire.mk "br_cond_mispred"),
    Gate.mkOR (Wire.mk "br_cond_mispred") is_jalr branch_mispredicted
  ]
  -- Redirect target for misprediction
  let mispredict_redirect_target := CPU.makeIndexedWires "mispredict_redirect_target" 32
  let mispredict_sel := Wire.mk "mispredict_sel"
  let mispredict_redirect_gates :=
    [Gate.mkNOT is_jal_or_jalr (Wire.mk "not_jal_or_jalr"),
     Gate.mkAND branch_predicted_taken (Wire.mk "not_jal_or_jalr") mispredict_sel] ++
    (List.range 32).map (fun i =>
      Gate.mkMUX final_branch_target[i]! br_pc_plus_4[i]! mispredict_sel mispredict_redirect_target[i]!)

  -- Memory execution unit
  let mem_address := CPU.makeIndexedWires "mem_address" (if config.xlen == 64 then 64 else 32)
  let mem_tag_out := CPU.makeIndexedWires "mem_tag_out" 6
  let mem_exec_inst : CircuitInstance := {
    moduleName := "MemoryExecUnit"
    instName := "u_exec_memory"
    portMap :=
      bundledPorts "base" (if config.xlen == 64 then rs_mem_dispatch_src1.take 64 else rs_mem_dispatch_src1.take 32) ++
      bundledPorts "offset" (captured_imm.take 32) ++
      bundledPorts "dest_tag" (rs_mem_dispatch_tag.take 6) ++
      bundledPorts "address" mem_address ++
      bundledPorts "tag_out" mem_tag_out
  }

  -- MulDiv execution unit (conditional)
  let muldiv_result := CPU.makeIndexedWires "muldiv_result" (if config.xlen == 64 then 64 else 32)
  let muldiv_tag_out := CPU.makeIndexedWires "muldiv_tag_out" 6
  let muldiv_valid_out := Wire.mk "muldiv_valid_out"
  let muldiv_op := CPU.makeIndexedWires "muldiv_op" (if config.xlen == 64 then 4 else 3)
  let muldiv_lut_gates : List Gate := []
  let muldiv_lut_inst : List CircuitInstance :=
    if enableM then
      [{ moduleName := s!"MulDivOpDecoder_{config.isaString}"
         instName := "u_muldiv_lut"
         portMap := bundledPorts "optype" rs_muldiv_dispatch_opcode ++
                    bundledPorts "out_op" muldiv_op }]
    else []

  let muldiv_exec_inst : CircuitInstance := {
    moduleName := "MulDivExecUnit"
    instName := "u_exec_muldiv"
    portMap :=
      bundledPorts "a" (if config.xlen == 64 then rs_muldiv_dispatch_src1.take 64 else rs_muldiv_dispatch_src1) ++
      bundledPorts "b" (if config.xlen == 64 then rs_muldiv_dispatch_src2.take 64 else rs_muldiv_dispatch_src2) ++
      bundledPorts "op" muldiv_op ++
      bundledPorts "dest_tag" (rs_muldiv_dispatch_tag.take 6) ++
      [("valid_in", rs_muldiv_dispatch_valid),
       ("clock", clock), ("reset", pipeline_reset_rs_muldiv),
       ("zero", zero), ("one", one)] ++
      bundledPorts "result" muldiv_result ++
      bundledPorts "tag_out" muldiv_tag_out ++
      [("valid_out", muldiv_valid_out), ("busy", muldiv_busy)]
  }

  -- === LSU + STORE BUFFER ===
  let lsu_sb_full := Wire.mk "lsu_sb_full"
  let lsu_sb_empty := Wire.mk "lsu_sb_empty"
  let lsu_sb_fwd_hit := Wire.mk "lsu_sb_fwd_hit"
  let lsu_sb_fwd_data := CPU.makeIndexedWires "lsu_sb_fwd_data" (if config.xlen == 64 || config.enableD then 64 else 32)
  let lsu_sb_fwd_size := CPU.makeIndexedWires "lsu_sb_fwd_size" 2
  let lsu_sb_deq_valid := Wire.mk "lsu_sb_deq_valid"
  let lsu_sb_deq_bits := CPU.makeIndexedWires "lsu_sb_deq_bits" (if config.xlen == 64 then 130 else (if config.enableD then 98 else 66))
  let lsu_agu_address := CPU.makeIndexedWires "lsu_agu_address" (if config.xlen == 64 then 64 else 32)
  let lsu_agu_tag := CPU.makeIndexedWires "lsu_agu_tag" 6
  let sb_enq_en := Wire.mk "sb_enq_en"
  let commit_store_en := Wire.mk "commit_store_en"  -- TODO: drive from commit control

  let store_data_masked := CPU.makeIndexedWires "store_data_masked" (if config.xlen == 64 || config.enableD then 64 else 32)

  let lsu_inst : CircuitInstance := {
    moduleName := "LSU"
    instName := "u_lsu"
    portMap := [("clock", clock), ("reset", reset),
                ("zero", zero), ("one", one),
                ("commit_store_en", commit_store_en),
                ("deq_ready", dmem_req_ready),
                ("flush_en", pipeline_flush_comb),
                ("sb_enq_en", sb_enq_en),
                ("sb_full", lsu_sb_full), ("sb_empty", lsu_sb_empty),
                ("sb_fwd_hit", lsu_sb_fwd_hit),
                ("sb_fwd_committed_hit", Wire.mk "lsu_sb_fwd_committed_hit"),
                ("sb_fwd_word_hit", Wire.mk "lsu_sb_fwd_word_hit"),
                ("sb_fwd_word_only_hit", Wire.mk "lsu_sb_fwd_word_only_hit"),
                ("sb_deq_valid", lsu_sb_deq_valid)] ++
               bundledPorts "dispatch_base" (if config.xlen == 64 then rs_mem_dispatch_src1.take 64 else rs_mem_dispatch_src1.take 32) ++
               bundledPorts "dispatch_offset" (captured_imm.take 32) ++
               bundledPorts "dispatch_dest_tag" (rs_mem_dispatch_tag.take 6) ++
               bundledPorts "store_data" store_data_masked ++
               bundledPorts "fwd_address" mem_addr_r ++
               bundledPorts "sb_enq_size" (CPU.makeIndexedWires "lsu_sb_enq_size" 2) ++
               bundledPorts "agu_address" lsu_agu_address ++
               bundledPorts "agu_tag_out" lsu_agu_tag ++
               bundledPorts "sb_fwd_data" lsu_sb_fwd_data ++
               bundledPorts "sb_fwd_size" lsu_sb_fwd_size ++
               bundledPorts "sb_deq_bits" lsu_sb_deq_bits ++
               bundledPorts "sb_enq_idx" lsu_sb_enq_idx ++
               bundledPorts "sb_enq_idx_in" sb_dispatch_idx ++
               bundledPorts "sb_flush_tail" lsu_sb_flush_tail
  }

  -- === LOAD TYPE DETECTION ===
  let is_lw := Wire.mk "is_lw"
  let is_lh := Wire.mk "is_lh"
  let is_lhu := Wire.mk "is_lhu"
  let is_lb := Wire.mk "is_lb"
  let is_lbu := Wire.mk "is_lbu"
  let is_ld := Wire.mk "is_ld"
  let is_lwu := Wire.mk "is_lwu"
  let is_load := Wire.mk "is_load"
  let lw_match_gates := mkMatch "lw_match" (oi .LW) rs_mem_dispatch_opcode is_lw
  let lh_match_gates := mkMatch "lh_match" (oi .LH) rs_mem_dispatch_opcode is_lh
  let lhu_match_gates := mkMatch "lhu_match" (oi .LHU) rs_mem_dispatch_opcode is_lhu
  let lb_match_gates := mkMatch "lb_match" (oi .LB) rs_mem_dispatch_opcode is_lb
  let lbu_match_gates := mkMatch "lbu_match" (oi .LBU) rs_mem_dispatch_opcode is_lbu
  let ld_match_gates := if config.xlen == 64 then mkMatch "ld_match" (oi .LD) rs_mem_dispatch_opcode is_ld else [Gate.mkBUF zero is_ld]
  let lwu_match_gates := if config.xlen == 64 then mkMatch "lwu_match" (oi .LWU) rs_mem_dispatch_opcode is_lwu else [Gate.mkBUF zero is_lwu]
  -- FLW/FSW detection (conditional on F extension)
  let is_flw := Wire.mk "is_flw"
  let is_fsw := Wire.mk "is_fsw"
  let flw_match_gates :=
    if enableF then mkMatch "flw_match" (oi .FLW) rs_mem_dispatch_opcode is_flw
    else [Gate.mkBUF zero is_flw]
  let fsw_match_gates :=
    if enableF then mkMatch "fsw_match" (oi .FSW) rs_mem_dispatch_opcode is_fsw
    else [Gate.mkBUF zero is_fsw]
  -- FLD/FSD detection (conditional on D extension)
  let is_fld := Wire.mk "is_fld"
  let is_fsd := Wire.mk "is_fsd"
  let fld_match_gates :=
    if config.enableD then mkMatch "fld_match" (oi .FLD) rs_mem_dispatch_opcode is_fld
    else [Gate.mkBUF zero is_fld]
  let fsd_match_gates :=
    if config.enableD then mkMatch "fsd_match" (oi .FSD) rs_mem_dispatch_opcode is_fsd
    else [Gate.mkBUF zero is_fsd]
  let is_fp_load := Wire.mk "is_fp_load"
  let is_fp_load_gate :=
    if config.enableD then [Gate.mkOR is_flw is_fld is_fp_load]
    else [Gate.mkBUF is_flw is_fp_load]

  -- === A EXTENSION: ATOMIC OPCODE DETECTION ===
  let is_lr := Wire.mk "is_lr"
  let is_sc := Wire.mk "is_sc"
  let is_amo := Wire.mk "is_amo"
  let is_atomic_d := Wire.mk "is_atomic_d"   -- 64-bit atomic (LR.D/SC.D/AMO*.D)
  let is_atomic_read := Wire.mk "is_atomic_read"   -- LR or AMO (read via DMEM)
  let amo_funct := CPU.makeIndexedWires "amo_funct" 4

  -- OpType encodings of the A-extension operations (word and doubleword)
  let amoW : List OpType :=
    [.AMOADD_W, .AMOSWAP_W, .AMOXOR_W, .AMOAND_W, .AMOOR_W,
     .AMOMIN_W, .AMOMAX_W, .AMOMINU_W, .AMOMAXU_W]
  let amoD : List OpType :=
    [.AMOADD_D, .AMOSWAP_D, .AMOXOR_D, .AMOAND_D, .AMOOR_D,
     .AMOMIN_D, .AMOMAX_D, .AMOMINU_D, .AMOMAXU_D]

  let lr_match_gates := if enableA then
      mkMatchAny "lr_match" [(oi .LR_W), (oi .LR_D)] rs_mem_dispatch_opcode is_lr
    else [Gate.mkBUF zero is_lr]
  let sc_match_gates := if enableA then
      mkMatchAny "sc_match" [(oi .SC_W), (oi .SC_D)] rs_mem_dispatch_opcode is_sc
    else [Gate.mkBUF zero is_sc]
  let amo_match_gates := if enableA then
      mkMatchAny "amo_match" ((amoW ++ amoD).map oi) rs_mem_dispatch_opcode is_amo
    else [Gate.mkBUF zero is_amo]
  let atomic_d_match_gates := if enableA then
      mkMatchAny "atomd_match" (([OpType.LR_D, OpType.SC_D] ++ amoD).map oi) rs_mem_dispatch_opcode is_atomic_d
    else [Gate.mkBUF zero is_atomic_d]
  let amo_lut_inst : List CircuitInstance :=
    if enableA then
      [{ moduleName := s!"AMOOpDecoder_{config.isaString}"
         instName := "u_amo_lut"
         portMap := bundledPorts "optype" rs_mem_dispatch_opcode ++
                    bundledPorts "out_op" amo_funct }]
    else []
  let amo_funct_gates := if enableA then []
    else (List.range 4).map (fun i => Gate.mkBUF zero amo_funct[i]!)
  let atomic_read_gates := [Gate.mkOR is_lr is_amo is_atomic_read]

  let is_load_gates := [
    Gate.mkOR is_lw is_lh (Wire.mk "is_load_tmp1"),
    Gate.mkOR (Wire.mk "is_load_tmp1") is_lhu (Wire.mk "is_load_tmp2"),
    Gate.mkOR (Wire.mk "is_load_tmp2") is_lb (Wire.mk "is_load_tmp3"),
    Gate.mkOR (Wire.mk "is_load_tmp3") is_lbu (Wire.mk "is_load_int"),
    Gate.mkOR (Wire.mk "is_load_int") is_ld (Wire.mk "is_load_int_d"),
    Gate.mkOR (Wire.mk "is_load_int_d") is_lwu (Wire.mk "is_load_int_all"),
    Gate.mkOR (Wire.mk "is_load_int_all") is_flw (Wire.mk "is_load_pre0"),
    Gate.mkOR (Wire.mk "is_load_pre0") is_fld (Wire.mk "is_load_pre"),
    Gate.mkOR (Wire.mk "is_load_pre") is_atomic_read is_load
  ]

  -- Store type detection
  let is_sw := Wire.mk "is_sw"
  let is_sh := Wire.mk "is_sh"
  let is_sb_w := Wire.mk "is_sb"
  let is_sd := Wire.mk "is_sd"
  let sw_match_gates := mkMatch "sw_match" (oi .SW) rs_mem_dispatch_opcode is_sw
  let sh_match_gates := mkMatch "sh_match" (oi .SH) rs_mem_dispatch_opcode is_sh
  let sb_match_gates := mkMatch "sb_match" (oi .SB) rs_mem_dispatch_opcode is_sb_w
  let sd_match_gates := if config.xlen == 64 then mkMatch "sd_match" (oi .SD) rs_mem_dispatch_opcode is_sd else [Gate.mkBUF zero is_sd]

  -- mem_size[1:0] and sign_extend
  let mem_size := CPU.makeIndexedWires "mem_size" 2
  let sign_extend := Wire.mk "sign_extend"
  let mem_size_gates := [
    Gate.mkOR is_lh is_lhu (Wire.mk "ms0_t1"),
    Gate.mkOR (Wire.mk "ms0_t1") is_sh (Wire.mk "ms0_t2"),
    Gate.mkOR (Wire.mk "ms0_t2") is_fld (Wire.mk "ms0_t3"),
    Gate.mkOR (Wire.mk "ms0_t3") is_fsd (Wire.mk "ms0_t4"),
    Gate.mkOR (Wire.mk "ms0_t4") is_ld (Wire.mk "ms0_t5"),
    Gate.mkOR (Wire.mk "ms0_t5") is_sd (Wire.mk "ms0_t5b"),
    -- LR.D/SC.D/AMO*.D are 64-bit accesses: size 2'b11 like LD/SD
    Gate.mkOR (Wire.mk "ms0_t5b") is_atomic_d mem_size[0]!,
    Gate.mkOR is_lw is_sw (Wire.mk "ms1_t1"),
    Gate.mkOR (Wire.mk "ms1_t1") is_flw (Wire.mk "ms1_t2"),
    Gate.mkOR (Wire.mk "ms1_t2") is_fsw (Wire.mk "ms1_t3"),
    Gate.mkOR (Wire.mk "ms1_t3") is_atomic_read (Wire.mk "ms1_t4"),
    Gate.mkOR (Wire.mk "ms1_t4") is_fld (Wire.mk "ms1_t5"),
    Gate.mkOR (Wire.mk "ms1_t5") is_fsd (Wire.mk "ms1_t6"),
    Gate.mkOR (Wire.mk "ms1_t6") is_ld (Wire.mk "ms1_t7"),
    Gate.mkOR (Wire.mk "ms1_t7") is_sd (Wire.mk "ms1_t8"),
    Gate.mkOR (Wire.mk "ms1_t8") is_lwu (Wire.mk "ms1_t9"),
    -- SC.W/SC.D are word/double writes: like SW/SD plus the .D bit from is_atomic_d
    Gate.mkOR (Wire.mk "ms1_t9") is_sc mem_size[1]!,
    Gate.mkOR is_lb is_lh (Wire.mk "se_t1"),
    -- LR/AMO word results sign-extend like LW; .D atomics are 64-bit and must NOT sign-extend
    Gate.mkNOT is_atomic_d (Wire.mk "not_is_atomic_d_se"),
    Gate.mkAND is_atomic_read (Wire.mk "not_is_atomic_d_se") (Wire.mk "is_atomic_w_se"),
    Gate.mkOR (Wire.mk "se_t1") (Wire.mk "is_atomic_w_se") (Wire.mk "se_t2"),
    Gate.mkOR (Wire.mk "se_t2") (if config.xlen == 64 then is_lw else zero) sign_extend
  ]

  -- Memory pipeline register (use 6-bit tag, domain bit not needed downstream)
  let (mem_pipe_gates, mem_pipe_insts) := mkMemPipeline clock reset
    rs_mem_dispatch_valid (Wire.mk "mem_dispatch_en_any")
    mem_address (rs_mem_dispatch_tag.take 6)
    is_load is_fp_load mem_size sign_extend
    mem_addr_r mem_tag_r is_load_r mem_size_r sign_extend_r is_flw_r mem_valid_r

  -- sb_enq_size
  let lsu_sb_enq_size := CPU.makeIndexedWires "lsu_sb_enq_size" 2
  let sb_enq_size_gates := (List.range 2).map (fun i => Gate.mkBUF mem_size[i]! lsu_sb_enq_size[i]!)

  -- Store data masking
  let store_mask_gates :=
    [Gate.mkBUF mem_size[1]! (Wire.mk "keep_hi16"),
     Gate.mkOR mem_size[1]! mem_size[0]! (Wire.mk "keep_lo16_hi8")] ++
    (if config.xlen == 64 || config.enableD then
      [Gate.mkAND mem_size[0]! mem_size[1]! (Wire.mk "keep_hi32")]
     else []) ++
    (List.range 8).map (fun i =>
      Gate.mkBUF rs_mem_dispatch_src2[i]! store_data_masked[i]!) ++
    (List.range 8).map (fun i =>
      Gate.mkAND rs_mem_dispatch_src2[8+i]! (Wire.mk "keep_lo16_hi8") store_data_masked[8+i]!) ++
    (List.range 16).map (fun i =>
      Gate.mkAND rs_mem_dispatch_src2[16+i]! (Wire.mk "keep_hi16") store_data_masked[16+i]!) ++
    (if config.xlen == 64 || config.enableD then
      (List.range 32).map (fun i =>
        Gate.mkAND rs_mem_dispatch_src2[32+i]! (Wire.mk "keep_hi32") store_data_masked[32+i]!)
     else [])

  -- SB enqueue gate
  -- Stores use mem_store_dispatch_en (no sb_deq_valid gate) since SB enqueue
  -- doesn't need the DMEM port. Loads use mem_dispatch_en (with sb_deq_valid gate).
  let not_is_load := Wire.mk "not_is_load"
  let not_is_sc := Wire.mk "not_is_sc"
  let sb_enq_gate_gates := [
    Gate.mkNOT is_load not_is_load,
    Gate.mkNOT is_sc not_is_sc,
    Gate.mkAND rs_mem_dispatch_valid not_is_load (Wire.mk "sb_enq_ungated0"),
    Gate.mkAND (Wire.mk "sb_enq_ungated0") not_is_sc (Wire.mk "sb_enq_ungated"),
    Gate.mkAND (Wire.mk "sb_enq_ungated") (Wire.mk "mem_store_dispatch_en") (Wire.mk "sb_enq_dispatched"),
    Gate.mkNOT pipeline_flush_comb (Wire.mk "not_flush_comb"),
    Gate.mkAND (Wire.mk "sb_enq_dispatched") (Wire.mk "not_flush_comb") sb_enq_en
  ]

  -- mem_store_dispatch_en: like mem_dispatch_en but WITHOUT sb_deq_valid gate
  -- (stores enqueue into SB, they don't use the DMEM port)
  -- Must still gate on pipe_valid_hold to avoid overwriting a pending load in the MEM pipeline
  let mem_store_dispatch_en_gates := [
    Gate.mkNOT (Wire.mk "dmem_load_pending") (Wire.mk "not_dmem_load_pend_for_st"),
    Gate.mkNOT (Wire.mk "pipe_valid_hold") (Wire.mk "not_pipe_hold_for_st"),
    -- Block store dispatch when SB is full
    Gate.mkAND (Wire.mk "not_is_load") lsu_sb_full (Wire.mk "store_sb_full_block"),
    Gate.mkNOT (Wire.mk "store_sb_full_block") (Wire.mk "not_store_sb_full"),
    Gate.mkAND (Wire.mk "not_dmem_load_pend_for_st") (Wire.mk "not_store_sb_full") (Wire.mk "mem_st_de_tmp1"),
    Gate.mkAND (Wire.mk "mem_st_de_tmp1") (Wire.mk "not_pipe_hold_for_st") (Wire.mk "mem_st_de_tmp1b"),
    -- Gate by cross_size_stall and cross_size_pending
    Gate.mkNOT (Wire.mk "cross_size_stall") (Wire.mk "not_cross_size_stall"),
    Gate.mkAND (Wire.mk "mem_st_de_tmp1b") (Wire.mk "not_cross_size_stall") (Wire.mk "mem_st_de_tmp2"),
    Gate.mkNOT (Wire.mk "cross_size_pending") (Wire.mk "not_cross_size_pending"),
    Gate.mkAND (Wire.mk "mem_st_de_tmp2") (Wire.mk "not_cross_size_pending") (Wire.mk "mem_store_dispatch_en")
  ]

  -- mem_dispatch_en: loads must also wait for sb_deq_valid (they need DMEM port)
  -- mem_dispatch_en_any: MUX between load path (with sb_deq gate) and store path (without)
  let mem_dispatch_en_gates := [
    Gate.mkNOT lsu_sb_deq_valid (Wire.mk "not_sb_deq_for_dispatch"),
    Gate.mkAND (Wire.mk "mem_store_dispatch_en") (Wire.mk "not_sb_deq_for_dispatch") mem_dispatch_en,
    -- Combined: stores use mem_store_dispatch_en, loads use mem_dispatch_en
    Gate.mkAND is_load mem_dispatch_en (Wire.mk "load_dispatch_ok"),
    Gate.mkAND not_is_load (Wire.mk "mem_store_dispatch_en") (Wire.mk "store_dispatch_ok"),
    Gate.mkOR (Wire.mk "load_dispatch_ok") (Wire.mk "store_dispatch_ok") (Wire.mk "mem_dispatch_en_raw"),
    Gate.mkAND (Wire.mk "mem_dispatch_en_raw") (Wire.mk "atom_disp_ok") (Wire.mk "mem_dispatch_en_any")
  ]

  -- Cross-size pending latch: prevents new mem dispatches until cross-size load
  -- goes through DMEM path
  let cross_size_pending_next := Wire.mk "cross_size_pending_next"
  let cross_size_pending_gates := [
    Gate.mkNOT (Wire.mk "load_no_fwd") (Wire.mk "not_load_no_fwd_for_csp"),
    Gate.mkAND (Wire.mk "cross_size_pending") (Wire.mk "not_load_no_fwd_for_csp") (Wire.mk "csp_hold"),
    Gate.mkOR (Wire.mk "cross_size_stall") (Wire.mk "csp_hold") cross_size_pending_next
  ]
  let cross_size_pending_inst : CircuitInstance :=
    { moduleName := "DFlipFlop", instName := "u_cross_size_pending",
      portMap := [("d", cross_size_pending_next), ("q", Wire.mk "cross_size_pending"),
                  ("clock", clock), ("reset", pipeline_reset_misc)] }

  -- commit_store_en is now driven by shadow registers above

  -- === DMEM RESPONSE PATH ===
  let load_no_fwd := Wire.mk "load_no_fwd"
  let dmem_load_tag_reg := CPU.makeIndexedWires "dmem_load_tag_reg" 6
  let dmem_load_pending := Wire.mk "dmem_load_pending"
  let dmem_load_pending_next := Wire.mk "dmem_load_pending_next"
  let not_dmem_load_pending := Wire.mk "not_dmem_load_pending"

  -- load_no_fwd: load that doesn't get SB forwarding → goes to DMEM
  -- Must NOT fire when:
  --   1. cross_size_stall: SB has the address but wrong size, wait for drain
  --   2. sb_enq_en: a store is being enqueued this cycle, SB fwd state is stale;
  --      the load holds in mem_valid_r and retries next cycle with updated SB
  -- Note: not_load_fwd_valid is already generated by mkMemPipeline
  let load_no_fwd_gates := [
    Gate.mkAND mem_valid_r is_load_r (Wire.mk "load_no_fwd_tmp"),
    Gate.mkAND (Wire.mk "load_no_fwd_tmp") (Wire.mk "not_load_fwd_valid") (Wire.mk "load_no_fwd_pre"),
    Gate.mkNOT lsu_sb_deq_valid (Wire.mk "not_sb_deq_valid"),
    Gate.mkAND (Wire.mk "load_no_fwd_pre") (Wire.mk "not_sb_deq_valid") (Wire.mk "load_no_fwd_no_deq"),
    Gate.mkNOT dmem_load_pending not_dmem_load_pending,
    Gate.mkAND (Wire.mk "load_no_fwd_no_deq") not_dmem_load_pending (Wire.mk "load_no_fwd_pre2"),
    -- Block when cross_size_stall: SB still has the entry, must wait for drain
    Gate.mkNOT (Wire.mk "cross_size_stall") (Wire.mk "not_cross_size_stall_lnf"),
    Gate.mkAND (Wire.mk "load_no_fwd_pre2") (Wire.mk "not_cross_size_stall_lnf") (Wire.mk "load_no_fwd_pre3"),
    -- Block while a pending atomic write drives dmem_req_we: a read issued in that
    -- cycle would be turned into a write and its response would never arrive
    Gate.mkNOT (Wire.mk "atom_aw_pending") (Wire.mk "not_aw_pending_lnf"),
    Gate.mkAND (Wire.mk "load_no_fwd_pre3") (Wire.mk "not_aw_pending_lnf") load_no_fwd
  ]

  let dmem_pending_gates := [
    Gate.mkNOT dmem_resp_valid (Wire.mk "not_dmem_resp_valid"),
    Gate.mkAND dmem_load_pending (Wire.mk "not_dmem_resp_valid") (Wire.mk "dmem_pending_hold"),
    Gate.mkOR load_no_fwd (Wire.mk "dmem_pending_hold") dmem_load_pending_next
  ]
  let dmem_pending_inst : CircuitInstance :=
    { moduleName := "DFlipFlop", instName := "u_dmem_load_pending",
      portMap := [("d", dmem_load_pending_next), ("q", dmem_load_pending),
                  ("clock", clock), ("reset", pipeline_reset_misc)] }

  let dmem_tag_capture_gates := (List.range 6).map (fun i =>
    Gate.mkMUX dmem_load_tag_reg[i]! mem_tag_r[i]! load_no_fwd (Wire.mk s!"dmem_load_tag_next_{i}"))
  let dmem_tag_capture_insts := (List.range 6).map (fun i =>
    ({ moduleName := "DFlipFlop", instName := s!"u_dmem_tag_{i}",
       portMap := [("d", Wire.mk s!"dmem_load_tag_next_{i}"), ("q", dmem_load_tag_reg[i]!),
                   ("clock", clock), ("reset", reset)] } : CircuitInstance))

  -- dmem_is_fp: track whether pending DMEM load is FP
  let dmem_is_fp_reg := Wire.mk "dmem_is_fp_reg"
  let dmem_is_fp_next := Wire.mk "dmem_is_fp_next"
  let dmem_is_fp_gates :=
    if enableF then
      [Gate.mkMUX dmem_is_fp_reg is_flw_r load_no_fwd dmem_is_fp_next]
    else []
  let dmem_is_fp_insts :=
    if enableF then
      [({ moduleName := "DFlipFlop", instName := "u_dmem_is_fp",
          portMap := [("d", dmem_is_fp_next), ("q", dmem_is_fp_reg),
                      ("clock", clock), ("reset", pipeline_reset_misc)] } : CircuitInstance)]
    else []

  -- SB forwarding formatting (sign/zero extend for byte/half loads)
  let lsu_sb_fwd_formatted := CPU.makeIndexedWires "lsu_sb_fwd_fmt" 32
  let sb_fwd_sign_bit := Wire.mk "sb_fwd_sign_bit"
  let sb_fwd_sign_bit_raw := Wire.mk "sb_fwd_sign_bit_raw"
  let sb_fwd_sign_gates :=
    if config.xlen == 64 then
      [Gate.mkMUX lsu_sb_fwd_data[7]! lsu_sb_fwd_data[15]! mem_size_r[0]! (Wire.mk "sb_fwd_sb_raw01"),
       Gate.mkMUX (Wire.mk "sb_fwd_sb_raw01") lsu_sb_fwd_data[31]! mem_size_r[1]! sb_fwd_sign_bit_raw,
       Gate.mkAND sb_fwd_sign_bit_raw sign_extend_r sb_fwd_sign_bit]
    else
      [Gate.mkMUX lsu_sb_fwd_data[7]! lsu_sb_fwd_data[15]! mem_size_r[0]! sb_fwd_sign_bit_raw,
       Gate.mkAND sb_fwd_sign_bit_raw sign_extend_r sb_fwd_sign_bit]
  let sb_fwd_ext_lo := Wire.mk "sb_fwd_ext_lo"
  let sb_fwd_ext_hi := Wire.mk "sb_fwd_ext_hi"
  let sb_fwd_format_gates :=
    [Gate.mkOR mem_size_r[0]! mem_size_r[1]! sb_fwd_ext_lo,
     Gate.mkBUF mem_size_r[1]! sb_fwd_ext_hi] ++
    (List.range 8).map (fun i =>
      Gate.mkBUF lsu_sb_fwd_data[i]! lsu_sb_fwd_formatted[i]!) ++
    (List.range 8).map (fun i =>
      Gate.mkMUX sb_fwd_sign_bit lsu_sb_fwd_data[8+i]! sb_fwd_ext_lo lsu_sb_fwd_formatted[8+i]!) ++
    (List.range 16).map (fun i =>
      Gate.mkMUX sb_fwd_sign_bit lsu_sb_fwd_data[16+i]! sb_fwd_ext_hi lsu_sb_fwd_formatted[16+i]!)
  let lsu_sb_fwd_format_all := sb_fwd_sign_gates ++ sb_fwd_format_gates

  -- LSU valid/tag/data: loads with SB fwd OR store completions
  let load_fwd_valid := Wire.mk "load_fwd_valid"
  let store_complete_valid := Wire.mk "store_complete_valid"
  let lsu_valid := Wire.mk "lsu_valid"
  let lsu_tag := CPU.makeIndexedWires "lsu_tag" 6
  let lsu_data := CPU.makeIndexedWires "lsu_data" (if config.xlen == 64 || config.enableD then 64 else 32)
  let not_is_load_r := Wire.mk "not_is_load_r"
  -- Cross-size forwarding check: only forward when store size covers load size
  let cross_size_stall := Wire.mk "cross_size_stall"
  let fwd_size_ok := Wire.mk "fwd_size_ok"
  let fwd_size_check_gates := [
    Gate.mkNOT mem_size_r[0]! (Wire.mk "not_load_size0"),
    Gate.mkOR lsu_sb_fwd_size[0]! (Wire.mk "not_load_size0") (Wire.mk "fwd_sz_k"),
    Gate.mkOR lsu_sb_fwd_size[1]! (Wire.mk "fwd_sz_k") (Wire.mk "fwd_sz_a"),
    Gate.mkAND lsu_sb_fwd_size[1]! (Wire.mk "fwd_sz_k") (Wire.mk "fwd_sz_b"),
    Gate.mkMUX (Wire.mk "fwd_sz_a") (Wire.mk "fwd_sz_b") mem_size_r[1]! fwd_size_ok
  ]
  let load_fwd_gates := [
    Gate.mkAND mem_valid_r is_load_r (Wire.mk "load_valid_tmp"),
    Gate.mkAND (Wire.mk "load_valid_tmp") lsu_sb_fwd_hit (Wire.mk "load_fwd_tmp2"),
    Gate.mkAND (Wire.mk "load_fwd_tmp2") fwd_size_ok (Wire.mk "load_fwd_pre_overlap"),
    -- Block SB fwd when there's a partial word overlap
    Gate.mkNOT (Wire.mk "lsu_sb_fwd_word_only_hit") (Wire.mk "not_word_only_hit"),
    Gate.mkAND (Wire.mk "load_fwd_pre_overlap") (Wire.mk "not_word_only_hit") load_fwd_valid,
    -- Cross-size detection: SB hit but size insufficient → stall
    Gate.mkNOT fwd_size_ok (Wire.mk "not_fwd_size_ok"),
    Gate.mkAND (Wire.mk "load_fwd_tmp2") (Wire.mk "not_fwd_size_ok") (Wire.mk "cross_size_any"),
    Gate.mkAND (Wire.mk "lsu_sb_fwd_word_only_hit") rs_mem_dispatch_valid (Wire.mk "wovlp_tmp1"),
    Gate.mkAND (Wire.mk "wovlp_tmp1") is_load (Wire.mk "word_overlap_stall"),
    Gate.mkOR (Wire.mk "cross_size_any") (Wire.mk "word_overlap_stall") cross_size_stall,
    -- Store completion: mem_valid_r AND NOT is_load_r
    Gate.mkNOT is_load_r not_is_load_r,
    Gate.mkAND mem_valid_r not_is_load_r store_complete_valid,
    -- LSU valid = load fwd OR store complete
    Gate.mkOR load_fwd_valid store_complete_valid lsu_valid
  ]
  -- SC broadcasts its result (0=success, 1=failure) instead of store data 0
  let sc_lsu_data := CPU.makeIndexedWires "sc_lsu_data" 32
  let sc_lsu_data_gates :=
    [Gate.mkAND (Wire.mk "atom_sc_sel") (Wire.mk "atom_sc_result") sc_lsu_data[0]!] ++
    (List.range 31).map (fun i => Gate.mkBUF zero sc_lsu_data[i+1]!)
  let lsu_is_double := Wire.mk "lsu_is_double"
  let lsu_is_double_gates :=
    if config.xlen == 64 || config.enableD then
      [Gate.mkAND mem_size_r[0]! mem_size_r[1]! lsu_is_double]
    else []
  let lsu_tag_data_gates :=
    (List.range 6).map (fun i => Gate.mkBUF mem_tag_r[i]! lsu_tag[i]!) ++
    -- Loads broadcast SB-forwarded data; SC broadcasts its result; stores broadcast 0
    (List.range 32).map (fun i =>
      Gate.mkMUX sc_lsu_data[i]! lsu_sb_fwd_formatted[i]! is_load_r lsu_data[i]!) ++
    (if config.xlen == 64 || config.enableD then
      (List.range 32).flatMap (fun i =>
        let fwd_hi_mux := Wire.mk s!"lsu_fwd_hi_m_{i}"
        let fwd_hi_src := if enableF then (Wire.mk s!"lsu_fwd_hi_src_{i}") else (if config.xlen == 64 then sb_fwd_sign_bit else zero)
        (if enableF then [Gate.mkMUX (if config.xlen == 64 then sb_fwd_sign_bit else zero) one is_flw_r fwd_hi_src] else []) ++
        [Gate.mkMUX fwd_hi_src lsu_sb_fwd_data[32+i]! lsu_is_double fwd_hi_mux,
         Gate.mkMUX zero fwd_hi_mux is_load_r lsu_data[32+i]!])
     else [])

  -- === A EXTENSION: ATOMIC UNIT ===
  let atomic_unit := mkAtomicUnit clock reset zero one
    rs_mem_dispatch_valid (Wire.mk "mem_dispatch_en_any")
    is_lr is_sc is_amo is_atomic_d amo_funct rs_mem_dispatch_src2
    pipeline_flush_comb mem_valid_r is_load_r mem_addr_r
    dmem_resp_valid (Wire.mk "dmem_load_pending") dmem_resp_data
    dmem_req_ready lsu_sb_empty lsu_sb_deq_valid lsu_sb_deq_bits
    (Wire.mk "rs_mem_pending_store")
  let atomic_gates := atomic_unit.gates
  let atomic_insts := atomic_unit.instances

  -- === DMEM LOAD METADATA CAPTURE (for sub-word load formatting) ===
  let dmem_addr_lo_reg := CPU.makeIndexedWires "dmem_addr_lo_reg" 2
  let dmem_addr_lo_next := CPU.makeIndexedWires "dmem_addr_lo_next" 2
  let dmem_mem_size_reg := CPU.makeIndexedWires "dmem_mem_size_reg" 2
  let dmem_mem_size_next := CPU.makeIndexedWires "dmem_mem_size_next" 2
  let dmem_sign_ext_reg := Wire.mk "dmem_sign_ext_reg"
  let dmem_sign_ext_next := Wire.mk "dmem_sign_ext_next"

  let dmem_addr_lo_capture_gates := (List.range 2).map (fun i =>
      Gate.mkMUX dmem_addr_lo_reg[i]! mem_addr_r[i]! load_no_fwd dmem_addr_lo_next[i]!)
  let dmem_addr_lo_capture_insts := (List.range 2).map (fun i =>
    ({ moduleName := "DFlipFlop", instName := s!"u_dmem_addr_lo_{i}",
       portMap := [("d", dmem_addr_lo_next[i]!), ("q", dmem_addr_lo_reg[i]!),
                   ("clock", clock), ("reset", reset)] } : CircuitInstance))
  let dmem_mem_size_capture_gates := (List.range 2).map (fun i =>
      Gate.mkMUX dmem_mem_size_reg[i]! mem_size_r[i]! load_no_fwd dmem_mem_size_next[i]!)
  let dmem_mem_size_capture_insts := (List.range 2).map (fun i =>
    ({ moduleName := "DFlipFlop", instName := s!"u_dmem_mem_size_{i}",
       portMap := [("d", dmem_mem_size_next[i]!), ("q", dmem_mem_size_reg[i]!),
                   ("clock", clock), ("reset", reset)] } : CircuitInstance))
  let dmem_meta_capture_gates :=
    dmem_addr_lo_capture_gates ++ dmem_mem_size_capture_gates ++
    [Gate.mkMUX dmem_sign_ext_reg sign_extend_r load_no_fwd dmem_sign_ext_next]
  let dmem_sign_ext_inst : CircuitInstance :=
    { moduleName := "DFlipFlop", instName := "u_dmem_sign_ext",
      portMap := [("d", dmem_sign_ext_next), ("q", dmem_sign_ext_reg),
                  ("clock", clock), ("reset", reset)] }
  let dmem_meta_capture_insts :=
    dmem_addr_lo_capture_insts ++ dmem_mem_size_capture_insts ++ [dmem_sign_ext_inst]

  -- === DMEM RESPONSE LOAD FORMATTING ===
  let dmem_is_double := Wire.mk "dmem_is_double"
  let dmem_is_double_gates :=
    if config.xlen == 64 || config.enableD then
      [Gate.mkAND dmem_mem_size_reg[0]! dmem_mem_size_reg[1]! dmem_is_double]
    else []

  let dmem_resp_formatted := CPU.makeIndexedWires "dmem_resp_fmt" (if config.xlen == 64 || config.enableD then 64 else 32)
  let dmem_resp_shifted := CPU.makeIndexedWires "dmem_resp_shifted" 32
  let dmem_sh8 := CPU.makeIndexedWires "dmem_sh8" 32
  let dmem_sh8_gates :=
    (List.range 24).map (fun i =>
      Gate.mkMUX dmem_resp_data[i]! dmem_resp_data[i+8]! dmem_addr_lo_reg[0]! dmem_sh8[i]!) ++
    (List.range 8).map (fun i =>
      Gate.mkMUX dmem_resp_data[24+i]! zero dmem_addr_lo_reg[0]! dmem_sh8[24+i]!)
  let dmem_sh16_gates :=
    (List.range 16).map (fun i =>
      Gate.mkMUX dmem_sh8[i]! dmem_sh8[i+16]! dmem_addr_lo_reg[1]! dmem_resp_shifted[i]!) ++
    (List.range 16).map (fun i =>
      Gate.mkMUX dmem_sh8[16+i]! zero dmem_addr_lo_reg[1]! dmem_resp_shifted[16+i]!)

  let dmem_sign_bit := Wire.mk "dmem_sign_bit"
  let dmem_sign_bit_raw := Wire.mk "dmem_sign_bit_raw"
  let dmem_sign_gates :=
    if config.xlen == 64 then
      [Gate.mkMUX dmem_resp_shifted[7]! dmem_resp_shifted[15]! dmem_mem_size_reg[0]! (Wire.mk "dmem_sb_raw01"),
       Gate.mkMUX (Wire.mk "dmem_sb_raw01") dmem_resp_shifted[31]! dmem_mem_size_reg[1]! dmem_sign_bit_raw,
       Gate.mkAND dmem_sign_bit_raw dmem_sign_ext_reg dmem_sign_bit]
    else
      [Gate.mkMUX dmem_resp_shifted[7]! dmem_resp_shifted[15]! dmem_mem_size_reg[0]! dmem_sign_bit_raw,
       Gate.mkAND dmem_sign_bit_raw dmem_sign_ext_reg dmem_sign_bit]
  let dmem_ext_lo := Wire.mk "dmem_ext_lo"
  let dmem_ext_hi := Wire.mk "dmem_ext_hi"
  let dmem_format_gates :=
    [Gate.mkOR dmem_mem_size_reg[0]! dmem_mem_size_reg[1]! dmem_ext_lo,
     Gate.mkBUF dmem_mem_size_reg[1]! dmem_ext_hi] ++
    (List.range 8).map (fun i =>
      Gate.mkBUF dmem_resp_shifted[i]! dmem_resp_formatted[i]!) ++
    (List.range 8).map (fun i =>
      Gate.mkMUX dmem_sign_bit dmem_resp_shifted[8+i]! dmem_ext_lo dmem_resp_formatted[8+i]!) ++
    (List.range 16).map (fun i =>
      Gate.mkMUX dmem_sign_bit dmem_resp_shifted[16+i]! dmem_ext_hi dmem_resp_formatted[16+i]!) ++
    (if config.xlen == 64 || config.enableD then
      (List.range 32).flatMap (fun i =>
        let dmem_hi_src := if enableF then (Wire.mk s!"dmem_hi_src_{i}") else (if config.xlen == 64 then dmem_sign_bit else zero)
        (if enableF then [Gate.mkMUX (if config.xlen == 64 then dmem_sign_bit else zero) one dmem_is_fp_reg dmem_hi_src] else []) ++
        [Gate.mkMUX dmem_hi_src dmem_resp_data[32+i]! dmem_is_double dmem_resp_formatted[32+i]!])
     else [])
  let dmem_resp_format_all := dmem_sh8_gates ++ dmem_sh16_gates ++
    dmem_sign_gates ++ dmem_format_gates ++ dmem_is_double_gates

  -- DMEM valid gating
  let dmem_valid_gated := Wire.mk "dmem_valid_gated"
  let dmem_valid_gate_gates := [
    Gate.mkNOT pipeline_flush_comb (Wire.mk "not_flush_comb_for_dmem"),
    Gate.mkNOT pipeline_flush (Wire.mk "not_flush_reg_for_dmem"),
    Gate.mkAND (Wire.mk "not_flush_comb_for_dmem") (Wire.mk "not_flush_reg_for_dmem") (Wire.mk "not_flushing_for_dmem"),
    Gate.mkAND dmem_resp_valid dmem_load_pending (Wire.mk "dmem_valid_pending"),
    Gate.mkAND (Wire.mk "dmem_valid_pending") (Wire.mk "not_flushing_for_dmem") dmem_valid_gated
  ]

  -- === CDB FIFO INFRASTRUCTURE ===
  -- IB FIFO 0: INT ALU lane 0 result
  let ib0_fifo_width := if config.xlen == 64 || config.enableD then 70 else 72
  let ib0_fifo_enq_data := CPU.makeIndexedWires "ib0_fifo_enq_data" ib0_fifo_width
  let ib0_fifo_deq := CPU.makeIndexedWires "ib0_fifo_deq" ib0_fifo_width
  let ib0_fifo_enq_ready := Wire.mk "ib0_fifo_enq_ready"
  let ib0_fifo_deq_valid := Wire.mk "ib0_fifo_deq_valid"
  let ib0_fifo_drain := Wire.mk "ib0_fifo_drain"

  let ib0_fifo_enq_assemble :=
    if config.xlen == 64 || config.enableD then
      (List.range 6).map (fun i => Gate.mkBUF tag0[i]! ib0_fifo_enq_data[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF result0[i]! ib0_fifo_enq_data[6+i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF (if config.xlen == 64 then result0[32+i]! else zero) ib0_fifo_enq_data[38+i]!)
    else
      (List.range 6).map (fun i => Gate.mkBUF tag0[i]! ib0_fifo_enq_data[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF result0[i]! ib0_fifo_enq_data[6+i]!) ++
      [Gate.mkBUF zero ib0_fifo_enq_data[38]!] ++
      (List.range 32).map (fun i => Gate.mkBUF zero ib0_fifo_enq_data[39+i]!) ++
      [Gate.mkBUF zero ib0_fifo_enq_data[71]!]

  let ib0_fifo_inst : CircuitInstance := {
    moduleName := if config.xlen == 64 || config.enableD then "Queue1Flow_70" else "Queue1Flow_72",
    instName := "u_cdb_fifo_ib0",
    portMap := [("clock", clock), ("reset", pipeline_reset_busy),
                ("enq_valid", issue0_valid),
                ("deq_ready", ib0_fifo_drain),
                ("enq_ready", ib0_fifo_enq_ready),
                ("deq_valid", ib0_fifo_deq_valid)] ++
      (List.range ib0_fifo_width).map (fun i => (s!"enq_data_{i}", ib0_fifo_enq_data[i]!)) ++
      (List.range ib0_fifo_width).map (fun i => (s!"deq_data_{i}", ib0_fifo_deq[i]!))
  }

  -- IB FIFO 1: INT ALU lane 1 only
  let ib1_fifo_width := if config.xlen == 64 || config.enableD then 70 else 39
  let ib1_fifo_enq_data := CPU.makeIndexedWires "ib1_fifo_enq_data" ib1_fifo_width
  let ib1_fifo_deq := CPU.makeIndexedWires "ib1_fifo_deq" ib1_fifo_width
  let ib1_fifo_enq_ready := Wire.mk "ib1_fifo_enq_ready"
  let ib1_fifo_deq_valid := Wire.mk "ib1_fifo_deq_valid"
  let ib1_fifo_drain := Wire.mk "ib1_fifo_drain"

  let ib1_merge_gates : List Gate := []  -- no merge needed, INT lane 1 goes directly to IB1

  let ib1_fifo_enq_assemble :=
    if config.xlen == 64 || config.enableD then
      (List.range 6).map (fun i => Gate.mkBUF tag1[i]! ib1_fifo_enq_data[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF result1[i]! ib1_fifo_enq_data[6+i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF (if config.xlen == 64 then result1[32+i]! else zero) ib1_fifo_enq_data[38+i]!)
    else
      (List.range 6).map (fun i => Gate.mkBUF tag1[i]! ib1_fifo_enq_data[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF result1[i]! ib1_fifo_enq_data[6+i]!) ++
      [Gate.mkBUF zero ib1_fifo_enq_data[38]!]

  let ib1_fifo_inst : CircuitInstance := {
    moduleName := if config.xlen == 64 || config.enableD then "Queue1Flow_70" else "Queue1Flow_39",
    instName := "u_cdb_fifo_ib1",
    portMap := [("clock", clock), ("reset", pipeline_reset_busy),
                ("enq_valid", issue1_valid),
                ("deq_ready", ib1_fifo_drain),
                ("enq_ready", ib1_fifo_enq_ready),
                ("deq_valid", ib1_fifo_deq_valid)] ++
      (List.range ib1_fifo_width).map (fun i => (s!"enq_data_{i}", ib1_fifo_enq_data[i]!)) ++
      (List.range ib1_fifo_width).map (fun i => (s!"deq_data_{i}", ib1_fifo_deq[i]!))
  }

  -- IB FIFO BR: Branch results only
  let ib_br_fifo_width := if config.xlen == 64 || config.enableD then 103 else 72
  let ib_br_fifo_enq_data := CPU.makeIndexedWires "ib_br_fifo_enq_data" ib_br_fifo_width
  let ib_br_fifo_deq := CPU.makeIndexedWires "ib_br_fifo_deq" ib_br_fifo_width
  let ib_br_fifo_enq_ready := Wire.mk "ib_br_fifo_enq_ready"
  let ib_br_fifo_deq_valid := Wire.mk "ib_br_fifo_deq_valid"
  let ib_br_fifo_drain := Wire.mk "ib_br_fifo_drain"

  let ib_br_fifo_enq_assemble :=
    if config.xlen == 64 || config.enableD then
      (List.range 6).map (fun i => Gate.mkBUF branch_tag_out[i]! ib_br_fifo_enq_data[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF branch_result_final[i]! ib_br_fifo_enq_data[6+i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF (if config.xlen == 64 then branch_result_final[32+i]! else zero) ib_br_fifo_enq_data[38+i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF mispredict_redirect_target[i]! ib_br_fifo_enq_data[70+i]!) ++
      [Gate.mkBUF branch_mispredicted ib_br_fifo_enq_data[102]!]
    else
      (List.range 6).map (fun i => Gate.mkBUF branch_tag_out[i]! ib_br_fifo_enq_data[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF branch_result_final[i]! ib_br_fifo_enq_data[6+i]!) ++
      [Gate.mkBUF zero ib_br_fifo_enq_data[38]!] ++
      (List.range 32).map (fun i => Gate.mkBUF mispredict_redirect_target[i]! ib_br_fifo_enq_data[39+i]!) ++
      [Gate.mkBUF branch_mispredicted ib_br_fifo_enq_data[71]!]

  let ib_br_fifo_inst : CircuitInstance := {
    moduleName := if config.xlen == 64 || config.enableD then "Queue1Flow_103" else "Queue1Flow_72",
    instName := "u_cdb_fifo_ib_br",
    portMap := [("clock", clock), ("reset", pipeline_reset_busy),
                ("enq_valid", rs_br_dispatch_valid),
                ("deq_ready", ib_br_fifo_drain),
                ("enq_ready", ib_br_fifo_enq_ready),
                ("deq_valid", ib_br_fifo_deq_valid)] ++
      (List.range ib_br_fifo_width).map (fun i => (s!"enq_data_{i}", ib_br_fifo_enq_data[i]!)) ++
      (List.range ib_br_fifo_width).map (fun i => (s!"deq_data_{i}", ib_br_fifo_deq[i]!))
  }

  -- Merge IB1 and IB_BR outputs for CDBMux input
  let ib1_br_merged_valid := Wire.mk "ib1_br_merged_valid"
  let ib1_br_merged_width := if config.xlen == 64 || config.enableD then 103 else 72
  let ib1_br_merged_deq := CPU.makeIndexedWires "ib1_br_merged_deq" ib1_br_merged_width
  let ib1_br_sel_br := Wire.mk "ib1_br_sel_br"       -- 1 = branch FIFO selected
  let not_ib1_valid := Wire.mk "not_ib1_valid"
  let ib1_br_merge_gates :=
    [Gate.mkNOT ib1_fifo_deq_valid not_ib1_valid,
     Gate.mkAND ib_br_fifo_deq_valid not_ib1_valid ib1_br_sel_br,
     Gate.mkOR ib1_fifo_deq_valid ib_br_fifo_deq_valid ib1_br_merged_valid] ++
    (if config.xlen == 64 || config.enableD then
      -- Bits 0-69: from whichever FIFO (IB1 has 70 bits)
      (List.range 70).map (fun i =>
        Gate.mkMUX ib1_fifo_deq[i]! ib_br_fifo_deq[i]! ib1_br_sel_br ib1_br_merged_deq[i]!) ++
      -- Bits 70-101: redirect target (only from branch FIFO)
      (List.range 32).map (fun i =>
        Gate.mkAND ib_br_fifo_deq[70+i]! ib1_br_sel_br ib1_br_merged_deq[70+i]!) ++
      -- Bit 102: mispredicted
      [Gate.mkAND ib_br_fifo_deq[102]! ib1_br_sel_br ib1_br_merged_deq[102]!]
    else
      -- Bits 0-38: tag + data + exc from whichever FIFO
      (List.range 39).map (fun i =>
        Gate.mkMUX ib1_fifo_deq[i]! ib_br_fifo_deq[i]! ib1_br_sel_br ib1_br_merged_deq[i]!) ++
      -- Bits 39-71: redirect + mispredicted (only from branch FIFO, zero for INT)
      (List.range 33).map (fun i =>
        Gate.mkAND ib_br_fifo_deq[39+i]! ib1_br_sel_br ib1_br_merged_deq[39+i]!))

  -- Drain routing: drain the FIFO that was selected
  let ib1_br_cdb_drain := Wire.mk "ib1_br_cdb_drain"  -- from CDBMux drain_ib_1
  let not_sel_br := Wire.mk "not_ib1_br_sel_br"
  let ib1_br_drain_gates :=
    [Gate.mkNOT ib1_br_sel_br not_sel_br,
     Gate.mkAND ib1_br_cdb_drain ib1_br_sel_br ib_br_fifo_drain,
     Gate.mkAND ib1_br_cdb_drain not_sel_br ib1_fifo_drain]

  -- LSU FIFO
  let lsu_fifo_width := if config.xlen == 64 || config.enableD then 72 else 39
  let lsu_fifo_enq_data := CPU.makeIndexedWires "lsu_fifo_enq_data" lsu_fifo_width
  let lsu_fifo_deq := CPU.makeIndexedWires "lsu_fifo_deq" lsu_fifo_width
  let lsu_fifo_enq_ready := Wire.mk "lsu_fifo_enq_ready"
  let lsu_fifo_deq_valid := Wire.mk "lsu_fifo_deq_valid"
  let lsu_fifo_drain := Wire.mk "lsu_fifo_drain"

  -- lsu_is_fp: track whether in-flight load is FP (from is_flw pipeline register)
  let lsu_is_fp := Wire.mk "lsu_is_fp"
  let lsu_is_fp_gates :=
    if enableF then
      [Gate.mkBUF is_flw_r lsu_is_fp]
    else [Gate.mkBUF zero lsu_is_fp]

  let lsu_fifo_enq_assemble :=
    (List.range 6).map (fun i => Gate.mkBUF lsu_tag[i]! lsu_fifo_enq_data[i]!) ++
    (List.range 32).map (fun i => Gate.mkBUF lsu_data[i]! lsu_fifo_enq_data[6+i]!) ++
    (if config.xlen == 64 || config.enableD then
      (List.range 32).map (fun i => Gate.mkBUF lsu_data[32+i]! lsu_fifo_enq_data[38+i]!) ++
      [Gate.mkBUF lsu_is_fp lsu_fifo_enq_data[70]!,
       Gate.mkBUF lsu_is_double lsu_fifo_enq_data[71]!]
     else
      [Gate.mkBUF lsu_is_fp lsu_fifo_enq_data[38]!])

  let lsu_fifo_inst : CircuitInstance := {
    moduleName := if config.xlen == 64 || config.enableD then "Queue1Flow_72" else "Queue1Flow_39",
    instName := "u_cdb_fifo_lsu",
    portMap := [("clock", clock), ("reset", pipeline_reset_misc),
                ("enq_valid", lsu_valid),
                ("deq_ready", lsu_fifo_drain),
                ("enq_ready", lsu_fifo_enq_ready),
                ("deq_valid", lsu_fifo_deq_valid)] ++
      (List.range lsu_fifo_width).map (fun i => (s!"enq_data_{i}", lsu_fifo_enq_data[i]!)) ++
      (List.range lsu_fifo_width).map (fun i => (s!"deq_data_{i}", lsu_fifo_deq[i]!))
  }

  -- MulDiv FIFO
  let muldiv_fifo_width := if config.xlen == 64 || config.enableD then 70 else 39
  let muldiv_fifo_enq_data := CPU.makeIndexedWires "muldiv_fifo_enq_data" muldiv_fifo_width
  let muldiv_fifo_deq := CPU.makeIndexedWires "muldiv_fifo_deq" muldiv_fifo_width
  let muldiv_fifo_deq_valid := Wire.mk "muldiv_fifo_deq_valid"
  let muldiv_fifo_drain := Wire.mk "muldiv_fifo_drain"

  let muldiv_fifo_enq_assemble :=
    if enableM then
      (List.range 6).map (fun i => Gate.mkBUF muldiv_tag_out[i]! muldiv_fifo_enq_data[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF muldiv_result[i]! muldiv_fifo_enq_data[6+i]!) ++
      (if config.xlen == 64 || config.enableD then
        (List.range 32).map (fun i => Gate.mkBUF (if config.xlen == 64 then muldiv_result[32+i]! else zero) muldiv_fifo_enq_data[38+i]!)
       else
        [Gate.mkBUF zero muldiv_fifo_enq_data[38]!])
    else
      (List.range muldiv_fifo_width).map (fun i => Gate.mkBUF zero muldiv_fifo_enq_data[i]!)

  let muldiv_fifo_inst : CircuitInstance := {
    moduleName := if config.xlen == 64 || config.enableD then "Queue1Flow_70" else "Queue1Flow_39",
    instName := "u_cdb_fifo_muldiv",
    portMap := [("clock", clock), ("reset", pipeline_reset_rs_muldiv),
                ("enq_valid", muldiv_valid_out),
                ("deq_ready", muldiv_fifo_drain),
                ("enq_ready", Wire.mk "muldiv_fifo_enq_ready"),
                ("deq_valid", muldiv_fifo_deq_valid)] ++
      (List.range muldiv_fifo_width).map (fun i => (s!"enq_data_{i}", muldiv_fifo_enq_data[i]!)) ++
      (List.range muldiv_fifo_width).map (fun i => (s!"deq_data_{i}", muldiv_fifo_deq[i]!))
  }

  -- FP stale result suppression: after pipeline flush, suppress FP FIFO enqueue
  -- for enough cycles to drain any in-flight pipelined FP results (max 5 cycles for FMA)
  -- plus a drain mode that stays set while FP EU is busy (covers iterative div/sqrt).
  let fp_flush_sr := CPU.makeIndexedWires "fp_flush_sr" 5  -- shift register
  let fp_flush_suppress := Wire.mk "fp_flush_suppress"     -- OR of shift register
  let fp_drain_mode := Wire.mk "fp_drain_mode"             -- set on flush, cleared when EU idle
  let fp_drain_mode_d := Wire.mk "fp_drain_mode_d"
  let fp_drain_hold := Wire.mk "fp_drain_hold"
  let fp_stale_suppress := Wire.mk "fp_stale_suppress"     -- suppress FP FIFO enqueue
  let fp_enq_valid_gated := Wire.mk "fp_enq_valid_gated"   -- gated enqueue valid
  let not_fp_stale_suppress := Wire.mk "not_fp_stale_suppress"
  let fp_stale_gates :=
    if enableF then
      -- 5-stage shift register: shift in pipeline_flush_comb
      [Gate.mkDFF pipeline_flush_comb clock reset fp_flush_sr[0]!,
       Gate.mkDFF fp_flush_sr[0]! clock reset fp_flush_sr[1]!,
       Gate.mkDFF fp_flush_sr[1]! clock reset fp_flush_sr[2]!,
       Gate.mkDFF fp_flush_sr[2]! clock reset fp_flush_sr[3]!,
       Gate.mkDFF fp_flush_sr[3]! clock reset fp_flush_sr[4]!] ++
      -- OR tree for shift register
      let or01 := Wire.mk "fp_fsr_or01"
      let or23 := Wire.mk "fp_fsr_or23"
      let or0123 := Wire.mk "fp_fsr_or0123"
      [Gate.mkOR fp_flush_sr[0]! fp_flush_sr[1]! or01,
       Gate.mkOR fp_flush_sr[2]! fp_flush_sr[3]! or23,
       Gate.mkOR or01 or23 or0123,
       Gate.mkOR or0123 fp_flush_sr[4]! fp_flush_suppress] ++
      -- Drain mode: set on flush, held while FP EU busy
      [Gate.mkAND fp_drain_mode fp_busy_eu fp_drain_hold,
       Gate.mkOR pipeline_flush_comb fp_drain_hold fp_drain_mode_d,
       Gate.mkDFF fp_drain_mode_d clock reset fp_drain_mode] ++
      -- Suppress = drain mode only (shift register is too aggressive for single-cycle FP ops)
      [Gate.mkBUF fp_drain_mode fp_stale_suppress,
       Gate.mkNOT fp_stale_suppress not_fp_stale_suppress,
       Gate.mkAND fp_valid_out not_fp_stale_suppress fp_enq_valid_gated]
    else
      [Gate.mkBUF zero fp_flush_suppress,
       Gate.mkBUF zero fp_drain_mode,
       Gate.mkBUF zero fp_stale_suppress,
       Gate.mkBUF zero fp_enq_valid_gated] ++
      (List.range 5).map (fun i => Gate.mkBUF zero fp_flush_sr[i]!) ++
      [Gate.mkBUF zero fp_drain_mode_d, Gate.mkBUF zero fp_drain_hold,
       Gate.mkBUF zero not_fp_stale_suppress]

  -- FP Result FIFO
  let fp_fifo_deq := CPU.makeIndexedWires "fp_fifo_deq" fp_fifo_width
  let fp_fifo_deq_valid := Wire.mk "fp_fifo_deq_valid"
  let fp_fifo_drain := Wire.mk "fp_fifo_drain"
  let fp_fifo_inst : CircuitInstance := {
    moduleName := if config.enableD then "Queue1Flow_71" else "Queue1Flow_39",
    instName := "u_cdb_fifo_fp",
    portMap := [("clock", clock), ("reset", pipeline_reset_rs_fp),
                ("enq_valid", fp_enq_valid_gated),
                ("deq_ready", fp_fifo_drain),
                ("enq_ready", fp_fifo_enq_ready),
                ("deq_valid", fp_fifo_deq_valid)] ++
      (List.range fp_fifo_width).map (fun i => (s!"enq_data_{i}", fp_fifo_enq_data[i]!)) ++
      (List.range fp_fifo_width).map (fun i => (s!"deq_data_{i}", fp_fifo_deq[i]!))
  }
  let fp_fifo_dummy_gates :=
    if enableF then [] else
    [Gate.mkBUF zero fp_fifo_deq_valid] ++
    (List.range fp_fifo_width).map (fun i => Gate.mkBUF zero fp_fifo_deq[i]!)

  -- Muldiv FIFO dummy gates (when M disabled)
  let muldiv_fifo_dummy_gates :=
    if enableM then []
    else [Gate.mkBUF zero muldiv_fifo_deq_valid] ++
         (List.range muldiv_fifo_width).map (fun i => Gate.mkBUF zero muldiv_fifo_deq[i]!)

  -- === CDB PRIORITY MUX (W2) ===
  -- Uses CDBMux_W2: 2 IB FIFOs, LSU, MulDiv, FP, DMEM → 2 CDB channels
  let cdb_pre_valid_0 := Wire.mk "cdb_pre_valid_0"
  let cdb_pre_tag_0 := CPU.makeIndexedWires "cdb_pre_tag_0" 6
  let cdb_pre_data_0 := CPU.makeIndexedWires "cdb_pre_data_0" (if config.enableD then 64 else 32)
  let cdb_pre_valid_1 := Wire.mk "cdb_pre_valid_1"
  let cdb_pre_tag_1 := CPU.makeIndexedWires "cdb_pre_tag_1" 6
  let cdb_pre_data_1 := CPU.makeIndexedWires "cdb_pre_data_1" (if config.enableD then 64 else 32)

  let cdb_mux_inst : CircuitInstance :=
    { moduleName := if config.enableD then "CDBMux_FD_W2" else (if enableF then "CDBMux_F_W2" else "CDBMux_W2")
      instName := "u_cdb_mux"
      portMap :=
        [("ib_valid_0", ib0_fifo_deq_valid), ("ib_valid_1", ib1_br_merged_valid),
         ("fp_valid", fp_fifo_deq_valid),
         ("muldiv_valid", muldiv_fifo_deq_valid),
         ("lsu_valid", lsu_fifo_deq_valid),
         ("dmem_valid", dmem_valid_gated)] ++
        (List.range (if config.enableD then 70 else 72)).map (fun i => (s!"ib_deq_0_{i}", ib0_fifo_deq[i]!)) ++
        (List.range (if config.enableD then 103 else 72)).map (fun i => (s!"ib_deq_1_{i}", ib1_br_merged_deq[i]!)) ++
        (List.range (if config.enableD then 71 else 39)).map (fun i => (s!"fp_deq_{i}", fp_fifo_deq[i]!)) ++
        (List.range (if config.enableD then 70 else 39)).map (fun i => (s!"muldiv_deq_{i}", muldiv_fifo_deq[i]!)) ++
        (List.range (if config.enableD then 72 else 39)).map (fun i => (s!"lsu_deq_{i}", lsu_fifo_deq[i]!)) ++
        (List.range (if config.enableD then 64 else 32)).map (fun i => (s!"dmem_fmt_{i}", dmem_resp_formatted[i]!)) ++
        (List.range 6).map (fun i => (s!"dmem_tag_{i}", dmem_load_tag_reg[i]!)) ++
        [("dmem_is_fp", if enableF then dmem_is_fp_reg else zero)] ++
        (if config.enableD then [("dmem_is_double", dmem_is_double)] else []) ++
        [("zero", zero)] ++
        -- Outputs (raw, before CSR injection)
        [("pre_valid_0", Wire.mk "cdb_pre_valid_0_raw")] ++
        (List.range 6).map (fun i => (s!"pre_tag_0_{i}", Wire.mk s!"cdb_pre_tag_0_raw_{i}")) ++
        (List.range (if config.enableD then 64 else 32)).map (fun i => (s!"pre_data_0_{i}", Wire.mk s!"cdb_pre_data_0_raw_{i}")) ++
        [("pre_is_fp_0", Wire.mk "cdb_pre_is_fp_0")] ++
        [("pre_valid_1", cdb_pre_valid_1)] ++
        (List.range 6).map (fun i => (s!"pre_tag_1_{i}", cdb_pre_tag_1[i]!)) ++
        (List.range (if config.enableD then 64 else 32)).map (fun i => (s!"pre_data_1_{i}", cdb_pre_data_1[i]!)) ++
        [("pre_is_fp_1", Wire.mk "cdb_pre_is_fp_1")] ++
        (if config.enableD then [("pre_is_double_0", Wire.mk "cdb_pre_is_double_0")] else []) ++
        [("drain_lsu", lsu_fifo_drain),
         ("drain_muldiv", muldiv_fifo_drain),
         ("drain_fp", fp_fifo_drain),
         ("drain_ib_0", ib0_fifo_drain),
         ("drain_ib_1", ib1_br_cdb_drain)] ++
        (List.range 32).map (fun i => (s!"redirect_1_{i}", Wire.mk s!"cdb_redirect_1_{i}")) ++
        [("pre_mispredicted_1", Wire.mk "cdb_mispredicted_1")] }

  let cdb_tag_nz_gates : List Gate := []

  -- CDB pipeline registers (2 channels)
  -- Channel 0 uses cdb_reset (= pipeline_reset_misc AND NOT csr_flush_suppress)
  -- to preserve CSR CDB injection through the flush cycle.
  let cdb_reset_w := Wire.mk "cdb_reset"
  let cdb_reg_insts : List CircuitInstance :=
    -- Channel 0
    [{ moduleName := "DFlipFlop", instName := "u_cdb_valid_reg_0",
       portMap := [("d", cdb_pre_valid_0), ("q", cdb_valid_0),
                   ("clock", clock), ("reset", cdb_reset_w)] }] ++
    (List.range 6).map (fun i => {
       moduleName := "DFlipFlop", instName := s!"u_cdb_tag_reg_0_{i}",
       portMap := [("d", cdb_pre_tag_0[i]!), ("q", cdb_tag_0[i]!),
                   ("clock", clock), ("reset", cdb_reset_w)] }) ++
    (if config.enableD then
      [{ moduleName := "Register64", instName := "u_cdb_data_reg_0",
         portMap := (cdb_pre_data_0.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
                    [("clock", clock), ("reset", cdb_reset_w)] ++
                    (cdb_data_0.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w))) }]
     else
      [{ moduleName := "Register32", instName := "u_cdb_data_reg_0",
         portMap := (cdb_pre_data_0.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
                    [("clock", clock), ("reset", cdb_reset_w)] ++
                    (cdb_data_0.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w))) }]) ++
    -- Channel 1
    [{ moduleName := "DFlipFlop", instName := "u_cdb_valid_reg_1",
       portMap := [("d", cdb_pre_valid_1), ("q", cdb_valid_1),
                   ("clock", clock), ("reset", pipeline_reset_misc)] }] ++
    (List.range 6).map (fun i => {
       moduleName := "DFlipFlop", instName := s!"u_cdb_tag_reg_1_{i}",
       portMap := [("d", cdb_pre_tag_1[i]!), ("q", cdb_tag_1[i]!),
                   ("clock", clock), ("reset", pipeline_reset_misc)] }) ++
    (if config.enableD then
      [{ moduleName := "Register64", instName := "u_cdb_data_reg_1",
         portMap := (cdb_pre_data_1.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
                    [("clock", clock), ("reset", pipeline_reset_misc)] ++
                    (cdb_data_1.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w))) }]
     else
      [{ moduleName := "Register32", instName := "u_cdb_data_reg_1",
         portMap := (cdb_pre_data_1.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
                    [("clock", clock), ("reset", pipeline_reset_misc)] ++
                    (cdb_data_1.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w))) }]) ++
    -- CDB is_fp pipeline registers
    [{ moduleName := "DFlipFlop", instName := "u_cdb_is_fp_reg_0",
       portMap := [("d", Wire.mk "cdb_pre_is_fp_0"), ("q", cdb_is_fp_0),
                   ("clock", clock), ("reset", cdb_reset_w)] },
     { moduleName := "DFlipFlop", instName := "u_cdb_is_fp_reg_1",
       portMap := [("d", Wire.mk "cdb_pre_is_fp_1"), ("q", cdb_is_fp_1),
                   ("clock", clock), ("reset", pipeline_reset_misc)] }]

  -- CDB redirect target + mispredicted pipeline registers (for shadow register writes)
  let cdb_redirect_reg_1 := CPU.makeIndexedWires "cdb_redirect_reg_1" 32
  let cdb_mispredicted_reg_1 := Wire.mk "cdb_mispredicted_reg_1"
  let cdb_redirect_1_wires := (List.range 32).map (fun i => Wire.mk s!"cdb_redirect_1_{i}")
  let cdb_redirect_reg_insts : List CircuitInstance :=
    [{ moduleName := "Register32", instName := "u_cdb_redirect_reg_1",
       portMap := (cdb_redirect_1_wires.enum.map (fun ⟨i, w⟩ => (s!"d_{i}", w))) ++
                  [("clock", clock), ("reset", pipeline_reset_misc)] ++
                  (cdb_redirect_reg_1.enum.map (fun ⟨i, w⟩ => (s!"q_{i}", w))) },
     { moduleName := "DFlipFlop", instName := "u_cdb_mispred_reg_1",
       portMap := [("d", Wire.mk "cdb_mispredicted_1"), ("q", cdb_mispredicted_reg_1),
                   ("clock", clock), ("reset", pipeline_reset_misc)] }]

  -- === SHADOW REGISTERS (isStore + redirect target, W=2) ===
  let (shadow_gates, shadow_insts, rob_head_isStore_0, rob_head_isStore_1,
       _rob_head_redirect_target_0, _rob_head_redirect_target_1) :=
    mkShadowRegisters2 zero one clock reset
      rob_alloc_idx_0 rob_alloc_idx_1
      rename_valid_0 rename_valid_1
      d0_is_st d1_is_st
      rd_phys_0 rd_phys_1
      cdb_tag_1
      cdb_valid_1
      cdb_mispredicted_reg_1
      cdb_redirect_reg_1
      rob_head_idx_0 rob_head_idx_1

  -- commit_store_en: fires when any store commit is owed.
  -- Store buffer advances commit_ptr by 1 per pulse.
  -- 3-bit pending counter tracks commits owed but not yet fired.
  -- pending_next = pending + s0 + s1 - en
  -- en = 1 whenever pending > 0 OR any new store commits.
  let commit_store_0 := Wire.mk "commit_store_s0"
  let commit_store_1 := Wire.mk "commit_store_s1"
  let csp := CPU.makeIndexedWires "csp_" 3  -- commit_store_pending counter
  let csp_next := CPU.makeIndexedWires "csp_next_" 3
  let commit_store_gate :=
    [Gate.mkAND retire_valid_0 rob_head_isStore_0 commit_store_0,
     Gate.mkAND retire_valid_1 rob_head_isStore_1 commit_store_1,
     -- commit_store_en = (pending > 0) OR (s0) OR (s1)
     Gate.mkOR csp[0]! csp[1]! (Wire.mk "csp_nz_t"),
     Gate.mkOR (Wire.mk "csp_nz_t") csp[2]! (Wire.mk "csp_nz"),
     Gate.mkOR commit_store_0 commit_store_1 (Wire.mk "commit_store_new"),
     Gate.mkOR (Wire.mk "commit_store_new") (Wire.mk "csp_nz") commit_store_en,
     -- delta = s0 + s1 - en (range: -1 to +1)
     -- When en=1: delta = s0 + s1 - 1; when en=0: delta = 0 (nothing happens)
     -- Compute add_val = s0 + s1 (0, 1, or 2): add_val[0] = s0 XOR s1, add_val[1] = s0 AND s1
     Gate.mkXOR commit_store_0 commit_store_1 (Wire.mk "add_val_0"),
     Gate.mkAND commit_store_0 commit_store_1 (Wire.mk "add_val_1"),
     -- sub_val = en (1 when en=1, 0 otherwise): just 1-bit
     -- net = add_val - sub_val = (s0+s1) - en
     -- net as 2-bit signed: when en=1, net = s0+s1-1 ∈ {-1,0,1}
     --   s0+s1=0, en=0: net=0  → csp_next = csp (no change, but this case doesn't happen since en=0 only when both are 0)
     --   s0+s1=0, en=1: net=-1 → csp_next = csp - 1
     --   s0+s1=1, en=1: net=0  → csp_next = csp
     --   s0+s1=2, en=1: net=+1 → csp_next = csp + 1
     -- Simplification: en=1 always (when anything fires). When en=0, csp_next=csp=0.
     -- net_signed[0] = add_val[0] XOR en = (s0 XOR s1) XOR en
     -- net_signed[1] = carry_out - borrow = add_val[1] XOR (NOT(add_val[0]) AND en)
     -- Actually let's just compute csp_next = csp + s0 + s1 - en directly.
     -- csp + s0: 3-bit add
     Gate.mkXOR csp[0]! commit_store_0 (Wire.mk "csp_a0"),
     Gate.mkAND csp[0]! commit_store_0 (Wire.mk "csp_c0"),
     Gate.mkXOR csp[1]! (Wire.mk "csp_c0") (Wire.mk "csp_a1"),
     Gate.mkAND csp[1]! (Wire.mk "csp_c0") (Wire.mk "csp_c1"),
     Gate.mkXOR csp[2]! (Wire.mk "csp_c1") (Wire.mk "csp_a2"),
     -- + s1: add s1 to csp_a[2:0]
     Gate.mkXOR (Wire.mk "csp_a0") commit_store_1 (Wire.mk "csp_b0"),
     Gate.mkAND (Wire.mk "csp_a0") commit_store_1 (Wire.mk "csp_d0"),
     Gate.mkXOR (Wire.mk "csp_a1") (Wire.mk "csp_d0") (Wire.mk "csp_b1"),
     Gate.mkAND (Wire.mk "csp_a1") (Wire.mk "csp_d0") (Wire.mk "csp_d1"),
     Gate.mkXOR (Wire.mk "csp_a2") (Wire.mk "csp_d1") (Wire.mk "csp_b2"),
     -- - en: subtract en from csp_b[2:0] (borrow chain)
     Gate.mkXOR (Wire.mk "csp_b0") commit_store_en (Wire.mk "csp_e0"),
     Gate.mkNOT (Wire.mk "csp_b0") (Wire.mk "not_csp_b0"),
     Gate.mkAND (Wire.mk "not_csp_b0") commit_store_en (Wire.mk "csp_borrow0"),
     Gate.mkXOR (Wire.mk "csp_b1") (Wire.mk "csp_borrow0") (Wire.mk "csp_e1"),
     Gate.mkNOT (Wire.mk "csp_b1") (Wire.mk "not_csp_b1"),
     Gate.mkAND (Wire.mk "not_csp_b1") (Wire.mk "csp_borrow0") (Wire.mk "csp_borrow1"),
     Gate.mkXOR (Wire.mk "csp_b2") (Wire.mk "csp_borrow1") (Wire.mk "csp_e2"),
     -- csp_next = csp_e (no flush gating — stores are already ROB-committed)
     Gate.mkBUF (Wire.mk "csp_e0") csp_next[0]!,
     Gate.mkBUF (Wire.mk "csp_e1") csp_next[1]!,
     Gate.mkBUF (Wire.mk "csp_e2") csp_next[2]!]
  let commit_store_pending_dffs := (List.range 3).map (fun i =>
    { moduleName := "DFlipFlop", instName := s!"u_commit_store_pending_{i}",
      portMap := [("d", csp_next[i]!), ("q", csp[i]!),
                  ("clock", clock), ("reset", reset)] : CircuitInstance })

  -- RS issue_full:
  -- INT RS dispatches to BOTH banks each cycle, so full = NOT(avail_0 AND avail_1)
  -- BR/MEM/MD RSs use bank 0 only, so full = NOT(avail_0)
  let rs_full_gates :=
    [Gate.mkAND (Wire.mk "rs_int_avail_0") (Wire.mk "rs_int_avail_1") (Wire.mk "rs_int_both_avail"),
     Gate.mkNOT (Wire.mk "rs_int_both_avail") rs_int_issue_full,
     Gate.mkNOT (Wire.mk "rs_br_avail_0") rs_br_issue_full,
     Gate.mkNOT (Wire.mk "rs_mem_avail_0") rs_mem_issue_full,
     Gate.mkNOT (Wire.mk "rs_md_avail_0") rs_muldiv_issue_full] ++
    (if enableF then [Gate.mkNOT (Wire.mk "rs_fp_avail_0") rs_fp_issue_full]
     else [Gate.mkBUF zero rs_fp_issue_full])

  -- === STALL GENERATION ===
  -- Cache line boundary: when fetch_pc word offset = 7 (bits [4:2] = 111),
  -- the L1I can only return one valid word (slot 1 would wrap to wrong line).
  -- Force half_step so only slot 0 dispatches and fetch advances by 4.
  let cache_line_boundary := Wire.mk "cache_line_boundary"
  let clb_gates :=
    [Gate.mkAND fetch_pc_0[2]! fetch_pc_0[3]! (Wire.mk "clb_23"),
     Gate.mkAND (Wire.mk "clb_23") fetch_pc_0[4]! cache_line_boundary]

  -- any_dual_stall: suppress slot 1 dispatch + hold fetch, but don't block slot 0
  let any_dual_stall := Wire.mk "any_dual_stall"
  let not_dual_stall := Wire.mk "not_dual_stall"
  let stall_gates :=
    if enableM then
      [Gate.mkOR br_dual_stall mem_dual_stall (Wire.mk "dual_stall_bm"),
       Gate.mkOR (Wire.mk "dual_stall_bm") muldiv_dual_stall (Wire.mk "dual_stall_bmm"),
       Gate.mkOR (Wire.mk "dual_stall_bmm") fp_dual_stall (Wire.mk "dual_stall_bmmf"),
       Gate.mkOR (Wire.mk "dual_stall_bmmf") cache_line_boundary (Wire.mk "dual_stall_bmmfc"),
       -- One ROB slot left: a 2-wide alloc would overflow the 16-entry ROB.
       Gate.mkOR (Wire.mk "dual_stall_bmmfc") rob_nearly_full any_dual_stall,
       Gate.mkNOT any_dual_stall not_dual_stall,
       Gate.mkOR (Wire.mk "rename_stall_0") rob_full (Wire.mk "stall_L0_a"),
       Gate.mkOR rs_int_issue_full rs_mem_issue_full (Wire.mk "stall_L0_b"),
       Gate.mkOR rs_br_issue_full rs_muldiv_issue_full (Wire.mk "stall_L0_c"),
       Gate.mkOR (Wire.mk "stall_L0_a") (Wire.mk "stall_L0_b") (Wire.mk "stall_L1_a"),
       Gate.mkOR (Wire.mk "stall_L1_a") (Wire.mk "stall_L0_c") (Wire.mk "stall_L1_b"),
       Gate.mkOR (Wire.mk "stall_L1_b") rs_fp_issue_full (Wire.mk "stall_L1_c"),
       Gate.mkOR (Wire.mk "stall_L1_c") lsu_sb_full (Wire.mk "global_stall_int"),
       Gate.mkOR (Wire.mk "global_stall_int") dmem_stall_ext global_stall]
    else
      [Gate.mkOR br_dual_stall cache_line_boundary (Wire.mk "dual_stall_xc"),
       Gate.mkOR (Wire.mk "dual_stall_xc") rob_nearly_full any_dual_stall,
       Gate.mkNOT any_dual_stall not_dual_stall,
       Gate.mkOR (Wire.mk "rename_stall_0") rob_full (Wire.mk "stall_L0_a"),
       Gate.mkOR rs_int_issue_full rs_mem_issue_full (Wire.mk "stall_L0_b"),
       Gate.mkOR rs_br_issue_full zero (Wire.mk "stall_L0_c"),
       Gate.mkOR (Wire.mk "stall_L0_a") (Wire.mk "stall_L0_b") (Wire.mk "stall_L1_a"),
       Gate.mkOR (Wire.mk "stall_L1_a") (Wire.mk "stall_L0_c") (Wire.mk "global_stall_int"),
       Gate.mkOR (Wire.mk "global_stall_int") dmem_stall_ext global_stall]

  -- === DMEM INTERFACE ===
  let dmem_req_valid := Wire.mk "dmem_req_valid"
  let dmem_req_we := Wire.mk "dmem_req_we"
  let dmem_req_addr := CPU.makeIndexedWires "dmem_req_addr" 32
  let dmem_req_data := CPU.makeIndexedWires "dmem_req_data" (if config.xlen == 64 || config.enableD then 64 else 32)
  let dmem_req_size := CPU.makeIndexedWires "dmem_req_size" 2

  let sb_deq_size_0 := if config.xlen == 64 then lsu_sb_deq_bits[128]! else (if config.enableD then lsu_sb_deq_bits[96]! else lsu_sb_deq_bits[64]!)
  let sb_deq_size_1 := if config.xlen == 64 then lsu_sb_deq_bits[129]! else (if config.enableD then lsu_sb_deq_bits[97]! else lsu_sb_deq_bits[65]!)

  let dmem_gates :=
    -- Request sources: DMEM load, store-buffer dequeue, atomic direct write
    [Gate.mkOR load_no_fwd lsu_sb_deq_valid (Wire.mk "dmem_v0"),
     Gate.mkOR (Wire.mk "dmem_v0") (Wire.mk "atom_aw_pending") dmem_req_valid,
     Gate.mkOR lsu_sb_deq_valid (Wire.mk "atom_aw_pending") dmem_req_we] ++
    (List.range 32).map (fun i =>
      Gate.mkMUX mem_addr_r[i]! lsu_sb_deq_bits[i]! lsu_sb_deq_valid (Wire.mk s!"dmem_addr_p{i}")) ++
    (List.range 32).map (fun i =>
      Gate.mkMUX (Wire.mk s!"dmem_addr_p{i}") (Wire.mk s!"atom_aw_addr_{i}") (Wire.mk "atom_aw_pending") dmem_req_addr[i]!) ++
    (List.range 32).map (fun i =>
      Gate.mkMUX (if config.xlen == 64 then lsu_sb_deq_bits[64+i]! else lsu_sb_deq_bits[32+i]!) (Wire.mk s!"atom_aw_data_{i}") (Wire.mk "atom_aw_pending") dmem_req_data[i]!) ++
    (if config.xlen == 64 || config.enableD then
      (List.range 32).map (fun i =>
        Gate.mkMUX (if config.xlen == 64 then lsu_sb_deq_bits[96+i]! else lsu_sb_deq_bits[64+i]!) (Wire.mk s!"atom_aw_data_{32+i}") (Wire.mk "atom_aw_pending") dmem_req_data[32+i]!)
     else []) ++
    [Gate.mkMUX mem_size_r[0]! sb_deq_size_0 lsu_sb_deq_valid (Wire.mk "dmem_msize0"),
     Gate.mkMUX mem_size_r[1]! sb_deq_size_1 lsu_sb_deq_valid (Wire.mk "dmem_msize1"),
     -- Atomic writes use mem_size_r; SB drains use sb_deq_size; reads use mem_size_r
     Gate.mkBUF (Wire.mk "dmem_msize0") dmem_req_size[0]!,
     Gate.mkBUF (Wire.mk "dmem_msize1") dmem_req_size[1]!]

  -- === CSR REGISTER FILE + EXECUTE LOGIC (W2) ===
  -- CSR drain_complete: fires when pipeline fully drained AND the serialized op was a CSR
  let csr_drain_complete := Wire.mk "csr_drain_complete"
  let csr_drain_gate := [Gate.mkAND fence_i_drain_complete csr_flag_reg csr_drain_complete]

  let csrDataWidth := if config.xlen == 64 || config.enableD then 64 else 32
  let csr_cdb_inject := Wire.mk "csr_cdb_inject"
  let csr_rd_nonzero := Wire.mk "csr_rd_nonzero"
  let csr_cdb_tag := (List.range 6).map (fun i => Wire.mk s!"csr_cdb_tg_e{i}")
  let csr_cdb_data := (List.range csrDataWidth).map (fun i => Wire.mk s!"csr_cdb_dt_e{i}")
  let frm_reg := CPU.makeIndexedWires "frm_reg" 3
  let fflags_reg := CPU.makeIndexedWires "fflags_reg" 5
  let irq_pending := Wire.mk "irq_pending"

  let csr_inst : CircuitInstance := {
    moduleName := s!"CSRFile_{config.isaString}",
    instName := "u_csr_file",
    portMap := [
      ("clock", clock),
      ("reset", reset),
      ("zero", zero),
      ("one", one)
    ] ++
    (csr_addr_reg.enum.map fun ⟨i, w⟩ => (s!"csr_addr_{i}", w)) ++
    (csr_optype_reg.enum.map fun ⟨i, w⟩ => (s!"csr_optype_{i}", w)) ++
    (csr_rs1cap_reg.enum.map fun ⟨i, w⟩ => (s!"csr_rs1cap_{i}", w)) ++
    (csr_zimm_reg.enum.map fun ⟨i, w⟩ => (s!"csr_zimm_{i}", w)) ++
    (csr_phys_reg.enum.map fun ⟨i, w⟩ => (s!"csr_phys_{i}", w)) ++
    (csr_rd_reg.enum.map fun ⟨i, w⟩ => (s!"csr_rd_{i}", w)) ++
    [("csr_drain_complete", csr_drain_complete)] ++
    (if enableTraps then
      [("useq_active", useq_active),
       ("useq_csr_sel_0", useq_csr_sel[0]!),
       ("useq_csr_sel_1", useq_csr_sel[1]!),
       ("useq_mstatus_trap", useq_mstatus_trap),
       ("useq_mstatus_mret", useq_mstatus_mret),
       ("useq_write_en", useq_write_en)] ++
      (useq_write_data.enum.map fun ⟨i, w⟩ => (s!"useq_write_data_{i}", w))
    else []) ++
    [("retire_valid_0", retire_valid_0),
     ("retire_valid_1", retire_valid_1),
     ("mtip_in", Wire.mk "mtip_in")] ++
    (if enableF then
      [("fp_valid_out", fp_valid_out)] ++
      (fp_exceptions.enum.map fun ⟨i, w⟩ => (s!"fp_exceptions_{i}", w))
    else []) ++
    [("csr_cdb_inject", csr_cdb_inject),
     ("csr_rd_nonzero", csr_rd_nonzero)] ++
    (csr_cdb_tag.enum.map fun ⟨i, w⟩ => (s!"csr_cdb_tag_{i}", w)) ++
    (csr_cdb_data.enum.map fun ⟨i, w⟩ => (s!"csr_cdb_data_{i}", w)) ++
    (frm_reg.enum.map fun ⟨i, w⟩ => (s!"frm_{i}", w)) ++
    (fflags_reg.enum.map fun ⟨i, w⟩ => (s!"fflags_{i}", w)) ++
    [("irq_pending", irq_pending)]
  }

  -- CSR commit injection: since CSR is NOT in ROB (gated by not_csr_rename_en),
  -- we need to fake a commit to free the old phys reg and update freelist.
  -- MUX the commit signals for slot 0 with CSR data when csr_cdb_inject fires.
  -- (ROB is empty at drain_complete, so retire_valid_0=0, no conflict.)
  let commit_archRd_muxed_0 := CPU.makeIndexedWires "cmt_archRd_mux_0" 5
  let commit_physRd_muxed_0 := CPU.makeIndexedWires "cmt_physRd_mux_0" 6
  let retire_tag_muxed_0 := CPU.makeIndexedWires "cmt_retag_mux_0" 6
  let csr_commit_valid_0 := Wire.mk "csr_commit_valid_0"
  let csr_commit_hasPhysRd_0 := Wire.mk "csr_commit_hasPhysRd_0"
  let csr_retire_hasPhysRd_0 := Wire.mk "csr_retire_hasPhysRd_0"
  let csr_commit_hasAllocSlot_0 := Wire.mk "csr_commit_hasAllocSlot_0"
  let csr_commit_inject_gates : List Gate :=
    if config.enableZicsr then
      [Gate.mkOR retire_valid_0 csr_cdb_inject csr_commit_valid_0,
       -- commit_hasPhysRd: for CRAT write only (branches excluded, FP excluded)
       Gate.mkMUX int_hasOldPhysRd_0 one csr_cdb_inject csr_commit_hasPhysRd_0,
       -- retire_hasPhysRd: for free list enqueue (branches included via branch_tracking, FP excluded)
       Gate.mkMUX int_retire_any_old_0 one csr_cdb_inject csr_retire_hasPhysRd_0,
       Gate.mkMUX int_hasPhysRd_0 one csr_cdb_inject csr_commit_hasAllocSlot_0] ++
      (List.range 5).map (fun i =>
        Gate.mkMUX commit_archRd_0[i]! csr_rd_reg[i]! csr_cdb_inject commit_archRd_muxed_0[i]!) ++
      (List.range 6).map (fun i =>
        Gate.mkMUX commit_physRd_0[i]! csr_phys_reg[i]! csr_cdb_inject commit_physRd_muxed_0[i]!) ++
      -- retire_tag: MUX with CSR's old phys reg for freelist return
      (List.range 6).map (fun i =>
        Gate.mkMUX retire_tag_bt_0[i]! csr_old_phys_reg[i]! csr_cdb_inject retire_tag_muxed_0[i]!)
    else
      [Gate.mkBUF retire_valid_0 csr_commit_valid_0,
       -- commit_hasPhysRd: CRAT write only (branches excluded, FP excluded)
       Gate.mkBUF int_hasOldPhysRd_0 csr_commit_hasPhysRd_0,
       -- retire_hasPhysRd: free list enqueue (branches included, FP excluded)
       Gate.mkBUF int_retire_any_old_0 csr_retire_hasPhysRd_0,
       Gate.mkBUF int_hasPhysRd_0 csr_commit_hasAllocSlot_0] ++
      (List.range 5).map (fun i =>
        Gate.mkBUF commit_archRd_0[i]! commit_archRd_muxed_0[i]!) ++
      (List.range 6).map (fun i =>
        Gate.mkBUF commit_physRd_0[i]! commit_physRd_muxed_0[i]!) ++
      (List.range 6).map (fun i =>
        Gate.mkBUF retire_tag_bt_0[i]! retire_tag_muxed_0[i]!)

  -- Rename port decoupling buffers (unused, ports eliminated on u_rename)
  let rename_buf_gates : List Gate := []

  -- CDB channel 0 injection: OR csr_cdb_inject into pre_valid_0, MUX tag/data
  let cdb_pre_valid_0_raw := Wire.mk "cdb_pre_valid_0_raw"
  let cdb_pre_tag_0_raw := CPU.makeIndexedWires "cdb_pre_tag_0_raw" 6
  let cdb_pre_data_0_raw := CPU.makeIndexedWires "cdb_pre_data_0_raw" (if config.enableD then 64 else 32)
  let csr_cdb_channel_inject_gates : List Gate :=
    [Gate.mkOR cdb_pre_valid_0_raw csr_cdb_inject cdb_pre_valid_0] ++
    (List.range 6).map (fun i =>
      Gate.mkMUX cdb_pre_tag_0_raw[i]! csr_cdb_tag[i]! csr_cdb_inject cdb_pre_tag_0[i]!) ++
    (List.range 32).map (fun i =>
      Gate.mkMUX cdb_pre_data_0_raw[i]! csr_cdb_data[i]! csr_cdb_inject cdb_pre_data_0[i]!) ++
    (if config.enableD then
      (List.range 32).map (fun i =>
        Gate.mkMUX cdb_pre_data_0_raw[32+i]! csr_cdb_data[32+i]! csr_cdb_inject cdb_pre_data_0[32+i]!)
     else [])

  -- CDB reset gating: suppress flush on cycle after CSR inject
  let not_csr_flush_suppress := Wire.mk "not_csr_fsup"
  let cdb_reset := Wire.mk "cdb_reset"
  let csr_cdb_reset_gates : List Gate :=
    [Gate.mkNOT csr_flush_suppress not_csr_flush_suppress,
     Gate.mkAND pipeline_reset_misc not_csr_flush_suppress cdb_reset]

  -- Collect all CSR gates
  let csr_all_gates := csr_drain_gate ++ csr_commit_inject_gates ++ rename_buf_gates ++
    csr_cdb_channel_inject_gates ++ csr_cdb_reset_gates

  -- === RVVI TRACE (full dual-retire for W2) ===
  let rvvi_valid_0 := Wire.mk "rvvi_validS0"
  let rvvi_valid_1 := Wire.mk "rvvi_validS1"
  let rvvi_trap_0  := Wire.mk "rvvi_trapS0"
  let rvvi_trap_1  := Wire.mk "rvvi_trapS1"
  let rvvi_rd_valid_0 := Wire.mk "rvvi_rd_validS0"
  let rvvi_rd_valid_1 := Wire.mk "rvvi_rd_validS1"
  let rvvi_pc_rdata_0 := CPU.makeIndexedWires "rvvi_pc_0" 32
  let rvvi_pc_rdata_1 := CPU.makeIndexedWires "rvvi_pc_1" 32
  let rvvi_insn_0     := CPU.makeIndexedWires "rvvi_insn_0" 32
  let rvvi_insn_1     := CPU.makeIndexedWires "rvvi_insn_1" 32
  let rvvi_rd_0       := CPU.makeIndexedWires "rvvi_rd_0" 5
  let rvvi_rd_1       := CPU.makeIndexedWires "rvvi_rd_1" 5
  let rvvi_rd_data_0  := CPU.makeIndexedWires "rvvi_rdd_0" (if config.xlen == 64 then 64 else 32)
  let rvvi_rd_data_1  := CPU.makeIndexedWires "rvvi_rdd_1" (if config.xlen == 64 then 64 else 32)

  -- PC Queue (dual-port: 2 writes at dispatch, 2 reads at commit)
  -- Use intermediate wires for queue output so we can MUX with CSR PC for RVVI
  let rob_pc_0 := CPU.makeIndexedWires "rob_pc_0" 32
  let rob_pc_1 := CPU.makeIndexedWires "rob_pc_1" 32
  let pc_queue_inst : CircuitInstance := {
    moduleName := "Queue16x32_DualPort"
    instName := "u_pc_queue"
    portMap :=
      [("clock", clock), ("reset", reset),
       ("wr_en_0", dispatch_base_valid_0), ("wr_en_1", dispatch_base_valid_1)] ++
      bundledPorts "wr_idx_0" rob_alloc_idx_0 ++ bundledPorts "wr_data_0" fetch_pc_0 ++
      bundledPorts "wr_idx_1" rob_alloc_idx_1 ++ bundledPorts "wr_data_1" fetch_pc_1 ++
      bundledPorts "rd_idx_0" rob_head_idx_0 ++ bundledPorts "rd_idx_1" rob_head_idx_1 ++
      bundledPorts "rd_data_0" rob_pc_0 ++ bundledPorts "rd_data_1" rob_pc_1
  }

  -- Instruction Queue (dual-port: stores raw instruction words)
  let rob_insn_0 := CPU.makeIndexedWires "rob_insn_0" 32
  let rob_insn_1 := CPU.makeIndexedWires "rob_insn_1" 32
  let insn_queue_inst : CircuitInstance := {
    moduleName := "Queue16x32_DualPort"
    instName := "u_insn_queue"
    portMap :=
      [("clock", clock), ("reset", reset),
       ("wr_en_0", dispatch_base_valid_0), ("wr_en_1", dispatch_base_valid_1)] ++
      bundledPorts "wr_idx_0" rob_alloc_idx_0 ++ bundledPorts "wr_data_0" imem_resp_data_0 ++
      bundledPorts "wr_idx_1" rob_alloc_idx_1 ++ bundledPorts "wr_data_1" imem_resp_data_1 ++
      bundledPorts "rd_idx_0" rob_head_idx_0 ++ bundledPorts "rd_idx_1" rob_head_idx_1 ++
      bundledPorts "rd_data_0" rob_insn_0 ++ bundledPorts "rd_data_1" rob_insn_1
  }

  -- RVVI output gates
  -- CSR retire: csr_drain_complete fires for ALL CSR instructions (including rd=x0).
  -- To avoid timing conflict with the last ROB retire on slot 0 (which can happen
  -- on the same cycle as drain_complete), emit the CSR RVVI on SLOT 1.
  -- At drain_complete, ROB is empty so retire_valid_1=0, no conflict.
  let csr_rd_nonzero_w := Wire.mk "csr_rd_nonzero"  -- already defined above
  let rvvi_gates :=
    (if config.enableZicsr then
      [Gate.mkBUF retire_valid_0 rvvi_valid_0,
       -- rvvi_valid_1 = retire_valid_1 OR csr_drain_complete
       Gate.mkOR retire_valid_1 csr_drain_complete rvvi_valid_1,
       -- trap: CSR retires are not traps
       Gate.mkAND rob_head_exception_0 retire_valid_0 rvvi_trap_0,
       Gate.mkAND rob_head_exception_1 retire_valid_1 rvvi_trap_1,
       -- slot 0 rd_valid: normal ROB path
       Gate.mkNOT rob_head_isBranch_0 (Wire.mk "not_isBr_0"),
       Gate.mkAND rob_head_hasPhysRd_0 (Wire.mk "not_isBr_0") (Wire.mk "hasRealRd_0"),
       Gate.mkAND (Wire.mk "hasRealRd_0") retire_valid_0 rvvi_rd_valid_0,
       -- slot 1 rd_valid: MUX(ROB, CSR, csr_drain_complete)
       Gate.mkNOT rob_head_isBranch_1 (Wire.mk "not_isBr_1"),
       Gate.mkAND rob_head_hasPhysRd_1 (Wire.mk "not_isBr_1") (Wire.mk "hasRealRd_1"),
       Gate.mkAND (Wire.mk "hasRealRd_1") retire_valid_1 (Wire.mk "rob_rd_valid_1"),
       Gate.mkAND csr_rd_nonzero_w csr_drain_complete (Wire.mk "csr_rd_valid_1"),
       Gate.mkOR (Wire.mk "rob_rd_valid_1") (Wire.mk "csr_rd_valid_1") rvvi_rd_valid_1] ++
      -- slot 0: unchanged
      (List.range 5).map (fun i => Gate.mkBUF commit_archRd_0[i]! rvvi_rd_0[i]!) ++
      (List.range (if config.xlen == 64 then 64 else 32)).map (fun i => Gate.mkBUF prf_rvvi_data_0[i]! rvvi_rd_data_0[i]!) ++
      -- slot 1 rd = MUX(commit_archRd_1, csr_rd_reg, csr_drain_complete)
      (List.range 5).map (fun i =>
        Gate.mkMUX commit_archRd_1[i]! csr_rd_reg[i]! csr_drain_complete rvvi_rd_1[i]!) ++
      -- slot 1 rd_data = MUX(prf_data_1, csr_cdb_data, csr_drain_complete)
      (List.range 32).map (fun i =>
        Gate.mkMUX prf_rvvi_data_1[i]! csr_cdb_data[i]! csr_drain_complete rvvi_rd_data_1[i]!) ++
      (if config.xlen == 64 then
        (List.range 32).map (fun i =>
          Gate.mkMUX prf_rvvi_data_1[32+i]! csr_cdb_data[32+i]! csr_drain_complete rvvi_rd_data_1[32+i]!)
       else [])
    else
      [Gate.mkBUF retire_valid_0 rvvi_valid_0,
       Gate.mkBUF retire_valid_1 rvvi_valid_1,
       Gate.mkAND rob_head_exception_0 retire_valid_0 rvvi_trap_0,
       Gate.mkAND rob_head_exception_1 retire_valid_1 rvvi_trap_1,
       Gate.mkNOT rob_head_isBranch_0 (Wire.mk "not_isBr_0"),
       Gate.mkAND rob_head_hasPhysRd_0 (Wire.mk "not_isBr_0") (Wire.mk "hasRealRd_0"),
       Gate.mkAND (Wire.mk "hasRealRd_0") retire_valid_0 rvvi_rd_valid_0,
       Gate.mkNOT rob_head_isBranch_1 (Wire.mk "not_isBr_1"),
       Gate.mkAND rob_head_hasPhysRd_1 (Wire.mk "not_isBr_1") (Wire.mk "hasRealRd_1"),
       Gate.mkAND (Wire.mk "hasRealRd_1") retire_valid_1 rvvi_rd_valid_1] ++
      (List.range 5).map (fun i => Gate.mkBUF commit_archRd_0[i]! rvvi_rd_0[i]!) ++
      (List.range 5).map (fun i => Gate.mkBUF commit_archRd_1[i]! rvvi_rd_1[i]!) ++
      (List.range (if config.xlen == 64 then 64 else 32)).map (fun i => Gate.mkBUF prf_rvvi_data_0[i]! rvvi_rd_data_0[i]!) ++
      (List.range (if config.xlen == 64 then 64 else 32)).map (fun i => Gate.mkBUF prf_rvvi_data_1[i]! rvvi_rd_data_1[i]!))

  -- RVVI PC/insn: MUX queue output with CSR captured data
  -- CSR RVVI is emitted on slot 1 to avoid conflict with last ROB retire on slot 0
  let rvvi_pc_insn_gates :=
    if config.enableZicsr then
      (List.range 32).map (fun i => Gate.mkBUF rob_pc_0[i]! rvvi_pc_rdata_0[i]!) ++
      -- rvvi_pc_1 = MUX(rob_pc_1, csr_pc_reg, csr_drain_complete)
      (List.range 32).map (fun i =>
        Gate.mkMUX rob_pc_1[i]! csr_pc_reg[i]! csr_drain_complete rvvi_pc_rdata_1[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF rob_insn_0[i]! rvvi_insn_0[i]!) ++
      -- rvvi_insn_1 = MUX(rob_insn_1, csr_insn_reg, csr_drain_complete)
      (List.range 32).map (fun i =>
        Gate.mkMUX rob_insn_1[i]! csr_insn_reg[i]! csr_drain_complete rvvi_insn_1[i]!)
    else
      (List.range 32).map (fun i => Gate.mkBUF rob_pc_0[i]! rvvi_pc_rdata_0[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF rob_pc_1[i]! rvvi_pc_rdata_1[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF rob_insn_0[i]! rvvi_insn_0[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF rob_insn_1[i]! rvvi_insn_1[i]!)

  -- === OUTPUT BUFFERS ===
  let global_stall_out := Wire.mk "global_stall_out"
  let output_gates := [Gate.mkBUF global_stall global_stall_out]

  -- === Assemble ===
  { name := s!"CPU_{config.isaString}"
    inputs := [clock, reset, zero, one, fetch_stall_ext, ifetch_last_word, dmem_stall_ext] ++
              imem_resp_data_0 ++ imem_resp_data_1 ++
              [dmem_req_ready, dmem_resp_valid] ++ dmem_resp_data ++
              [Wire.mk "mtip_in"]
    outputs := fetch_pc_0 ++ [fetch_stalled, global_stall_out] ++
               [dmem_req_valid, dmem_req_we] ++ dmem_req_addr ++ dmem_req_data ++ dmem_req_size ++
               [rob_empty] ++
               [rvvi_valid_0, rvvi_valid_1,
                rvvi_trap_0, rvvi_trap_1,
                rvvi_rd_valid_0, rvvi_rd_valid_1] ++
               rvvi_pc_rdata_0 ++ rvvi_pc_rdata_1 ++
               rvvi_insn_0 ++ rvvi_insn_1 ++
               rvvi_rd_0 ++ rvvi_rd_1 ++
               rvvi_rd_data_0 ++ rvvi_rd_data_1
    gates := flush_gate ++ fetch_stall_gates ++ fetch_valid_gates ++ dispatch_gates ++ has_rd_int_gates ++ rd_nox0_gates ++ rob_hasPhysRd_gates ++
             dual_stall_gates ++ int_de1_gates ++ br_route_gates ++ mem_route_gates ++ muldiv_route_gates ++
             src2_imm_mux_gates ++
             rob_physRd_mux_gates ++ rob_old_phys_mux_gates ++ fp_route_gates ++ fp_mux_data_gates ++
             br_mux_data_gates ++ mem_mux_data_gates ++ md_mux_data_gates ++
             suppress_gates ++ dest_tag_mask_gates ++ commit_gates ++ branch_tracking_gates ++ int_commit_fp_gate ++ branch_resolve_gates ++ branch_redirect_target_mux_gates ++
             shadow_gates ++ commit_store_gate ++
             int_pc_rf_gates ++ int_imm_rf_gates ++
             br_pc_rf_gates ++ br_imm_rf_gates ++
             br_pred_dec_gates ++ [br_pred_mux_gate] ++ br_pred_rf_gates ++ br_pred_sel_gates ++
             alu_lut_gates0 ++ alu_lut_gates1 ++
             lui_match_gates_0 ++ auipc_match_gates_0 ++ lui_auipc_gates_0 ++
             lui_match_gates_1 ++ auipc_match_gates_1 ++ lui_auipc_gates_1 ++
             jal_match_gates ++ jalr_match_gates ++ jal_jalr_gates ++
             branch_result_mux ++ jalr_target_gates ++ target_sel_gates ++
             beq_match ++ bne_match ++ blt_match ++ bge_match ++ bltu_match ++ bgeu_match ++
             branch_cond_gates ++ misprediction_gates ++ mispredict_redirect_gates ++
             muldiv_lut_gates ++ muldiv_dispatch_gate ++
             imm_rf_gates ++
             flw_match_gates ++ fsw_match_gates ++
             fld_match_gates ++ fsd_match_gates ++ is_fp_load_gate ++
             ld_match_gates ++ lwu_match_gates ++ sd_match_gates ++
             lw_match_gates ++ lh_match_gates ++ lhu_match_gates ++ lb_match_gates ++ lbu_match_gates ++ is_load_gates ++
             sw_match_gates ++ sh_match_gates ++ sb_match_gates ++ mem_size_gates ++
             mem_pipe_gates ++ sb_enq_size_gates ++ store_mask_gates ++
             sb_enq_gate_gates ++ mem_store_dispatch_en_gates ++ mem_dispatch_en_gates ++ cross_size_pending_gates ++
             fwd_size_check_gates ++ load_no_fwd_gates ++ dmem_pending_gates ++ dmem_tag_capture_gates ++
             dmem_is_fp_gates ++
             lsu_sb_fwd_format_all ++ load_fwd_gates ++ lsu_tag_data_gates ++ sc_lsu_data_gates ++
             lr_match_gates ++ sc_match_gates ++ amo_match_gates ++ atomic_d_match_gates ++ amo_funct_gates ++ atomic_read_gates ++ atomic_gates ++
             lsu_is_fp_gates ++ lsu_is_double_gates ++
             dmem_meta_capture_gates ++ dmem_resp_format_all ++ dmem_valid_gate_gates ++
             ib0_fifo_enq_assemble ++ ib1_merge_gates ++ ib1_fifo_enq_assemble ++
             ib_br_fifo_enq_assemble ++ ib1_br_merge_gates ++ ib1_br_drain_gates ++
             lsu_fifo_enq_assemble ++ muldiv_fifo_enq_assemble ++
             fp_fifo_enq_assemble ++ fp_enq_is_fp_gate ++ fp_stale_gates ++
             fp_fifo_dummy_gates ++ muldiv_fifo_dummy_gates ++
             fp_cdb_merge_gates ++ fp_int_prf_gate ++ fp_commit_gates ++ fp_commit_merge_gates ++ fp_redirect_gate ++
             fp_rename_buf_gates ++ fp_dest_tag_gates ++ fp_crossdomain_gates ++
             [fp_busy_set_gate] ++ fp_busy_stub_gates ++ fp_src3_busy_gates ++ fp_raw_bypass_gates ++ fp_ready_gates ++ fp_cdb_fwd_gates ++ crossdomain_stall_gates ++
             fpu_lut_gates ++ fp_rs_dispatch_gate ++ fp_rs_cdb_gates ++ fp_supp_gates ++
             fp_src3_alloc_decode ++ fp_src3_alloc_cdb_gates ++ fp_src3_cdb_data_mux ++ fp_src3_dff_gates ++ fp_src3_read_gates ++
             rm_resolve_gates ++ fp_rm_alloc_decode ++ fp_rm_dff_gates ++ fp_rm_read_gates ++
             fp_op_gates ++ fp_flush_reset_gates ++
             rs_full_gates ++ clb_gates ++ stall_gates ++ dmem_gates ++ rvvi_gates ++ rvvi_pc_insn_gates ++ output_gates ++
             fi_match_0 ++ fi_match_1 ++
             ecall_m0 ++ ecall_m1 ++
             mret_m0 ++ mret_m1 ++ wfi_m0 ++ wfi_m1 ++
             csrrw_m0 ++ csrrs_m0 ++ csrrc_m0 ++ csrrwi_m0 ++ csrrsi_m0 ++ csrrci_m0 ++
             csrrw_m1 ++ csrrs_m1 ++ csrrc_m1 ++ csrrwi_m1 ++ csrrsi_m1 ++ csrrci_m1 ++
             cdb_tag_nz_gates ++
             csr_detect_gates ++ ser_detect_gates ++ ser_fsm_gates ++
             ser_pc_mux_gates ++ cdb_fwd_rs1_gates ++ ser_capture_gates ++
             trap_rom_gates ++
             csr_all_gates ++
             [sb_alloc_inc_gate] ++ sb_alloc_inc_gates ++ [sb_inc_xor2_gate] ++
             sb_alloc_mux_gates ++ sb_alloc_next_gates ++
             sb_sc_we_gates ++ sb_sc_rf_gates ++ sb_sc_read_gates
    instances := [fetch_inst, dec0_inst, dec1_inst, rename_inst,
                  rs_int_inst, rs_br_inst, rs_mem_inst] ++
                 (if enableM then [rs_muldiv_inst] else []) ++
                 (if enableF then [rs_fp_inst, fp_rename_inst, fp_exec_inst] else []) ++
                 fpu_lut_inst ++
                 [alu_lut_inst0, alu_lut_inst1, exec_inst, auipc_adder_0_inst, auipc_adder_1_inst,
                  branch_exec_inst, br_pc_plus_4_adder, br_target_adder, jalr_target_adder, br_cmp_inst,
                  mem_exec_inst] ++
                 (if enableM then [muldiv_exec_inst] ++ muldiv_lut_inst else []) ++
                 [rob_inst, lsu_inst] ++
                 atomic_insts ++ amo_lut_inst ++
                 [redirect_valid_dff_inst, flush_dff_dispatch] ++
                 flush_dff_insts ++ flush_busy_dff_insts ++
                 redirect_target_dff_insts ++
                 [busy_inst] ++ fp_busy_instances ++ fp_cdb_fwd_instances ++
                 [ib0_fifo_inst, ib1_fifo_inst, ib_br_fifo_inst, lsu_fifo_inst] ++
                 (if enableM then [muldiv_fifo_inst] else []) ++
                 (if enableF then [fp_fifo_inst] else []) ++
                 [cdb_mux_inst] ++ cdb_reg_insts ++ cdb_redirect_reg_insts ++
                 shadow_insts ++
                 [dmem_pending_inst, cross_size_pending_inst] ++ dmem_tag_capture_insts ++ dmem_is_fp_insts ++ dmem_meta_capture_insts ++
                 mem_pipe_insts ++
                 ser_dff_insts ++ [ser_pc_adder_inst] ++
                 trap_seq_insts ++ cdb_fwd_rs1_insts ++
                 [pc_queue_inst, insn_queue_inst, csr_inst] ++
                 commit_store_pending_dffs ++
                 sb_alloc_ctr_dffs
  }

end Shoumei.RISCV.CPU_W2
