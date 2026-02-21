/-
Top-Level CPU Integration - RV32I/RV32IM Tomasulo Processor

Integrates all 77 verified pipeline components into a complete, working CPU.
Supports configurable ISA extensions (M enable/disable via CPUConfig).

Pipeline Stages (7 stages + memory):
1. Fetch - PC management, instruction memory
2. Decode - Instruction decode (RV32I or RV32IM based on config)
3. Rename - RAT + FreeList + PhysRegFile
4. Issue - Dispatch to appropriate Reservation Station
5. Execute - Execution units + CDB broadcast
6. Writeback - CDB snooping by RS and ROB
7. Commit - ROB in-order retirement

RVVI Infrastructure (Phase 8):
- PC queue and instruction queue track retirement info alongside ROB
- Prepared for future lock-step cosimulation with Spike
- See docs/cosimulation.md for details

Phase 8 scope: Behavioral model only. Structural circuit TBD.
-/

import Shoumei.RISCV.Config
import Shoumei.RISCV.CPUBehavioral
import Shoumei.RISCV.CPUCircuitHelpers
import Shoumei.RISCV.CPUHelpers
import Shoumei.DSL
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Sequential.Register

namespace Shoumei.RISCV.CPU

open Shoumei.RISCV
open Shoumei
open Shoumei.Circuits.Combinational
open Shoumei.Circuits.Sequential

section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def mkCPU (config : CPUConfig) : Circuit :=
  let enableM := config.enableM
  let enableF := config.enableF
  let enableVector := config.enableVector
  let sbFwdPipelined := config.sbFwdPipelineStages > 0
  let oi := config.opcodeIndex
  -- Opcode width: 7 bits when F extension (>64 instructions), 6 bits otherwise
  let opcodeWidth := if enableF then 7 else 6
  -- Global signals
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- === EXTERNAL INTERFACES ===
  let fetch_stall_ext := Wire.mk "fetch_stall_ext"
  let dmem_stall_ext := Wire.mk "dmem_stall_ext"
  let imem_resp_data := makeIndexedWires "imem_resp_data" 32
  let dmem_req_ready := Wire.mk "dmem_req_ready"
  let dmem_resp_valid := Wire.mk "dmem_resp_valid"
  let dmem_resp_data := makeIndexedWires "dmem_resp_data" 32

  -- === DECODER OUTPUTS (internal, driven by decoder instance) ===
  let decode_optype := makeIndexedWires "decode_optype" opcodeWidth
  let decode_rd := makeIndexedWires "decode_rd" 5
  let decode_rs1 := makeIndexedWires "decode_rs1" 5
  let decode_rs2 := makeIndexedWires "decode_rs2" 5
  let decode_imm := makeIndexedWires "decode_imm" 32
  let decode_valid_scalar := Wire.mk "decode_valid_scalar"
  let decode_valid := Wire.mk "decode_valid"
  let decode_has_rd := Wire.mk "decode_has_rd"
  let dispatch_is_integer := Wire.mk "dispatch_is_integer"
  let dispatch_is_memory := Wire.mk "dispatch_is_memory"
  let dispatch_is_scalar_memory := Wire.mk "dispatch_is_scalar_memory"
  let dispatch_is_branch := Wire.mk "dispatch_is_branch"
  let dispatch_is_muldiv := Wire.mk "dispatch_is_muldiv"
  let dispatch_is_store := Wire.mk "dispatch_is_store"
  let decode_use_imm := Wire.mk "decode_use_imm"

  -- FP decoder outputs (only used when enableF)
  let decode_rs3 := makeIndexedWires "decode_rs3" 5
  let decode_rm := makeIndexedWires "decode_rm" 3
  let dispatch_is_fp := Wire.mk "dispatch_is_fp"
  let decode_has_fp_rd := Wire.mk "decode_has_fp_rd"
  let decode_fp_rs1_read := Wire.mk "decode_fp_rs1_read"
  let decode_fp_rs2_read := Wire.mk "decode_fp_rs2_read"
  let decode_fp_rs3_used := Wire.mk "decode_fp_rs3_used"
  let dispatch_is_fp_load := Wire.mk "dispatch_is_fp_load"
  let dispatch_is_fp_store := Wire.mk "dispatch_is_fp_store"

  -- Vector decoder outputs (only used when enableVector)
  let dispatch_is_vector := Wire.mk "dispatch_is_vector"
  -- Vector dispatch signals
  let dispatch_vector_valid := Wire.mk "dispatch_vector_valid"
  -- RvvCore interface wires
  let rvv_rstn := Wire.mk "rvv_rstn"  -- active-low reset for RvvCore
  let rvv_inst_ready := Wire.mk "rvv_inst_ready"
  let rvv_inst_valid := Wire.mk "rvv_inst_valid"
  -- RVVInstruction bits: pc[31:0] + opcode[1:0] + bits[24:0] = 59 bits
  -- We pack instruction bits[31:7] = 25 bits for the RvvCore
  let rvv_inst_bits := makeIndexedWires "rvv_inst_bits" 25
  let rvv_opcode := makeIndexedWires "rvv_opcode" 2
  -- Async scalar writeback from RvvCore (vmv.x.s etc.)
  let rvv_async_rd_valid := Wire.mk "rvv_async_rd_valid"
  let rvv_async_rd_addr := makeIndexedWires "rvv_async_rd_addr" 5
  let rvv_async_rd_data := makeIndexedWires "rvv_async_rd_data" 32
  let rvv_async_rd_ready := Wire.mk "rvv_async_rd_ready"
  -- Synchronous scalar writeback (vsetvl config ops)
  let rvv_reg_write_valid := Wire.mk "rvv_reg_write_valid"
  let rvv_reg_write_addr := makeIndexedWires "rvv_reg_write_addr" 5
  let rvv_reg_write_data := makeIndexedWires "rvv_reg_write_data" 32
  -- RvvCore status signals
  let rvv_idle := Wire.mk "rvv_idle"
  let rvv_queue_capacity := makeIndexedWires "rvv_queue_cap" 4  -- $clog2(2*4+1) = 4 bits
  let rvv_trap_valid := Wire.mk "rvv_trap_valid"
  -- Vector CSR state wires (declared early for RvvCore portMap)
  let vstart_reg := (List.range 7).map (fun i => Wire.mk s!"vstart_e{i}")
  let vstart_next := (List.range 7).map (fun i => Wire.mk s!"vstart_nx_e{i}")
  let vxrm_reg := (List.range 2).map (fun i => Wire.mk s!"vxrm_e{i}")
  let vxrm_next := (List.range 2).map (fun i => Wire.mk s!"vxrm_nx_e{i}")
  let vxsat_reg := [Wire.mk "vxsat_e0"]
  let vxsat_next := [Wire.mk "vxsat_nx_e0"]
  let rvv_config_vl := (List.range 32).map (fun i => Wire.mk s!"rvv_cfg_vl_e{i}")
  let rvv_config_vtype := (List.range 32).map (fun i => Wire.mk s!"rvv_cfg_vtype_e{i}")
  let rvv_wr_vxsat_valid := Wire.mk "rvv_wr_vxsat_valid"
  let rvv_wr_vxsat := Wire.mk "rvv_wr_vxsat"
  -- Vector DMEM port (exposed as CPU I/O for external memory connection)
  let vec_dmem_req_ready := Wire.mk "vec_dmem_req_ready"
  let vec_dmem_resp_valid := Wire.mk "vec_dmem_resp_valid"
  let vec_dmem_resp_rdata := makeIndexedWires "vec_dmem_resp_rdata" 32
  let vec_dmem_req_valid := Wire.mk "vec_dmem_req_valid"
  let vec_dmem_req_we := Wire.mk "vec_dmem_req_we"
  let vec_dmem_req_addr := makeIndexedWires "vec_dmem_req_addr" 32
  let vec_dmem_req_data := makeIndexedWires "vec_dmem_req_data" 32
  let vec_dmem_req_size := makeIndexedWires "vec_dmem_req_size" 2
  -- RvvCore ↔ VecLsu interface wires (slot 0 only)
  let rvv_lsu_valid_rvv2lsu := Wire.mk "rvv_lsu_valid_rvv2lsu"
  let rvv_lsu_idx_valid_rvv2lsu := Wire.mk "rvv_lsu_idx_valid_rvv2lsu"
  let rvv_lsu_idx_data_rvv2lsu := makeIndexedWires "rvv_lsu_idx_data_rvv2lsu" 128
  let rvv_lsu_vregfile_valid_rvv2lsu := Wire.mk "rvv_lsu_vregfile_valid_rvv2lsu"
  let rvv_lsu_vregfile_data_rvv2lsu := makeIndexedWires "rvv_lsu_vregfile_data_rvv2lsu" 128
  let rvv_lsu_v0_valid_rvv2lsu := Wire.mk "rvv_lsu_v0_valid_rvv2lsu"
  let rvv_lsu_v0_data_rvv2lsu := makeIndexedWires "rvv_lsu_v0_data_rvv2lsu" 16
  let rvv_lsu_ready_rvv2lsu := Wire.mk "rvv_lsu_ready_rvv2lsu"
  let rvv_lsu_vd_addr_rvv2lsu := makeIndexedWires "rvv_lsu_vd_addr_rvv2lsu" 5
  let rvv_lsu_is_store_rvv2lsu := Wire.mk "rvv_lsu_is_store_rvv2lsu"
  -- VecLsu → RvvCore (lsu2rvv) wires
  let rvv_lsu_valid_lsu2rvv := Wire.mk "rvv_lsu_valid_lsu2rvv"
  let rvv_lsu_data_lsu2rvv := makeIndexedWires "rvv_lsu_data_lsu2rvv" 128
  let rvv_lsu_addr_lsu2rvv := makeIndexedWires "rvv_lsu_addr_lsu2rvv" 5
  let rvv_lsu_last_lsu2rvv := Wire.mk "rvv_lsu_last_lsu2rvv"
  let rvv_lsu_ready_lsu2rvv := Wire.mk "rvv_lsu_ready_lsu2rvv"
  -- Vector: force ROB auto-complete for all vector instructions
  let not_dispatch_is_vector := Wire.mk "not_dispatch_is_vector"
  -- Vector load/store dispatch detection
  let dispatch_is_vector_mem := Wire.mk "dispatch_is_vector_mem"
  -- Base address + stride sidecar registers
  let rvv_base_addr_reg := makeIndexedWires "rvv_base_addr_e" 32
  let rvv_base_addr_next := makeIndexedWires "rvv_base_addr_nx" 32
  let rvv_stride_reg := makeIndexedWires "rvv_stride_e" 32
  let rvv_stride_next := makeIndexedWires "rvv_stride_nx" 32
  -- EEW sidecar (from funct3 at dispatch)
  let rvv_eew_reg := makeIndexedWires "rvv_eew_e" 2
  let rvv_eew_next := makeIndexedWires "rvv_eew_nx" 2
  -- Has-stride flag sidecar
  let rvv_has_stride_reg := Wire.mk "rvv_has_stride_e"
  let rvv_has_stride_next := Wire.mk "rvv_has_stride_nx"
  -- Is-store sidecar (must be registered, not combinational, because RvvCore
  -- dispatches uops to VecLsu several cycles after CPU dispatch)
  let rvv_is_store_reg := Wire.mk "rvv_is_store_e"
  let rvv_is_store_next := Wire.mk "rvv_is_store_nx"

  let decode_has_any_rd := Wire.mk "decode_has_any_rd"
  let decode_rd_nonzero := Wire.mk "decode_rd_nonzero"
  let decode_has_rd_nox0 := Wire.mk "decode_has_rd_nox0"
  let decode_has_any_rd_nox0 := Wire.mk "decode_has_any_rd_nox0"

  -- Forward-declare FP wires needed by INT rename and cross-domain logic
  let cdb_is_fp_rd := Wire.mk "cdb_is_fp_rd"
  let cdb_valid_int_prf := Wire.mk "cdb_valid_int_prf"
  let cdb_valid_fp_prf := Wire.mk "cdb_valid_fp_prf"
  let not_cdb_is_fp := Wire.mk "not_cdb_is_fp"
  let int_retire_valid := Wire.mk "int_retire_valid"
  let fp_retire_recycle_valid := Wire.mk "fp_retire_recycle_valid"
  let rob_old_phys_muxed := makeIndexedWires "rob_old_phys_muxed" 6

  -- === FETCH STAGE ===
  let fetch_pc := makeIndexedWires "fetch_pc" 32
  let fetch_stalled := Wire.mk "fetch_stalled"
  let global_stall := Wire.mk "global_stall"
  let branch_redirect_target := makeIndexedWires "branch_redirect_target" 32

  let branch_redirect_valid_reg := Wire.mk "branch_redirect_valid_reg"
  let pipeline_flush_comb := Wire.mk "pipeline_flush_comb"
  let pipeline_flush := Wire.mk "pipeline_flush"
  -- Per-subsystem flush registers
  let flush_rs_int := Wire.mk "flush_rs_int"
  let flush_rs_mem := Wire.mk "flush_rs_mem"
  let flush_rs_br := Wire.mk "flush_rs_br"
  let flush_rs_muldiv := Wire.mk "flush_rs_muldiv"
  let flush_rob := Wire.mk "flush_rob"
  -- 8 replicated flush DFFs for busy bits (prevents Yosys from merging into single high-fanout net)
  let flush_busy_groups := (List.range 8).map fun g => Wire.mk s!"flush_busy_g{g}"
  let flush_misc := Wire.mk "flush_misc"
  let flush_rs_fp := Wire.mk "flush_rs_fp"
  let pipeline_reset_rs_int := Wire.mk "pipeline_reset_rs_int"
  let pipeline_reset_rs_mem := Wire.mk "pipeline_reset_rs_mem"
  let pipeline_reset_rs_br := Wire.mk "pipeline_reset_rs_br"
  let pipeline_reset_rs_muldiv := Wire.mk "pipeline_reset_rs_muldiv"
  let pipeline_reset_rs_fp := Wire.mk "pipeline_reset_rs_fp"
  let pipeline_reset_rob := Wire.mk "pipeline_reset_rob"
  let pipeline_reset_busy := Wire.mk "pipeline_reset_busy"
  let pipeline_reset_misc := Wire.mk "pipeline_reset_misc"
  let fetch_stall := Wire.mk "fetch_stall"
  let rob_redirect_valid := Wire.mk "rob_redirect_valid"
  -- === SERIALIZE FSM (FENCE.I + CSR) ===
  let fence_i_detected := Wire.mk "fence_i_detected"
  let fence_i_draining := Wire.mk "fence_i_draining"
  let fence_i_draining_next := Wire.mk "fence_i_draining_next"
  let fence_i_start := Wire.mk "fence_i_start"
  let fence_i_drain_complete := Wire.mk "fence_i_drain_complete"
  let fence_i_suppress := Wire.mk "fence_i_suppress"
  let fence_i_not_draining := Wire.mk "fence_i_not_draining"
  let fence_i_redir_target := (List.range 32).map (fun i => Wire.mk s!"fencei_redir_e{i}")
  let fence_i_redir_next := (List.range 32).map (fun i => Wire.mk s!"fencei_rnxt_e{i}")
  -- CSR serialize wires
  let csr_detected := Wire.mk "csr_detected"
  let csr_match := Wire.mk "csr_match"
  let serialize_detected := Wire.mk "serialize_detected"
  -- CSR flag register: distinguishes CSR drain from FENCE.I drain
  let csr_flag_reg := Wire.mk "csr_flag_reg"
  let csr_flag_next := Wire.mk "csr_flag_next"
  -- CSR capture registers (captured at serialize_start)
  let csr_addr_reg := (List.range 12).map (fun i => Wire.mk s!"csr_addr_e{i}")
  let csr_addr_next := (List.range 12).map (fun i => Wire.mk s!"csr_anxt_e{i}")
  let csr_optype_reg := (List.range opcodeWidth).map (fun i => Wire.mk s!"csr_opty_e{i}")
  let csr_optype_next := (List.range opcodeWidth).map (fun i => Wire.mk s!"csr_onxt_e{i}")
  let csr_rd_reg := (List.range 5).map (fun i => Wire.mk s!"csr_rdcap_e{i}")
  let csr_rd_next := (List.range 5).map (fun i => Wire.mk s!"csr_rdnx_e{i}")
  -- Captured rd_phys (newly allocated phys reg from rename, 6-bit)
  let csr_phys_reg := (List.range 6).map (fun i => Wire.mk s!"csr_phcap_e{i}")
  let csr_phys_next := (List.range 6).map (fun i => Wire.mk s!"csr_phnxt_e{i}")
  -- CSR rs1 data capture (32 bits, captured at serialize_start for CSR write source)
  let csr_rs1cap_reg := (List.range 32).map (fun i => Wire.mk s!"csr_r1c_e{i}")
  let csr_rs1cap_next := (List.range 32).map (fun i => Wire.mk s!"csr_r1n_e{i}")
  -- CSR zimm capture (5 bits, rs1 field used as immediate for CSRRWI/CSRRSI/CSRRCI)
  let csr_zimm_reg := (List.range 5).map (fun i => Wire.mk s!"csr_zmc_e{i}")
  let csr_zimm_next := (List.range 5).map (fun i => Wire.mk s!"csr_zmn_e{i}")
  -- CSR rename gating wires
  let csr_rename_en := Wire.mk "csr_rename_en"
  let not_csr_rename_en := Wire.mk "not_csr_rename_en"
  -- MUXed commit signals for CSR commit injection
  let rename_valid_gated := Wire.mk "rename_valid_gated"
  let commit_valid_muxed := Wire.mk "commit_valid_muxed"
  let commit_archRd_muxed := (List.range 5).map (fun i => Wire.mk s!"cmt_ard_m{i}")
  let commit_physRd_muxed := (List.range 6).map (fun i => Wire.mk s!"cmt_prd_m{i}")
  let commit_hasPhysRd_muxed := Wire.mk "cmt_hasrd_m"
  let commit_hasAllocSlot_muxed := Wire.mk "cmt_hasas_m"
  -- CSR flush suppression: suppress RenameStage flush_en on CSR redirect cycle
  -- so speculative RAT keeps the CSR's rd mapping (pipeline is drained, no need to flush)
  let csr_flush_suppress := Wire.mk "csr_flush_sup"
  let not_csr_flush_suppress := Wire.mk "not_csr_fsup"
  let rename_flush_en := Wire.mk "rename_flush_en"
  -- fetch_pc + 4 for FENCE.I redirect target
  let fence_i_pc_plus_4 := makeIndexedWires "fencei_pcp4" 32
  let fence_i_const_4 := (List.range 32).map (fun i => Wire.mk s!"fencei_c4_e{i}")
  let fence_i_const_4_gates := (List.range 32).map (fun i =>
    if i == 2 then Gate.mkBUF one fence_i_const_4[i]!
    else Gate.mkBUF zero fence_i_const_4[i]!)
  let fence_i_adder_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32"
    instName := "u_fencei_pc_plus_4"
    portMap :=
      (fetch_pc.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (fence_i_const_4.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("cin", zero)] ++
      (fence_i_pc_plus_4.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w)))
  }

  let rob_head_isBranch := Wire.mk "rob_head_isBranch"
  let rob_head_mispredicted := Wire.mk "rob_head_mispredicted"
  let rob_head_redirect_target := makeIndexedWires "rob_head_redirect_target" 32
  let retire_tag_muxed := makeIndexedWires "retire_tag_muxed" 6
  let branch_redirect_target_reg := makeIndexedWires "branch_redirect_target_reg" 32
  let redirect_valid_dff_inst : CircuitInstance := {
    moduleName := "DFlipFlop"
    instName := "u_redirect_valid_dff"
    portMap := [("d", rob_redirect_valid), ("q", branch_redirect_valid_reg),
                ("clock", clock), ("reset", reset)]
  }
  -- Replicated redirect_valid DFFs to reduce fanout on FP/INT RAT restore muxes
  let redirect_valid_fp := Wire.mk "redirect_valid_fp"
  let redirect_valid_int := Wire.mk "redirect_valid_int"
  let redirect_valid_fp_dff : CircuitInstance := {
    moduleName := "DFlipFlop"
    instName := "u_redirect_valid_dff_fp"
    portMap := [("d", rob_redirect_valid), ("q", redirect_valid_fp),
                ("clock", clock), ("reset", reset)]
  }
  let redirect_valid_int_dff : CircuitInstance := {
    moduleName := "DFlipFlop"
    instName := "u_redirect_valid_dff_int"
    portMap := [("d", rob_redirect_valid), ("q", redirect_valid_int),
                ("clock", clock), ("reset", reset)]
  }
  let redirect_target_dff_insts : List CircuitInstance := (List.range 32).map (fun i => {
    moduleName := "DFlipFlop"
    instName := s!"u_redirect_target_dff_{i}"
    portMap := [("d", branch_redirect_target[i]!), ("q", branch_redirect_target_reg[i]!),
                ("clock", clock), ("reset", reset)]
  })

  -- FENCE.I FSM DFFs (use `reset`, not pipeline_reset, so they survive flushes)
  let fence_i_draining_dff : CircuitInstance := {
    moduleName := "DFlipFlop"
    instName := "u_fence_i_draining_dff"
    portMap := [("d", fence_i_draining_next), ("q", fence_i_draining),
                ("clock", clock), ("reset", reset)]
  }
  let fence_i_redir_dffs : List CircuitInstance := (List.range 32).map (fun i => {
    moduleName := "DFlipFlop"
    instName := s!"u_fencei_redir_dff_{i}"
    portMap := [("d", fence_i_redir_next[i]!), ("q", fence_i_redir_target[i]!),
                ("clock", clock), ("reset", reset)]
  })

  -- CSR capture DFFs (use `reset`, survive flushes)
  let csr_flag_dff : CircuitInstance := {
    moduleName := "DFlipFlop"
    instName := "u_csr_flag_dff"
    portMap := [("d", csr_flag_next), ("q", csr_flag_reg),
                ("clock", clock), ("reset", reset)]
  }
  let csr_addr_dffs : List CircuitInstance := (List.range 12).map (fun i => {
    moduleName := "DFlipFlop"
    instName := s!"u_csr_addr_dff_{i}"
    portMap := [("d", csr_addr_next[i]!), ("q", csr_addr_reg[i]!),
                ("clock", clock), ("reset", reset)]
  })
  let csr_optype_dffs : List CircuitInstance := (List.range opcodeWidth).map (fun i => {
    moduleName := "DFlipFlop"
    instName := s!"u_csr_optype_dff_{i}"
    portMap := [("d", csr_optype_next[i]!), ("q", csr_optype_reg[i]!),
                ("clock", clock), ("reset", reset)]
  })
  let csr_rd_dffs : List CircuitInstance := (List.range 5).map (fun i => {
    moduleName := "DFlipFlop"
    instName := s!"u_csr_rd_dff_{i}"
    portMap := [("d", csr_rd_next[i]!), ("q", csr_rd_reg[i]!),
                ("clock", clock), ("reset", reset)]
  })
  let csr_phys_dffs : List CircuitInstance := (List.range 6).map (fun i => {
    moduleName := "DFlipFlop"
    instName := s!"u_csr_phys_dff_{i}"
    portMap := [("d", csr_phys_next[i]!), ("q", csr_phys_reg[i]!),
                ("clock", clock), ("reset", reset)]
  })
  let csr_rs1cap_dffs : List CircuitInstance := (List.range 32).map (fun i => {
    moduleName := "DFlipFlop"
    instName := s!"u_csr_rs1cap_dff_{i}"
    portMap := [("d", csr_rs1cap_next[i]!), ("q", csr_rs1cap_reg[i]!),
                ("clock", clock), ("reset", reset)]
  })
  let csr_zimm_dffs : List CircuitInstance := (List.range 5).map (fun i => {
    moduleName := "DFlipFlop"
    instName := s!"u_csr_zimm_dff_{i}"
    portMap := [("d", csr_zimm_next[i]!), ("q", csr_zimm_reg[i]!),
                ("clock", clock), ("reset", reset)]
  })
  -- CSR flush suppress DFF: captures merged_cdb_inject (CSR + RVV vsetvl),
  -- so it's high 1 cycle later (aligned with branch_redirect_valid_reg)
  let csr_flush_suppress_dff : CircuitInstance := {
    moduleName := "DFlipFlop"
    instName := "u_csr_flush_sup"
    portMap := [("d", Wire.mk "merged_cdb_inject"), ("q", csr_flush_suppress),
                ("clock", clock), ("reset", reset)]
  }
  -- Per-subsystem flush DFFs
  let flush_dff_dispatch : CircuitInstance := {
    moduleName := "DFlipFlop"
    instName := "u_flush_dff_dispatch"
    portMap := [("d", pipeline_flush_comb), ("q", pipeline_flush),
                ("clock", clock), ("reset", reset)]
  }
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
  -- 8 replicated flush DFFs for busy bit groups (each drives ~8 DFFs, not 128+)
  let flush_busy_dff_insts : List CircuitInstance := (List.range 8).map (fun g => {
    moduleName := "DFlipFlop"
    instName := s!"u_flush_dff_busy_g{g}"
    portMap := [("d", pipeline_flush_comb), ("q", flush_busy_groups[g]!),
                ("clock", clock), ("reset", reset)]
  })

  let fetch_predicted_taken := Wire.mk "fetch_predicted_taken"

  let fetch_inst : CircuitInstance := {
    moduleName := "FetchStage"
    instName := "u_fetch"
    portMap :=
      [("clock", clock), ("reset", reset),
       ("stall", fetch_stall),
       ("branch_valid", branch_redirect_valid_reg),
       ("const_0", zero), ("const_1", one)] ++
      (branch_redirect_target_reg.enum.map (fun ⟨i, w⟩ => (s!"branch_target_{i}", w))) ++
      (imem_resp_data.enum.map (fun ⟨i, w⟩ => (s!"instr_{i}", w))) ++
      (fetch_pc.enum.map (fun ⟨i, w⟩ => (s!"pc_{i}", w))) ++
      [("stalled_reg", fetch_stalled),
       ("predicted_taken", fetch_predicted_taken)]
  }

  -- === DECODER ===
  let decoderModuleName :=
    if enableF && enableM then "RV32IMFDecoder"
    else if enableF then "RV32IFDecoder"
    else if enableM then "RV32IMDecoder"
    else "RV32IDecoder"
  let decoder_inst : CircuitInstance := {
    moduleName := decoderModuleName
    instName := "u_decoder"
    portMap :=
      (imem_resp_data.enum.map (fun ⟨i, w⟩ => (s!"io_instr_{i}", w))) ++
      (decode_optype.enum.map (fun ⟨i, w⟩ => (s!"io_optype_{i}", w))) ++
      (decode_rd.enum.map (fun ⟨i, w⟩ => (s!"io_rd_{i}", w))) ++
      (decode_rs1.enum.map (fun ⟨i, w⟩ => (s!"io_rs1_{i}", w))) ++
      (decode_rs2.enum.map (fun ⟨i, w⟩ => (s!"io_rs2_{i}", w))) ++
      (decode_imm.enum.map (fun ⟨i, w⟩ => (s!"io_imm_{i}", w))) ++
      [("io_valid", decode_valid_scalar),
       ("io_has_rd", decode_has_rd),
       ("io_is_integer", dispatch_is_integer),
       ("io_is_memory", dispatch_is_memory),
       ("io_is_branch", dispatch_is_branch)] ++
      (if enableM then [("io_is_muldiv", dispatch_is_muldiv)] else []) ++
      [("io_is_store", dispatch_is_store),
       ("io_use_imm", decode_use_imm)] ++
      (if enableF then
        (decode_rs3.enum.map (fun ⟨i, w⟩ => (s!"io_rs3_{i}", w))) ++
        (decode_rm.enum.map (fun ⟨i, w⟩ => (s!"io_rm_{i}", w))) ++
        [("io_is_fp", dispatch_is_fp),
         ("io_has_fp_rd", decode_has_fp_rd),
         ("io_fp_rs1_read", decode_fp_rs1_read),
         ("io_fp_rs2_read", decode_fp_rs2_read),
         ("io_fp_rs3_used", decode_fp_rs3_used),
         ("io_is_fp_load", dispatch_is_fp_load),
         ("io_is_fp_store", dispatch_is_fp_store)]
      else [])
      -- Note: dispatch_is_vector is computed from raw instruction bits in CPU gates,
      -- not from the decoder (since vector instructions aren't in instr_dict.json)
  }

  -- === RENAME STAGE ===
  let rename_valid := Wire.mk "rename_valid"
  let rename_stall := Wire.mk "rename_stall"
  let rs1_phys := makeIndexedWires "rs1_phys" 6
  let rs2_phys := makeIndexedWires "rs2_phys" 6
  let rd_phys := makeIndexedWires "rd_phys" 6
  let old_rd_phys := makeIndexedWires "old_rd_phys" 6
  let rs1_data := makeIndexedWires "rs1_data" 32
  let rs2_data := makeIndexedWires "rs2_data" 32
  let cdb_valid := Wire.mk "cdb_valid"
  let cdb_tag := makeIndexedWires "cdb_tag" 6
  let cdb_data := makeIndexedWires "cdb_data" 32
  -- CDB tag buffer tree: each bit fans out to 15 consumers (2 rename + 2 busy tables + 4 fwd cmps
  -- + 5 RSs + ROB + RVVI + 16 redirect cmps + tag_nz). Split into 4 groups.
  let cdb_tag_int := makeIndexedWires "cdb_tag_int" 6  -- INT rename + busy + fwd + tag_nz
  let cdb_tag_fp := makeIndexedWires "cdb_tag_fp" 6   -- FP rename + busy + fwd
  let cdb_tag_rs := makeIndexedWires "cdb_tag_rs" 6   -- 5 RS instances
  let cdb_tag_rob := makeIndexedWires "cdb_tag_rob" 6 -- ROB + RVVI + redirect cmps
  let cdb_tag_buf_gates := (List.range 6).map (fun i => [
    Gate.mkBUF (cdb_tag[i]!) (cdb_tag_int[i]!),
    Gate.mkBUF (cdb_tag[i]!) (cdb_tag_fp[i]!),
    Gate.mkBUF (cdb_tag[i]!) (cdb_tag_rs[i]!),
    Gate.mkBUF (cdb_tag[i]!) (cdb_tag_rob[i]!)
  ]) |>.flatten
  -- CDB data buffer tree: each bit fans out to 11 consumers (2 PRFs + 2 fwd MUXes + 5 RSs + 2 FP fwd).
  -- Split into 3 groups: INT (PRF write + issue fwd), FP (PRF write + issue fwd), RS (5 stations).
  let cdb_data_int := makeIndexedWires "cdb_data_int" 32
  let cdb_data_fp := makeIndexedWires "cdb_data_fp" 32
  let cdb_data_rs := makeIndexedWires "cdb_data_rs" 32
  let cdb_data_buf_gates := (List.range 32).map (fun i => [
    Gate.mkBUF (cdb_data[i]!) (cdb_data_int[i]!),
    Gate.mkBUF (cdb_data[i]!) (cdb_data_fp[i]!),
    Gate.mkBUF (cdb_data[i]!) (cdb_data_rs[i]!)
  ]) |>.flatten
  -- Domain-gated CDB valid: prevent tag collisions between INT/FP phys reg pools
  let cdb_valid_int_domain := if enableF then Wire.mk "cdb_valid_for_int" else Wire.mk "cdb_valid_nz"
  let cdb_valid_fp_domain := if enableF then Wire.mk "cdb_valid_for_fp" else cdb_valid
  -- Pre-register CDB signals (before pipeline register)
  let cdb_pre_valid := Wire.mk "cdb_pre_valid"
  -- Domain-gated pre-register CDB (wires created in cdb_domain_gates)
  let cdb_pre_tag := makeIndexedWires "cdb_pre_tag" 6
  let cdb_pre_data := makeIndexedWires "cdb_pre_data" 32
  -- Mask CDB valid for PhysRegFile writes: don't write to p0 (x0's home register)
  let cdb_tag_nz_tmp := List.range 5 |>.map (fun i => Wire.mk s!"cdb_tag_nz_t{i}")
  let cdb_tag_nonzero := Wire.mk "cdb_tag_nonzero"
  let cdb_valid_prf := Wire.mk "cdb_valid_prf"
  let cdb_tag_nz_gates :=
    [Gate.mkOR cdb_tag_int[0]! cdb_tag_int[1]! cdb_tag_nz_tmp[0]!] ++
    (List.range 4).map (fun i =>
      Gate.mkOR cdb_tag_nz_tmp[i]! cdb_tag_int[i + 2]! (if i < 3 then cdb_tag_nz_tmp[i + 1]! else cdb_tag_nonzero)) ++
    -- Gate CDB writes to PRF during flush: squashed instructions' CDB broadcasts
    -- must not overwrite pregs that flush recovery will make architecturally live.
    -- Allow CSR CDB inject through (it's the committing instruction, not squashed).
    let cdb_valid_nz_pre := Wire.mk "cdb_valid_nz_pre"
    let not_flushing_prf := Wire.mk "not_flushing_prf"
    let prf_flush_allow := Wire.mk "prf_flush_allow"
    [Gate.mkAND cdb_valid cdb_tag_nonzero cdb_valid_nz_pre,
     Gate.mkNOT pipeline_flush_comb not_flushing_prf] ++
    (if config.enableZicsr then
      -- Use csr_flush_suppress (= DFF(csr_cdb_inject)) since cdb_valid is also registered
      [Gate.mkOR not_flushing_prf csr_flush_suppress prf_flush_allow,
       Gate.mkAND cdb_valid_nz_pre prf_flush_allow cdb_valid_prf]
    else
      [Gate.mkAND cdb_valid_nz_pre not_flushing_prf cdb_valid_prf])

  let rob_commit_en := Wire.mk "rob_commit_en"
  let commit_store_en := Wire.mk "commit_store_en"
  let _rob_head_isStore := Wire.mk "rob_head_isStore"
  let rob_head_physRd := makeIndexedWires "rob_head_physRd" 6
  let rob_head_oldPhysRd := makeIndexedWires "rob_head_oldPhysRd" 6
  let rob_head_hasOldPhysRd := Wire.mk "rob_head_hasOldPhysRd"
  let _retire_recycle_valid := Wire.mk "retire_recycle_valid"
  let retire_recycle_valid_filtered := Wire.mk "retire_recycle_valid_filtered"
  let rvvi_rd_data := makeIndexedWires "rvvi_rd_data_raw" 32
  let int_rename_rd_data3 := makeIndexedWires "int_rename_rd_data3" 32  -- unused rs3 data (INT has no FMA)
  let int_rename_rs3_phys := makeIndexedWires "int_rename_rs3_phys" 6  -- unused rs3 phys output (INT has no FMA)

  -- Gate rename's instr_valid during redirect/flush
  let decode_valid_rename := Wire.mk "decode_valid_rename"

  let rename_inst : CircuitInstance := {
    moduleName := "RenameStage_32x64"
    instName := "u_rename"
    portMap :=
      [("clock", clock), ("reset", reset),
       ("zero", zero), ("one", one),
       ("instr_valid", decode_valid_rename),
       ("has_rd", if enableF then Wire.mk "decode_has_rd_int" else decode_has_rd)] ++
      (decode_rs1.enum.map (fun ⟨i, w⟩ => (s!"rs1_addr_{i}", w))) ++
      (decode_rs2.enum.map (fun ⟨i, w⟩ => (s!"rs2_addr_{i}", w))) ++
      ((List.range 5).map (fun i => (s!"rs3_addr_{i}", zero))) ++  -- rs3_addr: unused on INT rename
      (decode_rd.enum.map (fun ⟨i, w⟩ => (s!"rd_addr_{i}", w))) ++
      [("cdb_valid", if enableF then cdb_valid_int_prf else cdb_valid_prf)] ++
      (cdb_tag_int.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag_{i}", w))) ++
      (cdb_data_int.enum.map (fun ⟨i, w⟩ => (s!"cdb_data_{i}", w))) ++
      [("retire_valid", if enableF then int_retire_valid else retire_recycle_valid_filtered)] ++
      (retire_tag_muxed.enum.map (fun ⟨i, w⟩ => (s!"retire_tag_{i}", w))) ++
      (rob_head_physRd.enum.map (fun ⟨i, w⟩ => (s!"rd_tag4_{i}", w))) ++  -- 4th read port: RVVI commit readback
      [("rename_valid", rename_valid), ("stall", rename_stall)] ++
      (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"rs1_phys_out_{i}", w))) ++
      (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"rs2_phys_out_{i}", w))) ++
      (int_rename_rs3_phys.enum.map (fun ⟨i, w⟩ => (s!"rs3_phys_out_{i}", w))) ++  -- unused on INT
      (rd_phys.enum.map (fun ⟨i, w⟩ => (s!"rd_phys_out_{i}", w))) ++
      (rs1_data.enum.map (fun ⟨i, w⟩ => (s!"rs1_data_{i}", w))) ++
      (rs2_data.enum.map (fun ⟨i, w⟩ => (s!"rs2_data_{i}", w))) ++
      (old_rd_phys.enum.map (fun ⟨i, w⟩ => (s!"old_rd_phys_out_{i}", w))) ++
      (int_rename_rd_data3.enum.map (fun ⟨i, w⟩ => (s!"rd_data3_{i}", w))) ++
      (rvvi_rd_data.enum.map (fun ⟨i, w⟩ => (s!"rd_data4_{i}", w))) ++
      -- Committed RAT recovery (CSR: suppress flush to keep speculative rd mapping)
      [("flush_en", rename_flush_en),
       ("commit_valid", commit_valid_muxed),
       ("commit_hasPhysRd", commit_hasPhysRd_muxed),
       ("force_alloc", dispatch_is_branch),
       ("commit_hasAllocSlot", commit_hasAllocSlot_muxed)] ++
      (commit_archRd_muxed.enum.map (fun ⟨i, w⟩ => (s!"commit_archRd_{i}", w))) ++
      (commit_physRd_muxed.enum.map (fun ⟨i, w⟩ => (s!"commit_physRd_{i}", w)))
  }

  -- === DISPATCH QUALIFICATION ===
  let not_stall := Wire.mk "not_stall"
  let dispatch_base_valid := Wire.mk "dispatch_base_valid"
  let dispatch_int_valid := Wire.mk "dispatch_int_valid"
  let dispatch_mem_valid := Wire.mk "dispatch_mem_valid"
  let dispatch_branch_valid := Wire.mk "dispatch_branch_valid"
  let dispatch_muldiv_valid := Wire.mk "dispatch_muldiv_valid"
  let dispatch_fp_valid := Wire.mk "dispatch_fp_valid"

  let sb_enq_en := Wire.mk "sb_enq_en"

  let not_redirecting := Wire.mk "not_redirecting"
  let redirect_or := Wire.mk "redirect_or"
  let redirect_or_flush := Wire.mk "redirect_or_flush"
  let decode_valid_no_redirect := Wire.mk "decode_valid_no_redirect"

  -- Forward-declare ROB/SB empty wires (needed by FENCE.I FSM, driven by instances below)
  let rob_empty := Wire.mk "rob_empty"
  let lsu_sb_empty := Wire.mk "lsu_sb_empty"

  -- === Serialize detection and FSM gates (FENCE.I + CSR) ===
  -- Config-gated: hardwired uses mkSerializeDetect, microcoded uses MicrocodeSequencer
  -- Forward-declare csr_read_data for microcode path (driven by CSR read MUX below)
  let csr_read_data_fwd := (List.range 32).map (fun i => Wire.mk s!"csr_rd_e{i}")
  -- Forward-declare csr_cdb wires for microcode path
  let csr_cdb_inject := Wire.mk "csr_cdb_inject"
  let csr_cdb_tag := (List.range 6).map (fun i => Wire.mk s!"csr_cdb_tg_e{i}")
  let csr_cdb_data := (List.range 32).map (fun i => Wire.mk s!"csr_cdb_dt_e{i}")
  let (fence_i_detect_gates, microcode_instances) := if config.microcodesCSR || config.microcodesFenceI then
      mkMicrocodeSerializePath config oi opcodeWidth zero one clock reset
        decode_optype decode_valid decode_imm decode_rd decode_rs1
        branch_redirect_valid_reg fetch_stall_ext
        fence_i_draining fence_i_not_draining
        rob_empty lsu_sb_empty pipeline_flush_comb
        fence_i_redir_target fence_i_pc_plus_4
        csr_flag_reg csr_addr_reg csr_optype_reg csr_rd_reg csr_phys_reg csr_rs1cap_reg csr_zimm_reg
        rd_phys csr_match
        fence_i_detected csr_detected serialize_detected
        fence_i_start fence_i_drain_complete fence_i_draining_next fence_i_suppress
        csr_rename_en not_csr_rename_en
        csr_flag_next csr_addr_next csr_optype_next csr_rd_next csr_phys_next csr_rs1cap_next csr_zimm_next
        fence_i_redir_next
        csr_read_data_fwd
        csr_cdb_inject csr_cdb_tag csr_cdb_data
        fetch_pc
    else
      mkSerializeDetect config oi opcodeWidth zero one clock reset
        decode_optype decode_valid decode_imm decode_rd decode_rs1
        branch_redirect_valid_reg fetch_stall_ext
        fence_i_draining fence_i_not_draining
        rob_empty lsu_sb_empty pipeline_flush_comb
        fence_i_redir_target fence_i_pc_plus_4
        csr_flag_reg csr_addr_reg csr_optype_reg csr_rd_reg csr_phys_reg csr_rs1cap_reg csr_zimm_reg
        rd_phys csr_match
        fence_i_detected csr_detected serialize_detected
        fence_i_start fence_i_drain_complete fence_i_draining_next fence_i_suppress
        csr_rename_en not_csr_rename_en
        csr_flag_next csr_addr_next csr_optype_next csr_rd_next csr_phys_next csr_rs1cap_next csr_zimm_next
        fence_i_redir_next
        csr_read_data_fwd
        fetch_pc

  -- fetch_stall = global_stall OR pipeline_flush OR fence_i_draining_next
  let fetch_stall_tmp := Wire.mk "fetch_stall_tmp"

  -- pipeline_flush_comb = reset OR redirect_valid_reg (feeds flush DFFs)
  let flush_gate :=
    [Gate.mkOR reset branch_redirect_valid_reg pipeline_flush_comb,
     Gate.mkOR global_stall pipeline_flush fetch_stall_tmp,
     Gate.mkOR fetch_stall_tmp fence_i_draining_next (Wire.mk "fetch_stall_tmp2"),
     Gate.mkOR (Wire.mk "fetch_stall_tmp2") fetch_stall_ext fetch_stall,
     -- Per-subsystem reset OR gates
     Gate.mkOR reset flush_rs_int pipeline_reset_rs_int,
     Gate.mkOR reset flush_rs_mem pipeline_reset_rs_mem,
     Gate.mkOR reset flush_rs_br pipeline_reset_rs_br] ++
    (if enableM then [Gate.mkOR reset flush_rs_muldiv pipeline_reset_rs_muldiv] else []) ++
    (if enableF then [Gate.mkOR reset flush_rs_fp pipeline_reset_rs_fp] else []) ++
    [Gate.mkOR reset flush_rob pipeline_reset_rob,
     Gate.mkOR reset flush_busy_groups[0]! pipeline_reset_busy,
     Gate.mkOR reset flush_misc pipeline_reset_misc]

  let decode_valid_no_redir_raw := Wire.mk "decode_valid_no_redir_raw"
  let not_fence_i_suppress := Wire.mk "not_fence_i_suppress"
  let dispatch_gates :=
    [Gate.mkOR global_stall fetch_stall_ext (Wire.mk "dispatch_stall"),
     Gate.mkNOT (Wire.mk "dispatch_stall") not_stall,
     Gate.mkOR rob_redirect_valid branch_redirect_valid_reg redirect_or,
     Gate.mkOR redirect_or pipeline_flush redirect_or_flush,
     Gate.mkNOT redirect_or_flush not_redirecting,
     Gate.mkAND decode_valid not_redirecting decode_valid_no_redir_raw,
     -- Gate FENCE.I suppress: don't let FENCE.I (or anything during drain) enter pipeline
     Gate.mkNOT fence_i_suppress not_fence_i_suppress,
     Gate.mkAND decode_valid_no_redir_raw not_fence_i_suppress decode_valid_no_redirect,
     Gate.mkAND decode_valid_no_redirect not_stall (Wire.mk "dvr_base"),
     -- CSR detection: allow rename even during redirect (pipeline will drain anyway)
     -- decode_valid_rename = dvr_base OR csr_rename_en
     Gate.mkOR (Wire.mk "dvr_base") csr_rename_en decode_valid_rename,
     -- Gate dispatch: CSR start cycle allows rename but suppresses ROB/RS entry
     Gate.mkAND rename_valid not_csr_rename_en rename_valid_gated,
     Gate.mkAND decode_valid_rename not_csr_rename_en dispatch_base_valid,
     Gate.mkAND dispatch_base_valid dispatch_is_integer dispatch_int_valid,
     Gate.mkAND dispatch_base_valid dispatch_is_scalar_memory dispatch_mem_valid,
     Gate.mkAND dispatch_base_valid dispatch_is_branch dispatch_branch_valid] ++
    (if enableM then [Gate.mkAND dispatch_base_valid dispatch_is_muldiv dispatch_muldiv_valid] else []) ++
    (if enableVector then [Gate.mkAND dispatch_base_valid dispatch_is_vector dispatch_vector_valid] else []) ++
    (if enableF then
      let not_has_fp_rd := Wire.mk "not_has_fp_rd"
      let decode_has_rd_int := Wire.mk "decode_has_rd_int"
      [Gate.mkAND dispatch_base_valid dispatch_is_fp dispatch_fp_valid,
       Gate.mkOR decode_has_rd decode_has_fp_rd decode_has_any_rd,
       -- Mask has_rd for INT rename: exclude FP-only-write instructions
       -- FP ops that write INT rd (FMV.X.W, FCMP, etc.) have has_fp_rd=0, so they keep has_rd=1
       Gate.mkNOT decode_has_fp_rd not_has_fp_rd,
       Gate.mkAND decode_has_rd not_has_fp_rd decode_has_rd_int]
    else [])

  -- INT rename has_rd: use masked version when F enabled (exclude FP-only-write ops)


  -- Compute decode_rd_nonzero = OR of all 5 bits of decode_rd (for x0 exclusion)
  -- Used to gate alloc_hasPhysRd/alloc_hasOldPhysRd in the ROB:
  -- if rd=x0, the rename stage doesn't allocate a physRd, so the ROB shouldn't
  -- record hasPhysRd=1 (otherwise it frees oldPhysRd=p0 at commit, putting p0
  -- back in the free list where CDB writes to tag=0 are blocked by cdb_tag_nonzero).
  let rd_nz_or1 := Wire.mk "rd_nz_or1"
  let rd_nz_or2 := Wire.mk "rd_nz_or2"
  let rd_nz_or3 := Wire.mk "rd_nz_or3"
  let rd_nonzero_gates := [
    Gate.mkOR decode_rd[0]! decode_rd[1]! rd_nz_or1,
    Gate.mkOR rd_nz_or1 decode_rd[2]! rd_nz_or2,
    Gate.mkOR rd_nz_or2 decode_rd[3]! rd_nz_or3,
    Gate.mkOR rd_nz_or3 decode_rd[4]! decode_rd_nonzero,
    Gate.mkAND decode_has_rd decode_rd_nonzero decode_has_rd_nox0
  ] ++ (if enableF then [
    -- For FP path: FP rd is always valid (f0 is a real register), so only gate INT rd on x0
    Gate.mkOR decode_has_rd_nox0 decode_has_fp_rd decode_has_any_rd_nox0
  ] else [])

  -- === BUSY-BIT TABLE ===
  let busy_set_en := Wire.mk "busy_set_en"
  -- Use int_has_rd_nox0 (excludes FP-only instructions) to avoid setting INT busy bits for FP dests
  let busy_set_gate :=
    if enableF then Gate.mkAND rename_valid_gated (Wire.mk "int_has_rd_nox0") busy_set_en
    else Gate.mkAND rename_valid_gated decode_has_rd_nox0 busy_set_en
  let busy_src1_ready := Wire.mk "busy_src1_ready"
  let busy_src2_ready := Wire.mk "busy_src2_ready"
  let busy_src2_ready_reg := Wire.mk "busy_src2_ready_reg"
  let (busy_gates, busy_instances) := mkBusyBitTable
    clock reset flush_busy_groups zero one
    rd_phys busy_set_en
    cdb_tag_int cdb_valid_int_domain
    rs1_phys rs2_phys
    decode_use_imm
    busy_src1_ready busy_src2_ready busy_src2_ready_reg

  -- === CDB FORWARDING (INT) ===
  let issue_src1_ready := Wire.mk "issue_src1_ready"
  let issue_src2_ready := Wire.mk "issue_src2_ready"
  let issue_src2_ready_reg := Wire.mk "issue_src2_ready_reg"
  let fwd_src1_data := makeIndexedWires "fwd_src1_data" 32
  let fwd_src2_data := makeIndexedWires "fwd_src2_data" 32
  let (cdb_fwd_gates, fwd_src_data_gates, cdb_fwd_instances) := mkCDBForwardInt
    enableF zero
    cdb_valid_int_domain cdb_pre_valid
    cdb_tag_int cdb_pre_tag
    rs1_phys rs2_phys
    cdb_data_int cdb_pre_data rs1_data rs2_data
    busy_src1_ready busy_src2_ready busy_src2_ready_reg
    fwd_src1_data fwd_src2_data
    issue_src1_ready issue_src2_ready issue_src2_ready_reg
  let fwd_src1_data_gates := fwd_src_data_gates.take 64
  let fwd_src2_data_gates := fwd_src_data_gates.drop 64

  -- === FP RENAME STAGE (conditional) ===
  let fp_rs1_phys := makeIndexedWires "fp_rs1_phys" 6
  let fp_rs2_phys := makeIndexedWires "fp_rs2_phys" 6
  let fp_rd_phys := makeIndexedWires "fp_rd_phys" 6
  let fp_old_rd_phys := makeIndexedWires "fp_old_rd_phys" 6
  let fp_rs1_data := makeIndexedWires "fp_rs1_data" 32
  let fp_rs2_data := makeIndexedWires "fp_rs2_data" 32
  let fp_rename_valid := Wire.mk "fp_rename_valid"
  let fp_rename_stall := Wire.mk "fp_rename_stall"
  let fp_rs3_data := makeIndexedWires "fp_rs3_data" 32
  let fp_rs3_phys := makeIndexedWires "fp_rs3_phys" 6  -- rs3 physical register (for busy check)
  let fp_rvvi_rd_data := makeIndexedWires "fp_rvvi_rd_data" 32  -- FP PRF 4th read port for RVVI

  -- CDB routing: split CDB writes between INT and FP PRFs
  -- INT PRF: gate by cdb_tag_nonzero (p0 = x0, must not be written)
  -- FP PRF: do NOT gate by cdb_tag_nonzero (p0 is a valid FP register)
  let cdb_valid_fp_nofilt := Wire.mk "cdb_valid_fp_nofilt"
  let cdb_prf_route_gates :=
    if enableF then
      [Gate.mkNOT cdb_is_fp_rd not_cdb_is_fp,
       Gate.mkAND cdb_valid_prf not_cdb_is_fp cdb_valid_int_prf,
       -- FP PRF write: skip tag_nonzero check since FP p0 is valid
       Gate.mkAND cdb_valid cdb_is_fp_rd cdb_valid_fp_nofilt] ++
      (if config.enableZicsr then
        [Gate.mkAND cdb_valid_fp_nofilt (Wire.mk "prf_flush_allow") cdb_valid_fp_prf]
       else
        [Gate.mkAND cdb_valid_fp_nofilt (Wire.mk "not_flushing_prf") cdb_valid_fp_prf])
    else []

  let fp_rename_inst : CircuitInstance := {
    moduleName := "RenameStage_32x64"
    instName := "u_fp_rename"
    portMap :=
      [("clock", clock), ("reset", reset),
       ("zero", zero), ("one", one),
       ("instr_valid", decode_valid_rename),
       ("has_rd", decode_has_fp_rd)] ++
      (decode_rs1.enum.map (fun ⟨i, w⟩ => (s!"rs1_addr_{i}", w))) ++
      (decode_rs2.enum.map (fun ⟨i, w⟩ => (s!"rs2_addr_{i}", w))) ++
      (decode_rs3.enum.map (fun ⟨i, w⟩ => (s!"rs3_addr_{i}", w))) ++  -- rs3 lookup via FP RAT
      (decode_rd.enum.map (fun ⟨i, w⟩ => (s!"rd_addr_{i}", w))) ++
      [("cdb_valid", cdb_valid_fp_prf)] ++
      (cdb_tag_fp.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag_{i}", w))) ++
      (cdb_data_fp.enum.map (fun ⟨i, w⟩ => (s!"cdb_data_{i}", w))) ++
      [("retire_valid", fp_retire_recycle_valid)] ++
      (retire_tag_muxed.enum.map (fun ⟨i, w⟩ => (s!"retire_tag_{i}", w))) ++
      (rob_head_physRd.enum.map (fun ⟨i, w⟩ => (s!"rd_tag4_{i}", w))) ++  -- 4th read port: RVVI FP commit readback
      [("rename_valid", fp_rename_valid), ("stall", fp_rename_stall)] ++
      (fp_rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"rs1_phys_out_{i}", w))) ++
      (fp_rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"rs2_phys_out_{i}", w))) ++
      (fp_rd_phys.enum.map (fun ⟨i, w⟩ => (s!"rd_phys_out_{i}", w))) ++
      (fp_rs1_data.enum.map (fun ⟨i, w⟩ => (s!"rs1_data_{i}", w))) ++
      (fp_rs2_data.enum.map (fun ⟨i, w⟩ => (s!"rs2_data_{i}", w))) ++
      (fp_old_rd_phys.enum.map (fun ⟨i, w⟩ => (s!"old_rd_phys_out_{i}", w))) ++
      (fp_rs3_data.enum.map (fun ⟨i, w⟩ => (s!"rd_data3_{i}", w))) ++
      (fp_rs3_phys.enum.map (fun ⟨i, w⟩ => (s!"rs3_phys_out_{i}", w))) ++  -- rs3 physical register tag
      (fp_rvvi_rd_data.enum.map (fun ⟨i, w⟩ => (s!"rd_data4_{i}", w))) ++
      -- Committed RAT recovery (FP uses same commit signals, filtered by is_fp)
      [("flush_en", redirect_valid_fp),  -- Committed RAT restore on misprediction (dedicated DFF)
       ("commit_valid", rob_commit_en),
       ("commit_hasPhysRd", Wire.mk "rob_head_is_fp"),
       ("force_alloc", zero),  -- FP rename doesn't need branch tracking
       ("commit_hasAllocSlot", Wire.mk "rob_head_is_fp")] ++  -- same as commit_hasPhysRd for FP
      ((List.range 5).map (fun i => (s!"commit_archRd_{i}", Wire.mk s!"rob_head_archRd_{i}"))) ++
      (rob_head_physRd.enum.map (fun ⟨i, w⟩ => (s!"commit_physRd_{i}", w)))
  }

  -- Mask dest_tag to 0 when no INT rd writeback (has_rd=0, rd=x0, or FP-only rd).
  -- This prevents stale tags from matching in RS entries via CDB forwarding.
  let int_has_rd_nox0 := Wire.mk "int_has_rd_nox0"
  let int_has_rd_nox0_gate :=
    if enableF then
      -- decode_has_rd_nox0 already excludes x0 and no-rd; just also exclude FP-only
      Gate.mkAND decode_has_rd_nox0 (Wire.mk "not_has_fp_rd") int_has_rd_nox0
    else
      Gate.mkBUF decode_has_rd_nox0 int_has_rd_nox0
  let int_dest_tag_masked := makeIndexedWires "int_dest_tag_masked" 6
  let int_dest_tag_mask_gates := [int_has_rd_nox0_gate] ++
    (List.range 6).map (fun i =>
      Gate.mkAND rd_phys[i]! int_has_rd_nox0 int_dest_tag_masked[i]!)

  -- === BRANCH UNIQUE TAG ALLOCATION ===
  -- Branches need unique CDB tags for misprediction tracking in ROB, even for rd=x0.
  -- Use the unmasked rename counter tag (rd_phys) for branches.
  let branch_alloc_physRd := makeIndexedWires "branch_alloc_physRd" 6
  let branch_alloc_hasPhysRd := Wire.mk "branch_alloc_hasPhysRd"
  let rob_alloc_physRd_fp := makeIndexedWires "rob_alloc_physRd_fp" 6
  let rob_alloc_hasPhysRd_fp := Wire.mk "rob_alloc_hasPhysRd_fp"
  let rob_alloc_hasPhysRd_pre := Wire.mk "rob_alloc_hasPhysRd_pre"
  let fp_issue_dest_tag := makeIndexedWires "fp_issue_dest_tag" 6
  let branch_alloc_physRd_gates :=
    -- branch_alloc_hasPhysRd = dispatch_is_branch OR decode_has_rd_nox0
    [Gate.mkOR dispatch_is_branch decode_has_rd_nox0 branch_alloc_hasPhysRd] ++
    -- branch_alloc_physRd = MUX(int_dest_tag_masked, rd_phys, dispatch_is_branch)
    -- Branches use unmasked rd_phys (unique free-list tag for CDB completion tracking)
    (List.range 6).map (fun i =>
      Gate.mkMUX int_dest_tag_masked[i]! rd_phys[i]! dispatch_is_branch branch_alloc_physRd[i]!) ++
    -- FP-aware: same force_alloc logic for branch override
    (if enableF then
      [Gate.mkOR dispatch_is_branch decode_has_any_rd_nox0 rob_alloc_hasPhysRd_pre] ++
      (List.range 6).map (fun i =>
        Gate.mkMUX fp_issue_dest_tag[i]! rd_phys[i]! dispatch_is_branch rob_alloc_physRd_fp[i]!)
    else
      [Gate.mkBUF branch_alloc_hasPhysRd rob_alloc_hasPhysRd_pre] ++
      (List.range 6).map (fun i =>
        Gate.mkBUF branch_alloc_physRd[i]! rob_alloc_physRd_fp[i]!)) ++
    -- Vector instructions auto-complete in ROB (no scalar CDB expected).
    -- RvvCore handles its own execution ordering; scalar writebacks (vsetvl)
    -- use the merged_cdb_inject path which bypasses the ROB.
    (if enableVector then
      [Gate.mkAND rob_alloc_hasPhysRd_pre not_dispatch_is_vector rob_alloc_hasPhysRd_fp]
    else
      [Gate.mkBUF rob_alloc_hasPhysRd_pre rob_alloc_hasPhysRd_fp])
  -- For retire: branches with rd=x0 need to free their tracking tag at commit
  let _branch_tracking := Wire.mk "branch_tracking"
  let _not_hasOldPhysRd := Wire.mk "not_hasOldPhysRd"
  let _branch_tracking_tmp := Wire.mk "branch_tracking_tmp"
  let _retire_any_old := Wire.mk "retire_any_old"

  -- === CROSS-DOMAIN SOURCE ROUTING ===
  let fp_issue_src1_tag := makeIndexedWires "fp_issue_src1_tag" 6
  let fp_issue_src2_tag := makeIndexedWires "fp_issue_src2_tag" 6
  let fp_issue_src1_data := makeIndexedWires "fp_issue_src1_data" 32
  let fp_issue_src2_data := makeIndexedWires "fp_issue_src2_data" 32

  let fp_crossdomain_gates :=
    if enableF then
      (List.range 6).map (fun i =>
        Gate.mkMUX rs1_phys[i]! fp_rs1_phys[i]! decode_fp_rs1_read fp_issue_src1_tag[i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkMUX (fwd_src1_data[i]!) fp_rs1_data[i]! decode_fp_rs1_read fp_issue_src1_data[i]!) ++
      (List.range 6).map (fun i =>
        Gate.mkMUX rs2_phys[i]! fp_rs2_phys[i]! decode_fp_rs2_read fp_issue_src2_tag[i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkMUX (fwd_src2_data[i]!) fp_rs2_data[i]! decode_fp_rs2_read fp_issue_src2_data[i]!) ++
      (List.range 6).map (fun i =>
        Gate.mkMUX int_dest_tag_masked[i]! fp_rd_phys[i]! decode_has_fp_rd fp_issue_dest_tag[i]!)
    else []

  -- === FP BUSY-BIT TABLE (conditional) ===
  let fp_busy_src1_ready_raw := Wire.mk "fp_busy_src1_ready_raw"
  let fp_busy_src2_ready_raw := Wire.mk "fp_busy_src2_ready_raw"
  let fp_busy_src2_ready_reg_raw := Wire.mk "fp_busy_src2_ready_reg_raw"
  let fp_busy_set_en := Wire.mk "fp_busy_set_en"

  let fp_busy_set_gate :=
    if enableF then Gate.mkAND rename_valid_gated decode_has_fp_rd fp_busy_set_en
    else Gate.mkBUF zero fp_busy_set_en

  let (fp_busy_gates, fp_busy_instances) :=
    if enableF then mkBusyBitTable
      clock reset flush_busy_groups zero one
      fp_rd_phys fp_busy_set_en
      cdb_tag_fp cdb_valid_fp_domain
      fp_rs1_phys fp_rs2_phys
      zero
      fp_busy_src1_ready_raw fp_busy_src2_ready_raw fp_busy_src2_ready_reg_raw
      "fp_busy"
    else ([], [])

  -- === FP SRC3 BUSY CHECK ===
  -- Read the FP busy table at fp_rs3_phys to check if src3 is still pending.
  -- If busy AND rs3 is used (FMA instruction), stall FP dispatch.
  let fp_src3_busy := Wire.mk "fp_src3_busy"
  let fp_src3_stall := Wire.mk "fp_src3_stall"
  let fp_src3_busy_gates :=
    if enableF then
      let busy_cur := (List.range 64).map fun i => Wire.mk s!"fp_busy_q_{i}"
      mkMux64to1 busy_cur fp_rs3_phys "fp_src3_bm" fp_src3_busy ++
      [Gate.mkAND fp_src3_busy decode_fp_rs3_used fp_src3_stall]
    else
      [Gate.mkBUF zero fp_src3_busy, Gate.mkBUF zero fp_src3_stall]

  -- === FP CDB FORWARDING ===
  let fp_issue_src1_ready := Wire.mk "fp_issue_src1_ready"
  let fp_issue_src2_ready := Wire.mk "fp_issue_src2_ready"
  let fp_fwd_src1_data := makeIndexedWires "fp_fwd_src1_data" 32
  let fp_fwd_src2_data := makeIndexedWires "fp_fwd_src2_data" 32
  let (fp_cdb_fwd_gates, fp_fwd_data_gates, fp_cdb_fwd_instances) := mkCDBForwardFP
    enableF zero
    cdb_valid cdb_pre_valid
    cdb_is_fp_rd
    cdb_tag_fp cdb_pre_tag
    fp_issue_src1_tag fp_issue_src2_tag
    cdb_data_fp cdb_pre_data fp_issue_src1_data fp_issue_src2_data
    busy_src1_ready busy_src2_ready
    fp_busy_src1_ready_raw fp_busy_src2_ready_raw
    decode_fp_rs1_read decode_fp_rs2_read
    fp_fwd_src1_data fp_fwd_src2_data
    fp_issue_src1_ready fp_issue_src2_ready

  -- === SRC2 MUX ===
  let issue_src2_muxed := makeIndexedWires "issue_src2_muxed" 32
  let src2_mux_gates := (List.range 32).map (fun i =>
    Gate.mkMUX (fwd_src2_data[i]!) (decode_imm[i]!) decode_use_imm (issue_src2_muxed[i]!))

  -- === RESERVATION STATIONS ===
  -- RS Integer
  let rs_int_alloc_ptr := makeIndexedWires "rs_int_alloc_ptr" 2
  let rs_int_grant := makeIndexedWires "rs_int_grant" 4
  let ib_fifo_enq_ready := Wire.mk "ib_fifo_enq_ready"
  let rs_int_issue_full := Wire.mk "rs_int_issue_full"
  let rs_int_dispatch_valid := Wire.mk "rs_int_dispatch_valid"
  let rs_int_dispatch_opcode := makeIndexedWires "rs_int_dispatch_opcode" 6
  let rs_int_dispatch_src1 := makeIndexedWires "rs_int_dispatch_src1" 32
  let rs_int_dispatch_src2 := makeIndexedWires "rs_int_dispatch_src2" 32
  let rs_int_dispatch_tag := makeIndexedWires "rs_int_dispatch_tag" 6

  let rs_int_inst : CircuitInstance := {
    moduleName := "ReservationStation4"
    instName := "u_rs_integer"
    portMap := [("clock", clock), ("reset", pipeline_reset_rs_int),
                ("zero", zero), ("one", one), ("issue_en", dispatch_int_valid),
                ("issue_src1_ready", issue_src1_ready), ("issue_src2_ready", issue_src2_ready),
                ("cdb_valid", cdb_valid_int_domain), ("dispatch_en", ib_fifo_enq_ready),
                ("issue_full", rs_int_issue_full), ("dispatch_valid", rs_int_dispatch_valid)] ++
               -- Only connect lower 6 bits of optype; bit 6 is FP flag, unused by integer RS
               ((decode_optype.take 6).enum.map (fun ⟨i, w⟩ => (s!"issue_opcode_{i}", w))) ++
               (int_dest_tag_masked.enum.map (fun ⟨i, w⟩ => (s!"issue_dest_tag_{i}", w))) ++
               (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_tag_{i}", w))) ++
               (fwd_src1_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_data_{i}", w))) ++
               (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_tag_{i}", w))) ++
               (issue_src2_muxed.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_data_{i}", w))) ++
               (cdb_tag_rs.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag_{i}", w))) ++
               (cdb_data_rs.enum.map (fun ⟨i, w⟩ => (s!"cdb_data_{i}", w))) ++
               (rs_int_dispatch_opcode.enum.map (fun ⟨i, w⟩ => (s!"dispatch_opcode_{i}", w))) ++
               (rs_int_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src1_data_{i}", w))) ++
               (rs_int_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src2_data_{i}", w))) ++
               (rs_int_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dispatch_dest_tag_{i}", w))) ++
               (rs_int_alloc_ptr.enum.map (fun ⟨i, w⟩ => (s!"alloc_ptr_{i}", w))) ++
               (rs_int_grant.enum.map (fun ⟨i, w⟩ => (s!"dispatch_grant_{i}", w)))
  }

  -- RS Memory
  let rs_mem_issue_full := Wire.mk "rs_mem_issue_full"
  let rs_mem_dispatch_valid := Wire.mk "rs_mem_dispatch_valid"
  let rs_mem_dispatch_opcode := makeIndexedWires "rs_mem_dispatch_opcode" 6
  let rs_mem_dispatch_src1 := makeIndexedWires "rs_mem_dispatch_src1" 32
  let rs_mem_dispatch_src2 := makeIndexedWires "rs_mem_dispatch_src2" 32
  let rs_mem_dispatch_tag := makeIndexedWires "rs_mem_dispatch_tag" 6
  let rs_mem_alloc_ptr := makeIndexedWires "rs_mem_alloc_ptr" 2
  let rs_mem_grant := makeIndexedWires "rs_mem_grant" 4

  -- FP memory path: MUX dest_tag and src2 for FLW/FSW
  let mem_dest_tag := if enableF then makeIndexedWires "mem_dest_tag" 6 else int_dest_tag_masked
  let mem_src2_tag := if enableF then makeIndexedWires "mem_src2_tag" 6 else rs2_phys
  let mem_src2_data := if enableF then makeIndexedWires "mem_src2_data" 32 else fwd_src2_data
  let mem_src2_ready := if enableF then Wire.mk "mem_src2_ready" else issue_src2_ready_reg
  let fp_mem_mux_gates :=
    if enableF then
      -- FLW: dest_tag from FP rename, not INT rename
      (List.range 6).map (fun i =>
        Gate.mkMUX int_dest_tag_masked[i]! fp_issue_dest_tag[i]! dispatch_is_fp_load mem_dest_tag[i]!) ++
      -- FSW: src2 tag/data from FP rename (store data from FP reg)
      (List.range 6).map (fun i =>
        Gate.mkMUX rs2_phys[i]! fp_rs2_phys[i]! dispatch_is_fp_store mem_src2_tag[i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkMUX fwd_src2_data[i]! fp_fwd_src2_data[i]! dispatch_is_fp_store mem_src2_data[i]!) ++
      -- FSW: src2 ready from FP busy table
      [Gate.mkMUX issue_src2_ready_reg fp_issue_src2_ready dispatch_is_fp_store mem_src2_ready]
    else []

  -- Forward-declare cross-size stall wires (driven later by load forwarding logic)
  let mem_dispatch_en := Wire.mk "mem_dispatch_en"
  let cross_size_stall := Wire.mk "cross_size_stall"
  let not_cross_size_stall := Wire.mk "not_cross_size_stall"
  let branch_dispatch_en := Wire.mk "branch_dispatch_en"
  let not_int_dispatching := Wire.mk "not_int_dispatching"

  -- Forward-declare memory address pipeline register wires (DFFs defined later)
  let mem_addr_r := makeIndexedWires "mem_addr_r" 32
  let mem_valid_r := Wire.mk "mem_valid_r"
  let mem_tag_r := makeIndexedWires "mem_tag_r" 6
  let is_load_r := Wire.mk "is_load_r"
  let mem_size_r := makeIndexedWires "mem_size_r" 2
  let sign_extend_r := Wire.mk "sign_extend_r"
  let is_flw_r := Wire.mk "is_flw_r"

  let rs_mem_inst : CircuitInstance := {
    moduleName := "MemoryRS4"
    instName := "u_rs_memory"
    portMap := [("clock", clock), ("reset", pipeline_reset_rs_mem),
                ("zero", zero), ("one", one), ("issue_en", dispatch_mem_valid),
                ("issue_is_store", dispatch_is_store),
                ("issue_src1_ready", issue_src1_ready), ("issue_src2_ready", mem_src2_ready),
                ("cdb_valid", cdb_valid_int_domain), ("dispatch_en", mem_dispatch_en),
                ("issue_full", rs_mem_issue_full), ("dispatch_valid", rs_mem_dispatch_valid)] ++
               -- Only connect lower 6 bits of optype; bit 6 is FP flag, unused by memory RS
               ((decode_optype.take 6).enum.map (fun ⟨i, w⟩ => (s!"issue_opcode_{i}", w))) ++
               (mem_dest_tag.enum.map (fun ⟨i, w⟩ => (s!"issue_dest_tag_{i}", w))) ++
               (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_tag_{i}", w))) ++
               (fwd_src1_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_data_{i}", w))) ++
               (mem_src2_tag.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_tag_{i}", w))) ++
               -- Memory RS: src2 = forwarded register value (store data), NOT immediate
               (mem_src2_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_data_{i}", w))) ++
               (cdb_tag_rs.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag_{i}", w))) ++
               (cdb_data_rs.enum.map (fun ⟨i, w⟩ => (s!"cdb_data_{i}", w))) ++
               (rs_mem_dispatch_opcode.enum.map (fun ⟨i, w⟩ => (s!"dispatch_opcode_{i}", w))) ++
               (rs_mem_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src1_data_{i}", w))) ++
               (rs_mem_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src2_data_{i}", w))) ++
               (rs_mem_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dispatch_dest_tag_{i}", w))) ++
               (rs_mem_alloc_ptr.enum.map (fun ⟨i, w⟩ => (s!"alloc_ptr_{i}", w))) ++
               (rs_mem_grant.enum.map (fun ⟨i, w⟩ => (s!"dispatch_grant_{i}", w)))
  }

  -- === IMMEDIATE REGISTER FILE (Memory RS) ===
  let captured_imm := makeIndexedWires "captured_imm" 32
  let (imm_rf_all_gates, _imm_rf_entries, imm_rf_decoder_inst, imm_rf_mux_inst) :=
    mkSidecarRegFile4x32 "imm_rf" clock reset rs_mem_alloc_ptr dispatch_mem_valid decode_imm rs_mem_grant captured_imm
  let imm_rf_we_gates := imm_rf_all_gates.take 4
  let imm_rf_gates := (imm_rf_all_gates.drop 4).take (4 * 32 * 2)
  let imm_rf_sel_gates := imm_rf_all_gates.drop (4 + 4 * 32 * 2)

  -- === INTEGER IMMEDIATE REGISTER FILE ===
  let int_captured_imm := makeIndexedWires "int_captured_imm" 32
  let (int_imm_rf_all_gates, _int_imm_rf_entries, int_imm_rf_decoder_inst, int_imm_rf_mux_inst) :=
    mkSidecarRegFile4x32 "int_imm_rf" clock reset rs_int_alloc_ptr dispatch_int_valid decode_imm rs_int_grant int_captured_imm
  let int_imm_rf_we_gates := int_imm_rf_all_gates.take 4
  let int_imm_rf_gates := (int_imm_rf_all_gates.drop 4).take (4 * 32 * 2)
  let int_imm_rf_sel_gates := int_imm_rf_all_gates.drop (4 + 4 * 32 * 2)

  -- === INTEGER PC REGISTER FILE ===
  -- Shares write enable with int_imm_rf (same alloc_ptr, same we_en)
  -- But writes fetch_pc instead of decode_imm, so we can't use the generic helper directly
  let int_pc_rf_entries := (List.range 4).map (fun e =>
    makeIndexedWires s!"int_pc_rf_e{e}" 32)
  let int_imm_rf_we := makeIndexedWires "int_imm_rf_we" 4
  let int_pc_rf_gates := (List.range 4).map (fun e =>
    let entry := int_pc_rf_entries[e]!
    (List.range 32).map (fun b =>
      let next := Wire.mk s!"int_pc_rf_next_e{e}_{b}"
      [ Gate.mkMUX entry[b]! fetch_pc[b]! int_imm_rf_we[e]! next,
        Gate.mkDFF next clock reset entry[b]! ]
    ) |>.flatten
  ) |>.flatten

  let int_captured_pc := makeIndexedWires "int_captured_pc" 32
  let int_imm_rf_sel := makeIndexedWires "int_imm_rf_sel" 2
  let int_pc_rf_mux_inst : CircuitInstance := {
    moduleName := "Mux4x32"
    instName := "u_int_pc_rf_mux"
    portMap :=
      (((List.range 4).map (fun e =>
          (List.range 32).map (fun b =>
            (s!"in{e}[{b}]", int_pc_rf_entries[e]![b]!)
          )
        )).flatten) ++
      (int_imm_rf_sel.enum.map (fun ⟨i, w⟩ => (s!"sel[{i}]", w))) ++
      (int_captured_pc.enum.map (fun ⟨i, w⟩ => (s!"out[{i}]", w)))
  }

  -- === BRANCH RS + PC/IMM REGISTER FILES ===
  let rs_branch_alloc_ptr := makeIndexedWires "rs_branch_alloc_ptr" 2
  let rs_branch_grant := makeIndexedWires "rs_branch_grant" 4
  let rs_branch_issue_full := Wire.mk "rs_branch_issue_full"
  let rs_branch_dispatch_valid := Wire.mk "rs_branch_dispatch_valid"
  let rs_branch_dispatch_opcode := makeIndexedWires "rs_branch_dispatch_opcode" 6
  let rs_branch_dispatch_src1 := makeIndexedWires "rs_branch_dispatch_src1" 32
  let rs_branch_dispatch_src2 := makeIndexedWires "rs_branch_dispatch_src2" 32
  let rs_branch_dispatch_tag := makeIndexedWires "rs_branch_dispatch_tag" 6

  let rs_branch_inst : CircuitInstance := {
    moduleName := "ReservationStation4"
    instName := "u_rs_branch"
    portMap := [("clock", clock), ("reset", pipeline_reset_rs_br),
                ("zero", zero), ("one", one), ("issue_en", dispatch_branch_valid),
                ("issue_src1_ready", issue_src1_ready), ("issue_src2_ready", issue_src2_ready),
                ("cdb_valid", cdb_valid_int_domain), ("dispatch_en", branch_dispatch_en),
                ("issue_full", rs_branch_issue_full), ("dispatch_valid", rs_branch_dispatch_valid)] ++
               -- Only connect lower 6 bits of optype; bit 6 is FP flag, unused by branch RS
               ((decode_optype.take 6).enum.map (fun ⟨i, w⟩ => (s!"issue_opcode_{i}", w))) ++
               -- Branch RS uses unmasked physRd (rd_phys) for unique CDB tag matching
               (rd_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_dest_tag_{i}", w))) ++
               (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_tag_{i}", w))) ++
               (fwd_src1_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_data_{i}", w))) ++
               (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_tag_{i}", w))) ++
               -- Branch RS: src2 = forwarded register value, NOT immediate
               (fwd_src2_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_data_{i}", w))) ++
               (cdb_tag_rs.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag_{i}", w))) ++
               (cdb_data_rs.enum.map (fun ⟨i, w⟩ => (s!"cdb_data_{i}", w))) ++
               (rs_branch_dispatch_opcode.enum.map (fun ⟨i, w⟩ => (s!"dispatch_opcode_{i}", w))) ++
               (rs_branch_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src1_data_{i}", w))) ++
               (rs_branch_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src2_data_{i}", w))) ++
               (rs_branch_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dispatch_dest_tag_{i}", w))) ++
               (rs_branch_alloc_ptr.enum.map (fun ⟨i, w⟩ => (s!"alloc_ptr_{i}", w))) ++
               (rs_branch_grant.enum.map (fun ⟨i, w⟩ => (s!"dispatch_grant_{i}", w)))
  }

  -- === BRANCH PC REGISTER FILE ===
  let br_captured_pc := makeIndexedWires "br_captured_pc" 32
  let (br_pc_rf_all_gates, _br_pc_rf_entries, br_pc_rf_decoder_inst, br_pc_rf_mux_inst) :=
    mkSidecarRegFile4x32 "br_pc_rf" clock reset rs_branch_alloc_ptr dispatch_branch_valid fetch_pc rs_branch_grant br_captured_pc
  let br_pc_rf_we_gates := br_pc_rf_all_gates.take 4
  let br_pc_rf_gates := (br_pc_rf_all_gates.drop 4).take (4 * 32 * 2)
  let br_pc_rf_sel_gates := br_pc_rf_all_gates.drop (4 + 4 * 32 * 2)

  -- === BRANCH IMMEDIATE REGISTER FILE ===
  -- Shares write enable with br_pc_rf but writes decode_imm
  let br_pc_rf_we := makeIndexedWires "br_pc_rf_we" 4
  let br_imm_rf_entries := (List.range 4).map (fun e =>
    makeIndexedWires s!"br_imm_rf_e{e}" 32)
  let br_imm_rf_gates := (List.range 4).map (fun e =>
    let entry := br_imm_rf_entries[e]!
    (List.range 32).map (fun b =>
      let next := Wire.mk s!"br_imm_rf_next_e{e}_{b}"
      [ Gate.mkMUX entry[b]! decode_imm[b]! br_pc_rf_we[e]! next,
        Gate.mkDFF next clock reset entry[b]! ]
    ) |>.flatten
  ) |>.flatten

  let br_captured_imm := makeIndexedWires "br_captured_imm" 32
  let br_pc_rf_sel := makeIndexedWires "br_pc_rf_sel" 2
  let br_imm_rf_mux_inst : CircuitInstance := {
    moduleName := "Mux4x32"
    instName := "u_br_imm_rf_mux"
    portMap :=
      (((List.range 4).map (fun e =>
          (List.range 32).map (fun b =>
            (s!"in{e}[{b}]", br_imm_rf_entries[e]![b]!)
          )
        )).flatten) ++
      (br_pc_rf_sel.enum.map (fun ⟨i, w⟩ => (s!"sel[{i}]", w))) ++
      (br_captured_imm.enum.map (fun ⟨i, w⟩ => (s!"out[{i}]", w)))
  }

  -- === BRANCH PREDICTED_TAKEN SHADOW DFFs (4 entries, indexed by RS alloc_ptr) ===
  -- Store predicted_taken from fetch stage alongside each branch RS entry.
  -- Write: gated by dispatch_branch_valid + decoded alloc_ptr
  -- Read: MUX4 selected by dispatch grant → branch_predicted_taken
  -- NOTE: Use distinct wire names (br_pred_e{N}) to prevent codegen from grouping
  -- them into a single bus (which would break multi-DFF assignment).
  let br_pred_e := (List.range 4).map (fun e => Wire.mk s!"br_pred_e{e}")
  let br_pred_taken_gates := (List.range 4).map (fun e =>
    let next := Wire.mk s!"br_pred_next_e{e}"
    [ Gate.mkMUX br_pred_e[e]! fetch_predicted_taken br_pc_rf_we[e]! next,
      Gate.mkDFF next clock reset br_pred_e[e]! ]
  ) |>.flatten

  -- Read predicted_taken for dispatching branch using grant one-hot
  -- MUX4: grant[0]→e0, grant[1]→e1, grant[2]→e2, grant[3]→e3
  let br_pred_sel0 := Wire.mk "br_pred_sel0"
  let br_pred_sel1 := Wire.mk "br_pred_sel1"
  let branch_predicted_taken := Wire.mk "branch_predicted_taken"
  let br_pred_mux_01 := Wire.mk "br_pred_mux_01"
  let br_pred_mux_23 := Wire.mk "br_pred_mux_23"
  let br_pred_read_gates := [
    -- sel = {grant[2]|grant[3], grant[1]|grant[3]}
    Gate.mkOR rs_branch_grant[1]! rs_branch_grant[3]! br_pred_sel0,
    Gate.mkOR rs_branch_grant[2]! rs_branch_grant[3]! br_pred_sel1,
    -- 4:1 mux using 2-level tree
    Gate.mkMUX br_pred_e[0]! br_pred_e[1]! br_pred_sel0 br_pred_mux_01,
    Gate.mkMUX br_pred_e[2]! br_pred_e[3]! br_pred_sel0 br_pred_mux_23,
    Gate.mkMUX br_pred_mux_01 br_pred_mux_23 br_pred_sel1 branch_predicted_taken
  ]

  -- === MULDIV RS (conditional) ===
  let rs_muldiv_alloc_ptr_unused := makeIndexedWires "rs_muldiv_alloc_ptr_unused" 2
  let rs_muldiv_grant_unused := makeIndexedWires "rs_muldiv_grant_unused" 4
  let rs_muldiv_issue_full := Wire.mk "rs_muldiv_issue_full"
  let rs_muldiv_dispatch_valid := Wire.mk "rs_muldiv_dispatch_valid"
  let rs_muldiv_dispatch_opcode := makeIndexedWires "rs_muldiv_dispatch_opcode" 6
  let rs_muldiv_dispatch_src1 := makeIndexedWires "rs_muldiv_dispatch_src1" 32
  let rs_muldiv_dispatch_src2 := makeIndexedWires "rs_muldiv_dispatch_src2" 32
  let rs_muldiv_dispatch_tag := makeIndexedWires "rs_muldiv_dispatch_tag" 6

  -- Gate MulDiv RS dispatch when divider is busy (prevents RS from consuming
  -- entries that the divider will ignore due to start_and_not_busy = 0)
  let muldiv_busy := Wire.mk "muldiv_busy"
  let muldiv_dispatch_en := Wire.mk "muldiv_dispatch_en"
  let not_muldiv_busy := Wire.mk "not_muldiv_busy"
  let muldiv_dispatch_gate :=
    if enableM then
      [Gate.mkNOT muldiv_busy not_muldiv_busy,
       Gate.mkBUF not_muldiv_busy muldiv_dispatch_en]
    else [Gate.mkBUF one muldiv_dispatch_en]

  let rs_muldiv_inst : CircuitInstance := {
    moduleName := "ReservationStation4"
    instName := "u_rs_muldiv"
    portMap := [("clock", clock), ("reset", pipeline_reset_rs_muldiv),
                ("zero", zero), ("one", one), ("issue_en", dispatch_muldiv_valid),
                ("issue_src1_ready", issue_src1_ready), ("issue_src2_ready", issue_src2_ready),
                ("cdb_valid", cdb_valid_int_domain), ("dispatch_en", muldiv_dispatch_en),
                ("issue_full", rs_muldiv_issue_full), ("dispatch_valid", rs_muldiv_dispatch_valid)] ++
               -- Only connect lower 6 bits of optype; bit 6 is FP flag, unused by muldiv RS
               ((decode_optype.take 6).enum.map (fun ⟨i, w⟩ => (s!"issue_opcode_{i}", w))) ++
               (int_dest_tag_masked.enum.map (fun ⟨i, w⟩ => (s!"issue_dest_tag_{i}", w))) ++
               (rs1_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_tag_{i}", w))) ++
               (fwd_src1_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_data_{i}", w))) ++
               (rs2_phys.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_tag_{i}", w))) ++
               (issue_src2_muxed.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_data_{i}", w))) ++
               (cdb_tag_rs.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag_{i}", w))) ++
               (cdb_data_rs.enum.map (fun ⟨i, w⟩ => (s!"cdb_data_{i}", w))) ++
               (rs_muldiv_dispatch_opcode.enum.map (fun ⟨i, w⟩ => (s!"dispatch_opcode_{i}", w))) ++
               (rs_muldiv_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src1_data_{i}", w))) ++
               (rs_muldiv_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src2_data_{i}", w))) ++
               (rs_muldiv_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dispatch_dest_tag_{i}", w))) ++
               (rs_muldiv_alloc_ptr_unused.enum.map (fun ⟨i, w⟩ => (s!"alloc_ptr_{i}", w))) ++
               (rs_muldiv_grant_unused.enum.map (fun ⟨i, w⟩ => (s!"dispatch_grant_{i}", w)))
  }

  -- === EXECUTION UNITS ===
  let int_result := makeIndexedWires "int_result" 32
  let int_tag_out := makeIndexedWires "int_tag_out" 6

  -- ALU opcode LUT: translate 6-bit dispatch optype → 4-bit ALU op
  let alu_op := makeIndexedWires "alu_op" 4
  let alu_lut_gates := mkOpTypeToALU4 "alulut" rs_int_dispatch_opcode alu_op
    (OpType.resolveMapping config.decoderInstrNames aluMappingByName)

  let int_exec_inst : CircuitInstance := {
    moduleName := "IntegerExecUnit"
    instName := "u_exec_integer"
    portMap :=
      (rs_int_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (rs_int_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      (alu_op.enum.map (fun ⟨i, w⟩ => (s!"opcode_{i}", w))) ++
      (rs_int_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dest_tag_{i}", w))) ++
      [("zero", zero), ("one", one)] ++
      (int_result.enum.map (fun ⟨i, w⟩ => (s!"result_{i}", w))) ++
      (int_tag_out.enum.map (fun ⟨i, w⟩ => (s!"tag_out_{i}", w)))
  }

  -- Branch execution unit
  let branch_result := makeIndexedWires "branch_result" 32
  let branch_tag_out := makeIndexedWires "branch_tag_out" 6

  let branch_exec_inst : CircuitInstance := {
    moduleName := "BranchExecUnit"
    instName := "u_exec_branch"
    portMap :=
      (rs_branch_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"src1_{i}", w))) ++
      (rs_branch_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"src2_{i}", w))) ++
      (rs_branch_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dest_tag_{i}", w))) ++
      [("zero", zero)] ++
      (branch_result.enum.map (fun ⟨i, w⟩ => (s!"result_{i}", w))) ++
      (branch_tag_out.enum.map (fun ⟨i, w⟩ => (s!"tag_out_{i}", w)))
  }

  let mem_address := makeIndexedWires "mem_address" 32
  let mem_tag_out := makeIndexedWires "mem_tag_out" 6

  let mem_exec_inst : CircuitInstance := {
    moduleName := "MemoryExecUnit"
    instName := "u_exec_memory"
    portMap :=
      (rs_mem_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"base_{i}", w))) ++
      (captured_imm.enum.map (fun ⟨i, w⟩ => (s!"offset_{i}", w))) ++
      (rs_mem_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dest_tag_{i}", w))) ++
      [("zero", zero)] ++
      (mem_address.enum.map (fun ⟨i, w⟩ => (s!"address_{i}", w))) ++
      (mem_tag_out.enum.map (fun ⟨i, w⟩ => (s!"tag_out_{i}", w)))
  }

  -- MulDiv exec unit (conditional)
  let muldiv_result := makeIndexedWires "muldiv_result" 32
  let muldiv_tag_out := makeIndexedWires "muldiv_tag_out" 6
  let muldiv_valid_out := Wire.mk "muldiv_valid_out"
  -- muldiv_busy already declared above (needed for RS dispatch gating)

  -- MulDiv opcode LUT: translate 6-bit dispatch optype → 3-bit MulDiv op
  let muldiv_op := makeIndexedWires "muldiv_op" 3
  let muldiv_lut_gates :=
    if enableM then mkOpTypeLUT "mdlut" rs_muldiv_dispatch_opcode muldiv_op
      (OpType.resolveMapping config.decoderInstrNames mulDivMappingByName)
    else []

  let muldiv_exec_inst : CircuitInstance := {
    moduleName := "MulDivExecUnit"
    instName := "u_exec_muldiv"
    portMap :=
      (rs_muldiv_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (rs_muldiv_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      (muldiv_op.enum.map (fun ⟨i, w⟩ => (s!"op_{i}", w))) ++
      (rs_muldiv_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dest_tag_{i}", w))) ++
      [("valid_in", rs_muldiv_dispatch_valid),
       ("clock", clock), ("reset", pipeline_reset_rs_muldiv),
       ("zero", zero), ("one", one)] ++
      (muldiv_result.enum.map (fun ⟨i, w⟩ => (s!"result_{i}", w))) ++
      (muldiv_tag_out.enum.map (fun ⟨i, w⟩ => (s!"tag_out_{i}", w))) ++
      [("valid_out", muldiv_valid_out), ("busy", muldiv_busy)]
  }

  -- === FP OPCODE LUT: 7-bit decoder optype → 5-bit FPU opcode ===
  let fpu_opcode := makeIndexedWires "fpu_opcode" 5
  let fpu_opcode_padded := fpu_opcode ++ [zero]  -- zero-pad to 6 bits for RS

  let fpu_lut_gates :=
    if enableF then mkOpTypeLUT "fpulut" decode_optype fpu_opcode
      (OpType.resolveMapping config.decoderInstrNames fpuMappingByName)
    else []

  -- === FP RESERVATION STATION (conditional) ===
  let rs_fp_alloc_ptr := makeIndexedWires "rs_fp_alloc_ptr" 2
  let rs_fp_grant := makeIndexedWires "rs_fp_grant" 4
  let rs_fp_issue_full := Wire.mk "rs_fp_issue_full"
  let rs_fp_dispatch_valid := Wire.mk "rs_fp_dispatch_valid"
  let rs_fp_dispatch_opcode := makeIndexedWires "rs_fp_dispatch_opcode" 6
  let rs_fp_dispatch_src1 := makeIndexedWires "rs_fp_dispatch_src1" 32
  let rs_fp_dispatch_src2 := makeIndexedWires "rs_fp_dispatch_src2" 32
  let rs_fp_dispatch_tag := makeIndexedWires "rs_fp_dispatch_tag" 6

  -- Gate FP RS dispatch when FP EU is busy
  -- Note: we do NOT gate on fp_fifo_enq_ready to avoid a combinational cycle
  -- (valid_in → valid_out is combinational in FPExecUnit for misc ops).
  -- The FIFO always has capacity when the EU accepts a new op because it drains
  -- before the next result arrives (EU latency ≥ 1 cycle).
  let fp_fifo_enq_ready := Wire.mk "fp_fifo_enq_ready"
  let fp_rs_dispatch_en := Wire.mk "fp_rs_dispatch_en"
  let fp_rs_dispatch_gate :=
    if enableF then
      let not_fp_eu_busy := Wire.mk "not_fp_eu_busy"
      [Gate.mkNOT (Wire.mk "fp_busy") not_fp_eu_busy,
       Gate.mkBUF not_fp_eu_busy fp_rs_dispatch_en]
    else [Gate.mkBUF one fp_rs_dispatch_en]

  let rs_fp_inst : CircuitInstance := {
    moduleName := "ReservationStation4"
    instName := "u_rs_fp"
    portMap := [("clock", clock), ("reset", pipeline_reset_rs_fp),
                ("zero", zero), ("one", one), ("issue_en", dispatch_fp_valid),
                ("issue_src1_ready", fp_issue_src1_ready), ("issue_src2_ready", fp_issue_src2_ready),
                ("cdb_valid", cdb_valid_fp_domain), ("dispatch_en", fp_rs_dispatch_en),
                ("issue_full", rs_fp_issue_full), ("dispatch_valid", rs_fp_dispatch_valid)] ++
               -- Use FPU LUT output (5-bit FPU opcode, zero-padded to 6 bits)
               (fpu_opcode_padded.enum.map (fun ⟨i, w⟩ => (s!"issue_opcode_{i}", w))) ++
               (fp_issue_dest_tag.enum.map (fun ⟨i, w⟩ => (s!"issue_dest_tag_{i}", w))) ++
               (fp_issue_src1_tag.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_tag_{i}", w))) ++
               (fp_fwd_src1_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src1_data_{i}", w))) ++
               (fp_issue_src2_tag.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_tag_{i}", w))) ++
               (fp_fwd_src2_data.enum.map (fun ⟨i, w⟩ => (s!"issue_src2_data_{i}", w))) ++
               (cdb_tag_rs.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag_{i}", w))) ++
               (cdb_data_rs.enum.map (fun ⟨i, w⟩ => (s!"cdb_data_{i}", w))) ++
               (rs_fp_dispatch_opcode.enum.map (fun ⟨i, w⟩ => (s!"dispatch_opcode_{i}", w))) ++
               (rs_fp_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src1_data_{i}", w))) ++
               (rs_fp_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"dispatch_src2_data_{i}", w))) ++
               (rs_fp_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dispatch_dest_tag_{i}", w))) ++
               (rs_fp_alloc_ptr.enum.map (fun ⟨i, w⟩ => (s!"alloc_ptr_{i}", w))) ++
               (rs_fp_grant.enum.map (fun ⟨i, w⟩ => (s!"dispatch_grant_{i}", w)))
  }

  -- === FP SRC3 SIDECAR: 4-entry × 32-bit storage for FMA rs3 data ===
  -- Written at issue time (alloc_ptr selects slot), read at dispatch (grant one-hot mux)
  let fp_src3_dispatch := makeIndexedWires "fp_src3_dispatch" 32

  -- Decode alloc_ptr to one-hot write-enable
  let fp_src3_we := (List.range 4).map (fun slot => Wire.mk s!"fp_src3_we_{slot}")
  let fp_src3_alloc_decode :=
    if enableF then
      let ap0 := rs_fp_alloc_ptr[0]!
      let ap1 := rs_fp_alloc_ptr[1]!
      let not_ap0 := Wire.mk "fp_src3_not_ap0"
      let not_ap1 := Wire.mk "fp_src3_not_ap1"
      [Gate.mkNOT ap0 not_ap0, Gate.mkNOT ap1 not_ap1] ++
      -- slot 0: !ap1 & !ap0 & issue_en
      [Gate.mkAND not_ap1 not_ap0 (Wire.mk "fp_src3_sel0"),
       Gate.mkAND (Wire.mk "fp_src3_sel0") dispatch_fp_valid fp_src3_we[0]!] ++
      -- slot 1: !ap1 & ap0 & issue_en
      [Gate.mkAND not_ap1 ap0 (Wire.mk "fp_src3_sel1"),
       Gate.mkAND (Wire.mk "fp_src3_sel1") dispatch_fp_valid fp_src3_we[1]!] ++
      -- slot 2: ap1 & !ap0 & issue_en
      [Gate.mkAND ap1 not_ap0 (Wire.mk "fp_src3_sel2"),
       Gate.mkAND (Wire.mk "fp_src3_sel2") dispatch_fp_valid fp_src3_we[2]!] ++
      -- slot 3: ap1 & ap0 & issue_en
      [Gate.mkAND ap1 ap0 (Wire.mk "fp_src3_sel3"),
       Gate.mkAND (Wire.mk "fp_src3_sel3") dispatch_fp_valid fp_src3_we[3]!]
    else []

  -- 4 slots × 32 DFFs each, with write-enable MUX
  let fp_src3_slots := (List.range 4).map (fun slot =>
    makeIndexedWires s!"fp_src3_slot{slot}" 32)
  let fp_src3_dff_gates :=
    if enableF then
      (List.range 4).flatMap (fun slot =>
        (List.range 32).flatMap (fun bit =>
          let d_mux := Wire.mk s!"fp_src3_slot{slot}_d_{bit}"
          [Gate.mkMUX fp_src3_slots[slot]![bit]! fp_rs3_data[bit]! fp_src3_we[slot]! d_mux,
           Gate.mkDFF d_mux clock reset fp_src3_slots[slot]![bit]!]))
    else []

  -- Read mux: one-hot grant selects which slot's data to output
  let fp_src3_read_gates :=
    if enableF then
      (List.range 32).flatMap (fun bit =>
        let and0 := Wire.mk s!"fp_src3_rd0_{bit}"
        let and1 := Wire.mk s!"fp_src3_rd1_{bit}"
        let and2 := Wire.mk s!"fp_src3_rd2_{bit}"
        let and3 := Wire.mk s!"fp_src3_rd3_{bit}"
        let or01 := Wire.mk s!"fp_src3_or01_{bit}"
        let or23 := Wire.mk s!"fp_src3_or23_{bit}"
        [Gate.mkAND fp_src3_slots[0]![bit]! rs_fp_grant[0]! and0,
         Gate.mkAND fp_src3_slots[1]![bit]! rs_fp_grant[1]! and1,
         Gate.mkAND fp_src3_slots[2]![bit]! rs_fp_grant[2]! and2,
         Gate.mkAND fp_src3_slots[3]![bit]! rs_fp_grant[3]! and3,
         Gate.mkOR and0 and1 or01,
         Gate.mkOR and2 and3 or23,
         Gate.mkOR or01 or23 fp_src3_dispatch[bit]!])
    else []

  -- Forward-declare frm_reg/frm_new wires (DFFs defined later near fflags)
  let frm_reg := makeIndexedWires "frm_reg" 3
  let frm_new := makeIndexedWires "frm_new" 3

  -- === FP RM SIDECAR: 4-entry × 3-bit storage for resolved rounding mode ===
  -- At issue: resolve rm (if decode_rm == 7 use frm_reg, else decode_rm), write to sidecar
  -- At dispatch: read from sidecar using grant one-hot mux
  let fp_rm_dispatch := makeIndexedWires "fp_rm_dispatch" 3

  -- Resolve rm at issue time: rm_is_dynamic = (decode_rm == 3'b111)
  let rm_is_dynamic := Wire.mk "rm_is_dynamic"
  let rm_resolved := makeIndexedWires "rm_resolved" 3
  let rm_resolve_gates :=
    if enableF then
      let rm_and01 := Wire.mk "rm_and01"
      [Gate.mkAND decode_rm[0]! decode_rm[1]! rm_and01,
       Gate.mkAND rm_and01 decode_rm[2]! rm_is_dynamic] ++
      (List.range 3).map (fun i =>
        Gate.mkMUX decode_rm[i]! frm_reg[i]! rm_is_dynamic rm_resolved[i]!)
    else []

  -- Decode alloc_ptr to one-hot write-enable (reuse same pattern as fp_src3)
  let fp_rm_we := (List.range 4).map (fun slot => Wire.mk s!"fp_rm_we_{slot}")
  let fp_rm_alloc_decode :=
    if enableF then
      let ap0 := rs_fp_alloc_ptr[0]!
      let ap1 := rs_fp_alloc_ptr[1]!
      let not_ap0 := Wire.mk "fp_rm_not_ap0"
      let not_ap1 := Wire.mk "fp_rm_not_ap1"
      [Gate.mkNOT ap0 not_ap0, Gate.mkNOT ap1 not_ap1] ++
      [Gate.mkAND not_ap1 not_ap0 (Wire.mk "fp_rm_sel0"),
       Gate.mkAND (Wire.mk "fp_rm_sel0") dispatch_fp_valid fp_rm_we[0]!] ++
      [Gate.mkAND not_ap1 ap0 (Wire.mk "fp_rm_sel1"),
       Gate.mkAND (Wire.mk "fp_rm_sel1") dispatch_fp_valid fp_rm_we[1]!] ++
      [Gate.mkAND ap1 not_ap0 (Wire.mk "fp_rm_sel2"),
       Gate.mkAND (Wire.mk "fp_rm_sel2") dispatch_fp_valid fp_rm_we[2]!] ++
      [Gate.mkAND ap1 ap0 (Wire.mk "fp_rm_sel3"),
       Gate.mkAND (Wire.mk "fp_rm_sel3") dispatch_fp_valid fp_rm_we[3]!]
    else []

  -- 4 slots × 3 DFFs each, with write-enable MUX
  let fp_rm_slots := (List.range 4).map (fun slot =>
    makeIndexedWires s!"fp_rm_slot{slot}" 3)
  let fp_rm_dff_gates :=
    if enableF then
      (List.range 4).flatMap (fun slot =>
        (List.range 3).flatMap (fun bit =>
          let d_mux := Wire.mk s!"fp_rm_slot{slot}_d_{bit}"
          [Gate.mkMUX fp_rm_slots[slot]![bit]! rm_resolved[bit]! fp_rm_we[slot]! d_mux,
           Gate.mkDFF d_mux clock reset fp_rm_slots[slot]![bit]!]))
    else []

  -- Read mux: one-hot grant selects which slot's data to output
  let fp_rm_read_gates :=
    if enableF then
      (List.range 3).flatMap (fun bit =>
        let and0 := Wire.mk s!"fp_rm_rd0_{bit}"
        let and1 := Wire.mk s!"fp_rm_rd1_{bit}"
        let and2 := Wire.mk s!"fp_rm_rd2_{bit}"
        let and3 := Wire.mk s!"fp_rm_rd3_{bit}"
        let or01 := Wire.mk s!"fp_rm_or01_{bit}"
        let or23 := Wire.mk s!"fp_rm_or23_{bit}"
        [Gate.mkAND fp_rm_slots[0]![bit]! rs_fp_grant[0]! and0,
         Gate.mkAND fp_rm_slots[1]![bit]! rs_fp_grant[1]! and1,
         Gate.mkAND fp_rm_slots[2]![bit]! rs_fp_grant[2]! and2,
         Gate.mkAND fp_rm_slots[3]![bit]! rs_fp_grant[3]! and3,
         Gate.mkOR and0 and1 or01,
         Gate.mkOR and2 and3 or23,
         Gate.mkOR or01 or23 fp_rm_dispatch[bit]!])
    else []

  -- === FP EXECUTION UNIT (conditional) ===
  let fp_result := makeIndexedWires "fp_result" 32
  let fp_tag_out := makeIndexedWires "fp_tag_out" 6
  let fp_exceptions := makeIndexedWires "fp_exceptions" 5
  let fp_valid_out := Wire.mk "fp_valid_out"
  let fp_busy := Wire.mk "fp_busy"
  let fp_result_is_int := Wire.mk "fp_result_is_int"

  -- FP opcode LUT: translate 6-bit RS dispatch optype → 5-bit FPU op
  let fp_op := makeIndexedWires "fp_op" 5
  let fp_rm := makeIndexedWires "fp_rm" 3

  -- For now, pass the lower 5 bits of opcode directly as FPU op
  -- (FP instructions start at position 48, so bits [4:0] give offsets 0-25)
  -- The FPExecUnit expects opTypeToFPUOpcode encoding
  let fp_op_gates :=
    if enableF then
      -- Gate EU valid_in with dispatch_en to prevent processing when stalled
      [Gate.mkAND rs_fp_dispatch_valid fp_rs_dispatch_en (Wire.mk "fp_eu_valid_in")] ++
      (List.range 5).map (fun i =>
        Gate.mkBUF rs_fp_dispatch_opcode[i]! fp_op[i]!) ++
      -- rm: from sidecar (resolved at issue time from decode_rm / frm_reg)
      (List.range 3).map (fun i =>
        Gate.mkBUF fp_rm_dispatch[i]! fp_rm[i]!)
    else []

  let fp_exec_inst : CircuitInstance := {
    moduleName := "FPExecUnit"
    instName := "u_exec_fp"
    portMap :=
      (rs_fp_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"src1_{i}", w))) ++
      (rs_fp_dispatch_src2.enum.map (fun ⟨i, w⟩ => (s!"src2_{i}", w))) ++
      -- src3: from sidecar storage (rs3 data captured at issue time)
      (fp_src3_dispatch.enum.map (fun ⟨i, w⟩ => (s!"src3_{i}", w))) ++
      (fp_op.enum.map (fun ⟨i, w⟩ => (s!"op_{i}", w))) ++
      (fp_rm.enum.map (fun ⟨i, w⟩ => (s!"rm_{i}", w))) ++
      (rs_fp_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dest_tag_{i}", w))) ++
      [("valid_in", Wire.mk "fp_eu_valid_in"),
       ("clock", clock), ("reset", reset),
       ("zero", zero), ("one", one)] ++
      (fp_result.enum.map (fun ⟨i, w⟩ => (s!"result_{i}", w))) ++
      (fp_tag_out.enum.map (fun ⟨i, w⟩ => (s!"tag_out_{i}", w))) ++
      (fp_exceptions.enum.map (fun ⟨i, w⟩ => (s!"exceptions_{i}", w))) ++
      [("valid_out", fp_valid_out), ("busy", fp_busy),
       ("result_is_int", fp_result_is_int)]
  }

  -- === VECTOR EXECUTION UNIT (RvvCore instance, conditional on enableVector) ===
  -- RvvCore is an external SV module from coralnpu. N=4 with lanes 1-3 tied off.
  -- The scalar CPU packs instruction bits and forwards scalar register values.
  let rvv_core_inst : CircuitInstance := {
    moduleName := "RvvCoreWrapper"
    instName := "u_rvv_core"
    portMap :=
      [("clk", clock), ("rstn", rvv_rstn)] ++
      -- CSR inputs (wired from scalar CSR state)
      (List.range 7).map (fun i => (s!"vstart_{i}", vstart_reg[i]!)) ++
      [("vxrm_1", vxrm_reg[1]!), ("vxrm_0", vxrm_reg[0]!), ("vxsat", vxsat_reg[0]!),
       ("frm_2", frm_reg[2]!), ("frm_1", frm_reg[1]!), ("frm_0", frm_reg[0]!)] ++
      -- Instruction input: only lane 0 used, lanes 1-3 tied off
      [("inst_valid_0", rvv_inst_valid),
       ("inst_valid_1", zero), ("inst_valid_2", zero), ("inst_valid_3", zero)] ++
      -- inst_data lane 0: flat struct fields
      (fetch_pc.enum.map (fun ⟨i, w⟩ => (s!"inst_data_0_pc_{i}", w))) ++
      (rvv_opcode.enum.map (fun ⟨i, w⟩ => (s!"inst_data_0_opcode_{i}", w))) ++
      (rvv_inst_bits.enum.map (fun ⟨i, w⟩ => (s!"inst_data_0_bits_{i}", w))) ++
      -- Tie off inst_data for lanes 1-3 (59-bit flat vectors)
      ((List.range 3).map (fun lane =>
        (List.range 59).map (fun bit => (s!"inst_data_{lane+1}_{bit}", zero)))).flatten ++
      [("inst_ready_0", rvv_inst_ready)] ++
      -- Scalar register read data (2*N = 8 ports, only 0-1 used)
      [("reg_read_valid_0", rvv_inst_valid), ("reg_read_valid_1", rvv_inst_valid)] ++
      (List.range 6).map (fun j => (s!"reg_read_valid_{j+2}", zero)) ++
      (rs1_data.enum.map (fun ⟨i, w⟩ => (s!"reg_read_data_0_{i}", w))) ++
      (rs2_data.enum.map (fun ⟨i, w⟩ => (s!"reg_read_data_1_{i}", w))) ++
      ((List.range 6).map (fun j =>
        (List.range 32).map (fun bit => (s!"reg_read_data_{j+2}_{bit}", zero)))).flatten ++
      -- FP register read data (N=4 ports, all tied off for Zve32x integer-only)
      ((List.range 4).map (fun j =>
        (List.range 32).map (fun bit => (s!"freg_read_data_{j}_{bit}", zero)))).flatten ++
      -- Scalar writeback outputs (config ops)
      [("reg_write_valid_0", rvv_reg_write_valid)] ++
      (rvv_reg_write_addr.enum.map (fun ⟨i, w⟩ => (s!"reg_write_addr_0_{i}", w))) ++
      (rvv_reg_write_data.enum.map (fun ⟨i, w⟩ => (s!"reg_write_data_0_{i}", w))) ++
      -- Async scalar writeback (vmv.x.s etc.)
      [("async_rd_valid", rvv_async_rd_valid),
       ("async_rd_ready", rvv_async_rd_ready)] ++
      (rvv_async_rd_addr.enum.map (fun ⟨i, w⟩ => (s!"async_rd_addr_{i}", w))) ++
      (rvv_async_rd_data.enum.map (fun ⟨i, w⟩ => (s!"async_rd_data_{i}", w))) ++
      -- Status
      [("rvv_idle", rvv_idle)] ++
      (rvv_queue_capacity.enum.map (fun ⟨i, w⟩ => (s!"queue_capacity_{i}", w))) ++
      -- Trap
      [("trap_valid_o", rvv_trap_valid)] ++
      -- LSU slot 0: connected to VecLsu
      -- RvvCore outputs (rvv2lsu): read by VecLsu
      [("uop_lsu_valid_rvv2lsu_0", rvv_lsu_valid_rvv2lsu),
       ("uop_lsu_idx_valid_rvv2lsu_0", rvv_lsu_idx_valid_rvv2lsu)] ++
      (rvv_lsu_idx_data_rvv2lsu.enum.map (fun ⟨i, w⟩ => (s!"uop_lsu_idx_data_rvv2lsu_0_{i}", w))) ++
      [("uop_lsu_vregfile_valid_rvv2lsu_0", rvv_lsu_vregfile_valid_rvv2lsu)] ++
      (rvv_lsu_vregfile_data_rvv2lsu.enum.map (fun ⟨i, w⟩ => (s!"uop_lsu_vregfile_data_rvv2lsu_0_{i}", w))) ++
      [("uop_lsu_v0_valid_rvv2lsu_0", rvv_lsu_v0_valid_rvv2lsu)] ++
      (rvv_lsu_v0_data_rvv2lsu.enum.map (fun ⟨i, w⟩ => (s!"uop_lsu_v0_data_rvv2lsu_0_{i}", w))) ++
      [("uop_lsu_ready_rvv2lsu_0", rvv_lsu_ready_rvv2lsu)] ++
      -- RvvCore outputs vd_addr via vregfile_addr
      (rvv_lsu_vd_addr_rvv2lsu.enum.map (fun ⟨i, w⟩ => (s!"uop_lsu_vregfile_addr_rvv2lsu_0_{i}", w))) ++
      -- RvvCore inputs (lsu2rvv): driven by VecLsu
      [("uop_lsu_ready_lsu2rvv_0", rvv_lsu_ready_lsu2rvv),
       ("uop_lsu_valid_lsu2rvv_0", rvv_lsu_valid_lsu2rvv)] ++
      (rvv_lsu_addr_lsu2rvv.enum.map (fun ⟨i, w⟩ => (s!"uop_lsu_addr_lsu2rvv_0_{i}", w))) ++
      (rvv_lsu_data_lsu2rvv.enum.map (fun ⟨i, w⟩ => (s!"uop_lsu_wdata_lsu2rvv_0_{i}", w))) ++
      [("uop_lsu_last_lsu2rvv_0", rvv_lsu_last_lsu2rvv)] ++
      -- LSU slot 1: tied off
      [("uop_lsu_ready_lsu2rvv_1", zero),
       ("uop_lsu_valid_lsu2rvv_1", zero)] ++
      (List.range 5).map (fun b => (s!"uop_lsu_addr_lsu2rvv_1_{b}", zero)) ++
      (List.range 128).map (fun b => (s!"uop_lsu_wdata_lsu2rvv_1_{b}", zero)) ++
      [("uop_lsu_last_lsu2rvv_1", zero)] ++
      -- VCSR writeback from RvvCore (saturation flag)
      [("wr_vxsat_valid_o", rvv_wr_vxsat_valid),
       ("wr_vxsat_o", rvv_wr_vxsat)] ++
      -- Config state outputs (vl/vtype for CSR reads)
      (rvv_config_vl.enum.map (fun ⟨i, w⟩ => (s!"config_state_vl_{i}", w))) ++
      (rvv_config_vtype.enum.map (fun ⟨i, w⟩ => (s!"config_state_vtype_{i}", w))) ++
      [("vcsr_ready", one)] ++
      -- Async FP writeback (tie off for Zve32x)
      [("async_frd_ready", zero)]
  }

  -- Vector instruction valid: gate dispatch with backpressure
  -- rvv_inst_valid = dispatch_vector_valid AND rvv_inst_ready already handled by dispatch
  -- Pack instruction bits[31:7] from raw instruction word
  -- Vector opcode detection from raw instruction bits (imem_resp_data[6:0])
  -- OP-V = 1010111: bit0=1, bit1=1, bit2=1, bit3=0, bit4=1, bit5=0, bit6=1
  let rvv_detect_opv := Wire.mk "rvv_detect_opv"
  let rvv_pack_gates :=
    if enableVector then
      -- Detect OP-V opcode (1010111 = 0x57)
      let n3 := Wire.mk "rvv_n3"  -- NOT bit3
      let n5 := Wire.mk "rvv_n5"  -- NOT bit5
      let a01 := Wire.mk "rvv_a01"
      let a23 := Wire.mk "rvv_a23"
      let a45 := Wire.mk "rvv_a45"
      let a0123 := Wire.mk "rvv_a0123"
      let a01234 := Wire.mk "rvv_a01234"
      let _a456 := Wire.mk "rvv_a456"
      -- Vector load/store opcode detection
      -- VL: opcode=0000111 (0x07), VS: opcode=0100111 (0x27)
      -- Disambiguate from FLW/FSW: funct3 != 010
      let is_vload_opcode := Wire.mk "rvv_is_vload"    -- bits[6:0] == 0000111
      let is_vstore_opcode := Wire.mk "rvv_is_vstore"  -- bits[6:0] == 0100111
      let funct3_not_010 := Wire.mk "rvv_f3n010"
      let vl_a01 := Wire.mk "rvv_vl_a01"    -- bit0 AND bit1
      let vl_a012 := Wire.mk "rvv_vl_a012"  -- bit0 AND bit1 AND bit2
      let not_b3 := Wire.mk "rvv_vlnb3"
      let not_b4 := Wire.mk "rvv_vlnb4"
      let not_b6 := Wire.mk "rvv_vlnb6"
      let vl_upper := Wire.mk "rvv_vl_up"   -- NOT bit3 AND NOT bit4 AND NOT bit5 AND NOT bit6
      let vl_up34 := Wire.mk "rvv_vl_up34"
      let vl_up56 := Wire.mk "rvv_vl_up56"
      let vs_b5_nb6 := Wire.mk "rvv_vs_b5n6"  -- bit5 AND NOT bit6
      let vs_upper := Wire.mk "rvv_vs_up"    -- NOT bit3 AND NOT bit4 AND bit5 AND NOT bit6
      let vls_or := Wire.mk "rvv_vls_or"      -- is_vload OR is_vstore
      -- funct3 = bits[14:12]: disambiguate vector (not 010) from scalar FP (010)
      let not_b12 := Wire.mk "rvv_nb12"
      let b13_nb14 := Wire.mk "rvv_b13nb14"
      let not_b14 := Wire.mk "rvv_nb14"
      let f3_is_010 := Wire.mk "rvv_f3_010"
      -- Strided mode detection: funct3 bit patterns
      -- unit-stride:  funct3[2:1] = 00 (nf varies)
      -- strided:      funct3[2:1] = 01 or 10 or 11 depending on width
      -- Actually for RVV: funct3 encodes EEW. Stride mode is in mop = bits[27:26].
      -- mop=00: unit-stride, mop=10: strided, mop=01/11: indexed
      let mop0 := Wire.mk "rvv_mop0"  -- bit 26
      let mop1 := Wire.mk "rvv_mop1"  -- bit 27
      let not_mop0 := Wire.mk "rvv_nmop0"
      let not_mop1 := Wire.mk "rvv_nmop1"
      let mop_strided := Wire.mk "rvv_mop_str"  -- mop == 10
      let vs_up2 := Wire.mk "rvv_vs_up2"
      let vls_f3 := Wire.mk "rvv_vls_f3"
      let vec_or := Wire.mk "rvv_vec_or"
      let is_vmem := Wire.mk "rvv_is_vmem"
      let not_vmem := Wire.mk "rvv_not_vmem"
      let not_vec_mem := Wire.mk "rvv_nvmem"
      [Gate.mkNOT (imem_resp_data[3]!) n3,
       Gate.mkNOT (imem_resp_data[5]!) n5,
       Gate.mkAND (imem_resp_data[0]!) (imem_resp_data[1]!) a01,
       Gate.mkAND (imem_resp_data[2]!) n3 a23,
       Gate.mkAND (imem_resp_data[4]!) n5 a45,
       Gate.mkAND a01 a23 a0123,
       Gate.mkAND a0123 a45 a01234,
       Gate.mkAND a01234 (imem_resp_data[6]!) rvv_detect_opv,
       -- Vector load: opcode = 0000111
       Gate.mkAND (imem_resp_data[0]!) (imem_resp_data[1]!) vl_a01,
       Gate.mkAND vl_a01 (imem_resp_data[2]!) vl_a012,
       Gate.mkNOT (imem_resp_data[3]!) not_b3,
       Gate.mkNOT (imem_resp_data[4]!) not_b4,
       Gate.mkNOT (imem_resp_data[6]!) not_b6,
       Gate.mkAND not_b3 not_b4 vl_up34,
       Gate.mkAND n5 not_b6 vl_up56,
       Gate.mkAND vl_up34 vl_up56 vl_upper,
       Gate.mkAND vl_a012 vl_upper is_vload_opcode,
       -- Vector store: opcode = 0100111
       Gate.mkAND (imem_resp_data[5]!) not_b6 vs_b5_nb6,
       Gate.mkAND not_b3 not_b4 vs_upper,  -- reuse for bits[4:3] = 00
       Gate.mkAND vs_upper vs_b5_nb6 vs_up2,
       Gate.mkAND vl_a012 vs_up2 is_vstore_opcode,
       -- funct3 disambiguation: NOT (funct3 == 010)
       Gate.mkNOT (imem_resp_data[12]!) not_b12,
       Gate.mkNOT (imem_resp_data[14]!) not_b14,
       Gate.mkAND not_b12 (imem_resp_data[13]!) b13_nb14,
       Gate.mkAND b13_nb14 not_b14 f3_is_010,
       Gate.mkNOT f3_is_010 funct3_not_010,
       -- vls_f3 = (vload OR vstore) AND funct3_not_010 (raw, no decode_valid)
       Gate.mkOR is_vload_opcode is_vstore_opcode vls_or,
       Gate.mkAND vls_or funct3_not_010 vls_f3,
       -- vec_or = OP-V OR vls_f3 (raw vector opcode detection)
       Gate.mkOR rvv_detect_opv vls_f3 vec_or,
       -- Extend decode_valid to include vector instructions (decoder doesn't know them)
       Gate.mkOR decode_valid_scalar vec_or decode_valid,
       -- dispatch_is_vector_mem = vls_f3 AND decode_valid
       Gate.mkAND vls_f3 decode_valid dispatch_is_vector_mem,
       -- dispatch_is_vector = vec_or AND decode_valid
       Gate.mkAND vec_or decode_valid dispatch_is_vector,
       Gate.mkNOT dispatch_is_vector not_dispatch_is_vector,
       -- Strided mode: mop = bits[27:26] == 10
       Gate.mkBUF (imem_resp_data[26]!) mop0,
       Gate.mkBUF (imem_resp_data[27]!) mop1,
       Gate.mkNOT mop0 not_mop0,
       Gate.mkNOT mop1 not_mop1,
       Gate.mkAND not_mop0 mop1 mop_strided] ++
      -- Active-low reset for RvvCore (invert active-high CPU reset)
      [Gate.mkNOT reset rvv_rstn] ++
      -- rvv_inst_valid = dispatch_vector_valid (backpressure handled externally)
      [Gate.mkBUF dispatch_vector_valid rvv_inst_valid] ++
      -- rvv_inst_bits = imem_resp_data[31:7] (bits[31:7] of the instruction)
      (List.range 25).map (fun i => Gate.mkBUF (imem_resp_data[i + 7]!) (rvv_inst_bits[i]!)) ++
      -- rvv_opcode: LOAD=0(00), STORE=1(01), RVV=2(10)
      -- opcode[0] = is_vstore (1 for store, 0 for load and RVV)
      -- opcode[1] = NOT (is_vload OR is_vstore) = rvv_detect_opv effectively
      [Gate.mkOR is_vload_opcode is_vstore_opcode is_vmem,
       Gate.mkNOT is_vmem not_vmem,
       Gate.mkBUF is_vstore_opcode (rvv_opcode[0]!),
       Gate.mkBUF not_vmem (rvv_opcode[1]!),
       -- Gate dispatch_is_memory: exclude vector memory from scalar memory path
       Gate.mkNOT dispatch_is_vector_mem not_vec_mem,
       Gate.mkAND dispatch_is_memory not_vec_mem dispatch_is_scalar_memory] ++
      -- rvv_lsu_is_store output for VecLsu
      [Gate.mkBUF rvv_is_store_reg rvv_lsu_is_store_rvv2lsu] ++
      -- Sidecar capture: base_addr, stride, eew, has_stride
      -- Only capture when VecLsu is idle (ready), preventing overwrites from
      -- back-to-back vector mem instructions before VecLsu consumes the first.
      let sidecar_capture := Wire.mk "sidecar_capture"
      [Gate.mkAND dispatch_is_vector_mem rvv_idle sidecar_capture] ++
      -- base_addr ← rs1_data
      (List.range 32).map (fun i =>
        Gate.mkMUX rvv_base_addr_reg[i]! rs1_data[i]! sidecar_capture rvv_base_addr_next[i]!) ++
      -- stride ← rs2_data
      (List.range 32).map (fun i =>
        Gate.mkMUX rvv_stride_reg[i]! rs2_data[i]! sidecar_capture rvv_stride_next[i]!) ++
      -- EEW from funct3: funct3[1:0] encodes width (00=e8, 01=e16, 10=e32, 11=reserved)
      -- funct3 = bits[14:12], but width encoding is in bits[13:12] for VL/VS
      (List.range 2).map (fun i =>
        Gate.mkMUX rvv_eew_reg[i]! (imem_resp_data[i + 12]!) sidecar_capture rvv_eew_next[i]!) ++
      -- has_stride ← mop_strided
      [Gate.mkMUX rvv_has_stride_reg mop_strided sidecar_capture rvv_has_stride_next,
       Gate.mkMUX rvv_is_store_reg is_vstore_opcode sidecar_capture rvv_is_store_next]
    else [Gate.mkBUF decode_valid_scalar decode_valid,
          Gate.mkBUF dispatch_is_memory dispatch_is_scalar_memory,
          Gate.mkBUF one not_dispatch_is_vector]

  -- Async rd ready: always accept for now
  let rvv_async_gates :=
    if enableVector then [Gate.mkBUF one rvv_async_rd_ready]
    else []

  -- vsetvl scalar writeback: detect OPCFG (funct3=111) at dispatch, capture rd_phys
  -- funct3 = imem_resp_data[14:12], OPCFG = 111
  let rvv_vsetvl_detect := Wire.mk "rvv_vsetvl_detect"
  let rvv_vsetvl_dispatch := Wire.mk "rvv_vsetvl_dispatch"
  let rvv_sidecar_phys := makeIndexedWires "rvv_sidecar_phys" 6
  let rvv_sidecar_phys_next := makeIndexedWires "rvv_sidecar_phys_nx" 6
  let rvv_vsetvl_gates : List Gate :=
    if enableVector then
      -- Detect funct3 = 111 (all three bits high)
      let f3_and := Wire.mk "rvv_f3_and01"
      [Gate.mkAND (imem_resp_data[12]!) (imem_resp_data[13]!) f3_and,
       Gate.mkAND f3_and (imem_resp_data[14]!) rvv_vsetvl_detect,
       -- vsetvl dispatch = vector dispatch AND funct3==111
       Gate.mkAND dispatch_vector_valid rvv_vsetvl_detect rvv_vsetvl_dispatch] ++
      -- Sidecar: capture rd_phys when vsetvl dispatches, hold otherwise
      (List.range 6).map (fun i =>
        Gate.mkMUX rvv_sidecar_phys[i]! rd_phys[i]! rvv_vsetvl_dispatch rvv_sidecar_phys_next[i]!)
    else []
  let rvv_sidecar_dffs : List CircuitInstance :=
    if enableVector then
      (List.range 6).map (fun i => {
        moduleName := "DFlipFlop", instName := s!"u_rvv_sidecar_phys_dff_{i}",
        portMap := [("d", rvv_sidecar_phys_next[i]!), ("q", rvv_sidecar_phys[i]!),
                    ("clock", clock), ("reset", reset)] })
    else []

  -- VecLsu sidecar DFFs: base_addr, stride, eew, has_stride
  let rvv_mem_sidecar_dffs : List CircuitInstance :=
    if enableVector then
      (List.range 32).map (fun i => {
        moduleName := "DFlipFlop", instName := s!"u_rvv_base_addr_dff_{i}",
        portMap := [("d", rvv_base_addr_next[i]!), ("q", rvv_base_addr_reg[i]!),
                    ("clock", clock), ("reset", reset)] }) ++
      (List.range 32).map (fun i => {
        moduleName := "DFlipFlop", instName := s!"u_rvv_stride_dff_{i}",
        portMap := [("d", rvv_stride_next[i]!), ("q", rvv_stride_reg[i]!),
                    ("clock", clock), ("reset", reset)] }) ++
      (List.range 2).map (fun i => {
        moduleName := "DFlipFlop", instName := s!"u_rvv_eew_dff_{i}",
        portMap := [("d", rvv_eew_next[i]!), ("q", rvv_eew_reg[i]!),
                    ("clock", clock), ("reset", reset)] }) ++
      [{ moduleName := "DFlipFlop", instName := "u_rvv_has_stride_dff",
         portMap := [("d", rvv_has_stride_next), ("q", rvv_has_stride_reg),
                     ("clock", clock), ("reset", reset)] },
       { moduleName := "DFlipFlop", instName := "u_rvv_is_store_dff",
         portMap := [("d", rvv_is_store_next), ("q", rvv_is_store_reg),
                     ("clock", clock), ("reset", reset)] }]
    else []

  -- VecLsu instance
  let rvv_vec_lsu_inst : List CircuitInstance :=
    if enableVector then
      [{ moduleName := "VecLsu", instName := "u_vec_lsu",
         portMap :=
           [("clock", clock), ("reset", reset), ("zero_const", zero), ("one_const", one)] ++
           (rvv_base_addr_reg.enum.map (fun ⟨i, w⟩ => (s!"base_addr_{i}", w))) ++
           (rvv_stride_reg.enum.map (fun ⟨i, w⟩ => (s!"stride_{i}", w))) ++
           [("has_stride", rvv_has_stride_reg)] ++
           -- rvv2lsu inputs (from RvvCore)
           [("rvv2lsu_valid", rvv_lsu_valid_rvv2lsu),
            ("rvv2lsu_idx_valid", rvv_lsu_idx_valid_rvv2lsu)] ++
           (rvv_lsu_idx_data_rvv2lsu.enum.map (fun ⟨i, w⟩ => (s!"rvv2lsu_idx_data_{i}", w))) ++
           [("rvv2lsu_vregfile_valid", rvv_lsu_vregfile_valid_rvv2lsu)] ++
           (rvv_lsu_vregfile_data_rvv2lsu.enum.map (fun ⟨i, w⟩ => (s!"rvv2lsu_vregfile_data_{i}", w))) ++
           [("rvv2lsu_mask_valid", rvv_lsu_v0_valid_rvv2lsu)] ++
           (rvv_lsu_v0_data_rvv2lsu.enum.map (fun ⟨i, w⟩ => (s!"rvv2lsu_mask_{i}", w))) ++
           (rvv_lsu_vd_addr_rvv2lsu.enum.map (fun ⟨i, w⟩ => (s!"rvv2lsu_vd_addr_{i}", w))) ++
           [("rvv2lsu_is_store", rvv_lsu_is_store_rvv2lsu)] ++
           -- lsu2rvv ready (from RvvCore)
           [("lsu2rvv_ready", rvv_lsu_ready_rvv2lsu)] ++
           -- DMEM interface
           [("dmem_req_ready", vec_dmem_req_ready),
            ("dmem_resp_valid", vec_dmem_resp_valid)] ++
           (vec_dmem_resp_rdata.enum.map (fun ⟨i, w⟩ => (s!"dmem_resp_data_{i}", w))) ++
           -- EEW
           (rvv_eew_reg.enum.map (fun ⟨i, w⟩ => (s!"eew_{i}", w))) ++
           -- Outputs
           [("rvv2lsu_ready", rvv_lsu_ready_lsu2rvv)] ++
           [("lsu2rvv_valid", rvv_lsu_valid_lsu2rvv)] ++
           (rvv_lsu_data_lsu2rvv.enum.map (fun ⟨i, w⟩ => (s!"lsu2rvv_data_{i}", w))) ++
           (rvv_lsu_addr_lsu2rvv.enum.map (fun ⟨i, w⟩ => (s!"lsu2rvv_addr_{i}", w))) ++
           [("lsu2rvv_last", rvv_lsu_last_lsu2rvv)] ++
           [("dmem_req_valid", vec_dmem_req_valid),
            ("dmem_req_we", vec_dmem_req_we)] ++
           (vec_dmem_req_addr.enum.map (fun ⟨i, w⟩ => (s!"dmem_req_addr_{i}", w))) ++
           (vec_dmem_req_data.enum.map (fun ⟨i, w⟩ => (s!"dmem_req_data_{i}", w))) ++
           (vec_dmem_req_size.enum.map (fun ⟨i, w⟩ => (s!"dmem_req_size_{i}", w)))
       }]
    else []

  -- OR RvvCore scalar writeback into CSR CDB inject path
  -- rvv_reg_write_valid is mutually exclusive with csr_cdb_inject (both serialize)
  -- Create merged inject/tag/data wires that combine CSR and RVV sources
  let merged_cdb_inject := Wire.mk "merged_cdb_inject"
  let merged_cdb_tag := makeIndexedWires "merged_cdb_tg" 6
  let merged_cdb_data := makeIndexedWires "merged_cdb_dt" 32
  let rvv_cdb_or_gates : List Gate :=
    if enableVector then
      [Gate.mkOR csr_cdb_inject rvv_reg_write_valid merged_cdb_inject] ++
      -- MUX tag: if rvv_reg_write_valid, use sidecar phys; else use csr_cdb_tag
      (List.range 6).map (fun i =>
        Gate.mkMUX csr_cdb_tag[i]! rvv_sidecar_phys[i]! rvv_reg_write_valid merged_cdb_tag[i]!) ++
      -- MUX data: if rvv_reg_write_valid, use rvv_reg_write_data; else use csr_cdb_data
      (List.range 32).map (fun i =>
        Gate.mkMUX csr_cdb_data[i]! rvv_reg_write_data[i]! rvv_reg_write_valid merged_cdb_data[i]!)
    else
      -- No vector: just BUF through
      [Gate.mkBUF csr_cdb_inject merged_cdb_inject] ++
      (List.range 6).map (fun i => Gate.mkBUF csr_cdb_tag[i]! merged_cdb_tag[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF csr_cdb_data[i]! merged_cdb_data[i]!)

  -- === LUI/AUIPC POST-ALU MUX ===
  let auipc_result := makeIndexedWires "auipc_result" 32
  let auipc_adder_inst : CircuitInstance := {
    moduleName := "KoggeStoneAdder32"
    instName := "u_auipc_adder"
    portMap :=
      (int_captured_pc.enum.map (fun ⟨i, w⟩ => (s!"a_{i}", w))) ++
      (int_captured_imm.enum.map (fun ⟨i, w⟩ => (s!"b_{i}", w))) ++
      [("cin", zero)] ++
      (auipc_result.enum.map (fun ⟨i, w⟩ => (s!"sum_{i}", w))) ++
      []
  }

  -- Opcode match: LUI and AUIPC encodings from config
  let is_lui := Wire.mk "is_lui"
  let is_auipc := Wire.mk "is_auipc"
  let lui_match_gates := mkOpcodeMatch6 "lui_match" (oi .LUI) rs_int_dispatch_opcode is_lui
  let auipc_match_gates := mkOpcodeMatch6 "auipc_match" (oi .AUIPC) rs_int_dispatch_opcode is_auipc

  -- Post-ALU MUX: int_result_final = MUX(MUX(int_result, auipc_result, is_auipc), int_captured_imm, is_lui)
  let int_result_final := makeIndexedWires "int_result_final" 32
  let int_auipc_muxed := makeIndexedWires "int_auipc_muxed" 32
  let lui_auipc_gates := (List.range 32).map (fun i =>
    [ Gate.mkMUX int_result[i]! auipc_result[i]! is_auipc int_auipc_muxed[i]!,
      Gate.mkMUX int_auipc_muxed[i]! int_captured_imm[i]! is_lui int_result_final[i]! ]
  ) |>.flatten

  -- === BRANCH RESOLVE (extracted helper) ===
  let (branch_resolve_gates, branch_resolve_insts,
       _branch_taken, branch_mispredicted, final_branch_target,
       br_pc_plus_4, branch_result_final, _is_jal_or_jalr,
       mispredict_redirect_target) :=
    mkBranchResolve config oi zero one
      br_captured_pc br_captured_imm
      rs_branch_dispatch_src1 rs_branch_dispatch_src2 rs_branch_dispatch_opcode
      branch_result branch_predicted_taken
      rob_commit_en rob_head_isBranch rob_head_mispredicted
      rob_head_redirect_target fence_i_redir_target fence_i_drain_complete
      csr_flush_suppress not_csr_flush_suppress rename_flush_en redirect_valid_int
      rob_redirect_valid branch_redirect_target

  -- === LSU ===
  let lsu_agu_address := makeIndexedWires "lsu_agu_address" 32
  let lsu_agu_tag := makeIndexedWires "lsu_agu_tag" 6
  let lsu_sb_full := Wire.mk "lsu_sb_full"
  let lsu_sb_empty := Wire.mk "lsu_sb_empty"
  let lsu_sb_fwd_hit := Wire.mk "lsu_sb_fwd_hit"
  let lsu_sb_fwd_committed_hit := Wire.mk "lsu_sb_fwd_committed_hit"
  let lsu_sb_fwd_word_hit := Wire.mk "lsu_sb_fwd_word_hit"
  let lsu_sb_fwd_word_only_hit := Wire.mk "lsu_sb_fwd_word_only_hit"
  let lsu_sb_fwd_data := makeIndexedWires "lsu_sb_fwd_data" 32
  let lsu_sb_fwd_size := makeIndexedWires "lsu_sb_fwd_size" 2
  let lsu_sb_deq_valid := Wire.mk "lsu_sb_deq_valid"
  let lsu_sb_deq_bits := makeIndexedWires "lsu_sb_deq_bits" 66
  let lsu_sb_enq_idx := makeIndexedWires "lsu_sb_enq_idx" 3

  let lsu_inst : CircuitInstance := {
    moduleName := "LSU"
    instName := "u_lsu"
    portMap := [("clock", clock), ("reset", reset),
                ("zero", zero), ("one", one),
                ("commit_store_en", commit_store_en),
                ("deq_ready", dmem_req_ready),
                ("flush_en", pipeline_flush_comb),
                ("sb_enq_en", sb_enq_en),
                ("sb_full", lsu_sb_full), ("sb_empty", lsu_sb_empty), ("sb_fwd_hit", lsu_sb_fwd_hit),
                ("sb_fwd_committed_hit", lsu_sb_fwd_committed_hit),
                ("sb_fwd_word_hit", lsu_sb_fwd_word_hit),
                ("sb_fwd_word_only_hit", lsu_sb_fwd_word_only_hit),
                ("sb_deq_valid", lsu_sb_deq_valid)] ++
               (rs_mem_dispatch_src1.enum.map (fun ⟨i, w⟩ => (s!"dispatch_base_{i}", w))) ++
               (captured_imm.enum.map (fun ⟨i, w⟩ => (s!"dispatch_offset_{i}", w))) ++
               (rs_mem_dispatch_tag.enum.map (fun ⟨i, w⟩ => (s!"dispatch_dest_tag_{i}", w))) ++
               ((makeIndexedWires "store_data_masked" 32).enum.map (fun ⟨i, w⟩ => (s!"store_data_{i}", w))) ++
               (mem_addr_r.enum.map (fun ⟨i, w⟩ => (s!"fwd_address_{i}", w))) ++
               ((makeIndexedWires "lsu_sb_enq_size" 2).enum.map (fun ⟨i, w⟩ => (s!"sb_enq_size_{i}", w))) ++
               (lsu_agu_address.enum.map (fun ⟨i, w⟩ => (s!"agu_address_{i}", w))) ++
               (lsu_agu_tag.enum.map (fun ⟨i, w⟩ => (s!"agu_tag_out_{i}", w))) ++
               (lsu_sb_fwd_data.enum.map (fun ⟨i, w⟩ => (s!"sb_fwd_data_{i}", w))) ++
               (lsu_sb_fwd_size.enum.map (fun ⟨i, w⟩ => (s!"sb_fwd_size_{i}", w))) ++
               (lsu_sb_deq_bits.enum.map (fun ⟨i, w⟩ => (s!"sb_deq_bits_{i}", w))) ++
               (lsu_sb_enq_idx.enum.map (fun ⟨i, w⟩ => (s!"sb_enq_idx_{i}", w)))
  }

  -- === ROB ===
  let rob_full := Wire.mk "rob_full"
  let rob_empty := Wire.mk "rob_empty"
  let rob_alloc_idx := makeIndexedWires "rob_alloc_idx" 4
  let rob_head_valid := Wire.mk "rob_head_valid"
  let rob_head_complete := Wire.mk "rob_head_complete"
  let rob_head_hasPhysRd := Wire.mk "rob_head_hasPhysRd"
  let rob_head_archRd := makeIndexedWires "rob_head_archRd" 5
  let rob_head_exception := Wire.mk "rob_head_exception"
  let rob_head_idx := makeIndexedWires "rob_head_idx" 4

  let rob_inst : CircuitInstance := {
    moduleName := "ROB16"
    instName := "u_rob"
    portMap :=
      [("clock", clock), ("reset", pipeline_reset_rob),
       ("zero", zero), ("one", one),
       ("alloc_en", rename_valid_gated)] ++
      -- Branches get unmasked unique tag for CDB misprediction tracking.
      -- rob_alloc_physRd = branch ? rd_phys : (enableF ? fp_issue_dest_tag : int_dest_tag_masked)
      ((if enableF then rob_alloc_physRd_fp else branch_alloc_physRd).enum.map (fun ⟨i, w⟩ => (s!"alloc_physRd[{i}]", w))) ++
      [("alloc_hasPhysRd", if enableF then rob_alloc_hasPhysRd_fp else branch_alloc_hasPhysRd)] ++
      ((if enableF then rob_old_phys_muxed else old_rd_phys).enum.map (fun ⟨i, w⟩ => (s!"alloc_oldPhysRd[{i}]", w))) ++
      [("alloc_hasOldPhysRd", if enableF then decode_has_any_rd_nox0 else decode_has_rd_nox0)] ++
      (decode_rd.enum.map (fun ⟨i, w⟩ => (s!"alloc_archRd[{i}]", w))) ++
      [("alloc_isBranch", dispatch_is_branch),
       ("cdb_valid", cdb_valid)] ++
      (cdb_tag_rob.enum.map (fun ⟨i, w⟩ => (s!"cdb_tag[{i}]", w))) ++
      [("cdb_exception", zero),
       ("cdb_mispredicted", Wire.mk "cdb_mispredicted"),
       ("cdb_is_fp", if enableF then cdb_is_fp_rd else zero)] ++
      ((List.range 16).map (fun i =>
        (s!"is_fp_shadow_{i}", if enableF then Wire.mk s!"rob_is_fp_e{i}" else zero))) ++
      [("commit_en", rob_commit_en),
       ("flush_en", branch_redirect_valid_reg),
       ("full", rob_full),
       ("empty", rob_empty)] ++
      (rob_alloc_idx.enum.map (fun ⟨i, w⟩ => (s!"alloc_idx[{i}]", w))) ++
      (rob_head_idx.enum.map (fun ⟨i, w⟩ => (s!"head_idx[{i}]", w))) ++
      [("head_valid", rob_head_valid),
       ("head_complete", rob_head_complete)] ++
      (rob_head_physRd.enum.map (fun ⟨i, w⟩ => (s!"head_physRd[{i}]", w))) ++
      [("head_hasPhysRd", rob_head_hasPhysRd)] ++
      (rob_head_oldPhysRd.enum.map (fun ⟨i, w⟩ => (s!"head_oldPhysRd[{i}]", w))) ++
      [("head_hasOldPhysRd", rob_head_hasOldPhysRd)] ++
      (rob_head_archRd.enum.map (fun ⟨i, w⟩ => (s!"head_archRd[{i}]", w))) ++
      [("head_exception", rob_head_exception),
       ("head_isBranch", rob_head_isBranch),
       ("head_mispredicted", rob_head_mispredicted)]
  }

  -- === RVVI INFRASTRUCTURE ===
  -- PC queue and instruction queue for RVVI-TRACE output
  let rvvi_valid := Wire.mk "rvvi_valid"
  let rvvi_trap := Wire.mk "rvvi_trap"
  let rvvi_pc_rdata := makeIndexedWires "rvvi_pc_rdata" 32
  let rvvi_insn := makeIndexedWires "rvvi_insn" 32
  let rvvi_rd := makeIndexedWires "rvvi_rd" 5
  let rvvi_rd_valid := Wire.mk "rvvi_rd_valid"
  -- FP RVVI signals (F extension)
  let rvvi_frd := makeIndexedWires "rvvi_frd" 5
  let rvvi_frd_valid := Wire.mk "rvvi_frd_valid"
  let rvvi_frd_data := makeIndexedWires "rvvi_frd_data" 32

  let pc_queue_inst : CircuitInstance := {
    moduleName := "Queue16x32"
    instName := "u_pc_queue"
    portMap :=
      [("clock", clock), ("reset", reset),
       ("wr_en", rename_valid_gated)] ++
      (rob_alloc_idx.enum.map (fun ⟨i, w⟩ => (s!"wr_idx_{i}", w))) ++
      (fetch_pc.enum.map (fun ⟨i, w⟩ => (s!"wr_data_{i}", w))) ++
      (rob_head_idx.enum.map (fun ⟨i, w⟩ => (s!"rd_idx_{i}", w))) ++
      (rvvi_pc_rdata.enum.map (fun ⟨i, w⟩ => (s!"rd_data_{i}", w)))
  }

  let insn_queue_inst : CircuitInstance := {
    moduleName := "Queue16x32"
    instName := "u_insn_queue"
    portMap :=
      [("clock", clock), ("reset", reset),
       ("wr_en", rename_valid_gated)] ++
      (rob_alloc_idx.enum.map (fun ⟨i, w⟩ => (s!"wr_idx_{i}", w))) ++
      (imem_resp_data.enum.map (fun ⟨i, w⟩ => (s!"wr_data_{i}", w))) ++
      (rob_head_idx.enum.map (fun ⟨i, w⟩ => (s!"rd_idx_{i}", w))) ++
      (rvvi_insn.enum.map (fun ⟨i, w⟩ => (s!"rd_data_{i}", w)))
  }

  -- RVVI output logic
  -- rvvi_valid = rob_commit_en (head_valid AND head_complete)
  -- rvvi_trap = rob_head_exception AND rob_commit_en
  -- rvvi_rd[4:0] = rob_head_archRd
  -- rvvi_rd_valid = rob_head_hasPhysRd AND rob_commit_en
  -- rvvi_rd_data = prf rd_data4 with CDB bypass
  -- When CDB writes to the same preg as rob_head_physRd in the same cycle,
  -- the PRF DFF hasn't updated yet. Bypass CDB data to get correct RVVI value.
  -- CDB bypass for RVVI: when CDB writes to rob_head_physRd in same cycle,
  -- PRF DFF hasn't updated yet. Use CDB data instead.
  let rvvi_cdb_bypass_match := Wire.mk "rvvi_cdb_bypass_match"
  let rvvi_cdb_tag_xor := (List.range 6).map (fun i => Wire.mk s!"rvvi_cdb_xor_{i}")
  let rvvi_cdb_bypass_gates :=
    -- XOR each bit: 0 if equal, 1 if different
    (List.range 6).map (fun i =>
      Gate.mkXOR cdb_tag_rob[i]! rob_head_physRd[i]! rvvi_cdb_tag_xor[i]!) ++
    -- OR all XOR bits: any_diff = 1 if tags differ
    (let or01 := Wire.mk "rvvi_xor_or01"
     let or23 := Wire.mk "rvvi_xor_or23"
     let or45 := Wire.mk "rvvi_xor_or45"
     let or0123 := Wire.mk "rvvi_xor_or0123"
     let any_diff := Wire.mk "rvvi_any_diff"
     let tags_eq := Wire.mk "rvvi_tags_eq"
     [Gate.mkOR rvvi_cdb_tag_xor[0]! rvvi_cdb_tag_xor[1]! or01,
      Gate.mkOR rvvi_cdb_tag_xor[2]! rvvi_cdb_tag_xor[3]! or23,
      Gate.mkOR rvvi_cdb_tag_xor[4]! rvvi_cdb_tag_xor[5]! or45,
      Gate.mkOR or01 or23 or0123,
      Gate.mkOR or0123 or45 any_diff,
      Gate.mkNOT any_diff tags_eq,
      Gate.mkAND tags_eq cdb_valid_prf rvvi_cdb_bypass_match]) ++
    -- MUX: bypass CDB data when match
    (List.range 32).map (fun i =>
      Gate.mkMUX rvvi_rd_data[i]! cdb_data[i]! rvvi_cdb_bypass_match (Wire.mk s!"rvvi_rd_data_{i}"))
  let rvvi_rd_data_final := (List.range 32).map (fun i => Wire.mk s!"rvvi_rd_data_{i}")

  let rvvi_gates :=
    [Gate.mkBUF rob_commit_en rvvi_valid,
     Gate.mkAND rob_head_exception rob_commit_en rvvi_trap,
     Gate.mkAND rob_head_hasPhysRd rob_commit_en rvvi_rd_valid] ++
    (List.range 5).map (fun i =>
      Gate.mkBUF rob_head_archRd[i]! rvvi_rd[i]!)

  -- FP RVVI gates: rvvi_frd_valid = rob_head_is_fp AND rob_commit_en
  -- rvvi_frd = rob_head_archRd (same arch rd field, FP regs share encoding)
  -- rvvi_frd_data = FP PRF rd_data4 (via fp_rename 4th read port)
  let rvvi_fp_gates :=
    if enableF then
      [Gate.mkAND (Wire.mk "rob_head_is_fp") rob_commit_en rvvi_frd_valid] ++
      (List.range 5).map (fun i => Gate.mkBUF rob_head_archRd[i]! rvvi_frd[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF fp_rvvi_rd_data[i]! rvvi_frd_data[i]!)
    else
      [Gate.mkBUF zero rvvi_frd_valid] ++
      (List.range 5).map (fun i => Gate.mkBUF zero rvvi_frd[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF zero rvvi_frd_data[i]!)

  -- === FFLAGS ACCUMULATOR + FRM REGISTER ===
  let fflags_acc := makeIndexedWires "fflags_acc" 5
  let fflags_reg := makeIndexedWires "fflags_reg" 5
  let fflags_new := makeIndexedWires "fflags_new" 5
  let fflags_masked := makeIndexedWires "fflags_masked" 5
  let fflags_acc_val := makeIndexedWires "fflags_acc_val" 5
  let (fflags_gates, fflags_frm_dff_instances) := mkFPFlags
    enableF zero one clock reset
    fp_valid_out fp_exceptions
    fflags_reg fflags_new fflags_acc fflags_masked fflags_acc_val
    frm_reg frm_new
  let fflags_dff_instances := fflags_frm_dff_instances.take 5
  let frm_dff_instances := fflags_frm_dff_instances.drop 5
  let frm_gates : List Gate := []  -- included in fflags_gates

  -- === CDB FIFO-BASED ARBITRATION ===
  -- Each execution unit output enters a Queue1_39 FIFO (6 tag + 32 data + 1 is_fp_rd).
  -- The CDB arbiter is a priority drain over FIFO deq_valid signals.
  -- Backpressure (enq_ready) stalls the RS when the FIFO is occupied.

  -- Level 0: Merge Branch into Integer (mutually exclusive — same dispatch slot)
  let int_branch_valid := Wire.mk "int_branch_valid"
  let int_branch_tag := makeIndexedWires "int_branch_tag" 6
  let int_branch_data := makeIndexedWires "int_branch_data" 32

  let branch_dispatch_gated := Wire.mk "branch_dispatch_gated"
  let branch_dispatch_gated_pre := Wire.mk "branch_dispatch_gated_pre"
  let arb_level0_gates :=
    [Gate.mkAND rs_branch_dispatch_valid not_cross_size_stall branch_dispatch_gated_pre,
     Gate.mkAND branch_dispatch_gated_pre not_int_dispatching branch_dispatch_gated,
     Gate.mkOR rs_int_dispatch_valid branch_dispatch_gated int_branch_valid] ++
    (List.range 6).map (fun i =>
      Gate.mkMUX branch_tag_out[i]! int_tag_out[i]! rs_int_dispatch_valid int_branch_tag[i]!) ++
    (List.range 32).map (fun i =>
      Gate.mkMUX branch_result_final[i]! int_result_final[i]! rs_int_dispatch_valid int_branch_data[i]!)

  -- FP is_fp_rd computation: NOT fp_result_is_int (FMV.X.W etc. target INT PRF)
  let fp_enq_is_fp := Wire.mk "fp_enq_is_fp"
  let fp_enq_is_fp_gate :=
    if enableF then [Gate.mkNOT fp_result_is_int fp_enq_is_fp]
    else [Gate.mkBUF zero fp_enq_is_fp]

  -- FIFO enqueue data buses
  -- IB FIFO: 72 bits: tag[5:0] ++ data[37:6] ++ is_fp_rd[38] ++ redirect_target[70:39] ++ mispredicted[71]
  -- Assembled via BUF gates so Chisel codegen sees them as coherent signal groups.
  let ib_fifo_enq_data := makeIndexedWires "ib_fifo_enq_data" 72
  let muldiv_fifo_enq_data := makeIndexedWires "muldiv_fifo_enq_data" 39
  let fp_fifo_enq_data := makeIndexedWires "fp_fifo_enq_data" 39
  let lsu_fifo_enq_data := makeIndexedWires "lsu_fifo_enq_data" 39

  let ib_fifo_enq_assemble :=
    (List.range 6).map (fun i => Gate.mkBUF int_branch_tag[i]! ib_fifo_enq_data[i]!) ++
    (List.range 32).map (fun i => Gate.mkBUF int_branch_data[i]! ib_fifo_enq_data[6+i]!) ++
    [Gate.mkBUF zero ib_fifo_enq_data[38]!] ++  -- is_fp_rd = 0
    -- bits [70:39]: redirect_target (gated by branch dispatch; zero for integer)
    (List.range 32).map (fun i =>
      Gate.mkAND mispredict_redirect_target[i]! branch_dispatch_gated ib_fifo_enq_data[39+i]!) ++
    -- bit [71]: mispredicted flag (gated by branch dispatch; zero for integer)
    [Gate.mkAND branch_mispredicted branch_dispatch_gated ib_fifo_enq_data[71]!]

  let muldiv_fifo_enq_assemble :=
    if enableM then
      (List.range 6).map (fun i => Gate.mkBUF muldiv_tag_out[i]! muldiv_fifo_enq_data[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF muldiv_result[i]! muldiv_fifo_enq_data[6+i]!) ++
      [Gate.mkBUF zero muldiv_fifo_enq_data[38]!]  -- is_fp_rd = 0
    else
      (List.range 39).map (fun i => Gate.mkBUF zero muldiv_fifo_enq_data[i]!)

  let fp_fifo_enq_assemble :=
    if enableF then
      (List.range 6).map (fun i => Gate.mkBUF fp_tag_out[i]! fp_fifo_enq_data[i]!) ++
      (List.range 32).map (fun i => Gate.mkBUF fp_result[i]! fp_fifo_enq_data[6+i]!) ++
      [Gate.mkBUF fp_enq_is_fp fp_fifo_enq_data[38]!]  -- is_fp_rd = NOT is_int
    else
      (List.range 39).map (fun i => Gate.mkBUF zero fp_fifo_enq_data[i]!)

  -- FIFO output wires (ib_fifo_enq_ready declared earlier near RS instances)
  let ib_fifo_deq_valid := Wire.mk "ib_fifo_deq_valid"
  let ib_fifo_deq := makeIndexedWires "ib_fifo_deq" 72
  let ib_fifo_drain := Wire.mk "ib_fifo_drain"

  let muldiv_fifo_enq_ready := Wire.mk "muldiv_fifo_enq_ready"
  let muldiv_fifo_deq_valid := Wire.mk "muldiv_fifo_deq_valid"
  let muldiv_fifo_deq := makeIndexedWires "muldiv_fifo_deq" 39
  let muldiv_fifo_drain := Wire.mk "muldiv_fifo_drain"

  let fp_fifo_deq_valid := Wire.mk "fp_fifo_deq_valid"
  let fp_fifo_deq := makeIndexedWires "fp_fifo_deq" 39
  let fp_fifo_drain := Wire.mk "fp_fifo_drain"

  let lsu_fifo_enq_ready := Wire.mk "lsu_fifo_enq_ready"
  let lsu_fifo_deq_valid := Wire.mk "lsu_fifo_deq_valid"
  let lsu_fifo_deq := makeIndexedWires "lsu_fifo_deq" 39
  let lsu_fifo_drain := Wire.mk "lsu_fifo_drain"

  -- INT/Branch FIFO instance (72 bits: tag+data+is_fp+redirect_target+mispredicted)
  let ib_fifo_inst : CircuitInstance := {
    moduleName := "Queue1Flow_72", instName := "u_cdb_fifo_ib",
    portMap := [("clock", clock), ("reset", pipeline_reset_busy),
                ("enq_valid", int_branch_valid),
                ("deq_ready", ib_fifo_drain),
                ("enq_ready", ib_fifo_enq_ready),
                ("deq_valid", ib_fifo_deq_valid)] ++
      (List.range 72).map (fun i => (s!"enq_data_{i}", ib_fifo_enq_data[i]!)) ++
      (List.range 72).map (fun i => (s!"deq_data_{i}", ib_fifo_deq[i]!))
  }

  -- MulDiv FIFO instance (conditional on M-extension)
  let muldiv_fifo_inst : CircuitInstance := {
    moduleName := "Queue1Flow_39", instName := "u_cdb_fifo_muldiv",
    portMap := [("clock", clock), ("reset", pipeline_reset_rs_muldiv),
                ("enq_valid", muldiv_valid_out),
                ("deq_ready", muldiv_fifo_drain),
                ("enq_ready", muldiv_fifo_enq_ready),
                ("deq_valid", muldiv_fifo_deq_valid)] ++
      (List.range 39).map (fun i => (s!"enq_data_{i}", muldiv_fifo_enq_data[i]!)) ++
      (List.range 39).map (fun i => (s!"deq_data_{i}", muldiv_fifo_deq[i]!))
  }

  -- FP FIFO instance (conditional on F-extension)
  let fp_fifo_inst : CircuitInstance := {
    moduleName := "Queue1Flow_39", instName := "u_cdb_fifo_fp",
    portMap := [("clock", clock), ("reset", pipeline_reset_rs_fp),
                ("enq_valid", fp_valid_out),
                ("deq_ready", fp_fifo_drain),
                ("enq_ready", fp_fifo_enq_ready),
                ("deq_valid", fp_fifo_deq_valid)] ++
      (List.range 39).map (fun i => (s!"enq_data_{i}", fp_fifo_enq_data[i]!)) ++
      (List.range 39).map (fun i => (s!"deq_data_{i}", fp_fifo_deq[i]!))
  }

  -- Dummy gates to tie off unused FIFO wires when extensions disabled
  let muldiv_fifo_dummy_gates :=
    if enableM then []
    else [Gate.mkBUF one muldiv_fifo_enq_ready,
          Gate.mkBUF zero muldiv_fifo_deq_valid] ++
         (List.range 39).map (fun i => Gate.mkBUF zero muldiv_fifo_deq[i]!)

  let fp_fifo_dummy_gates :=
    if enableF then []
    else [Gate.mkBUF one fp_fifo_enq_ready,
          Gate.mkBUF zero fp_fifo_deq_valid] ++
         (List.range 39).map (fun i => Gate.mkBUF zero fp_fifo_deq[i]!)

  -- === LSU STORE-TO-LOAD FORWARDING ===
  let is_lw := Wire.mk "is_lw"
  let is_lh := Wire.mk "is_lh"
  let is_lhu := Wire.mk "is_lhu"
  let is_lb := Wire.mk "is_lb"
  let is_lbu := Wire.mk "is_lbu"
  let is_load := Wire.mk "is_load"
  let is_load_tmp1 := Wire.mk "is_load_tmp1"
  let is_load_tmp2 := Wire.mk "is_load_tmp2"
  let is_load_tmp3 := Wire.mk "is_load_tmp3"

  let lw_match_gates := mkOpcodeMatch6 "lw_match" (oi .LW) rs_mem_dispatch_opcode is_lw
  let lh_match_gates := mkOpcodeMatch6 "lh_match" (oi .LH) rs_mem_dispatch_opcode is_lh
  let lhu_match_gates := mkOpcodeMatch6 "lhu_match" (oi .LHU) rs_mem_dispatch_opcode is_lhu
  let lb_match_gates := mkOpcodeMatch6 "lb_match" (oi .LB) rs_mem_dispatch_opcode is_lb
  let lbu_match_gates := mkOpcodeMatch6 "lbu_match" (oi .LBU) rs_mem_dispatch_opcode is_lbu
  -- FLW detection (conditional on F extension)
  let is_flw := Wire.mk "is_flw"
  let flw_match_gates :=
    if enableF then mkOpcodeMatch6 "flw_match" (oi .FLW) rs_mem_dispatch_opcode is_flw
    else [Gate.mkBUF zero is_flw]

  let is_load_gates := [
    Gate.mkOR is_lw is_lh is_load_tmp1,
    Gate.mkOR is_load_tmp1 is_lhu is_load_tmp2,
    Gate.mkOR is_load_tmp2 is_lb is_load_tmp3,
    Gate.mkOR is_load_tmp3 is_lbu (Wire.mk "is_load_int"),
    Gate.mkOR (Wire.mk "is_load_int") is_flw is_load
  ]

  -- === STORE TYPE DECODE ===
  let is_sw := Wire.mk "is_sw"
  let is_sh := Wire.mk "is_sh"
  let is_sb := Wire.mk "is_sb"
  let is_fsw := Wire.mk "is_fsw"
  let sw_match_gates := mkOpcodeMatch6 "sw_match" (oi .SW) rs_mem_dispatch_opcode is_sw
  let sh_match_gates := mkOpcodeMatch6 "sh_match" (oi .SH) rs_mem_dispatch_opcode is_sh
  let sb_match_gates := mkOpcodeMatch6 "sb_match" (oi .SB) rs_mem_dispatch_opcode is_sb
  let fsw_match_gates :=
    if enableF then mkOpcodeMatch6 "fsw_match" (oi .FSW) rs_mem_dispatch_opcode is_fsw
    else [Gate.mkBUF zero is_fsw]

  -- Derive mem_size[1:0]: 00=byte, 01=half, 10=word
  -- For loads: is_lb|is_lbu → 00, is_lh|is_lhu → 01, is_lw|is_flw → 10
  -- For stores: is_sb → 00, is_sh → 01, is_sw|is_fsw → 10
  -- mem_size_0 = is_lh | is_lhu | is_sh
  -- mem_size_1 = is_lw | is_flw | is_sw | is_fsw
  let mem_size := makeIndexedWires "mem_size" 2
  let mem_size_0_tmp1 := Wire.mk "mem_size_0_tmp1"
  let mem_size_0_tmp2 := Wire.mk "mem_size_0_tmp2"
  let mem_size_1_tmp1 := Wire.mk "mem_size_1_tmp1"
  let mem_size_1_tmp2 := Wire.mk "mem_size_1_tmp2"
  let mem_size_gates := [
    Gate.mkOR is_lh is_lhu mem_size_0_tmp1,
    Gate.mkOR mem_size_0_tmp1 is_sh mem_size_0_tmp2,
    Gate.mkBUF mem_size_0_tmp2 mem_size[0]!,
    Gate.mkOR is_lw is_sw mem_size_1_tmp1,
    Gate.mkOR mem_size_1_tmp1 is_flw mem_size_1_tmp2,
    Gate.mkOR mem_size_1_tmp2 is_fsw mem_size[1]!
  ]

  -- sign_extend: 1 for LB/LH, 0 for LBU/LHU/LW/FLW and all stores
  let sign_extend := Wire.mk "sign_extend"
  let sign_extend_gates := [
    Gate.mkOR is_lb is_lh sign_extend
  ]

  -- === MEMORY ADDRESS PIPELINE REGISTER ===
  let (mem_pipe_gates, mem_pipe_insts) := mkMemPipeline clock reset
    rs_mem_dispatch_valid mem_dispatch_en
    mem_address rs_mem_dispatch_tag
    is_load is_flw mem_size sign_extend
    mem_addr_r mem_tag_r is_load_r mem_size_r sign_extend_r is_flw_r mem_valid_r

  -- Drive lsu_sb_enq_size[1:0] from store type
  -- sb_enq_size = mem_size (00=byte, 01=half, 10=word)
  let lsu_sb_enq_size := makeIndexedWires "lsu_sb_enq_size" 2
  let sb_enq_size_gates :=
    (List.range 2).map (fun i => Gate.mkBUF mem_size[i]! lsu_sb_enq_size[i]!)

  -- Mask store data: SB keeps [7:0], SH keeps [15:0], SW keeps all 32
  -- For SB: zero bits [31:8]; for SH: zero bits [31:16]
  -- is_sw means keep all bits. is_sh means keep [15:0]. is_sb means keep [7:0].
  -- mask_bit[i] = is_sw | (is_sh & i<16) | (is_sb & i<8)
  -- Equivalently: keep bit i if mem_size_1 | (mem_size_0 & i<16) | (!mem_size_0 & !mem_size_1 & i<8)
  -- Simpler: keep_hi16 = mem_size[1] (word), keep_lo16_hi8 = mem_size[1] | mem_size[0] (word or half)
  let store_data_masked := makeIndexedWires "store_data_masked" 32
  let keep_hi16 := Wire.mk "keep_hi16"
  let keep_lo16_hi8 := Wire.mk "keep_lo16_hi8"
  let store_mask_gates :=
    [Gate.mkBUF mem_size[1]! keep_hi16,
     Gate.mkOR mem_size[1]! mem_size[0]! keep_lo16_hi8] ++
    -- Bits [7:0]: always kept (AND with one = passthrough)
    (List.range 8).map (fun i =>
      Gate.mkBUF rs_mem_dispatch_src2[i]! store_data_masked[i]!) ++
    -- Bits [15:8]: kept for half or word
    (List.range 8).map (fun i =>
      Gate.mkAND rs_mem_dispatch_src2[8+i]! keep_lo16_hi8 store_data_masked[8+i]!) ++
    -- Bits [31:16]: kept for word only
    (List.range 16).map (fun i =>
      Gate.mkAND rs_mem_dispatch_src2[16+i]! keep_hi16 store_data_masked[16+i]!)

  let load_fwd_valid := Wire.mk "load_fwd_valid"
  let cross_size_any := Wire.mk "cross_size_any"
  let cross_size_uncommitted := Wire.mk "cross_size_uncommitted"
  let fwd_size_check_gates_and_load_fwd_gates := mkLoadForwarding
    mem_size_r lsu_sb_fwd_size
    lsu_sb_fwd_hit lsu_sb_fwd_committed_hit lsu_sb_fwd_word_only_hit
    mem_valid_r is_load_r is_load
    rs_mem_dispatch_valid rs_int_dispatch_valid ib_fifo_enq_ready
    load_fwd_valid cross_size_stall not_cross_size_stall cross_size_any cross_size_uncommitted
    not_int_dispatching branch_dispatch_en

  -- Cross-size pending latch: prevents stores from re-filling the SB with the
  -- same address while a load is stalled on cross-size.  Blocks ALL mem dispatches
  -- until the load successfully fires to DMEM (load_no_fwd).
  let cross_size_pending := Wire.mk "cross_size_pending"
  let cross_size_pending_next := Wire.mk "cross_size_pending_next"
  let _not_cross_size_pending := Wire.mk "not_cross_size_pending"

  -- === LOAD BYTE/HALF FORMATTING (SB forwarding path) ===
  -- SB fwd data is already low-aligned (store data was masked before SB entry):
  --   SB stores: data[7:0]; SH stores: data[15:0]; SW stores: data[31:0]
  -- NO barrel shift needed — just sign/zero extend directly.
  -- (Barrel shift is only needed on the DMEM path where data is word-positioned.)
  let lsu_sb_fwd_formatted := makeIndexedWires "lsu_sb_fwd_fmt" 32

  -- Sign/zero extension for SB fwd path
  -- For byte (mem_size=00): sign bit = data[7], extend bits [31:8]
  -- For half (mem_size=01): sign bit = data[15], extend bits [31:16]
  -- For word (mem_size=10): no extension needed
  let sb_fwd_sign_bit := Wire.mk "sb_fwd_sign_bit"
  let sb_fwd_sign_bit_raw := Wire.mk "sb_fwd_sign_bit_raw"
  let sb_fwd_sign_gates := [
    Gate.mkMUX lsu_sb_fwd_data[7]! lsu_sb_fwd_data[15]! mem_size_r[0]! sb_fwd_sign_bit_raw,
    Gate.mkAND sb_fwd_sign_bit_raw sign_extend_r sb_fwd_sign_bit
  ]
  let sb_fwd_ext_lo := Wire.mk "sb_fwd_ext_lo"  -- keep bits [15:8]?
  let sb_fwd_ext_hi := Wire.mk "sb_fwd_ext_hi"  -- keep bits [31:16]?
  let sb_fwd_format_gates :=
    [Gate.mkOR mem_size_r[0]! mem_size_r[1]! sb_fwd_ext_lo,
     Gate.mkBUF mem_size_r[1]! sb_fwd_ext_hi] ++
    -- Bits [7:0]: passthrough
    (List.range 8).map (fun i =>
      Gate.mkBUF lsu_sb_fwd_data[i]! lsu_sb_fwd_formatted[i]!) ++
    -- Bits [15:8]: MUX(sign_bit, data[i], ext_lo)
    (List.range 8).map (fun i =>
      Gate.mkMUX sb_fwd_sign_bit lsu_sb_fwd_data[8+i]! sb_fwd_ext_lo lsu_sb_fwd_formatted[8+i]!) ++
    -- Bits [31:16]: MUX(sign_bit, data[i], ext_hi)
    (List.range 16).map (fun i =>
      Gate.mkMUX sb_fwd_sign_bit lsu_sb_fwd_data[16+i]! sb_fwd_ext_hi lsu_sb_fwd_formatted[16+i]!)

  let lsu_sb_fwd_format_all := sb_fwd_sign_gates ++ sb_fwd_format_gates

  let lsu_valid := Wire.mk "lsu_valid"
  let lsu_tag := makeIndexedWires "lsu_tag" 6
  let lsu_data := makeIndexedWires "lsu_data" 32

  -- When sbFwdPipelineStages > 0, register the SB forwarding result through DFFs.
  -- This breaks the timing-critical path: mem_address → SB compare → CDB arbiter.
  -- The registered result enters the CDB arbiter one cycle later.
  -- When sbFwdPipelineStages = 0, use combinational BUF (current behavior).
  let lsu_valid_gate :=
    if sbFwdPipelined then
      [Gate.mkDFF load_fwd_valid clock pipeline_reset_misc lsu_valid]
    else
      [Gate.mkBUF load_fwd_valid lsu_valid]

  let lsu_tag_data_mux_gates :=
    if sbFwdPipelined then
      (List.range 6).map (fun i =>
        Gate.mkDFF mem_tag_r[i]! clock pipeline_reset_misc lsu_tag[i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkDFF lsu_sb_fwd_formatted[i]! clock pipeline_reset_misc lsu_data[i]!)
    else
      (List.range 6).map (fun i =>
        Gate.mkBUF mem_tag_r[i]! lsu_tag[i]!) ++
      (List.range 32).map (fun i =>
        Gate.mkBUF lsu_sb_fwd_formatted[i]! lsu_data[i]!)

  let lsu_pipeline_insts : List CircuitInstance := []

  -- Track is_fp_load through LSU path for FIFO is_fp_rd bit
  let lsu_is_fp := Wire.mk "lsu_is_fp"
  let lsu_is_fp_gates :=
    if enableF then
      if sbFwdPipelined then
        [Gate.mkDFF is_flw_r clock pipeline_reset_misc lsu_is_fp]
      else
        [Gate.mkBUF is_flw_r lsu_is_fp]
    else [Gate.mkBUF zero lsu_is_fp]

  -- Assemble LSU FIFO enqueue data bus
  let lsu_fifo_enq_assemble :=
    (List.range 6).map (fun i => Gate.mkBUF lsu_tag[i]! lsu_fifo_enq_data[i]!) ++
    (List.range 32).map (fun i => Gate.mkBUF lsu_data[i]! lsu_fifo_enq_data[6+i]!) ++
    [Gate.mkBUF lsu_is_fp lsu_fifo_enq_data[38]!]

  -- LSU FIFO instance: SB-forwarded load results enter here
  let lsu_fifo_inst : CircuitInstance := {
    moduleName := "Queue1Flow_39", instName := "u_cdb_fifo_lsu",
    portMap := [("clock", clock), ("reset", pipeline_reset_misc),
                ("enq_valid", lsu_valid),
                ("deq_ready", lsu_fifo_drain),
                ("enq_ready", lsu_fifo_enq_ready),
                ("deq_valid", lsu_fifo_deq_valid)] ++
      (List.range 39).map (fun i => (s!"enq_data_{i}", lsu_fifo_enq_data[i]!)) ++
      (List.range 39).map (fun i => (s!"deq_data_{i}", lsu_fifo_deq[i]!))
  }

  -- === DMEM RESPONSE PATH ===
  let load_no_fwd := Wire.mk "load_no_fwd"
  let load_no_fwd_tmp := Wire.mk "load_no_fwd_tmp"
  let not_sb_fwd_hit := Wire.mk "not_sb_fwd_hit"
  let dmem_load_tag_reg := makeIndexedWires "dmem_load_tag_reg" 6
  let dmem_load_tag_next := makeIndexedWires "dmem_load_tag_next" 6

  -- DMEM load pending: 1-cycle busy flag to prevent back-to-back DMEM loads.
  -- The DMEM path has a single tag register, so a second load_no_fwd before
  -- dmem_resp_valid would overwrite the first load's tag.
  let dmem_load_pending := Wire.mk "dmem_load_pending"
  let dmem_load_pending_next := Wire.mk "dmem_load_pending_next"
  let not_dmem_load_pending := Wire.mk "not_dmem_load_pending"

  let load_no_fwd_base := Wire.mk "load_no_fwd_base"
  let load_no_fwd_no_deq := Wire.mk "load_no_fwd_no_deq"
  let not_sb_deq_valid := Wire.mk "not_sb_deq_valid"
  let not_word_overlap := Wire.mk "not_word_overlap"
  let load_no_fwd_gates := [
    Gate.mkNOT lsu_sb_fwd_hit not_sb_fwd_hit,
    Gate.mkAND mem_valid_r is_load_r load_no_fwd_tmp,
    -- Normal DMEM path: no SB hit AND no word overlap
    Gate.mkNOT (Wire.mk "word_overlap_stall") not_word_overlap,
    Gate.mkAND load_no_fwd_tmp not_sb_fwd_hit (Wire.mk "load_no_fwd_pre"),
    Gate.mkAND (Wire.mk "load_no_fwd_pre") not_word_overlap load_no_fwd_base,
    -- Yield to SB store dequeue: DMEM port is shared, store dequeue takes priority
    Gate.mkNOT lsu_sb_deq_valid not_sb_deq_valid,
    Gate.mkAND load_no_fwd_base not_sb_deq_valid load_no_fwd_no_deq,
    -- Gate by not_dmem_load_pending: only one DMEM load in flight at a time
    -- (DMEM path has single tag register, back-to-back would overwrite first tag)
    Gate.mkAND load_no_fwd_no_deq not_dmem_load_pending load_no_fwd
  ]

  let dmem_pending_gates := [
    -- Set on load_no_fwd, clear on dmem_resp_valid (or reset)
    -- pending_next = load_no_fwd OR (pending AND NOT dmem_resp_valid)
    Gate.mkNOT dmem_resp_valid (Wire.mk "not_dmem_resp_valid"),
    Gate.mkAND dmem_load_pending (Wire.mk "not_dmem_resp_valid") (Wire.mk "dmem_pending_hold"),
    Gate.mkOR load_no_fwd (Wire.mk "dmem_pending_hold") dmem_load_pending_next,
    Gate.mkNOT dmem_load_pending not_dmem_load_pending
  ]
  let dmem_pending_inst : CircuitInstance :=
    { moduleName := "DFlipFlop", instName := "u_dmem_load_pending",
      portMap := [("d", dmem_load_pending_next), ("q", dmem_load_pending),
                  ("clock", clock), ("reset", pipeline_reset_misc)] }

  -- Cross-size pending DFF: latches when cross_size_stall fires, clears when
  -- the load successfully fires to DMEM (load_no_fwd=1).  While latched, blocks
  -- ALL mem dispatches to prevent stores from re-filling the SB at the same address.
  let cross_size_pending_gates := [
    -- pending_next = cross_size_stall OR (pending AND NOT load_no_fwd)
    Gate.mkNOT load_no_fwd (Wire.mk "not_load_no_fwd_for_csp"),
    Gate.mkAND cross_size_pending (Wire.mk "not_load_no_fwd_for_csp") (Wire.mk "csp_hold"),
    Gate.mkOR cross_size_stall (Wire.mk "csp_hold") cross_size_pending_next
  ]
  let cross_size_pending_inst : CircuitInstance :=
    { moduleName := "DFlipFlop", instName := "u_cross_size_pending",
      portMap := [("d", cross_size_pending_next), ("q", cross_size_pending),
                  ("clock", clock), ("reset", pipeline_reset_misc)] }

  -- mem_dispatch_en: gate by cross_size_stall, dmem_load_pending, sb_deq_valid,
  -- AND store-into-full-SB AND cross_size_pending. When the SB is draining a store
  -- to DMEM (sb_deq_valid=1), the DMEM port is busy. A load that misses SB
  -- forwarding would try to use DMEM but get blocked by load_no_fwd_no_deq=0,
  -- losing the dispatched instruction forever (the RS entry is already cleared).
  -- Gating dispatch_en prevents this.
  -- Also: if the dispatching instruction is a store and the SB is full, block dispatch
  -- to prevent enqueuing into a full SB (the RS entry would be cleared but the store lost).
  let mem_dispatch_en_tmp := Wire.mk "mem_dispatch_en_tmp"
  let mem_dispatch_en_tmp2 := Wire.mk "mem_dispatch_en_tmp2"
  let mem_dispatch_en_tmp3 := Wire.mk "mem_dispatch_en_tmp3"
  let not_sb_deq_for_dispatch := Wire.mk "not_sb_deq_for_dispatch"
  let store_sb_full_block := Wire.mk "store_sb_full_block"
  let not_store_sb_full := Wire.mk "not_store_sb_full"
  let mem_dispatch_en_gates := [
    Gate.mkNOT cross_size_stall mem_dispatch_en_tmp,
    Gate.mkAND mem_dispatch_en_tmp not_dmem_load_pending mem_dispatch_en_tmp2,
    Gate.mkNOT lsu_sb_deq_valid not_sb_deq_for_dispatch,
    Gate.mkAND mem_dispatch_en_tmp2 not_sb_deq_for_dispatch mem_dispatch_en_tmp3,
    -- Block store dispatch when SB is full (wire driven by gate in sb_enq_gate_gates)
    Gate.mkAND (Wire.mk "not_is_load") lsu_sb_full store_sb_full_block,
    Gate.mkNOT store_sb_full_block not_store_sb_full,
    Gate.mkAND mem_dispatch_en_tmp3 not_store_sb_full mem_dispatch_en
  ]

  -- DMEM metadata DFFs use CircuitInstance DFlipFlop with external `reset`
  -- (NOT pipeline_reset_misc) because the DMEM response arrives 1 cycle after
  -- the request, and the pipeline flush happens in between. The metadata must
  -- survive the flush. Flat Gate.mkDFF gets grouped into pipeline_reset_busy
  -- by the codegen, so we must use instances.
  let dmem_tag_capture_gates := (List.range 6).map (fun i =>
    Gate.mkMUX dmem_load_tag_reg[i]! mem_tag_r[i]! load_no_fwd dmem_load_tag_next[i]!)
  let dmem_tag_capture_insts := (List.range 6).map (fun i =>
    ({ moduleName := "DFlipFlop", instName := s!"u_dmem_tag_{i}",
       portMap := [("d", dmem_load_tag_next[i]!), ("q", dmem_load_tag_reg[i]!),
                   ("clock", clock), ("reset", reset)] } : CircuitInstance))

  -- Track is_fp_load through dmem response path (1-cycle load latency)
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
                      ("clock", clock), ("reset", reset)] } : CircuitInstance)]
    else []

  -- === DMEM LOAD METADATA CAPTURE (for sub-word load formatting) ===
  -- Capture addr[1:0], mem_size[1:0], sign_extend alongside dmem_load_tag
  let dmem_addr_lo_reg := makeIndexedWires "dmem_addr_lo_reg" 2
  let dmem_addr_lo_next := makeIndexedWires "dmem_addr_lo_next" 2
  let dmem_mem_size_reg := makeIndexedWires "dmem_mem_size_reg" 2
  let dmem_mem_size_next := makeIndexedWires "dmem_mem_size_next" 2
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
  -- Same barrel-shift + sign/zero-extend as SB fwd path, using registered metadata
  let dmem_resp_formatted := makeIndexedWires "dmem_resp_fmt" 32
  let dmem_resp_shifted := makeIndexedWires "dmem_resp_shifted" 32
  let dmem_sh8 := makeIndexedWires "dmem_sh8" 32
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
  let dmem_sign_gates := [
    Gate.mkMUX dmem_resp_shifted[7]! dmem_resp_shifted[15]! dmem_mem_size_reg[0]! dmem_sign_bit_raw,
    Gate.mkAND dmem_sign_bit_raw dmem_sign_ext_reg dmem_sign_bit
  ]
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
      Gate.mkMUX dmem_sign_bit dmem_resp_shifted[16+i]! dmem_ext_hi dmem_resp_formatted[16+i]!)

  let dmem_resp_format_all := dmem_sh8_gates ++ dmem_sh16_gates ++
    dmem_sign_gates ++ dmem_format_gates

  -- === CDB PRIORITY DRAIN MUX (submodule) ===
  -- Factored into CDBMux module with keepHierarchy to preserve buffer topology
  -- Gate DMEM response: suppress stale loads dispatched before flush
  let dmem_valid_gated := Wire.mk "dmem_valid_gated"
  let not_flushing_for_dmem := Wire.mk "not_flushing_for_dmem"
  let dmem_valid_gate_gates := [
    Gate.mkNOT pipeline_flush_comb (Wire.mk "not_flush_comb_for_dmem"),
    Gate.mkNOT pipeline_flush (Wire.mk "not_flush_reg_for_dmem"),
    Gate.mkAND (Wire.mk "not_flush_comb_for_dmem") (Wire.mk "not_flush_reg_for_dmem") not_flushing_for_dmem,
    Gate.mkAND dmem_resp_valid dmem_load_pending (Wire.mk "dmem_valid_pending"),
    Gate.mkAND (Wire.mk "dmem_valid_pending") not_flushing_for_dmem dmem_valid_gated
  ]
  -- csr_cdb_inject/tag/data already declared above (forward-declared for microcode path)
  let cdb_pre_is_fp := Wire.mk "cdb_pre_is_fp"
  let cdb_redirect_target_pre := makeIndexedWires "cdb_redirect_target_pre" 32
  let cdb_pre_mispredicted := Wire.mk "cdb_pre_mispredicted"
  let cdb_redirect_target := makeIndexedWires "cdb_redirect_target" 32
  let cdb_mispredicted := Wire.mk "cdb_mispredicted"

  let cdb_mux_inst : CircuitInstance :=
    { moduleName := if enableF then "CDBMux_F" else "CDBMux"
      instName := "u_cdb_mux"
      portMap :=
        -- Inputs: valid signals
        [("ib_valid", ib_fifo_deq_valid),
         ("fp_valid", fp_fifo_deq_valid),
         ("muldiv_valid", muldiv_fifo_deq_valid),
         ("lsu_valid", lsu_fifo_deq_valid),
         ("dmem_valid", dmem_valid_gated)] ++
        -- Inputs: FIFO deq buses
        (List.range 72).map (fun i => (s!"ib_deq_{i}", ib_fifo_deq[i]!)) ++
        (List.range 39).map (fun i => (s!"fp_deq_{i}", fp_fifo_deq[i]!)) ++
        (List.range 39).map (fun i => (s!"muldiv_deq_{i}", muldiv_fifo_deq[i]!)) ++
        (List.range 39).map (fun i => (s!"lsu_deq_{i}", lsu_fifo_deq[i]!)) ++
        -- Inputs: DMEM
        (List.range 32).map (fun i => (s!"dmem_fmt_{i}", dmem_resp_formatted[i]!)) ++
        (List.range 6).map (fun i => (s!"dmem_tag_{i}", dmem_load_tag_reg[i]!)) ++
        [("dmem_is_fp", if enableF then dmem_is_fp_reg else zero)] ++
        -- Inputs: CSR (merged with RVV vsetvl inject when enableVector)
        [("csr_inject", merged_cdb_inject)] ++
        (List.range 6).map (fun i => (s!"csr_tag_{i}", merged_cdb_tag[i]!)) ++
        (List.range 32).map (fun i => (s!"csr_data_{i}", merged_cdb_data[i]!)) ++
        [("zero", zero)] ++
        -- Outputs
        [("pre_valid", cdb_pre_valid)] ++
        (List.range 6).map (fun i => (s!"pre_tag_{i}", cdb_pre_tag[i]!)) ++
        (List.range 32).map (fun i => (s!"pre_data_{i}", cdb_pre_data[i]!)) ++
        [("pre_is_fp", cdb_pre_is_fp),
         ("drain_lsu", lsu_fifo_drain),
         ("drain_muldiv", muldiv_fifo_drain),
         ("drain_fp", fp_fifo_drain),
         ("drain_ib", ib_fifo_drain)] ++
        (List.range 32).map (fun i => (s!"redirect_{i}", cdb_redirect_target_pre[i]!)) ++
        [("pre_mispredicted", cdb_pre_mispredicted)] }

  -- CDB pipeline register
  -- Custom reset: preserves CSR CDB injections through flush.
  -- cdb_reset = pipeline_reset_misc AND NOT(csr_flush_suppress)
  -- DMEM responses during flush are now gated at dmem_wins (dmem_load_pending cleared on flush),
  -- so no need to suppress cdb_reset for them.
  -- csr_flush_suppress = DFF(csr_cdb_inject), so it's high 1 cycle after CSR inject,
  -- exactly when the CDB pipeline DFF would be reset by the flush.
  let cdb_reset := Wire.mk "cdb_reset"
  let cdb_reset_gates := [
    Gate.mkAND pipeline_reset_misc not_csr_flush_suppress cdb_reset
  ]

  let cdb_reg_insts : List CircuitInstance :=
    [{ moduleName := "DFlipFlop", instName := "u_cdb_valid_reg",
       portMap := [("d", cdb_pre_valid), ("q", cdb_valid),
                   ("clock", clock), ("reset", cdb_reset)] }] ++
    (List.range 6).map (fun i => {
       moduleName := "DFlipFlop", instName := s!"u_cdb_tag_reg_{i}",
       portMap := [("d", cdb_pre_tag[i]!), ("q", cdb_tag[i]!),
                   ("clock", clock), ("reset", cdb_reset)] }) ++
    (List.range 32).map (fun i => {
       moduleName := "DFlipFlop", instName := s!"u_cdb_data_reg_{i}",
       portMap := [("d", cdb_pre_data[i]!), ("q", cdb_data[i]!),
                   ("clock", clock), ("reset", cdb_reset)] }) ++
    (if enableF then
      [{ moduleName := "DFlipFlop", instName := "u_cdb_is_fp_rd_reg",
         portMap := [("d", cdb_pre_is_fp), ("q", cdb_is_fp_rd),
                     ("clock", clock), ("reset", cdb_reset)] }]
    else []) ++
    -- CDB redirect target pipeline registers (32 DFFs)
    (List.range 32).map (fun i => {
       moduleName := "DFlipFlop", instName := s!"u_cdb_redirect_target_reg_{i}",
       portMap := [("d", cdb_redirect_target_pre[i]!), ("q", cdb_redirect_target[i]!),
                   ("clock", clock), ("reset", cdb_reset)] }) ++
    -- CDB mispredicted pipeline register (1 DFF)
    [{ moduleName := "DFlipFlop", instName := "u_cdb_mispredicted_reg",
       portMap := [("d", cdb_pre_mispredicted), ("q", cdb_mispredicted),
                   ("clock", clock), ("reset", cdb_reset)] }]

  -- CDB domain gating: prevent tag collisions between INT/FP phys reg pools
  -- Also gate with cdb_tag_nonzero to suppress tag=0 broadcasts (x0 writeback)
  -- which would otherwise corrupt CDB forwarding in RS for src tags matching p0.
  let not_cdb_pre_is_fp := Wire.mk "not_cdb_pre_is_fp"
  let cdb_valid_nz := Wire.mk "cdb_valid_nz"
  -- Pre-register tag nonzero check
  let cdb_pre_tag_nz_tmp := List.range 5 |>.map (fun i => Wire.mk s!"cdb_pre_tag_nz_t{i}")
  let cdb_pre_tag_nonzero := Wire.mk "cdb_pre_tag_nonzero"
  let cdb_pre_valid_nz := Wire.mk "cdb_pre_valid_nz"
  let cdb_pre_tag_nz_gates :=
    [Gate.mkOR cdb_pre_tag[0]! cdb_pre_tag[1]! cdb_pre_tag_nz_tmp[0]!] ++
    (List.range 4).map (fun i =>
      Gate.mkOR cdb_pre_tag_nz_tmp[i]! cdb_pre_tag[i + 2]! (if i < 3 then cdb_pre_tag_nz_tmp[i + 1]! else cdb_pre_tag_nonzero)) ++
    [Gate.mkAND cdb_valid cdb_tag_nonzero cdb_valid_nz,
     Gate.mkAND cdb_pre_valid cdb_pre_tag_nonzero cdb_pre_valid_nz]
  let cdb_domain_gates :=
    cdb_pre_tag_nz_gates ++
    if enableF then
      [Gate.mkAND cdb_valid_nz not_cdb_is_fp (Wire.mk "cdb_valid_for_int"),
       -- FP domain: don't filter by tag_nonzero since FP p0 is a valid register
       Gate.mkAND cdb_valid cdb_is_fp_rd (Wire.mk "cdb_valid_for_fp"),
       Gate.mkNOT cdb_pre_is_fp not_cdb_pre_is_fp,
       Gate.mkAND cdb_pre_valid_nz not_cdb_pre_is_fp (Wire.mk "cdb_pre_valid_for_int"),
       -- FP pre-domain: don't filter by pre_tag_nonzero since FP p0 is valid
       Gate.mkAND cdb_pre_valid cdb_pre_is_fp (Wire.mk "cdb_pre_valid_for_fp")]
    else []

  let cdb_arb_gates := arb_level0_gates ++ fp_enq_is_fp_gate ++
    ib_fifo_enq_assemble ++ muldiv_fifo_enq_assemble ++ fp_fifo_enq_assemble ++
    lsu_fifo_enq_assemble ++
    muldiv_fifo_dummy_gates ++ fp_fifo_dummy_gates ++
    mem_pipe_gates ++
    load_no_fwd_gates ++ dmem_pending_gates ++ cross_size_pending_gates ++ mem_dispatch_en_gates ++
    dmem_tag_capture_gates ++ dmem_valid_gate_gates ++
    cdb_reset_gates ++ cdb_domain_gates

  -- Shadow registers (is_fp, isStore, redirect target)
  let alloc_physRd_for_shadow := if enableF then rob_alloc_physRd_fp else branch_alloc_physRd
  let (shadow_gates, shadow_insts, rob_head_is_fp, not_rob_head_is_fp, rob_head_isStore, _rob_head_redirect_target) :=
    mkShadowRegisters enableF zero one clock reset
      rob_alloc_idx rename_valid_gated
      decode_has_fp_rd dispatch_is_store
      alloc_physRd_for_shadow
      cdb_tag_rob cdb_valid cdb_mispredicted cdb_redirect_target
      rob_head_idx
  let rob_fp_shadow_gates := shadow_gates
  let rob_isStore_shadow_gates : List Gate := []
  let redir_shadow_all_gates : List Gate := []
  let rob_isStore_shadow_insts := shadow_insts
  let redir_tag_cmp_insts : List CircuitInstance := []
  let redir_target_shadow_insts : List CircuitInstance := []

  -- ROB old_rd_phys MUX: at dispatch, select FP or INT old_rd_phys for ROB storage
  -- When has_fp_rd, use fp_old_rd_phys; else use int old_rd_phys
  let rob_old_phys_mux_gates :=
    if enableF then
      (List.range 6).map (fun i =>
        Gate.mkMUX old_rd_phys[i]! fp_old_rd_phys[i]! decode_has_fp_rd rob_old_phys_muxed[i]!)
    else []

  -- === COMMIT CONTROL ===
  let retire_recycle_valid_filtered := Wire.mk "retire_recycle_valid_filtered"
  let commit_and_retire_gates := mkCommitControl
    enableF zero
    branch_redirect_valid_reg rob_head_valid rob_head_complete
    rob_commit_en rob_head_isBranch rob_head_hasOldPhysRd
    rob_head_isStore
    rob_head_physRd rob_head_oldPhysRd
    retire_tag_muxed
    rob_head_is_fp not_rob_head_is_fp
    retire_recycle_valid_filtered int_retire_valid fp_retire_recycle_valid
  let commit_gates := commit_and_retire_gates
  let retire_tag_filter_gates : List Gate := []  -- included in commit_gates
  let fp_retire_gates : List Gate := []  -- included in commit_gates

  -- === CROSS-DOMAIN DISPATCH STALLS ===
  -- Stall FP instruction dispatch when INT source is not ready (prevents INT tags in FP RS)
  let fp_crossdomain_stall := Wire.mk "fp_crossdomain_stall"
  -- Stall FSW dispatch when FP source is not ready (prevents FP tags in Memory RS)
  let mem_fp_src_stall := Wire.mk "mem_fp_src_stall"
  let crossdomain_stall_gates :=
    if enableF then
      let not_fp_rs1_read := Wire.mk "not_fp_rs1_read_for_stall"
      let not_fp_src1_rdy := Wire.mk "not_fp_src1_rdy_for_stall"
      let fp_has_int_src := Wire.mk "fp_has_int_src"
      let not_mem_src2_rdy := Wire.mk "not_mem_src2_rdy_for_stall"
      [Gate.mkNOT decode_fp_rs1_read not_fp_rs1_read,
       Gate.mkNOT fp_issue_src1_ready not_fp_src1_rdy,
       Gate.mkAND dispatch_is_fp not_fp_rs1_read fp_has_int_src,
       Gate.mkAND fp_has_int_src not_fp_src1_rdy fp_crossdomain_stall,
       Gate.mkNOT mem_src2_ready not_mem_src2_rdy,
       Gate.mkAND dispatch_is_fp_store not_mem_src2_rdy mem_fp_src_stall]
    else
      [Gate.mkBUF zero fp_crossdomain_stall,
       Gate.mkBUF zero mem_fp_src_stall]

  -- === STALL GENERATION (balanced OR tree for timing) ===
  -- Pair up stall sources at each level to minimize depth
  let stall_L0_a := Wire.mk "stall_L0_a"  -- rename_stall | rob_full
  let stall_L0_b := Wire.mk "stall_L0_b"  -- rs_int_full | rs_mem_full
  let stall_L0_c := Wire.mk "stall_L0_c"  -- rs_branch_full | lsu_sb_full
  let stall_L1_a := Wire.mk "stall_L1_a"  -- L0_a | L0_b
  let stall_L1_b := Wire.mk "stall_L1_b"  -- L0_c | (config-dependent)
  let stall_L2 := Wire.mk "stall_L2"      -- L1_a | L1_b

  -- Extra wires for larger config branches
  let stall_L0_d := Wire.mk "stall_L0_d"
  let stall_L0_e := Wire.mk "stall_L0_e"
  let stall_L1_c := Wire.mk "stall_L1_c"

  -- Vector memory fence stall: stall pipeline when
  -- (a) a scalar memory instruction is decoded while RvvCore is busy, OR
  -- (b) a vector memory instruction is decoded while VecLsu is busy (sidecar protection)
  let vec_mem_fence_stall := Wire.mk "vec_mem_fence_stall"
  let vec_fence_gates : List Gate :=
    if enableVector then
      let not_rvv_idle := Wire.mk "not_rvv_idle"
      let scalar_mem_stall := Wire.mk "scalar_mem_fence_stall"
      let vec_lsu_busy_stall := Wire.mk "vec_lsu_busy_stall"
      [Gate.mkNOT rvv_idle not_rvv_idle,
       Gate.mkAND dispatch_is_scalar_memory not_rvv_idle scalar_mem_stall,
       Gate.mkAND dispatch_is_vector_mem not_rvv_idle vec_lsu_busy_stall,
       Gate.mkOR scalar_mem_stall vec_lsu_busy_stall vec_mem_fence_stall]
    else
      [Gate.mkBUF zero vec_mem_fence_stall]

  let stall_gates :=
    if enableM && enableF then
      -- 11+1 sources → balanced tree depth 4
      -- L0: pair up sources
      [Gate.mkOR rename_stall rob_full stall_L0_a,
       Gate.mkOR rs_int_issue_full rs_mem_issue_full stall_L0_b,
       Gate.mkOR rs_branch_issue_full rs_muldiv_issue_full stall_L0_c,
       Gate.mkOR rs_fp_issue_full fp_rename_stall stall_L0_d,
       Gate.mkOR fp_crossdomain_stall mem_fp_src_stall stall_L0_e,
       -- L1: pair up 5+2 (fp_src3_stall, lsu_sb_full, vec_fence) → 4
       Gate.mkOR stall_L0_a stall_L0_b stall_L1_a,
       Gate.mkOR stall_L0_c stall_L0_d stall_L1_b,
       Gate.mkOR stall_L0_e fp_src3_stall stall_L1_c,
       -- L2: 3+1 → 2
       Gate.mkOR stall_L1_a stall_L1_b stall_L2,
       Gate.mkOR stall_L1_c lsu_sb_full (Wire.mk "stall_L2b"),
       -- L3: final + external DMEM stall + vec fence
       Gate.mkOR stall_L2 (Wire.mk "stall_L2b") (Wire.mk "global_stall_int"),
       Gate.mkOR (Wire.mk "global_stall_int") dmem_stall_ext (Wire.mk "global_stall_pre"),
       Gate.mkOR (Wire.mk "global_stall_pre") vec_mem_fence_stall global_stall]
    else if enableM then
      [Gate.mkOR rename_stall rob_full stall_L0_a,
       Gate.mkOR rs_int_issue_full rs_mem_issue_full stall_L0_b,
       Gate.mkOR rs_branch_issue_full rs_muldiv_issue_full stall_L0_c,
       Gate.mkOR stall_L0_a stall_L0_b stall_L1_a,
       Gate.mkOR stall_L0_c lsu_sb_full stall_L1_b,
       Gate.mkOR stall_L1_a stall_L1_b (Wire.mk "global_stall_int"),
       Gate.mkOR (Wire.mk "global_stall_int") dmem_stall_ext (Wire.mk "global_stall_pre"),
       Gate.mkOR (Wire.mk "global_stall_pre") vec_mem_fence_stall global_stall]
    else if enableF then
      [Gate.mkOR rename_stall rob_full stall_L0_a,
       Gate.mkOR rs_int_issue_full rs_mem_issue_full stall_L0_b,
       Gate.mkOR rs_branch_issue_full rs_fp_issue_full stall_L0_c,
       Gate.mkOR fp_rename_stall fp_crossdomain_stall stall_L0_d,
       Gate.mkOR mem_fp_src_stall fp_src3_stall stall_L0_e,
       Gate.mkOR stall_L0_a stall_L0_b stall_L1_a,
       Gate.mkOR stall_L0_c stall_L0_d stall_L1_b,
       Gate.mkOR stall_L0_e lsu_sb_full stall_L1_c,
       Gate.mkOR stall_L1_a stall_L1_b stall_L2,
       Gate.mkOR stall_L2 stall_L1_c (Wire.mk "global_stall_int"),
       Gate.mkOR (Wire.mk "global_stall_int") dmem_stall_ext (Wire.mk "global_stall_pre"),
       Gate.mkOR (Wire.mk "global_stall_pre") vec_mem_fence_stall global_stall]
    else
      [Gate.mkOR rename_stall rob_full stall_L0_a,
       Gate.mkOR rs_int_issue_full rs_mem_issue_full stall_L0_b,
       Gate.mkOR rs_branch_issue_full lsu_sb_full stall_L0_c,
       Gate.mkOR stall_L0_a stall_L0_b stall_L1_a,
       Gate.mkOR stall_L1_a stall_L0_c (Wire.mk "global_stall_int"),
       Gate.mkOR (Wire.mk "global_stall_int") dmem_stall_ext (Wire.mk "global_stall_pre"),
       Gate.mkOR (Wire.mk "global_stall_pre") vec_mem_fence_stall global_stall]

  -- === MEMORY INTERFACE ===
  let dmem_req_valid := Wire.mk "dmem_req_valid"
  let dmem_req_we := Wire.mk "dmem_req_we"
  let dmem_req_addr := makeIndexedWires "dmem_req_addr" 32
  let dmem_req_data := makeIndexedWires "dmem_req_data" 32
  let dmem_req_size := makeIndexedWires "dmem_req_size" 2

  let not_is_load := Wire.mk "not_is_load"
  let sb_enq_ungated := Wire.mk "sb_enq_ungated"
  let not_flush_comb := Wire.mk "not_flush_comb"
  let sb_enq_dispatched := Wire.mk "sb_enq_dispatched"
  let sb_enq_gate_gates := [
    Gate.mkNOT is_load not_is_load,
    Gate.mkAND rs_mem_dispatch_valid not_is_load sb_enq_ungated,
    -- Only enqueue when RS actually dispatches (mem_dispatch_en=1),
    -- otherwise the RS won't free the entry and we'd get duplicate enqueues
    Gate.mkAND sb_enq_ungated mem_dispatch_en sb_enq_dispatched,
    -- Block wrong-path stores from entering SB during pipeline flush
    Gate.mkNOT pipeline_flush_comb not_flush_comb,
    Gate.mkAND sb_enq_dispatched not_flush_comb sb_enq_en
  ]

  let dmem_valid_tmp := Wire.mk "dmem_valid_tmp"
  let dmem_gates := sb_enq_gate_gates ++ [
    Gate.mkOR load_no_fwd lsu_sb_deq_valid dmem_valid_tmp,
    Gate.mkBUF dmem_valid_tmp dmem_req_valid,
    Gate.mkBUF lsu_sb_deq_valid dmem_req_we] ++
    (List.range 32).map (fun i =>
      Gate.mkMUX mem_addr_r[i]! lsu_sb_deq_bits[i]! lsu_sb_deq_valid dmem_req_addr[i]!) ++
    (List.range 32).map (fun i =>
      Gate.mkBUF lsu_sb_deq_bits[32+i]! dmem_req_data[i]!) ++
    -- dmem_req_size: from SB dequeue bits[65:64] on stores, 10 (word) on loads
    -- On store (dmem_req_we=1): use sb_deq_bits[64:65]
    -- On load (dmem_req_we=0): size=10 (word) since DMEM always returns full word
    [Gate.mkMUX zero lsu_sb_deq_bits[64]! dmem_req_we dmem_req_size[0]!,
     Gate.mkMUX one lsu_sb_deq_bits[65]! dmem_req_we dmem_req_size[1]!]

  -- === CSR REGISTER FILE + EXECUTE LOGIC ===
  -- CSR drain_complete for CSR ops (only when flag register says this was a CSR, not FENCE.I)
  let csr_drain_complete := Wire.mk "csr_drain_complete"
  let csr_drain_gate := [Gate.mkAND fence_i_drain_complete csr_flag_reg csr_drain_complete]

  -- CSR register file: mscratch, mcycle, minstret (writable)
  -- Read-only: misa (hardwired), mhartid (0)
  let mscratch_reg := (List.range 32).map (fun i => Wire.mk s!"mscratch_e{i}")
  let mscratch_next := (List.range 32).map (fun i => Wire.mk s!"mscratch_nx_e{i}")
  let mcycle_reg := (List.range 32).map (fun i => Wire.mk s!"mcycle_e{i}")
  let mcycle_next := (List.range 32).map (fun i => Wire.mk s!"mcycle_nx_e{i}")
  let mcycleh_reg := (List.range 32).map (fun i => Wire.mk s!"mcycleh_e{i}")
  let mcycleh_next := (List.range 32).map (fun i => Wire.mk s!"mcycleh_nx_e{i}")
  let minstret_reg := (List.range 32).map (fun i => Wire.mk s!"minstret_e{i}")
  let minstret_next := (List.range 32).map (fun i => Wire.mk s!"minstret_nx_e{i}")
  let minstreth_reg := (List.range 32).map (fun i => Wire.mk s!"minstreth_e{i}")
  let minstreth_next := (List.range 32).map (fun i => Wire.mk s!"minstreth_nx_e{i}")

  -- Trap CSR registers (M-mode trap handling)
  let mstatus_reg := (List.range 32).map (fun i => Wire.mk s!"mstatus_e{i}")
  let mstatus_next := (List.range 32).map (fun i => Wire.mk s!"mstatus_nx_e{i}")
  let mie_reg := (List.range 32).map (fun i => Wire.mk s!"mie_e{i}")
  let mie_next := (List.range 32).map (fun i => Wire.mk s!"mie_nx_e{i}")
  let mtvec_reg := (List.range 32).map (fun i => Wire.mk s!"mtvec_e{i}")
  let mtvec_next := (List.range 32).map (fun i => Wire.mk s!"mtvec_nx_e{i}")
  let mepc_reg := (List.range 32).map (fun i => Wire.mk s!"mepc_e{i}")
  let mepc_next := (List.range 32).map (fun i => Wire.mk s!"mepc_nx_e{i}")
  let mcause_reg := (List.range 32).map (fun i => Wire.mk s!"mcause_e{i}")
  let mcause_next := (List.range 32).map (fun i => Wire.mk s!"mcause_nx_e{i}")
  let mtval_reg := (List.range 32).map (fun i => Wire.mk s!"mtval_e{i}")
  let mtval_next := (List.range 32).map (fun i => Wire.mk s!"mtval_nx_e{i}")
  let mip_reg := (List.range 32).map (fun i => Wire.mk s!"mip_e{i}")
  let mip_next := (List.range 32).map (fun i => Wire.mk s!"mip_nx_e{i}")

  -- CSR register DFFs (use `reset`, not pipeline_reset)
  let csr_reg_instances : List CircuitInstance :=
    if config.enableZicsr then
      (List.range 32).map (fun i => {
        moduleName := "DFlipFlop", instName := s!"u_mscratch_dff_{i}",
        portMap := [("d", mscratch_next[i]!), ("q", mscratch_reg[i]!),
                    ("clock", clock), ("reset", reset)] }) ++
      (List.range 32).map (fun i => {
        moduleName := "DFlipFlop", instName := s!"u_mcycle_dff_{i}",
        portMap := [("d", mcycle_next[i]!), ("q", mcycle_reg[i]!),
                    ("clock", clock), ("reset", reset)] }) ++
      (List.range 32).map (fun i => {
        moduleName := "DFlipFlop", instName := s!"u_mcycleh_dff_{i}",
        portMap := [("d", mcycleh_next[i]!), ("q", mcycleh_reg[i]!),
                    ("clock", clock), ("reset", reset)] }) ++
      (List.range 32).map (fun i => {
        moduleName := "DFlipFlop", instName := s!"u_minstret_dff_{i}",
        portMap := [("d", minstret_next[i]!), ("q", minstret_reg[i]!),
                    ("clock", clock), ("reset", reset)] }) ++
      (List.range 32).map (fun i => {
        moduleName := "DFlipFlop", instName := s!"u_minstreth_dff_{i}",
        portMap := [("d", minstreth_next[i]!), ("q", minstreth_reg[i]!),
                    ("clock", clock), ("reset", reset)] }) ++
      (List.range 32).map (fun i => {
        moduleName := "DFlipFlop", instName := s!"u_mstatus_dff_{i}",
        portMap := [("d", mstatus_next[i]!), ("q", mstatus_reg[i]!),
                    ("clock", clock), ("reset", reset)] }) ++
      (List.range 32).map (fun i => {
        moduleName := "DFlipFlop", instName := s!"u_mie_dff_{i}",
        portMap := [("d", mie_next[i]!), ("q", mie_reg[i]!),
                    ("clock", clock), ("reset", reset)] }) ++
      (List.range 32).map (fun i => {
        moduleName := "DFlipFlop", instName := s!"u_mtvec_dff_{i}",
        portMap := [("d", mtvec_next[i]!), ("q", mtvec_reg[i]!),
                    ("clock", clock), ("reset", reset)] }) ++
      (List.range 32).map (fun i => {
        moduleName := "DFlipFlop", instName := s!"u_mepc_dff_{i}",
        portMap := [("d", mepc_next[i]!), ("q", mepc_reg[i]!),
                    ("clock", clock), ("reset", reset)] }) ++
      (List.range 32).map (fun i => {
        moduleName := "DFlipFlop", instName := s!"u_mcause_dff_{i}",
        portMap := [("d", mcause_next[i]!), ("q", mcause_reg[i]!),
                    ("clock", clock), ("reset", reset)] }) ++
      (List.range 32).map (fun i => {
        moduleName := "DFlipFlop", instName := s!"u_mtval_dff_{i}",
        portMap := [("d", mtval_next[i]!), ("q", mtval_reg[i]!),
                    ("clock", clock), ("reset", reset)] }) ++
      (List.range 32).map (fun i => {
        moduleName := "DFlipFlop", instName := s!"u_mip_dff_{i}",
        portMap := [("d", mip_next[i]!), ("q", mip_reg[i]!),
                    ("clock", clock), ("reset", reset)] })
    else []

  -- Vector CSR DFFs (use `reset`, not pipeline_reset)
  let vec_csr_reg_instances : List CircuitInstance :=
    if enableVector then
      (List.range 7).map (fun i => {
        moduleName := "DFlipFlop", instName := s!"u_vstart_dff_{i}",
        portMap := [("d", vstart_next[i]!), ("q", vstart_reg[i]!),
                    ("clock", clock), ("reset", reset)] }) ++
      (List.range 2).map (fun i => {
        moduleName := "DFlipFlop", instName := s!"u_vxrm_dff_{i}",
        portMap := [("d", vxrm_next[i]!), ("q", vxrm_reg[i]!),
                    ("clock", clock), ("reset", reset)] }) ++
      [{ moduleName := "DFlipFlop", instName := "u_vxsat_dff_0",
         portMap := [("d", vxsat_next[0]!), ("q", vxsat_reg[0]!),
                     ("clock", clock), ("reset", reset)] }]
    else []

  -- CSR address decode
  let (csr_addr_decode_gates, is_mscratch, is_mcycle_m, is_mcycleh_m, is_minstret_m, is_minstreth_m,
       is_misa, is_fflags, is_frm, is_fcsr, is_mstatus, is_mie, is_mtvec, is_mepc, is_mcause,
       is_mtval, is_mip, is_mcycle, is_mcycleh, is_minstret, is_minstreth,
       is_vstart, is_vxsat, is_vxrm, is_vcsr, is_vl, is_vtype, is_vlenb) :=
    mkCsrAddrDecode csr_addr_reg enableVector

  -- Force is_mstatus high during MSTATUS_TRAP so the CSR read mux outputs
  -- the current mstatus value (needed for MPIE = old MIE transform).
  -- useq_mstatus_trap is declared later but the wire name is stable.
  let (is_mstatus_for_read, mstatus_force_gates) :=
    if config.microcodesTraps && !config.microcodesCSR then
      let forced := Wire.mk "is_mstatus_forced"
      (forced, [Gate.mkOR is_mstatus (Wire.mk "useq_mstatus_trap") forced])
    else
      (is_mstatus, [])

  -- CSR read MUX
  let misa_val : Nat := 0x40000100 +
    (if config.enableM then 0x00001000 else 0) +
    (if config.enableF then 0x00000020 else 0)
  let (csr_read_mux_all_gates, csr_read_data, _mstatus_sd_bit, _mstatus_fs_inv0, _mstatus_fs_inv1) :=
    mkCsrReadMux config enableF zero one misa_val
      is_misa is_mscratch is_mcycle is_mcycleh is_minstret is_minstreth
      is_fflags is_frm is_fcsr
      is_mstatus_for_read is_mie is_mtvec is_mepc is_mcause is_mtval is_mip
      mscratch_reg mcycle_reg mcycleh_reg minstret_reg minstreth_reg
      mstatus_reg mie_reg mtvec_reg mepc_reg mcause_reg mtval_reg
      fflags_reg frm_reg
      is_vstart is_vxsat is_vxrm is_vcsr is_vl is_vtype is_vlenb
      vstart_reg vxsat_reg vxrm_reg rvv_config_vl rvv_config_vtype

  -- CSR operation decode + write logic + CDB injection (config-gated)
  let useq_write_en := Wire.mk "useq_write_en"  -- from sequencer (microcoded mode)
  let useq_write_data := (List.range 32).map (fun i => Wire.mk s!"useq_wr_dt_{i}")

  let (csr_op_decode_gates, csr_write_logic_gates, csr_write_val,
       csr_we_mscratch, csr_we_mcycle, csr_we_mcycleh, csr_we_minstret, csr_we_minstreth,
       csr_we_mstatus, csr_we_mie, csr_we_mtvec, csr_we_mepc, csr_we_mcause, csr_we_mtval,
       csr_cdb_inject_gates) := if config.microcodesCSR then
      -- Fully microcoded CSR: sequencer drives write_en + write_data + CDB inject directly
      -- CSR write value uses same wire names as hardwired path for compatibility
      -- with downstream fflags/frm/fcsr logic
      let wrVal := (List.range 32).map (fun i => Wire.mk s!"csr_wv_e{i}")
      -- Per-CSR write enables: useq_write_en AND is_<csr>
      let we_mscr := Wire.mk "csr_we_mscratch"
      let we_mcyc := Wire.mk "csr_we_mcycle"
      let we_mcych := Wire.mk "csr_we_mcycleh"
      let we_minst := Wire.mk "csr_we_minstret"
      let we_minsth := Wire.mk "csr_we_minstreth"
      let we_mstat := Wire.mk "csr_we_mstatus"
      let we_mie_w := Wire.mk "csr_we_mie"
      let we_mtvec := Wire.mk "csr_we_mtvec"
      let we_mepc := Wire.mk "csr_we_mepc"
      let we_mcause := Wire.mk "csr_we_mcause"
      let we_mtval := Wire.mk "csr_we_mtval"
      -- F-extension CSR write enables (fflags, frm, fcsr) - used by mkFPFlags
      let we_fflags := Wire.mk "csr_we_fflags"
      let we_frm := Wire.mk "csr_we_frm"
      let we_fcsr := Wire.mk "csr_we_fcsr"
      let weGates :=
        if config.enableZicsr then
          [Gate.mkAND useq_write_en is_mscratch we_mscr,
           Gate.mkAND useq_write_en is_mcycle_m we_mcyc,
           Gate.mkAND useq_write_en is_mcycleh_m we_mcych,
           Gate.mkAND useq_write_en is_minstret_m we_minst,
           Gate.mkAND useq_write_en is_minstreth_m we_minsth,
           Gate.mkAND useq_write_en is_mstatus we_mstat,
           Gate.mkAND useq_write_en is_mie we_mie_w,
           Gate.mkAND useq_write_en is_mtvec we_mtvec,
           Gate.mkAND useq_write_en is_mepc we_mepc,
           Gate.mkAND useq_write_en is_mcause we_mcause,
           Gate.mkAND useq_write_en is_mtval we_mtval] ++
          (if enableF then
            [Gate.mkAND useq_write_en is_fflags we_fflags,
             Gate.mkAND useq_write_en is_frm we_frm,
             Gate.mkAND useq_write_en is_fcsr we_fcsr]
           else
            [Gate.mkBUF zero we_fflags, Gate.mkBUF zero we_frm,
             Gate.mkBUF zero we_fcsr])
        else
          [Gate.mkBUF zero we_mscr, Gate.mkBUF zero we_mcyc,
           Gate.mkBUF zero we_mcych, Gate.mkBUF zero we_minst,
           Gate.mkBUF zero we_minsth, Gate.mkBUF zero we_mstat,
           Gate.mkBUF zero we_mie_w, Gate.mkBUF zero we_mtvec,
           Gate.mkBUF zero we_mepc, Gate.mkBUF zero we_mcause,
           Gate.mkBUF zero we_mtval,
           Gate.mkBUF zero we_fflags, Gate.mkBUF zero we_frm,
           Gate.mkBUF zero we_fcsr]
      -- Bridge useq write data to canonical csr_wv_e names
      let wrBridgeGates := (List.range 32).map (fun i =>
        Gate.mkBUF useq_write_data[i]! wrVal[i]!)
      -- No op decode or CDB inject gates needed (sequencer handles these)
      ([], weGates ++ wrBridgeGates, wrVal,
       we_mscr, we_mcyc, we_mcych, we_minst, we_minsth,
       we_mstat, we_mie_w, we_mtvec, we_mepc, we_mcause, we_mtval,
       [])
    else
      let (opDecGates, csr_is_rw, csr_is_rs, csr_is_rc, _csr_is_imm, csr_src) :=
        mkCsrOpDecode config oi opcodeWidth zero csr_optype_reg csr_rs1cap_reg csr_zimm_reg
      let (wrGates, wrVal,
           we_mscr, we_mcyc, we_mcych, we_minst, we_minsth,
           we_mstat, we_mie, we_mtvec, we_mepc, we_mcause, we_mtval,
           _act_writes, _drain_writes) :=
        mkCsrWriteLogic config zero csr_read_data csr_src csr_is_rw csr_is_rs csr_is_rc
          csr_drain_complete csr_zimm_reg
          is_mscratch is_mcycle_m is_mcycleh_m is_minstret_m is_minstreth_m
          is_fflags is_frm is_fcsr
          is_mstatus is_mie is_mtvec is_mepc is_mcause is_mtval
      -- CDB injection (hardwired): rd_nonzero check + BUF from csr_read_data
      let csr_rd_nonzero := Wire.mk "csr_rd_nonzero"
      let csr_rd_nz_tmp := (List.range 4).map (fun i => Wire.mk s!"csr_rdnz_e{i}")
      let cdbGates :=
        if config.enableZicsr then
          [Gate.mkOR csr_rd_reg[0]! csr_rd_reg[1]! csr_rd_nz_tmp[0]!,
           Gate.mkOR csr_rd_nz_tmp[0]! csr_rd_reg[2]! csr_rd_nz_tmp[1]!,
           Gate.mkOR csr_rd_nz_tmp[1]! csr_rd_reg[3]! csr_rd_nz_tmp[2]!,
           Gate.mkOR csr_rd_nz_tmp[2]! csr_rd_reg[4]! csr_rd_nonzero,
           Gate.mkAND csr_drain_complete csr_rd_nonzero csr_cdb_inject] ++
          (List.range 6).map (fun i =>
            Gate.mkBUF csr_phys_reg[i]! csr_cdb_tag[i]!) ++
          (List.range 32).map (fun i =>
            Gate.mkBUF csr_read_data[i]! csr_cdb_data[i]!)
        else
          [Gate.mkBUF zero csr_rd_nonzero,
           Gate.mkBUF zero csr_cdb_inject] ++
          (List.range 6).map (fun i => Gate.mkBUF zero csr_cdb_tag[i]!) ++
          (List.range 32).map (fun i => Gate.mkBUF zero csr_cdb_data[i]!)
      (opDecGates, wrGates, wrVal,
       we_mscr, we_mcyc, we_mcych, we_minst, we_minsth,
       we_mstat, we_mie, we_mtvec, we_mepc, we_mcause, we_mtval,
       cdbGates)

  -- Merge trap sequencer writes into hardwired CSR write path
  -- When microcodesTraps is true (but not microcodesCSR), the trap sequencer
  -- also needs to write mepc, mcause, mstatus via useq_write_en.
  -- OR the sequencer write-enables with hardwired write-enables, and MUX write data.
  -- Merge trap sequencer writes into hardwired CSR write path
  -- When microcodesTraps is true (but not microcodesCSR), the trap sequencer
  -- also needs to write mepc, mcause, mstatus via useq_write_en.
  -- MSTATUS_TRAP uses mstatus_trap_active (addr is forced combinationally, not registered).
  -- WRITE_CSR for mepc/mcause uses useq_write_en AND is_<csr> (addr is pre-registered via SET_CSR_ADDR).
  let useq_mstatus_trap := Wire.mk "useq_mstatus_trap"
  let (csr_write_val, csr_we_mstatus, csr_we_mepc, csr_we_mcause, trap_we_merge_gates) :=
    if config.microcodesTraps && !config.microcodesCSR && config.enableZicsr then
      -- Per-CSR sequencer write enables
      let useq_we_mepc := Wire.mk "useq_we_mepc"
      let useq_we_mcause := Wire.mk "useq_we_mcause"
      -- Merged write enables
      let merged_we_mstat := Wire.mk "merged_we_mstatus"
      let merged_we_mepc := Wire.mk "merged_we_mepc"
      let merged_we_mcause := Wire.mk "merged_we_mcause"
      -- Merged write data (MUX: useq_write_en selects useq_write_data, else hardwired)
      let merged_wr := (List.range 32).map (fun i => Wire.mk s!"csr_mwv_e{i}")
      let weGates :=
        [-- MSTATUS_TRAP: use dedicated signal (addr forced combinationally, not in csr_addr_reg)
         Gate.mkOR csr_we_mstatus useq_mstatus_trap merged_we_mstat,
         -- WRITE_CSR for mepc/mcause: addr was set by SET_CSR_ADDR and registered
         Gate.mkAND useq_write_en is_mepc useq_we_mepc,
         Gate.mkAND useq_write_en is_mcause useq_we_mcause,
         Gate.mkOR csr_we_mepc useq_we_mepc merged_we_mepc,
         Gate.mkOR csr_we_mcause useq_we_mcause merged_we_mcause] ++
        (List.range 32).map (fun i =>
          Gate.mkMUX csr_write_val[i]! useq_write_data[i]! useq_write_en merged_wr[i]!)
      (merged_wr, merged_we_mstat, merged_we_mepc, merged_we_mcause, weGates)
    else
      (csr_write_val, csr_we_mstatus, csr_we_mepc, csr_we_mcause, [])

  -- CSR next-value logic (WARL masking, MUX, counter auto-increment)
  let (csr_next_value_gates, csr_counter_instances) := mkCsrNextValue config enableF zero one
    csr_write_val
    csr_we_mscratch csr_we_mcycle csr_we_mcycleh csr_we_minstret csr_we_minstreth
    csr_we_mstatus csr_we_mie csr_we_mtvec csr_we_mepc csr_we_mcause csr_we_mtval
    mscratch_reg mscratch_next mstatus_reg mstatus_next
    mie_reg mie_next mtvec_reg mtvec_next mepc_reg mepc_next
    mcause_reg mcause_next mtval_reg mtval_next mip_next
    mcycle_reg mcycle_next mcycleh_reg mcycleh_next
    minstret_reg minstret_next minstreth_reg minstreth_next
    commit_valid_muxed

  -- Vector CSR write enables and next-value logic
  let vec_csr_write_gates : List Gate :=
    if enableVector && config.enableZicsr then
      -- Write enables for vstart, vxrm, vxsat (from CSR instruction path)
      let csr_we_vstart := Wire.mk "csr_we_vstart"
      let csr_we_vxrm := Wire.mk "csr_we_vxrm"
      let csr_we_vxsat := Wire.mk "csr_we_vxsat"
      let csr_we_vcsr := Wire.mk "csr_we_vcsr"
      -- Write enable source: microcoded uses useq_write_en, hardwired uses csr_drain_and_writes
      let we_src := if config.microcodesCSR then useq_write_en
                    else Wire.mk "csr_drain_and_writes"
      -- Per-CSR write enables
      [Gate.mkAND we_src is_vstart csr_we_vstart,
       Gate.mkAND we_src is_vxrm csr_we_vxrm,
       Gate.mkAND we_src is_vxsat csr_we_vxsat,
       Gate.mkAND we_src is_vcsr csr_we_vcsr] ++
      -- vcsr composes vxrm and vxsat: OR write enables
      let we_vxsat_final := Wire.mk "we_vxsat_final"
      let we_vxrm_final := Wire.mk "we_vxrm_final"
      -- Also OR in RvvCore vxsat writeback
      let we_vxsat_csr_or_vcsr := Wire.mk "we_vxsat_csr_or_vcsr"
      [Gate.mkOR csr_we_vxsat csr_we_vcsr we_vxsat_csr_or_vcsr,
       Gate.mkOR we_vxsat_csr_or_vcsr rvv_wr_vxsat_valid we_vxsat_final,
       Gate.mkOR csr_we_vxrm csr_we_vcsr we_vxrm_final] ++
      -- vstart next-value: MUX(hold, write_val, we)
      (List.range 7).map (fun i =>
        Gate.mkMUX vstart_reg[i]! csr_write_val[i]! csr_we_vstart vstart_next[i]!) ++
      -- vxrm next-value: MUX(hold, write_val, we)
      -- For vcsr write: vxrm comes from bits [2:1] of write value
      let vxrm_wval := (List.range 2).map (fun i => Wire.mk s!"vxrm_wval_e{i}")
      (List.range 2).map (fun i =>
        Gate.mkMUX csr_write_val[i]! csr_write_val[i + 1]! csr_we_vcsr vxrm_wval[i]!) ++
      (List.range 2).map (fun i =>
        Gate.mkMUX vxrm_reg[i]! vxrm_wval[i]! we_vxrm_final vxrm_next[i]!) ++
      -- vxsat next-value: MUX(hold, write_val, we) with RvvCore OR path
      -- For vcsr write: vxsat comes from bit [0] of write value (same as csr_write_val[0])
      -- For RvvCore writeback: OR into current value
      let vxsat_or_rvv := Wire.mk "vxsat_or_rvv"
      let vxsat_wval := Wire.mk "vxsat_wval"
      [Gate.mkOR vxsat_reg[0]! rvv_wr_vxsat vxsat_or_rvv,
       Gate.mkMUX vxsat_or_rvv csr_write_val[0]! we_vxsat_final vxsat_wval,
       -- When only rvv_wr_vxsat_valid (no CSR write), use the OR'd value
       -- When CSR write, use csr_write_val. The MUX above handles this since
       -- we_vxsat_final includes rvv_wr_vxsat_valid
       Gate.mkMUX vxsat_reg[0]! vxsat_wval we_vxsat_final vxsat_next[0]!]
    else if enableVector then
      -- No Zicsr: tie next to current (hold)
      (List.range 7).map (fun i => Gate.mkBUF zero vstart_next[i]!) ++
      (List.range 2).map (fun i => Gate.mkBUF zero vxrm_next[i]!) ++
      [Gate.mkBUF zero vxsat_next[0]!]
    else []

  -- Commit injection: MUX rob_commit vs CSR fake commit
  -- At drain_complete, rob_commit_en is 0 (ROB empty), so OR works as MUX
  let csr_commit_inject_gates : List Gate :=
    if config.enableZicsr then
      [Gate.mkOR rob_commit_en merged_cdb_inject commit_valid_muxed,
       Gate.mkMUX (if enableF then Wire.mk "int_commit_hasPhysRd" else rob_head_hasOldPhysRd)
                  one merged_cdb_inject commit_hasPhysRd_muxed,
       Gate.mkMUX (if enableF then Wire.mk "int_commit_hasAllocSlot" else Wire.mk "rob_head_hasPhysRd")
                  one merged_cdb_inject commit_hasAllocSlot_muxed] ++
      (List.range 5).map (fun i =>
        Gate.mkMUX (Wire.mk s!"rob_head_archRd_{i}") csr_rd_reg[i]! merged_cdb_inject commit_archRd_muxed[i]!) ++
      (List.range 6).map (fun i =>
        Gate.mkMUX rob_head_physRd[i]! csr_phys_reg[i]! merged_cdb_inject commit_physRd_muxed[i]!)
    else
      [Gate.mkBUF rob_commit_en commit_valid_muxed,
       Gate.mkBUF (if enableF then Wire.mk "int_commit_hasPhysRd" else rob_head_hasOldPhysRd)
                  commit_hasPhysRd_muxed,
       Gate.mkBUF (if enableF then Wire.mk "int_commit_hasAllocSlot" else Wire.mk "rob_head_hasPhysRd")
                  commit_hasAllocSlot_muxed] ++
      (List.range 5).map (fun i =>
        Gate.mkBUF (Wire.mk s!"rob_head_archRd_{i}") commit_archRd_muxed[i]!) ++
      (List.range 6).map (fun i =>
        Gate.mkBUF rob_head_physRd[i]! commit_physRd_muxed[i]!)

  -- Collect all CSR gates
  let csr_all_gates := csr_drain_gate ++ csr_addr_decode_gates ++
    mstatus_force_gates ++ csr_read_mux_all_gates ++ csr_op_decode_gates ++
    csr_write_logic_gates ++ trap_we_merge_gates ++ csr_next_value_gates ++
    vec_csr_write_gates ++
    csr_cdb_inject_gates ++ csr_commit_inject_gates

  -- === OUTPUT BUFFERS ===
  let global_stall_out := Wire.mk "global_stall_out"
  -- Kanata trace output wires
  let trace_alloc_valid := Wire.mk "trace_alloc_valid"
  let trace_alloc_idx := makeIndexedWires "trace_alloc_idx" 4
  let trace_alloc_physrd := makeIndexedWires "trace_alloc_physrd" 6
  let trace_cdb_valid := Wire.mk "trace_cdb_valid"
  let trace_cdb_tag := makeIndexedWires "trace_cdb_tag" 6
  let trace_flush := Wire.mk "trace_flush"
  let trace_head_idx := makeIndexedWires "trace_head_idx" 4
  -- Dispatch tracking: OR of all RS dispatch_valids, with per-RS valid + tag outputs
  let trace_dispatch_int := Wire.mk "trace_dispatch_int"
  let trace_dispatch_mem := Wire.mk "trace_dispatch_mem"
  let trace_dispatch_branch := Wire.mk "trace_dispatch_branch"
  let trace_dispatch_muldiv := Wire.mk "trace_dispatch_muldiv"
  let trace_dispatch_fp := Wire.mk "trace_dispatch_fp"
  let trace_dispatch_int_tag := makeIndexedWires "trace_dispatch_int_tag" 6
  let trace_dispatch_mem_tag := makeIndexedWires "trace_dispatch_mem_tag" 6
  let trace_dispatch_branch_tag := makeIndexedWires "trace_dispatch_branch_tag" 6
  let trace_dispatch_muldiv_tag := makeIndexedWires "trace_dispatch_muldiv_tag" 6
  let trace_dispatch_fp_tag := makeIndexedWires "trace_dispatch_fp_tag" 6
  let alloc_physrd_wires := if enableF then rob_alloc_physRd_fp else branch_alloc_physRd
  let output_gates := [Gate.mkBUF global_stall global_stall_out,
                        Gate.mkBUF rename_valid_gated trace_alloc_valid,
                        Gate.mkBUF cdb_valid trace_cdb_valid,
                        Gate.mkBUF pipeline_flush_comb trace_flush,
                        -- AND dispatch_valid with dispatch_en for each RS
                        -- (dispatch_valid = RS has ready entry, dispatch_en = EU can accept)
                        Gate.mkAND rs_int_dispatch_valid ib_fifo_enq_ready trace_dispatch_int,
                        Gate.mkAND rs_mem_dispatch_valid mem_dispatch_en trace_dispatch_mem,
                        Gate.mkAND rs_branch_dispatch_valid branch_dispatch_en trace_dispatch_branch] ++
    (if enableM then [Gate.mkAND rs_muldiv_dispatch_valid muldiv_dispatch_en trace_dispatch_muldiv]
     else [Gate.mkBUF zero trace_dispatch_muldiv]) ++
    (if enableF then [Gate.mkAND rs_fp_dispatch_valid fp_rs_dispatch_en trace_dispatch_fp]
     else [Gate.mkBUF zero trace_dispatch_fp]) ++
    (List.range 4).map (fun i => Gate.mkBUF rob_alloc_idx[i]! trace_alloc_idx[i]!) ++
    (List.range 6).map (fun i => Gate.mkBUF alloc_physrd_wires[i]! trace_alloc_physrd[i]!) ++
    (List.range 6).map (fun i => Gate.mkBUF cdb_tag[i]! trace_cdb_tag[i]!) ++
    (List.range 4).map (fun i => Gate.mkBUF rob_head_idx[i]! trace_head_idx[i]!) ++
    (List.range 6).map (fun i => Gate.mkBUF rs_int_dispatch_tag[i]! trace_dispatch_int_tag[i]!) ++
    (List.range 6).map (fun i => Gate.mkBUF rs_mem_dispatch_tag[i]! trace_dispatch_mem_tag[i]!) ++
    (List.range 6).map (fun i => Gate.mkBUF rs_branch_dispatch_tag[i]! trace_dispatch_branch_tag[i]!) ++
    (if enableM then (List.range 6).map (fun i => Gate.mkBUF rs_muldiv_dispatch_tag[i]! trace_dispatch_muldiv_tag[i]!)
     else (List.range 6).map (fun i => Gate.mkBUF zero trace_dispatch_muldiv_tag[i]!)) ++
    (if enableF then (List.range 6).map (fun i => Gate.mkBUF rs_fp_dispatch_tag[i]! trace_dispatch_fp_tag[i]!)
     else (List.range 6).map (fun i => Gate.mkBUF zero trace_dispatch_fp_tag[i]!))

  { name := s!"CPU_{config.isaString}"
    inputs := [clock, reset, zero, one, fetch_stall_ext, dmem_stall_ext] ++
              imem_resp_data ++
              [dmem_req_ready, dmem_resp_valid] ++ dmem_resp_data ++
              (if enableVector then [vec_dmem_req_ready, vec_dmem_resp_valid] ++ vec_dmem_resp_rdata else [])
    outputs := fetch_pc ++ [fetch_stalled, global_stall_out] ++
               [dmem_req_valid, dmem_req_we] ++ dmem_req_addr ++ dmem_req_data ++ dmem_req_size ++
               [rob_empty, fence_i_drain_complete] ++
               -- RVVI-TRACE outputs
               [rvvi_valid, rvvi_trap] ++ rvvi_pc_rdata ++ rvvi_insn ++
               rvvi_rd ++ [rvvi_rd_valid] ++ rvvi_rd_data_final ++
               rvvi_frd ++ [rvvi_frd_valid] ++ rvvi_frd_data ++
               fflags_acc ++
               -- Kanata trace outputs
               [trace_alloc_valid] ++ trace_alloc_idx ++
               trace_alloc_physrd ++
               [trace_cdb_valid] ++ trace_cdb_tag ++
               [trace_flush] ++ trace_head_idx ++
               [trace_dispatch_int] ++ trace_dispatch_int_tag ++
               [trace_dispatch_mem] ++ trace_dispatch_mem_tag ++
               [trace_dispatch_branch] ++ trace_dispatch_branch_tag ++
               [trace_dispatch_muldiv] ++ trace_dispatch_muldiv_tag ++
               [trace_dispatch_fp] ++ trace_dispatch_fp_tag ++
               (if enableVector then
                 [rvv_async_rd_valid] ++ rvv_async_rd_addr ++ rvv_async_rd_data ++
                 [rvv_reg_write_valid] ++ rvv_reg_write_addr ++ rvv_reg_write_data ++
                 [rvv_trap_valid, rvv_idle] ++ rvv_queue_capacity ++
                 [vec_dmem_req_valid, vec_dmem_req_we] ++ vec_dmem_req_addr ++ vec_dmem_req_data ++ vec_dmem_req_size
               else [])
    gates := fence_i_const_4_gates ++ fence_i_detect_gates ++ flush_gate ++ dispatch_gates ++ rd_nonzero_gates ++ int_dest_tag_mask_gates ++ branch_alloc_physRd_gates ++ src2_mux_gates ++ [busy_set_gate] ++ busy_gates ++
             cdb_tag_buf_gates ++ cdb_data_buf_gates ++ cdb_prf_route_gates ++
             (if enableF then [fp_busy_set_gate] ++ fp_busy_gates ++ fp_src3_busy_gates else []) ++
             fp_crossdomain_gates ++ fp_cdb_fwd_gates ++ fp_fwd_data_gates ++
             fpu_lut_gates ++ fp_rs_dispatch_gate ++ muldiv_dispatch_gate ++
             fp_src3_alloc_decode ++ fp_src3_dff_gates ++ fp_src3_read_gates ++
             rm_resolve_gates ++ fp_rm_alloc_decode ++ fp_rm_dff_gates ++ fp_rm_read_gates ++
             frm_gates ++
             (if enableF then fp_op_gates else []) ++
             cdb_fwd_gates ++ fwd_src1_data_gates ++ fwd_src2_data_gates ++
             alu_lut_gates ++ muldiv_lut_gates ++ cdb_tag_nz_gates ++ cdb_arb_gates ++
             rob_fp_shadow_gates ++ rob_isStore_shadow_gates ++ redir_shadow_all_gates ++ rob_old_phys_mux_gates ++ fp_retire_gates ++
             imm_rf_we_gates ++ imm_rf_gates ++ imm_rf_sel_gates ++
             int_imm_rf_we_gates ++ int_imm_rf_gates ++ int_imm_rf_sel_gates ++
             int_pc_rf_gates ++
             lui_match_gates ++ auipc_match_gates ++ lui_auipc_gates ++
             br_pred_taken_gates ++ br_pred_read_gates ++
             br_pc_rf_we_gates ++ br_pc_rf_gates ++ br_pc_rf_sel_gates ++
             br_imm_rf_gates ++
             branch_resolve_gates ++
             fp_mem_mux_gates ++ flw_match_gates ++
             lw_match_gates ++ lh_match_gates ++ lhu_match_gates ++
             lb_match_gates ++ lbu_match_gates ++ is_load_gates ++
             sw_match_gates ++ sh_match_gates ++ sb_match_gates ++ fsw_match_gates ++
             mem_size_gates ++ sign_extend_gates ++ sb_enq_size_gates ++ store_mask_gates ++
             fwd_size_check_gates_and_load_fwd_gates ++ lsu_sb_fwd_format_all ++
             lsu_valid_gate ++ lsu_tag_data_mux_gates ++
             lsu_is_fp_gates ++ dmem_is_fp_gates ++ dmem_meta_capture_gates ++ dmem_resp_format_all ++
             commit_gates ++ retire_tag_filter_gates ++ crossdomain_stall_gates ++ vec_fence_gates ++ stall_gates ++ dmem_gates ++ output_gates ++ rvvi_cdb_bypass_gates ++ rvvi_gates ++
             rvvi_fp_gates ++
             fflags_gates ++
             csr_all_gates ++
             rvv_pack_gates ++ rvv_async_gates ++ rvv_vsetvl_gates ++ rvv_cdb_or_gates
    instances := microcode_instances ++
                  [fence_i_draining_dff, fence_i_adder_inst] ++ fence_i_redir_dffs ++
                  [csr_flag_dff, csr_flush_suppress_dff] ++ csr_addr_dffs ++ csr_optype_dffs ++ csr_rd_dffs ++ csr_phys_dffs ++ csr_rs1cap_dffs ++ csr_zimm_dffs ++
                  csr_reg_instances ++ vec_csr_reg_instances ++ csr_counter_instances ++
                  [fetch_inst, decoder_inst, rename_inst] ++
                  (if enableF then [fp_rename_inst] else []) ++
                  [redirect_valid_dff_inst, redirect_valid_fp_dff, redirect_valid_int_dff,
                   flush_dff_dispatch] ++ flush_dff_insts ++ flush_busy_dff_insts ++
                  redirect_target_dff_insts ++
                  busy_instances ++
                  (if enableF then fp_busy_instances else []) ++
                  cdb_fwd_instances ++
                  fp_cdb_fwd_instances ++
                  [rs_int_inst, rs_mem_inst, rs_branch_inst] ++
                  (if enableM then [rs_muldiv_inst] else []) ++
                  (if enableF then [rs_fp_inst] else []) ++
                  [int_exec_inst, branch_exec_inst, mem_exec_inst] ++
                  (if enableM then [muldiv_exec_inst] else []) ++
                  (if enableF then [fp_exec_inst] else []) ++
                  (if enableVector then [rvv_core_inst] ++ rvv_sidecar_dffs ++ rvv_mem_sidecar_dffs ++ rvv_vec_lsu_inst else []) ++
                  [rob_inst, lsu_inst,
                  imm_rf_decoder_inst, imm_rf_mux_inst,
                  int_imm_rf_decoder_inst, int_imm_rf_mux_inst, int_pc_rf_mux_inst,
                  br_pc_rf_decoder_inst, br_pc_rf_mux_inst, br_imm_rf_mux_inst,
                  auipc_adder_inst] ++
                  branch_resolve_insts ++
                  [cdb_mux_inst] ++ cdb_reg_insts ++
                  [ib_fifo_inst, lsu_fifo_inst] ++
                  (if enableM then [muldiv_fifo_inst] else []) ++
                  (if enableF then [fp_fifo_inst] else []) ++
                  lsu_pipeline_insts ++
                  [pc_queue_inst, insn_queue_inst] ++
                  fflags_dff_instances ++ frm_dff_instances ++
                  rob_isStore_shadow_insts ++
                  redir_tag_cmp_insts ++ redir_target_shadow_insts ++
                  [dmem_pending_inst, cross_size_pending_inst] ++ dmem_tag_capture_insts ++ dmem_is_fp_insts ++
                  dmem_meta_capture_insts ++
                  mem_pipe_insts
    signalGroups :=
      [{ name := "imem_resp_data", width := 32, wires := imem_resp_data },
       { name := "dmem_resp_data", width := 32, wires := dmem_resp_data },
       { name := "decode_optype", width := opcodeWidth, wires := decode_optype },
       { name := "decode_rd", width := 5, wires := decode_rd },
       { name := "decode_rs1", width := 5, wires := decode_rs1 },
       { name := "decode_rs2", width := 5, wires := decode_rs2 },
       { name := "decode_imm", width := 32, wires := decode_imm },
       { name := "branch_redirect_target", width := 32, wires := branch_redirect_target },
       { name := "fetch_pc", width := 32, wires := fetch_pc },
       { name := "rs1_phys", width := 6, wires := rs1_phys },
       { name := "rs2_phys", width := 6, wires := rs2_phys },
       { name := "rd_phys", width := 6, wires := rd_phys },
       { name := "old_rd_phys", width := 6, wires := old_rd_phys },
       { name := "rs1_data", width := 32, wires := rs1_data },
       { name := "rs2_data", width := 32, wires := rs2_data },
       { name := "issue_src2_muxed", width := 32, wires := issue_src2_muxed },
       { name := "cdb_tag", width := 6, wires := cdb_tag },
       { name := "cdb_tag_int", width := 6, wires := cdb_tag_int },
       { name := "cdb_tag_fp", width := 6, wires := cdb_tag_fp },
       { name := "cdb_tag_rs", width := 6, wires := cdb_tag_rs },
       { name := "cdb_tag_rob", width := 6, wires := cdb_tag_rob },
       { name := "cdb_data", width := 32, wires := cdb_data },
       { name := "rob_head_physRd", width := 6, wires := rob_head_physRd },
       { name := "rob_alloc_idx", width := 4, wires := rob_alloc_idx },
       { name := "rob_head_oldPhysRd", width := 6, wires := rob_head_oldPhysRd },
       { name := "rob_head_archRd", width := 5, wires := rob_head_archRd },
       { name := "int_result", width := 32, wires := int_result },
       { name := "int_result_final", width := 32, wires := int_result_final },
       { name := "int_captured_imm", width := 32, wires := int_captured_imm },
       { name := "int_captured_pc", width := 32, wires := int_captured_pc },
       { name := "auipc_result", width := 32, wires := auipc_result },
       { name := "int_tag_out", width := 6, wires := int_tag_out },
       { name := "branch_result_final", width := 32, wires := branch_result_final },
       { name := "br_captured_pc", width := 32, wires := br_captured_pc },
       { name := "br_captured_imm", width := 32, wires := br_captured_imm },
       { name := "br_pc_plus_4", width := 32, wires := br_pc_plus_4 },
       { name := "branch_target", width := 32, wires := makeIndexedWires "branch_target" 32 },
       { name := "final_branch_target", width := 32, wires := final_branch_target },
       { name := "mem_address", width := 32, wires := mem_address },
       { name := "mem_addr_r", width := 32, wires := mem_addr_r },
       { name := "mem_tag_r", width := 6, wires := mem_tag_r },
       { name := "mem_size_r", width := 2, wires := mem_size_r },
       { name := "mem_tag_out", width := 6, wires := mem_tag_out }] ++
      (if enableM then [
       { name := "muldiv_result", width := 32, wires := muldiv_result },
       { name := "muldiv_tag_out", width := 6, wires := muldiv_tag_out },
       { name := "muldiv_fifo_enq_data", width := 39, wires := muldiv_fifo_enq_data },
       { name := "muldiv_fifo_deq", width := 39, wires := muldiv_fifo_deq }] else []) ++
      [{ name := "ib_fifo_enq_data", width := 72, wires := ib_fifo_enq_data },
       { name := "ib_fifo_deq", width := 72, wires := ib_fifo_deq },
       { name := "lsu_fifo_enq_data", width := 39, wires := lsu_fifo_enq_data },
       { name := "lsu_fifo_deq", width := 39, wires := lsu_fifo_deq }] ++
      (if enableF then [
       { name := "fp_fifo_enq_data", width := 39, wires := fp_fifo_enq_data },
       { name := "fp_fifo_deq", width := 39, wires := fp_fifo_deq }] else []) ++
      [{ name := "lsu_agu_address", width := 32, wires := lsu_agu_address },
       { name := "lsu_agu_tag", width := 6, wires := lsu_agu_tag },
       { name := "lsu_sb_fwd_data", width := 32, wires := lsu_sb_fwd_data },
       { name := "lsu_sb_fwd_size", width := 2, wires := lsu_sb_fwd_size },
       { name := "lsu_sb_deq_bits", width := 66, wires := lsu_sb_deq_bits },
       { name := "lsu_sb_enq_idx", width := 3, wires := lsu_sb_enq_idx },
       { name := "dmem_req_addr", width := 32, wires := dmem_req_addr },
       { name := "dmem_req_data", width := 32, wires := dmem_req_data },
       { name := "dmem_req_size", width := 2, wires := dmem_req_size },
       { name := "rs_int_dispatch_opcode", width := 6, wires := rs_int_dispatch_opcode },
       { name := "rs_int_dispatch_src1", width := 32, wires := rs_int_dispatch_src1 },
       { name := "rs_int_dispatch_src2", width := 32, wires := rs_int_dispatch_src2 },
       { name := "rs_int_dispatch_tag", width := 6, wires := rs_int_dispatch_tag },
       { name := "rs_mem_dispatch_opcode", width := 6, wires := rs_mem_dispatch_opcode },
       { name := "rs_mem_dispatch_src1", width := 32, wires := rs_mem_dispatch_src1 },
       { name := "rs_mem_dispatch_src2", width := 32, wires := rs_mem_dispatch_src2 },
       { name := "rs_mem_dispatch_tag", width := 6, wires := rs_mem_dispatch_tag },
       { name := "rs_branch_dispatch_opcode", width := 6, wires := rs_branch_dispatch_opcode },
       { name := "rs_branch_dispatch_src1", width := 32, wires := rs_branch_dispatch_src1 },
       { name := "rs_branch_dispatch_src2", width := 32, wires := rs_branch_dispatch_src2 },
       { name := "rs_branch_dispatch_tag", width := 6, wires := rs_branch_dispatch_tag }] ++
      (if enableM then [
       { name := "rs_muldiv_dispatch_opcode", width := 6, wires := rs_muldiv_dispatch_opcode },
       { name := "rs_muldiv_dispatch_src1", width := 32, wires := rs_muldiv_dispatch_src1 },
       { name := "rs_muldiv_dispatch_src2", width := 32, wires := rs_muldiv_dispatch_src2 },
       { name := "rs_muldiv_dispatch_tag", width := 6, wires := rs_muldiv_dispatch_tag },
       { name := "muldiv_fifo_deq", width := 39, wires := muldiv_fifo_deq }] else []) ++
      [{ name := "rvvi_pc_rdata", width := 32, wires := rvvi_pc_rdata },
       { name := "rvvi_insn", width := 32, wires := rvvi_insn },
       { name := "rvvi_rd", width := 5, wires := rvvi_rd },
       { name := "rvvi_rd_data", width := 32, wires := rvvi_rd_data_final },
       { name := "rvvi_frd", width := 5, wires := rvvi_frd },
       { name := "rvvi_frd_data", width := 32, wires := rvvi_frd_data },
       { name := "fflags_acc", width := 5, wires := fflags_acc },
       { name := "rob_head_idx", width := 4, wires := rob_head_idx },
       -- Kanata trace signal groups (source + output wires)
       { name := "trace_alloc_idx", width := 4, wires := trace_alloc_idx },
       { name := "trace_alloc_physrd", width := 6, wires := trace_alloc_physrd },
       { name := "trace_cdb_tag", width := 6, wires := trace_cdb_tag },
       { name := "trace_head_idx", width := 4, wires := trace_head_idx },
       { name := "trace_dispatch_int_tag", width := 6, wires := trace_dispatch_int_tag },
       { name := "trace_dispatch_mem_tag", width := 6, wires := trace_dispatch_mem_tag },
       { name := "trace_dispatch_branch_tag", width := 6, wires := trace_dispatch_branch_tag },
       { name := "trace_dispatch_muldiv_tag", width := 6, wires := trace_dispatch_muldiv_tag },
       { name := "trace_dispatch_fp_tag", width := 6, wires := trace_dispatch_fp_tag },
       { name := "rob_alloc_physRd_fp", width := 6, wires := rob_alloc_physRd_fp }] ++
      (if enableF then [
       { name := "fp_rs1_phys", width := 6, wires := fp_rs1_phys },
       { name := "fp_rs2_phys", width := 6, wires := fp_rs2_phys },
       { name := "fp_rd_phys", width := 6, wires := fp_rd_phys },
       { name := "fp_result", width := 32, wires := fp_result },
       { name := "fp_tag_out", width := 6, wires := fp_tag_out },
       { name := "rs_fp_dispatch_opcode", width := 6, wires := rs_fp_dispatch_opcode },
       { name := "rs_fp_dispatch_src1", width := 32, wires := rs_fp_dispatch_src1 },
       { name := "rs_fp_dispatch_src2", width := 32, wires := rs_fp_dispatch_src2 },
       { name := "rs_fp_dispatch_tag", width := 6, wires := rs_fp_dispatch_tag },
       { name := "fp_rvvi_rd_data", width := 32, wires := fp_rvvi_rd_data }] else [])
  }

/-- RV32I CPU (backward-compatible alias) -/
def mkCPU_RV32I : Circuit := mkCPU rv32iConfig

/-- RV32IM CPU (backward-compatible alias) -/
def mkCPU_RV32IM : Circuit := mkCPU rv32imConfig

/-- RV32IF CPU (F extension only) -/
def mkCPU_RV32IF : Circuit := mkCPU rv32ifConfig

/-- RV32IMF CPU (M + F extensions) -/
def mkCPU_RV32IMF : Circuit := mkCPU rv32imfConfig

/-- RV32IMF CPU with microcoded CSR sequencer -/
def mkCPU_RV32IMF_Microcoded : Circuit := mkCPU rv32imfMicrocodedConfig

/-- RV32IMF_Zve32x CPU with vector extension (RvvCore) -/
def mkCPU_RV32IMF_Vector : Circuit := mkCPU rv32imfVectorConfig

end -- section

end Shoumei.RISCV.CPU
