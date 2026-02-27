// Synthesis wrapper for CPU_RV32IMF_Zicsr_Zifencei_Microcoded (W=2 superscalar)
// Ties off constant zero/one and external stall ports.
// RVVI/trace/fflags debug ports are left unconnected (optimized away).

module CPU_RV32IMF_Zicsr_Zifencei_Microcoded_synth (
  input  logic          clock,
  input  logic          reset,
  // Instruction memory
  input  logic [31:0]   imem_resp_data,
  // Data memory
  input  logic          dmem_req_ready,
  input  logic          dmem_resp_valid,
  input  logic [31:0]   dmem_resp_data,
  output logic [31:0]   fetch_pc,
  output logic          fetch_stalled,
  output logic          global_stall_out,
  output logic          dmem_req_valid,
  output logic          dmem_req_we,
  output logic [31:0]   dmem_req_addr,
  output logic [31:0]   dmem_req_data,
  output logic          dmem_req_size_0,
  output logic          dmem_req_size_1,
  output logic          rob_empty,
  output logic          fence_i_drain_complete
);

  CPU_RV32IMF_Zicsr_Zifencei_Microcoded u_cpu (
    .clock(clock),
    .reset(reset),
    .zero(1'b0),
    .one(1'b1),
    .fetch_stall_ext(1'b0),
    .dmem_stall_ext(1'b0),
    .imem_resp_data(imem_resp_data),
    .dmem_req_ready(dmem_req_ready),
    .dmem_resp_valid(dmem_resp_valid),
    .dmem_resp_data(dmem_resp_data),
    .fetch_pc(fetch_pc),
    .fetch_stalled(fetch_stalled),
    .global_stall_out(global_stall_out),
    .dmem_req_valid(dmem_req_valid),
    .dmem_req_we(dmem_req_we),
    .dmem_req_addr(dmem_req_addr),
    .dmem_req_data(dmem_req_data),
    .dmem_req_size_0(dmem_req_size_0),
    .dmem_req_size_1(dmem_req_size_1),
    .rob_empty(rob_empty),
    .fence_i_drain_complete(fence_i_drain_complete),
    // Debug ports — unconnected, synthesized away
    .rvvi_valid(),
    .rvvi_trap(),
    .rvvi_pc_rdata(),
    .rvvi_insn(),
    .rvvi_rd(),
    .rvvi_rd_valid(),
    .rvvi_rd_data(),
    .rvvi_frd(),
    .rvvi_frd_valid(),
    .rvvi_frd_data(),
    .fflags_acc(),
    .trace_alloc_valid(),
    .trace_alloc_idx(),
    .trace_alloc_physrd(),
    .trace_cdb_valid(),
    .trace_cdb_tag(),
    .trace_flush(),
    .trace_head_idx(),
    .trace_dispatch_int(),
    .trace_dispatch_int_tag(),
    .trace_dispatch_mem(),
    .trace_dispatch_mem_tag(),
    .trace_dispatch_branch(),
    .trace_dispatch_branch_tag(),
    .trace_dispatch_muldiv(),
    .trace_dispatch_muldiv_tag(),
    .trace_dispatch_fp(),
    .trace_dispatch_fp_tag()
  );

endmodule
