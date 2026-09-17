// Synthesis wrapper for CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded (W=2 superscalar RV64)
// Ties off constant zero/one, external stalls, and mtip ports.
// RVVI/trace/fflags debug ports are left unconnected (optimized away).

module CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth (
  input  logic        clock,
  input  logic        reset,
  // Instruction memory (dual fetch W=2)
  input  logic [31:0] imem_resp_data_0,
  input  logic [31:0] imem_resp_data_1,
  // Data memory (64-bit XLEN)
  input  logic        dmem_req_ready,
  input  logic        dmem_resp_valid,
  input  logic [63:0] dmem_resp_data,
  output logic [31:0] fetch_pc,
  output logic        fetch_stalled,
  output logic        global_stall_out,
  output logic        dmem_req_valid,
  output logic        dmem_req_we,
  output logic [31:0] dmem_req_addr,
  output logic [63:0] dmem_req_data,
  output logic [1:0]  dmem_req_size,
  output logic        rob_empty
);

  CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded u_cpu (
    .clock(clock),
    .reset(reset),
    .zero(1'b0),
    .one(1'b1),
    .fetch_stall_ext(1'b0),
    .ifetch_last_word(1'b0),
    .dmem_stall_ext(1'b0),
    .mtip_in(1'b0),
    .imem_resp_data_0(imem_resp_data_0),
    .imem_resp_data_1(imem_resp_data_1),
    .dmem_req_ready(dmem_req_ready),
    .dmem_resp_valid(dmem_resp_valid),
    .dmem_resp_data(dmem_resp_data),
    .fetch_pc_0(fetch_pc),
    .fetch_stalled(fetch_stalled),
    .global_stall_out(global_stall_out),
    .dmem_req_valid(dmem_req_valid),
    .dmem_req_we(dmem_req_we),
    .dmem_req_addr(dmem_req_addr),
    .dmem_req_data(dmem_req_data),
    .dmem_req_size(dmem_req_size),
    .rob_empty(rob_empty),
    // Debug ports — unconnected, synthesized away
    .rvvi_validS0(),
    .rvvi_validS1(),
    .rvvi_trapS0(),
    .rvvi_trapS1(),
    .rvvi_rd_validS0(),
    .rvvi_rd_validS1(),
    .rvvi_pc_0(),
    .rvvi_pc_1(),
    .rvvi_insn_0(),
    .rvvi_insn_1(),
    .rvvi_rd_0(),
    .rvvi_rd_1(),
    .rvvi_rdd_0(),
    .rvvi_rdd_1()
  );

endmodule
