// Synthesis wrapper for CPU_RV32IMF_Zicsr_Zifencei_Microcoded_L1I256B_L1D256B_L2512B
// W=2 superscalar CPU + L1I (256B) + L1D (256B) + L2 (512B) with microcode trap support
// Ties off constant zero/one ports and exposes only the main memory interface.
// RVVI/store_snoop debug ports are left unconnected (optimized away).

module CachedCPU_RV32IMF_Zicsr_Zifencei_Microcoded_synth (
  input  logic          clock,
  input  logic          reset,
  // Main memory interface (to DRAM/AXI)
  input  logic          mem_resp_valid,
  input  logic [255:0]  mem_resp_data,
  output logic          mem_req_valid,
  output logic [31:0]   mem_req_addr,
  output logic          mem_req_we,
  output logic [255:0]  mem_req_data,
  // Status
  output logic          rob_empty
);

  CPU_RV32IMF_Zicsr_Zifencei_Microcoded_L1I256B_L1D256B_L2512B u_cpu (
    .clock(clock),
    .reset(reset),
    .zero(1'b0),
    .one(1'b1),
    .mem_resp_valid(mem_resp_valid),
    .mem_resp_data(mem_resp_data),
    .mem_req_valid(mem_req_valid),
    .mem_req_addr(mem_req_addr),
    .mem_req_we(mem_req_we),
    .mem_req_data(mem_req_data),
    .rob_empty(rob_empty),
    // Debug ports — unconnected, synthesized away
    .store_snoop_valid(),
    .store_snoop_addr(),
    .store_snoop_data(),
    .rvvi_retire(),
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
