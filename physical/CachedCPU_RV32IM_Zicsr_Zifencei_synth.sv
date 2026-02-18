// Synthesis wrapper for CachedCPU_RV32IM_Zicsr_Zifencei
// CPU + L1I (8 sets) + L1D (4 sets, 2-way) + L2 (8 sets, 2-way)
// Ties off constant zero/one ports and exposes only the main memory interface.
// RVVI/store_snoop/fflags debug ports are left unconnected (optimized away).

module CachedCPU_RV32IM_Zicsr_Zifencei_synth (
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

  CachedCPU_RV32IM_Zicsr_Zifencei u_cpu (
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
    .fflags_acc()
  );

endmodule
