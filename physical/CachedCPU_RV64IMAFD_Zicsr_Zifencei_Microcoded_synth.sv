// Synthesis wrapper for CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_L1I8K_L1D16K_L232K
// W=2 superscalar CPU + L1I (8KB) + L1D (16KB) + L2 (32KB) with microcode trap support
// Ties off constant zero/one and mtip ports, exposing only the main memory interface.
// RVVI/store_snoop debug ports are left unconnected (optimized away).

module CachedCPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_synth (
  input  logic          clock,
  input  logic          reset,
  input  logic          mtip_in,
  input  logic          msip_in,
  input  logic          meip_in,
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

  CPU_RV64IMAFD_Zicsr_Zifencei_Microcoded_L1I8K_L1D16K_L232K u_cpu (
    .clock(clock),
    .reset(reset),
    .mem_resp_valid(mem_resp_valid),
    .mtip_in(mtip_in),
    .msip_in(msip_in),
    .meip_in(meip_in),
    .mem_resp_data(mem_resp_data),
    .mem_req_valid(mem_req_valid),
    .mem_req_addr(mem_req_addr),
    .mem_req_we(mem_req_we),
    .mem_req_data(mem_req_data),
    .rob_empty(rob_empty)
    // Debug ports left unconnected; stale renamed `.port()` ties removed
    // (they break hierarchical FLATTEN=0 synthesis with a port mismatch)
  );

endmodule
