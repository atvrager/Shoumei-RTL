// Synthesis wrapper for CPU_RV32IMF
// Ties off constant zero/one ports that the DSL exposes as inputs.
// This eliminates buffer tree overhead in physical synthesis.

module CPU_RV32IMF_synth (
  input logic clock,
  input logic reset,
  input logic [31:0] imem_resp_data,
  input logic dmem_req_ready,
  input logic dmem_resp_valid,
  input logic [31:0] dmem_resp_data,
  output logic [31:0] fetch_pc,
  output logic fetch_stalled,
  output logic global_stall_out,
  output logic dmem_req_valid,
  output logic dmem_req_we,
  output logic [31:0] dmem_req_addr,
  output logic [31:0] dmem_req_data,
  output logic rob_empty
);

  CPU_RV32IMF u_cpu (
    .clock(clock),
    .reset(reset),
    .zero(1'b0),
    .one(1'b1),
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
    .rob_empty(rob_empty)
  );

endmodule
