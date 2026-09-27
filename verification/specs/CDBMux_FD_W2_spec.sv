// Expressive, human-readable specification of Dual CDB Priority Drain Mux.

module CDBMux_FD_W2_spec (
  input  logic [1:0]   ib_valid,
  input  logic         fp_valid,
  input  logic         muldiv_valid,
  input  logic         lsu_valid,
  input  logic         dmem_valid,
  input  logic [69:0]  ib_deq_0,
  input  logic [102:0] ib_deq_1,
  input  logic [70:0]  fp_deq,
  input  logic [69:0]  muldiv_deq,
  input  logic [71:0]  lsu_deq,
  input  logic [63:0]  dmem_fmt,
  input  logic [5:0]   dmem_tag,
  input  logic         dmem_is_fp,
  input  logic         dmem_is_double,
  output logic [1:0]   pre_valid,
  output logic [5:0]   pre_tag_0,
  output logic [5:0]   pre_tag_1,
  output logic [63:0]  pre_data_0,
  output logic [63:0]  pre_data_1,
  output logic [1:0]   pre_is_fp,
  output logic         pre_is_double_0,
  output logic         drain_lsu,
  output logic         drain_muldiv,
  output logic         drain_fp,
  output logic [1:0]   drain_ib,
  output logic [31:0]  redirect_1,
  output logic         pre_mispredicted_1
);

  // CDB 0: dmem (highest) > lsu > ib_0 (lowest)
  wire dmem_wins = dmem_valid;
  wire lsu_wins  = lsu_valid & ~dmem_valid;
  wire ib0_wins  = ib_valid[0] & ~dmem_valid & ~lsu_wins;

  assign drain_lsu     = lsu_wins;
  assign drain_ib[0]   = ib0_wins;
  assign pre_valid[0]  = dmem_wins | lsu_wins | ib0_wins;

  assign pre_tag_0       = dmem_wins ? dmem_tag : (lsu_wins ? lsu_deq[5:0] : ib_deq_0[5:0]);
  assign pre_data_0      = dmem_wins ? dmem_fmt : (lsu_wins ? lsu_deq[69:6] : ib_deq_0[69:6]);
  assign pre_is_fp[0]    = dmem_wins ? dmem_is_fp : (lsu_wins ? lsu_deq[70] : 1'b0);
  assign pre_is_double_0 = dmem_wins ? dmem_is_double : (lsu_wins ? lsu_deq[71] : 1'b0);

  // CDB 1: fp (highest) > muldiv > ib_1 (lowest)
  wire fp_wins     = fp_valid;
  wire muldiv_wins = muldiv_valid & ~fp_valid;
  wire ib1_wins    = ib_valid[1] & ~fp_valid & ~muldiv_wins;

  assign drain_fp      = fp_wins;
  assign drain_muldiv  = muldiv_wins;
  assign drain_ib[1]   = ib1_wins;
  assign pre_valid[1]  = fp_wins | muldiv_wins | ib1_wins;

  assign pre_tag_1     = fp_wins ? fp_deq[5:0] : (muldiv_wins ? muldiv_deq[5:0] : ib_deq_1[5:0]);
  assign pre_data_1    = fp_wins ? fp_deq[69:6] : (muldiv_wins ? muldiv_deq[69:6] : ib_deq_1[69:6]);
  assign pre_is_fp[1]  = fp_wins ? fp_deq[70] : 1'b0;

  assign redirect_1         = ib1_wins ? ib_deq_1[101:70] : 32'b0;
  assign pre_mispredicted_1 = ib1_wins ? ib_deq_1[102] : 1'b0;

`ifdef FORMAL
  // SVA assertions
  a_dmem_priority: assert property (
    dmem_valid |-> (pre_valid[0] && (pre_tag_0 == dmem_tag))
  );

  a_fp_priority: assert property (
    fp_valid |-> (pre_valid[1] && (pre_tag_1 == fp_deq[5:0]))
  );
`endif

endmodule
