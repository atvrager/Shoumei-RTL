// Expressive, human-readable specification of 2-stage Reset Synchronizer.

module ResetSync_spec (
  output logic sync_reset,
  input  logic clock,
  input  logic reset
);

  logic stage1_q;
  logic stage2_q;

  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      stage1_q <= 1'b0;
      stage2_q <= 1'b0;
    end else begin
      stage1_q <= 1'b1;
      stage2_q <= stage1_q;
    end
  end

  assign sync_reset = ~stage2_q;

`ifdef FORMAL
  // SVA assertions
  a_output_boolean: assert property (
    (sync_reset == 1'b0) || (sync_reset == 1'b1)
  );
`endif

endmodule
