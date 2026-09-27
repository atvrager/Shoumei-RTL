// Expressive, human-readable specification of Branch Execution Unit.

module BranchExecUnit_spec (
  input  logic [31:0] src1,
  input  logic [31:0] src2,
  input  logic [5:0]  dest_tag,
  output logic [31:0] result,
  output logic [5:0]  tag_out
);

  assign result  = 32'b0;
  assign tag_out = dest_tag;

`ifdef FORMAL
  // SVA assertions
  a_result_zero: assert property (
    result == 32'b0
  );

  a_tag_passthru: assert property (
    tag_out == dest_tag
  );
`endif

endmodule
