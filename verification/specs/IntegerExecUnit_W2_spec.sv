// Reference spec: Dual-Issue 32-bit Integer Execution Unit.
// Two independent ALU32 slots; each result is the ALU32 output, and each
// destination tag passes through unmodified.
//
// Structure mirrors the emitted netlist exactly: two ALU32 instances.

module IntegerExecUnit_W2_spec (
  input  logic [31:0] a0,
  input  logic [31:0] b0,
  input  logic [3:0]  opcode0,
  input  logic [5:0]  dest_tag0,
  input  logic [31:0] a1,
  input  logic [31:0] b1,
  input  logic [3:0]  opcode1,
  input  logic [5:0]  dest_tag1,
  output logic [31:0] result0,
  output logic [5:0]  tag_out0,
  output logic [31:0] result1,
  output logic [5:0]  tag_out1
);

  ALU32_spec u_alu0 (
    .a(a0),
    .b(b0),
    .op(opcode0),
    .result(result0)
  );

  ALU32_spec u_alu1 (
    .a(a1),
    .b(b1),
    .op(opcode1),
    .result(result1)
  );

  assign tag_out0 = dest_tag0;
  assign tag_out1 = dest_tag1;

`ifdef FORMAL
  // SVA assertions
  a_tag0_passthru: assert property (
    tag_out0 == dest_tag0
  );

  a_tag1_passthru: assert property (
    tag_out1 == dest_tag1
  );
`endif

endmodule
