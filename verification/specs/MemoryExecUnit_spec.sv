// Expressive, human-readable specification of Memory Execution Unit (AGU).

module MemoryExecUnit_spec (
  input  logic [63:0] base,
  input  logic [31:0] offset,
  input  logic [5:0]  dest_tag,
  output logic [63:0] address,
  output logic [5:0]  tag_out
);

  assign address = base + {{32{offset[31]}}, offset};
  assign tag_out = dest_tag;

`ifdef FORMAL
  // SVA assertions
  a_zero_offset: assert property (
    (offset == 32'b0) |-> (address == base)
  );

  a_tag_passthru: assert property (
    tag_out == dest_tag
  );
`endif

endmodule
