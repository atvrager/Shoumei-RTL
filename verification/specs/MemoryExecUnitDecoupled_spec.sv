// Expressive, human-readable specification of Decoupled Memory Execution Unit.

module MemoryExecUnitDecoupled_spec (
  input  logic [63:0] base,
  input  logic [31:0] offset,
  input  logic [5:0]  dest_tag,
  input  logic [63:0] store_data,
  input  logic        sta_valid,
  input  logic        std_valid,
  output logic [63:0] address,
  output logic [5:0]  tag_out,
  output logic [63:0] std_data
);

  assign address  = base + {{32{offset[31]}}, offset};
  assign tag_out  = dest_tag;
  assign std_data = store_data;

`ifdef FORMAL
  // SVA assertions
  a_zero_offset: assert property (
    (offset == 32'b0) |-> (address == base)
  );

  a_store_passthru: assert property (
    std_data == store_data
  );
`endif

endmodule
