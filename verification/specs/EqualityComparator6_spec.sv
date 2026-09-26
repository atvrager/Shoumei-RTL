// Expressive, human-readable specification of 6-bit equality comparator.
module EqualityComparator6_spec (
  input  logic [5:0] a,
  input  logic [5:0] b,
  output logic       eq
);

  assign eq = (a == b);

`ifdef FORMAL
  // SVA reflexivity and symmetric properties
  always_comb begin
    if (a == b) assert(eq == 1'b1);
    if (a != b) assert(eq == 1'b0);
  end
`endif

endmodule
