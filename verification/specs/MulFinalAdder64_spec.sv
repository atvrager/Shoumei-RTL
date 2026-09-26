// Expressive, human-readable specification of 64-bit Multiplier Final Adder.

module MulFinalAdder64_spec (
  input  logic [63:0] a,
  input  logic [62:0] b,
  output logic [63:0] sum
);

  assign sum = a + {b, 1'b0};

`ifdef FORMAL
  // SVA arithmetic invariants
  always_comb begin
    assert (sum[0] == a[0]);
    if (b == 63'd0) assert (sum == a);
  end
`endif

endmodule
