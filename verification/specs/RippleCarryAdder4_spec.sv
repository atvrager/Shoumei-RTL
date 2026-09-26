// Expressive, human-readable specification of 4-bit Ripple Carry Adder.

module RippleCarryAdder4_spec (
  input  logic [3:0] a,
  input  logic [3:0] b,
  input  logic       cin,
  output logic [3:0] sum,
  output logic       cout
);

  assign {cout, sum} = {1'b0, a} + {1'b0, b} + {4'd0, cin};

`ifdef FORMAL
  // SVA arithmetic invariants
  always_comb begin
    if (cin == 1'b0 && b == 4'd0) assert (sum == a && cout == 1'b0);
    if (cin == 1'b0 && a == 4'd0) assert (sum == b && cout == 1'b0);
  end
`endif

endmodule
