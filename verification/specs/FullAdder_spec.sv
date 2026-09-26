// Expressive, human-readable specification of 1-bit Full Adder.

module FullAdder_spec (
  input  logic a,
  input  logic b,
  input  logic cin,
  output logic sum,
  output logic cout
);

  assign {cout, sum} = {1'b0, a} + {1'b0, b} + {1'b0, cin};

`ifdef FORMAL
  // SVA arithmetic invariants
  always_comb begin
    assert (sum == (a ^ b ^ cin));
    if (cin == 1'b0 && b == 1'b0) assert (sum == a && cout == 1'b0);
    if (cin == 1'b0 && a == 1'b0) assert (sum == b && cout == 1'b0);
  end
`endif

endmodule
