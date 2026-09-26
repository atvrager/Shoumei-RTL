// Expressive, human-readable specification of N-bit adder with variable cin.
// Parameterized for width and Cin configuration.

module Adder_spec #(
  parameter int WIDTH = 32
) (
  input  logic [WIDTH-1:0] a,
  input  logic [WIDTH-1:0] b,
  input  logic             cin,
  output logic [WIDTH-1:0] sum
);

  assign sum = a + b + {{(WIDTH-1){1'b0}}, cin};

`ifdef FORMAL
  // SVA arithmetic invariants
  always_comb begin
    assert (sum == a + b + cin);
    if (cin == 1'b0 && b == '0) assert (sum == a);
    if (cin == 1'b0 && a == '0) assert (sum == b);
  end
`endif

endmodule
