// Expressive, human-readable specification of N-bit adder with fixed cin = 1'b1.

module AdderWithCin1_spec #(
  parameter int WIDTH = 32
) (
  input  logic [WIDTH-1:0] a,
  input  logic [WIDTH-1:0] b,
  output logic [WIDTH-1:0] sum
);

  assign sum = a + b + {{(WIDTH-1){1'b0}}, 1'b1};

`ifdef FORMAL
  always_comb begin
    assert (sum == a + b + 1'b1);
  end
`endif

endmodule
