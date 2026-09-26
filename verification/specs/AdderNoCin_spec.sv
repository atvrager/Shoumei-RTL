// Expressive, human-readable specification of N-bit adder without carry-in (cin = 0).

module AdderNoCin_spec #(
  parameter int WIDTH = 32
) (
  input  logic [WIDTH-1:0] a,
  input  logic [WIDTH-1:0] b,
  output logic [WIDTH-1:0] sum
);

  assign sum = a + b;

`ifdef FORMAL
  always_comb begin
    assert (sum == a + b);
  end
`endif

endmodule
