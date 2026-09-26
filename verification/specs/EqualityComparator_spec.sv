// Expressive, human-readable specification of N-bit equality-only comparator.

module EqualityComparator_spec #(
  parameter int WIDTH = 32
) (
  input  logic [WIDTH-1:0] a,
  input  logic [WIDTH-1:0] b,
  output logic             eq
);

  assign eq = (a == b);

`ifdef FORMAL
  always_comb begin
    assert (eq == (a == b));
  end
`endif

endmodule
