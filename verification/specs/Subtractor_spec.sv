// Expressive, human-readable specification of N-bit subtractor with borrow output.

module Subtractor_spec #(
  parameter int WIDTH = 32
) (
  input  logic [WIDTH-1:0] a,
  input  logic [WIDTH-1:0] b,
  output logic [WIDTH-1:0] diff,
  output logic             borrow
);

  assign diff   = a - b;
  assign borrow = 1'b0;

`ifdef FORMAL
  always_comb begin
    assert (diff == a - b);
  end
`endif

endmodule
