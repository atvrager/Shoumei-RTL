// Expressive, human-readable specification of 32x32 -> 64 unsigned multiplier.

module Mul32x32To64_spec #(
  parameter int WIDTH = 64
) (
  input  logic [31:0] a,
  input  logic [31:0] b,
  output logic [63:0] product
);

  assign product = 64'(a) * 64'(b);

`ifdef FORMAL
  // Zero multiplication property
  a_zero_mul: assert property (
    (a == 32'd0 || b == 32'd0) |-> (product == 64'd0)
  );

  // Identity multiplication property
  a_identity_mul: assert property (
    (b == 32'd1) |-> (product == WIDTH'(a))
  );
`endif

endmodule
