// Expressive, human-readable specification of 3:2 Carry-Save Compressor.

module CSACompressor_spec #(
  parameter int WIDTH = 64
) (
  input  logic [WIDTH-1:0] x,
  input  logic [WIDTH-1:0] y,
  input  logic [WIDTH-1:0] z,
  output logic [WIDTH-1:0] sum,
  output logic [WIDTH-1:0] carry
);

  logic [WIDTH-1:0] raw_carry;

  assign sum       = x ^ y ^ z;
  assign raw_carry = (x & y) | (y & z) | (x & z);
  assign carry     = {raw_carry[WIDTH-2:0], 1'b0};

`ifdef FORMAL
  // SVA arithmetic invariants
  always_comb begin
    assert (sum == (x ^ y ^ z));
    assert (carry[0] == 1'b0);
    if (z == '0 && y == '0) assert (sum == x && carry == '0);
  end
`endif

endmodule
