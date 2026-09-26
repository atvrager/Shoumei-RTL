// Expressive, human-readable specification of full N-bit comparator (signed and unsigned).

module Comparator_spec #(
  parameter int WIDTH = 32
) (
  input  logic [WIDTH-1:0] a,
  input  logic [WIDTH-1:0] b,
  output logic             eq,
  output logic             lt,
  output logic             ltu,
  output logic             gt,
  output logic             gtu
);

  assign eq  = (a == b);
  assign ltu = (a < b);
  assign gtu = (a > b);
  assign lt  = ($signed(a) < $signed(b));
  assign gt  = ($signed(a) > $signed(b));

`ifdef FORMAL
  always_comb begin
    assert (eq == (a == b));
    assert (ltu == (a < b));
    assert (gtu == (a > b));
  end
`endif

endmodule
