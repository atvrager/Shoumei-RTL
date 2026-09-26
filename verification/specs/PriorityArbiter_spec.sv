// Parameterized priority arbiter specification
// Grants request from lowest index bit 0 up to WIDTH-1 (fixed priority).

module PriorityArbiter_spec #(
  parameter int WIDTH = 8
) (
  input  logic [WIDTH-1:0] request,
  output logic [WIDTH-1:0] grant,
  output logic             valid
);

  assign valid = |request;
  assign grant = request & ~(request - WIDTH'(1));

endmodule
