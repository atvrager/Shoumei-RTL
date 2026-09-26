// Expressive, human-readable specification of 4:1 multiplexer with WIDTH-bit data paths.

module Mux4_spec #(
  parameter int WIDTH = 32
) (
  input  logic [WIDTH-1:0] in0,
  input  logic [WIDTH-1:0] in1,
  input  logic [WIDTH-1:0] in2,
  input  logic [WIDTH-1:0] in3,
  input  logic [1:0]       sel,
  output logic [WIDTH-1:0] out
);

  always_comb begin
    case (sel)
      2'd0: out = in0;
      2'd1: out = in1;
      2'd2: out = in2;
      2'd3: out = in3;
    endcase
  end

`ifdef FORMAL
  always_comb begin
    if (sel == 2'd0) assert (out == in0);
    if (sel == 2'd1) assert (out == in1);
    if (sel == 2'd2) assert (out == in2);
    if (sel == 2'd3) assert (out == in3);
  end
`endif

endmodule
