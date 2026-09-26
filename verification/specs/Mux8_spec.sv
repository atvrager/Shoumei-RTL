// SystemVerilog reference specification: Parameterized 8:1 Multiplexer
// Selects one of eight WIDTH-bit inputs via 3-bit sel.

module Mux8_spec #(
  parameter int WIDTH = 32
) (
  input  logic [WIDTH-1:0] in0,
  input  logic [WIDTH-1:0] in1,
  input  logic [WIDTH-1:0] in2,
  input  logic [WIDTH-1:0] in3,
  input  logic [WIDTH-1:0] in4,
  input  logic [WIDTH-1:0] in5,
  input  logic [WIDTH-1:0] in6,
  input  logic [WIDTH-1:0] in7,
  input  logic [2:0]       sel,
  output logic [WIDTH-1:0] out
);

  always_comb begin
    case (sel)
      3'd0:    out = in0;
      3'd1:    out = in1;
      3'd2:    out = in2;
      3'd3:    out = in3;
      3'd4:    out = in4;
      3'd5:    out = in5;
      3'd6:    out = in6;
      3'd7:    out = in7;
      default: out = '0;
    endcase
  end

endmodule
