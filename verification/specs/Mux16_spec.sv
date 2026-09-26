// SystemVerilog reference specification: Parameterized 16:1 Multiplexer
// Selects one of sixteen WIDTH-bit inputs via 4-bit sel.

module Mux16_spec #(
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
  input  logic [WIDTH-1:0] in8,
  input  logic [WIDTH-1:0] in9,
  input  logic [WIDTH-1:0] in10,
  input  logic [WIDTH-1:0] in11,
  input  logic [WIDTH-1:0] in12,
  input  logic [WIDTH-1:0] in13,
  input  logic [WIDTH-1:0] in14,
  input  logic [WIDTH-1:0] in15,
  input  logic [3:0]       sel,
  output logic [WIDTH-1:0] out
);

  always_comb begin
    case (sel)
      4'd0:    out = in0;
      4'd1:    out = in1;
      4'd2:    out = in2;
      4'd3:    out = in3;
      4'd4:    out = in4;
      4'd5:    out = in5;
      4'd6:    out = in6;
      4'd7:    out = in7;
      4'd8:    out = in8;
      4'd9:    out = in9;
      4'd10:   out = in10;
      4'd11:   out = in11;
      4'd12:   out = in12;
      4'd13:   out = in13;
      4'd14:   out = in14;
      4'd15:   out = in15;
      default: out = '0;
    endcase
  end

endmodule
