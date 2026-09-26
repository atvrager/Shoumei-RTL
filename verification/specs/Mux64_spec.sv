// SystemVerilog reference specification: Parameterized 64:1 Multiplexer
// Selects one of sixty-four WIDTH-bit inputs via 6-bit sel.

module Mux64_spec #(
  parameter int WIDTH = 32
) (
  input  logic [WIDTH-1:0] in0,  input  logic [WIDTH-1:0] in1,  input  logic [WIDTH-1:0] in2,  input  logic [WIDTH-1:0] in3,
  input  logic [WIDTH-1:0] in4,  input  logic [WIDTH-1:0] in5,  input  logic [WIDTH-1:0] in6,  input  logic [WIDTH-1:0] in7,
  input  logic [WIDTH-1:0] in8,  input  logic [WIDTH-1:0] in9,  input  logic [WIDTH-1:0] in10, input  logic [WIDTH-1:0] in11,
  input  logic [WIDTH-1:0] in12, input  logic [WIDTH-1:0] in13, input  logic [WIDTH-1:0] in14, input  logic [WIDTH-1:0] in15,
  input  logic [WIDTH-1:0] in16, input  logic [WIDTH-1:0] in17, input  logic [WIDTH-1:0] in18, input  logic [WIDTH-1:0] in19,
  input  logic [WIDTH-1:0] in20, input  logic [WIDTH-1:0] in21, input  logic [WIDTH-1:0] in22, input  logic [WIDTH-1:0] in23,
  input  logic [WIDTH-1:0] in24, input  logic [WIDTH-1:0] in25, input  logic [WIDTH-1:0] in26, input  logic [WIDTH-1:0] in27,
  input  logic [WIDTH-1:0] in28, input  logic [WIDTH-1:0] in29, input  logic [WIDTH-1:0] in30, input  logic [WIDTH-1:0] in31,
  input  logic [WIDTH-1:0] in32, input  logic [WIDTH-1:0] in33, input  logic [WIDTH-1:0] in34, input  logic [WIDTH-1:0] in35,
  input  logic [WIDTH-1:0] in36, input  logic [WIDTH-1:0] in37, input  logic [WIDTH-1:0] in38, input  logic [WIDTH-1:0] in39,
  input  logic [WIDTH-1:0] in40, input  logic [WIDTH-1:0] in41, input  logic [WIDTH-1:0] in42, input  logic [WIDTH-1:0] in43,
  input  logic [WIDTH-1:0] in44, input  logic [WIDTH-1:0] in45, input  logic [WIDTH-1:0] in46, input  logic [WIDTH-1:0] in47,
  input  logic [WIDTH-1:0] in48, input  logic [WIDTH-1:0] in49, input  logic [WIDTH-1:0] in50, input  logic [WIDTH-1:0] in51,
  input  logic [WIDTH-1:0] in52, input  logic [WIDTH-1:0] in53, input  logic [WIDTH-1:0] in54, input  logic [WIDTH-1:0] in55,
  input  logic [WIDTH-1:0] in56, input  logic [WIDTH-1:0] in57, input  logic [WIDTH-1:0] in58, input  logic [WIDTH-1:0] in59,
  input  logic [WIDTH-1:0] in60, input  logic [WIDTH-1:0] in61, input  logic [WIDTH-1:0] in62, input  logic [WIDTH-1:0] in63,
  input  logic [5:0]       sel,
  output logic [WIDTH-1:0] out
);

  always_comb begin
    case (sel)
      6'd0:  out = in0;   6'd1:  out = in1;   6'd2:  out = in2;   6'd3:  out = in3;
      6'd4:  out = in4;   6'd5:  out = in5;   6'd6:  out = in6;   6'd7:  out = in7;
      6'd8:  out = in8;   6'd9:  out = in9;   6'd10: out = in10;  6'd11: out = in11;
      6'd12: out = in12;  6'd13: out = in13;  6'd14: out = in14;  6'd15: out = in15;
      6'd16: out = in16;  6'd17: out = in17;  6'd18: out = in18;  6'd19: out = in19;
      6'd20: out = in20;  6'd21: out = in21;  6'd22: out = in22;  6'd23: out = in23;
      6'd24: out = in24;  6'd25: out = in25;  6'd26: out = in26;  6'd27: out = in27;
      6'd28: out = in28;  6'd29: out = in29;  6'd30: out = in30;  6'd31: out = in31;
      6'd32: out = in32;  6'd33: out = in33;  6'd34: out = in34;  6'd35: out = in35;
      6'd36: out = in36;  6'd37: out = in37;  6'd38: out = in38;  6'd39: out = in39;
      6'd40: out = in40;  6'd41: out = in41;  6'd42: out = in42;  6'd43: out = in43;
      6'd44: out = in44;  6'd45: out = in45;  6'd46: out = in46;  6'd47: out = in47;
      6'd48: out = in48;  6'd49: out = in49;  6'd50: out = in50;  6'd51: out = in51;
      6'd52: out = in52;  6'd53: out = in53;  6'd54: out = in54;  6'd55: out = in55;
      6'd56: out = in56;  6'd57: out = in57;  6'd58: out = in58;  6'd59: out = in59;
      6'd60: out = in60;  6'd61: out = in61;  6'd62: out = in62;  6'd63: out = in63;
      default: out = '0;
    endcase
  end

endmodule
