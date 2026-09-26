// SystemVerilog reference specification: Parameterized Barrel Shifter
// Supports RISC-V shift operations:
// op = 2'b00: SLL (Shift Left Logical)
// op = 2'b01: SRL (Shift Right Logical)
// op = 2'b10 / 2'b11: SRA (Shift Right Arithmetic)

module Shifter_spec #(
  parameter int WIDTH = 32,
  parameter int SHAMT_WIDTH = $clog2(WIDTH)
) (
  input  logic [WIDTH-1:0]       in,
  input  logic [SHAMT_WIDTH-1:0] shamt,
  input  logic [1:0]             op,
  output logic [WIDTH-1:0]       result
);

  always_comb begin
    case (op)
      2'b00:   result = in << shamt;
      2'b01:   result = in >> shamt;
      default: result = $signed(in) >>> shamt;
    endcase
  end

endmodule
