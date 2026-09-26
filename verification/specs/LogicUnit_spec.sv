// SystemVerilog reference specification: Parameterized Logic Unit
// Performs bitwise operations according to RISC-V ALU op[1:0]:
// 2'b00: AND
// 2'b01: OR
// 2'b10: XOR
// 2'b11: XOR (op[1] selects XOR)

module LogicUnit_spec #(
  parameter int WIDTH = 32
) (
  input  logic [WIDTH-1:0] a,
  input  logic [WIDTH-1:0] b,
  input  logic [1:0]       op,
  output logic [WIDTH-1:0] result
);

  always_comb begin
    case (op)
      2'b00:   result = a & b;
      2'b01:   result = a | b;
      default: result = a ^ b;
    endcase
  end

endmodule
