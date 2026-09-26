// Expressive, human-readable specification of 32-bit RV32I ALU.

module ALU32_spec (
  input  logic [31:0] a,
  input  logic [31:0] b,
  input  logic [3:0]  op,
  output logic [31:0] result
);

  logic [31:0] arith_res;
  logic [31:0] logic_res;
  logic [31:0] shift_res;

  // Arithmetic unit (op[1:0])
  always_comb begin
    case (op[1:0])
      2'b00: arith_res = a + b;
      2'b01: arith_res = a - b;
      2'b10: arith_res = ($signed(a) < $signed(b)) ? 32'd1 : 32'd0;
      2'b11: arith_res = (a < b) ? 32'd1 : 32'd0;
    endcase
  end

  // Logic unit (LogicUnit: if op1 then XOR else (if op0 then OR else AND))
  always_comb begin
    if (op[1]) begin
      logic_res = a ^ b;
    end else if (op[0]) begin
      logic_res = a | b;
    end else begin
      logic_res = a & b;
    end
  end

  // Shifter unit (Shifter: 00=SLL, 01=SRL, 10=SRA, 11=SRA)
  always_comb begin
    if (op[1]) begin
      shift_res = $signed(a) >>> b[4:0];
    end else if (op[0]) begin
      shift_res = a >> b[4:0];
    end else begin
      shift_res = a << b[4:0];
    end
  end

  // Top-level multiplexer tree
  always_comb begin
    case (op[3:2])
      2'b00: result = arith_res;
      2'b01: result = logic_res;
      2'b10: result = shift_res;
      2'b11: result = 32'd0;
    endcase
  end

`ifdef FORMAL
  // SVA arithmetic/logic invariants
  a_add: assert property (op == 4'b0000 |-> result == a + b);
  a_sub: assert property (op == 4'b0001 |-> result == a - b);
  a_and: assert property (op == 4'b0100 |-> result == (a & b));
  a_or:  assert property (op == 4'b0101 |-> result == (a | b));
  a_xor: assert property (op == 4'b0110 |-> result == (a ^ b));
`endif

endmodule
