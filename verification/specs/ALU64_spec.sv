// Expressive, human-readable specification of 64-bit RV64I ALU.

module ALU64_spec (
  input  logic [63:0] a,
  input  logic [63:0] b,
  input  logic [4:0]  op,
  output logic [63:0] result
);

  logic is_word;
  logic [3:0] base_op;
  logic [5:0] shamt;
  logic [63:0] shifter_in;
  logic [63:0] arith_res;
  logic [63:0] logic_res;
  logic [63:0] shift_res;
  logic [63:0] raw_result;

  assign is_word = op[4];
  assign base_op = op[3:0];

  assign shamt = is_word ? {1'b0, b[4:0]} : b[5:0];
  assign shifter_in = is_word ? (base_op[1] ? {{32{a[31]}}, a[31:0]} : {32'd0, a[31:0]}) : a;

  // Arithmetic unit
  always_comb begin
    case (base_op[1:0])
      2'b00: arith_res = a + b;
      2'b01: arith_res = a - b;
      2'b10: arith_res = ($signed(a) < $signed(b)) ? 64'd1 : 64'd0;
      2'b11: arith_res = (a < b) ? 64'd1 : 64'd0;
    endcase
  end

  // Logic unit
  always_comb begin
    if (base_op[1]) begin
      logic_res = a ^ b;
    end else if (base_op[0]) begin
      logic_res = a | b;
    end else begin
      logic_res = a & b;
    end
  end

  // Shifter unit
  always_comb begin
    if (base_op[1]) begin
      shift_res = $signed(shifter_in) >>> shamt;
    end else if (base_op[0]) begin
      shift_res = shifter_in >> shamt;
    end else begin
      shift_res = shifter_in << shamt;
    end
  end

  // Top-level category multiplexer
  always_comb begin
    case (base_op[3:2])
      2'b00: raw_result = arith_res;
      2'b01: raw_result = logic_res;
      2'b10: raw_result = shift_res;
      2'b11: raw_result = 64'd0;
    endcase

    result = is_word ? {{32{raw_result[31]}}, raw_result[31:0]} : raw_result;
  end

`ifdef FORMAL
  // SVA arithmetic/logic invariants
  a_add: assert property (op == 5'b00000 |-> result == a + b);
  a_sub: assert property (op == 5'b00001 |-> result == a - b);
  a_and: assert property (op == 5'b00100 |-> result == (a & b));
  a_or:  assert property (op == 5'b00101 |-> result == (a | b));
  a_xor: assert property (op == 5'b00110 |-> result == (a ^ b));
`endif

endmodule
