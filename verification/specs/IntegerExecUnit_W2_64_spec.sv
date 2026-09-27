// Expressive, human-readable specification of 64-bit Dual-Issue Integer Execution Unit.
//
// Opcode encoding (mirrors ALU64, 5 bits):
//   [3:0] base op, [4] = is_word (32-bit word op, result sign-extended to 64 bits)
//   [3]=0,[2]=0 -> arith  : [1]=0,[0]=1 ADD, [0]=0 SUB ; [1]=1,[0]=1 SLTU, [0]=0 SLT
//   [3]=0,[2]=1 -> logic  : [1]=1 XOR ; [0]=1 OR ; [0]=0 AND
//   [3]=1,[2]=1 -> shift  : [1]=1 SRA ; [0]=1 SRL ; [0]=0 SLL
//   [3]=1,[2]=0 -> zero
//   shift amount = {is_word ? 1'b0 : b[5], b[4:0]}
//   shift operand = is_word ? {[1] ? {32{a[31]}} : 32'b0, a[31:0]} : a

module IntegerExecUnit_W2_64_spec (
  input  logic [63:0] a0,
  input  logic [63:0] b0,
  input  logic [4:0]  opcode0,
  input  logic [5:0]  dest_tag0,
  input  logic [63:0] a1,
  input  logic [63:0] b1,
  input  logic [4:0]  opcode1,
  input  logic [5:0]  dest_tag1,
  output logic [63:0] result0,
  output logic [5:0]  tag_out0,
  output logic [63:0] result1,
  output logic [5:0]  tag_out1
);

  function automatic [63:0] alu64 (input [63:0] a, input [63:0] b, input [4:0] op);
    logic        is_word;
    logic [5:0]  shamt;
    logic [63:0] sh_in;
    logic [63:0] arith;
    logic [63:0] logic_r;
    logic [63:0] shift_r;
    logic [63:0] raw;

    is_word = op[4];
    shamt   = {is_word ? 1'b0 : b[5], b[4:0]};
    logic [31:0] pad;
    pad     = op[1] ? {32{a[31]}} : 32'b0;
    sh_in   = is_word ? {pad, a[31:0]} : a;

    arith   = op[1] ? (op[0] ? {63'b0, a < b} : {63'b0, $signed(a) < $signed(b)})
                    : (op[0] ? a - b : a + b);
    logic_r = op[1] ? (a ^ b) : (op[0] ? (a | b) : (a & b));
    shift_r = op[1] ? ($signed(sh_in) >>> shamt)
                    : (op[0] ? (sh_in >> shamt) : (sh_in << shamt));
    raw     = op[3] ? (op[2] ? shift_r : 64'b0)
                    : (op[2] ? logic_r : arith);

    logic [63:0] ext;
    ext     = {32{raw[31]}};
    alu64   = is_word ? {ext[31:0], raw[31:0]} : raw;
  endfunction

  assign result0  = alu64(a0, b0, opcode0);
  assign tag_out0 = dest_tag0;
  assign result1  = alu64(a1, b1, opcode1);
  assign tag_out1 = dest_tag1;

`ifdef FORMAL
  // SVA assertions
  a_tag0_passthru: assert property (
    tag_out0 == dest_tag0
  );

  a_tag1_passthru: assert property (
    tag_out1 == dest_tag1
  );
`endif

endmodule
