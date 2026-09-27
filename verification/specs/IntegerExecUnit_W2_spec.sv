// Expressive, human-readable specification of 32-bit Dual-Issue Integer Execution Unit.
//
// Opcode encoding (mirrors ALU32, 4 bits):
//   [3]=0,[2]=0 -> arith  : [1]=0,[0]=1 ADD, [0]=0 SUB ; [1]=1,[0]=1 SLTU, [0]=0 SLT
//   [3]=0,[2]=1 -> logic  : [1]=1 XOR ; [0]=1 OR ; [0]=0 AND
//   [3]=1,[2]=1 -> shift  : [1]=1 SRA ; [0]=1 SRL ; [0]=0 SLL   (shamt = b[4:0])
//   [3]=1,[2]=0 -> zero

module IntegerExecUnit_W2_spec (
  input  logic [31:0] a0,
  input  logic [31:0] b0,
  input  logic [3:0]  opcode0,
  input  logic [5:0]  dest_tag0,
  input  logic [31:0] a1,
  input  logic [31:0] b1,
  input  logic [3:0]  opcode1,
  input  logic [5:0]  dest_tag1,
  output logic [31:0] result0,
  output logic [5:0]  tag_out0,
  output logic [31:0] result1,
  output logic [5:0]  tag_out1
);

  function automatic [31:0] alu32 (input [31:0] a, input [31:0] b, input [3:0] op);
    logic [31:0] arith;
    logic [31:0] logic_r;
    logic [31:0] shift_r;
    arith   = op[1] ? (op[0] ? {31'b0, a < b} : {31'b0, $signed(a) < $signed(b)})
                    : (op[0] ? a - b : a + b);
    logic_r = op[1] ? (a ^ b) : (op[0] ? (a | b) : (a & b));
    shift_r = op[1] ? ($signed(a) >>> b[4:0])
                    : (op[0] ? (a >> b[4:0]) : (a << b[4:0]));
    alu32   = op[3] ? (op[2] ? shift_r : 32'b0)
                    : (op[2] ? logic_r : arith);
  endfunction

  assign result0  = alu32(a0, b0, opcode0);
  assign tag_out0 = dest_tag0;
  assign result1  = alu32(a1, b1, opcode1);
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
