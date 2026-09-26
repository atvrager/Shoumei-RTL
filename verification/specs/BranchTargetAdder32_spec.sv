// Expressive, human-readable specification of 32-bit Branch Target Adder.

module BranchTargetAdder32_spec (
  input  logic [31:0] pc,
  input  logic [24:0] instr,
  input  logic        is_jal,
  output logic [31:0] target
);

  logic [30:0] b_imm;
  logic [30:0] j_imm;
  logic [30:0] imm;

  assign b_imm = {{20{instr[24]}}, instr[0], instr[23:18], instr[4:1]};
  assign j_imm = {{12{instr[24]}}, instr[12:5], instr[13], instr[23:14]};
  assign imm = is_jal ? j_imm : b_imm;

  assign target = {pc[31:1] + imm, pc[0]};

`ifdef FORMAL
  // SVA arithmetic invariants
  always_comb begin
    assert (target[0] == pc[0]);
    if (instr == 25'd0) assert (target == pc);
  end
`endif

endmodule
