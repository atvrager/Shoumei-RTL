// SystemVerilog reference specification: Parameterized PC Incrementer
// Advances 32-bit program counter by constant INC bytes (e.g. 4 or 8)

module PCIncrementer_spec #(
  parameter int INC = 4
) (
  input  logic [31:0] pc,
  output logic [31:0] pc_next
);

  assign pc_next = pc + INC[31:0];

endmodule
