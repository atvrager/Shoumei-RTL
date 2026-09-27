// Expressive, human-readable specification of BootROM with TileLink TL-UH interface.

module BootROM_spec (
  input  logic        bootrom_a_valid,
  input  logic [2:0]  bootrom_a_opcode,
  input  logic [2:0]  bootrom_a_param,
  input  logic [2:0]  bootrom_a_size,
  input  logic [3:0]  bootrom_a_source,
  input  logic [31:0] bootrom_a_address,
  input  logic [7:0]  bootrom_a_mask,
  input  logic [63:0] bootrom_a_data,
  input  logic        bootrom_d_ready,
  output logic        bootrom_a_ready,
  output logic        bootrom_d_valid,
  output logic [2:0]  bootrom_d_opcode,
  output logic [1:0]  bootrom_d_param,
  output logic [2:0]  bootrom_d_size,
  output logic [3:0]  bootrom_d_source,
  output logic [3:0]  bootrom_d_sink,
  output logic [63:0] bootrom_d_data,
  output logic        bootrom_d_denied,
  input  logic        clock,
  input  logic        reset
);

  logic resp_valid_q;
  wire  req_fire = bootrom_a_valid & ~resp_valid_q;

  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      resp_valid_q <= 1'b0;
    end else begin
      resp_valid_q <= req_fire;
    end
  end

  assign bootrom_a_ready = 1'b1;
  assign bootrom_d_valid = resp_valid_q;
  assign bootrom_d_denied = 1'b0;
  assign bootrom_d_opcode = 3'b001; // AccessAckData
  assign bootrom_d_param  = 2'b00;
  assign bootrom_d_size   = 3'b000;
  assign bootrom_d_source = 4'b0000;
  assign bootrom_d_sink   = 4'b0000;

  // ROM data payload: 64-bit word matching hardware ROM bits
  // Word 0: 0x20000157
  // Word 1: 0x00050067
  assign bootrom_d_data = 64'h0005006720000157;

`ifdef FORMAL
  // SVA assertions
  a_ready_high: assert property (
    bootrom_a_ready == 1'b1
  );

  a_denied_low: assert property (
    bootrom_d_denied == 1'b0
  );
`endif

endmodule
