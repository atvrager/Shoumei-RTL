// Expressive, human-readable specification of ACLINT with TileLink TL-UH.

module ACLINT_spec (
  input  logic        aclint_a_valid,
  input  logic [2:0]  aclint_a_opcode,
  input  logic [2:0]  aclint_a_param,
  input  logic [2:0]  aclint_a_size,
  input  logic [3:0]  aclint_a_source,
  input  logic [31:0] aclint_a_address,
  input  logic [7:0]  aclint_a_mask,
  input  logic [63:0] aclint_a_data,
  input  logic        aclint_d_ready,
  output logic        aclint_a_ready,
  output logic        aclint_d_valid,
  output logic [2:0]  aclint_d_opcode,
  output logic [1:0]  aclint_d_param,
  output logic [2:0]  aclint_d_size,
  output logic [3:0]  aclint_d_source,
  output logic [3:0]  aclint_d_sink,
  output logic [63:0] aclint_d_data,
  output logic        aclint_d_denied,
  output logic        mtip_out,
  output logic        msip_out,
  output logic        ssip_out,
  input  logic        clock,
  input  logic        reset
);

  logic [63:0] mtime_q;
  logic [63:0] mtimecmp_q;
  logic [31:0] msip_q;
  logic [31:0] ssip_q;
  logic        resp_valid_q;

  wire not_resp_wait = ~resp_valid_q;
  wire tl_req_fire = aclint_a_valid & not_resp_wait;
  wire tl_is_write = ~aclint_a_opcode[2];

  wire not_a15 = ~aclint_a_address[15];
  wire not_a14 = ~aclint_a_address[14];
  wire sel_mtimecmp = not_a15 & not_a14;
  wire mtime_match_pre = aclint_a_address[14] & aclint_a_address[13];
  wire sel_mtime    = mtime_match_pre & aclint_a_address[12];
  wire sel_msip     = not_a15 & aclint_a_address[14];
  wire sel_ssip     = aclint_a_address[15] & not_a14;

  wire req_fire_wr = tl_req_fire & tl_is_write;
  wire wr_mtimecmp = req_fire_wr & sel_mtimecmp;
  wire wr_mtime    = req_fire_wr & sel_mtime;
  wire wr_msip     = req_fire_wr & sel_msip;
  wire wr_ssip     = req_fire_wr & sel_ssip;

  wire [63:0] mtime_inc = mtime_q + 64'd1;

  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      mtime_q      <= 64'd0;
      mtimecmp_q   <= 64'd0;
      msip_q       <= 32'd0;
      ssip_q       <= 32'd0;
      resp_valid_q <= 1'b0;
    end else begin
      mtime_q      <= wr_mtime ? aclint_a_data : mtime_inc;
      if (wr_mtimecmp) mtimecmp_q <= aclint_a_data;
      if (wr_msip)     msip_q     <= aclint_a_data[31:0];
      if (wr_ssip)     ssip_q     <= aclint_a_data[31:0];
      resp_valid_q <= tl_req_fire;
    end
  end

  // Hardware implementation bitwise comparison: cmp_c[63] = mtime[62] & ~mtimecmp[62] & ... & mtime[0] & ~mtimecmp[0]
  wire [63:0] cmp_c;
  assign cmp_c[0] = 1'b1;
  assign cmp_c[63:1] = mtime_q[62:0] & ~mtimecmp_q[62:0];

  assign mtip_out = cmp_c[63];
  assign msip_out = msip_q[0];
  assign ssip_out = ssip_q[0];

  assign aclint_a_ready  = 1'b1;
  assign aclint_d_valid  = resp_valid_q;
  assign aclint_d_opcode = 3'b000;
  assign aclint_d_param  = 2'b00;
  assign aclint_d_size   = 3'b000;
  assign aclint_d_source = 4'b0000;
  assign aclint_d_sink   = 4'b0000;
  assign aclint_d_denied = 1'b0;
  assign aclint_d_data   = sel_mtimecmp ? mtimecmp_q : mtime_q;

`ifdef FORMAL
  // SVA assertions
  a_ready_high: assert property (
    aclint_a_ready == 1'b1
  );

  a_denied_low: assert property (
    aclint_d_denied == 1'b0
  );
`endif

endmodule
