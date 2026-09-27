// Expressive, human-readable specification of APLIC with TileLink TL-UH.

module APLIC_spec (
  input  logic        aplic_a_valid,
  input  logic [2:0]  aplic_a_opcode,
  input  logic [2:0]  aplic_a_param,
  input  logic [2:0]  aplic_a_size,
  input  logic [3:0]  aplic_a_source,
  input  logic [31:0] aplic_a_address,
  input  logic [7:0]  aplic_a_mask,
  input  logic [63:0] aplic_a_data,
  input  logic        aplic_d_ready,
  input  logic [15:0] irq_src,
  output logic        aplic_a_ready,
  output logic        aplic_d_valid,
  output logic [2:0]  aplic_d_opcode,
  output logic [1:0]  aplic_d_param,
  output logic [2:0]  aplic_d_size,
  output logic [3:0]  aplic_d_source,
  output logic [3:0]  aplic_d_sink,
  output logic [63:0] aplic_d_data,
  output logic        aplic_d_denied,
  output logic        meip_out,
  output logic        seip_out,
  input  logic        clock,
  input  logic        reset
);

  logic [31:0] domaincfg_q;
  logic [15:0] ip_q;
  logic [15:0] ie_q;
  logic        resp_valid_q;

  wire not_resp_wait = ~resp_valid_q;
  wire aplic_req_fire = aplic_a_valid & not_resp_wait;
  wire aplic_is_write = ~aplic_a_opcode[2];

  wire not_a4 = ~aplic_a_address[4];
  wire not_a5 = ~aplic_a_address[5];
  wire sel_domaincfg = not_a4 & not_a5;
  wire sel_setip     = aplic_a_address[4] & not_a5;
  wire sel_setie     = aplic_a_address[5] & not_a4;

  wire fire_wr = aplic_req_fire & aplic_is_write;
  wire wr_domaincfg = fire_wr & sel_domaincfg;
  wire wr_setip     = fire_wr & sel_setip;
  wire wr_setie     = fire_wr & sel_setie;

  wire [15:0] ip_or = irq_src | aplic_a_data[15:0];

  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      domaincfg_q  <= 32'd0;
      ip_q         <= 16'd0;
      ie_q         <= 16'd0;
      resp_valid_q <= 1'b0;
    end else begin
      if (wr_domaincfg) domaincfg_q <= aplic_a_data[31:0];
      ip_q[15:1]   <= ip_or[15:1];
      if (wr_setie)     ie_q        <= aplic_a_data[15:0];
      resp_valid_q <= aplic_req_fire;
    end
  end

  wire [15:0] active_irq = ip_q & ie_q;
  wire any_active_irq = |active_irq[15:1];

  assign meip_out = any_active_irq & domaincfg_q[8];
  assign seip_out = 1'b0;

  assign aplic_a_ready  = 1'b1;
  assign aplic_d_valid  = resp_valid_q;
  assign aplic_d_opcode = 3'b000;
  assign aplic_d_param  = 2'b00;
  assign aplic_d_size   = 3'b000;
  assign aplic_d_source = 4'b0000;
  assign aplic_d_sink   = 4'b0000;
  assign aplic_d_denied = 1'b0;

  wire [15:0] aplic_rdata = sel_setie ? ie_q : ip_q;
  assign aplic_d_data = {48'd0, aplic_rdata};

`ifdef FORMAL
  // SVA assertions
  a_ready_high: assert property (
    aplic_a_ready == 1'b1
  );

  a_denied_low: assert property (
    aplic_d_denied == 1'b0
  );
`endif

endmodule
