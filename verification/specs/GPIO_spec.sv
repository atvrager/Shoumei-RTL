// Expressive, human-readable specification of 8-bit GPIO peripheral with TileLink TL-UH.

module GPIO_spec (
  input  logic        gpio_a_valid,
  input  logic [2:0]  gpio_a_opcode,
  input  logic [2:0]  gpio_a_param,
  input  logic [2:0]  gpio_a_size,
  input  logic [3:0]  gpio_a_source,
  input  logic [31:0] gpio_a_address,
  input  logic [7:0]  gpio_a_mask,
  input  logic [63:0] gpio_a_data,
  input  logic        gpio_d_ready,
  input  logic [7:0]  gpio_i,
  output logic        gpio_a_ready,
  output logic        gpio_d_valid,
  output logic [2:0]  gpio_d_opcode,
  output logic [1:0]  gpio_d_param,
  output logic [2:0]  gpio_d_size,
  output logic [3:0]  gpio_d_source,
  output logic [3:0]  gpio_d_sink,
  output logic [63:0] gpio_d_data,
  output logic        gpio_d_denied,
  output logic        gpio_irq,
  output logic [7:0]  gpio_o,
  output logic [7:0]  gpio_oen,
  input  logic        clock,
  input  logic        reset
);

  logic [7:0] data_out_q;
  logic [7:0] dir_q;
  logic [7:0] int_en_q;
  logic       resp_valid_q;

  wire not_resp_wait = ~resp_valid_q;
  wire gpio_req_fire = gpio_a_valid & not_resp_wait;
  wire gpio_is_write = ~gpio_a_opcode[2];

  wire not_a2 = ~gpio_a_address[2];
  wire not_a3 = ~gpio_a_address[3];
  wire sel_din  = not_a3 & not_a2;
  wire sel_dout = not_a3 & gpio_a_address[2];
  wire sel_dir  = gpio_a_address[3] & not_a2;
  wire sel_ie   = gpio_a_address[3] & gpio_a_address[2];

  wire fire_wr = gpio_req_fire & gpio_is_write;
  wire wr_dout = fire_wr & sel_dout;
  wire wr_dir  = fire_wr & sel_dir;
  wire wr_ie   = fire_wr & sel_ie;

  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      data_out_q   <= 8'h00;
      dir_q        <= 8'h00;
      int_en_q     <= 8'h00;
      resp_valid_q <= 1'b0;
    end else begin
      if (wr_dout) data_out_q <= gpio_a_data[7:0];
      if (wr_dir)  dir_q      <= gpio_a_data[7:0];
      if (wr_ie)   int_en_q   <= gpio_a_data[7:0];
      resp_valid_q <= gpio_req_fire;
    end
  end

  assign gpio_o   = data_out_q;
  assign gpio_oen = dir_q;
  assign gpio_irq = |(gpio_i & int_en_q);

  assign gpio_a_ready  = 1'b1;
  assign gpio_d_valid  = resp_valid_q;
  assign gpio_d_opcode = 3'b000;
  assign gpio_d_param  = 2'b00;
  assign gpio_d_size   = 3'b000;
  assign gpio_d_source = 4'b0000;
  assign gpio_d_sink   = 4'b0000;
  assign gpio_d_denied = 1'b0;

  logic [7:0] rdata;
  always_comb begin
    if (sel_dout)      rdata = data_out_q;
    else if (sel_dir)  rdata = dir_q;
    else if (sel_ie)   rdata = int_en_q;
    else               rdata = gpio_i;
  end

  assign gpio_d_data = {56'd0, rdata};

`ifdef FORMAL
  // SVA assertions
  a_ready_high: assert property (
    gpio_a_ready == 1'b1
  );

  a_denied_low: assert property (
    gpio_d_denied == 1'b0
  );
`endif

endmodule
