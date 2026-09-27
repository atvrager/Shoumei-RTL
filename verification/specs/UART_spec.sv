// Expressive, human-readable specification of 8-N-1 UART peripheral with TileLink TL-UH.

module UART_spec (
  input  logic        uart_a_valid,
  input  logic [2:0]  uart_a_opcode,
  input  logic [2:0]  uart_a_param,
  input  logic [2:0]  uart_a_size,
  input  logic [3:0]  uart_a_source,
  input  logic [31:0] uart_a_address,
  input  logic [7:0]  uart_a_mask,
  input  logic [63:0] uart_a_data,
  input  logic        uart_d_ready,
  input  logic        uart_rx,
  output logic        uart_a_ready,
  output logic        uart_d_valid,
  output logic [2:0]  uart_d_opcode,
  output logic [1:0]  uart_d_param,
  output logic [2:0]  uart_d_size,
  output logic [3:0]  uart_d_source,
  output logic [3:0]  uart_d_sink,
  output logic [63:0] uart_d_data,
  output logic        uart_d_denied,
  output logic        uart_tx,
  output logic        uart_irq,
  input  logic        clock,
  input  logic        reset
);

  logic [7:0]  tx_buf_q;
  logic        rx_buf0_q;
  logic        tx_busy_q;
  logic        rx_ready_q;
  logic        tx_irq_en_q;
  logic        rx_irq_en_q;
  logic        resp_valid_q;

  wire not_resp_wait = ~resp_valid_q;
  wire uart_req_fire = uart_a_valid & not_resp_wait;
  wire uart_is_write = ~uart_a_opcode[2];
  wire uart_is_read  = ~uart_is_write;

  wire not_a2 = ~uart_a_address[2];
  wire not_a3 = ~uart_a_address[3];
  wire sel_data   = not_a3 & not_a2;
  wire sel_status = not_a3 & uart_a_address[2];
  wire sel_ctrl   = uart_a_address[3] & not_a2;

  wire fire_wr = uart_req_fire & uart_is_write;
  wire wr_data = fire_wr & sel_data;
  wire wr_ctrl = fire_wr & sel_ctrl;

  wire fire_rd = uart_req_fire & uart_is_read;
  wire rd_data = fire_rd & sel_data;

  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      tx_buf_q     <= 8'h00;
      rx_buf0_q    <= 1'b0;
      tx_busy_q    <= 1'b0;
      rx_ready_q   <= 1'b0;
      tx_irq_en_q  <= 1'b0;
      rx_irq_en_q  <= 1'b0;
      resp_valid_q <= 1'b0;
    end else begin
      if (wr_data) begin
        tx_buf_q  <= uart_a_data[7:0];
        tx_busy_q <= 1'b1;
      end
      rx_buf0_q <= uart_rx;
      rx_ready_q <= rx_ready_q & ~rd_data;
      if (wr_ctrl) begin
        tx_irq_en_q <= uart_a_data[0];
        rx_irq_en_q <= uart_a_data[1];
      end
      resp_valid_q <= uart_req_fire;
    end
  end

  wire not_tx_busy = ~tx_busy_q;
  assign uart_tx  = tx_busy_q ? tx_buf_q[0] : 1'b1;
  assign uart_irq = (not_tx_busy & tx_irq_en_q) | (rx_ready_q & rx_irq_en_q);

  assign uart_a_ready  = 1'b1;
  assign uart_d_valid  = resp_valid_q;
  assign uart_d_opcode = 3'b000;
  assign uart_d_param  = 2'b00;
  assign uart_d_size   = 3'b000;
  assign uart_d_source = 4'b0000;
  assign uart_d_sink   = 4'b0000;
  assign uart_d_denied = 1'b0;

  wire [7:0] rdata = sel_status ? {5'd0, rx_ready_q, not_tx_busy, tx_busy_q} : {7'd0, rx_buf0_q};
  assign uart_d_data = {56'd0, rdata};

`ifdef FORMAL
  // SVA assertions
  a_ready_high: assert property (
    uart_a_ready == 1'b1
  );

  a_denied_low: assert property (
    uart_d_denied == 1'b0
  );
`endif

endmodule
