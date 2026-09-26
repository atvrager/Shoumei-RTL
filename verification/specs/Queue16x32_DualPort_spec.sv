// Parameterized 16-entry x 32-bit dual-write, dual-read register file.
// Write port 1 wins over port 0 when both target the same entry.

module Queue16x32_DualPort_spec (
  input  logic [1:0]  wr_en,
  input  logic [3:0]  wr_idx_0,
  input  logic [31:0] wr_data_0,
  input  logic [3:0]  wr_idx_1,
  input  logic [31:0] wr_data_1,
  input  logic [3:0]  rd_idx_0,
  input  logic [3:0]  rd_idx_1,
  output logic [31:0] rd_data_0,
  output logic [31:0] rd_data_1,
  input  logic        clock,
  input  logic        reset
);

  localparam int DEPTH = 16;
  localparam int WIDTH = 32;

  logic [WIDTH-1:0] mem [DEPTH];

  // Write decode: which entry each port drives, and the merged write data.
  logic [DEPTH-1:0] we0_hit, we1_hit, we;
  logic [WIDTH-1:0] wdata_sel [DEPTH];

  always_comb begin
    for (int i = 0; i < DEPTH; i++) begin
      we0_hit[i] = wr_en[0] && (wr_idx_0 == 4'(i));
      we1_hit[i] = wr_en[1] && (wr_idx_1 == 4'(i));
      we[i]      = we0_hit[i] || we1_hit[i];
      wdata_sel[i] = we1_hit[i] ? wr_data_1 : wr_data_0;
    end
  end

  assign rd_data_0 = mem[rd_idx_0];
  assign rd_data_1 = mem[rd_idx_1];

  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      for (int i = 0; i < DEPTH; i++) begin
        mem[i] <= '0;
      end
    end else begin
      for (int i = 0; i < DEPTH; i++) begin
        if (we[i]) begin
          mem[i] <= wdata_sel[i];
        end
      end
    end
  end

endmodule
