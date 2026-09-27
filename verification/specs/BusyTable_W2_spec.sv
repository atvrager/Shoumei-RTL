// Expressive, human-readable specification of 64-entry Dual-Port Busy Bit Table.

module BusyTable_W2_spec (
  input  logic        reset,
  input  logic [7:0]  flush_groups,
  input  logic [5:0]  set_tag_0,
  input  logic [5:0]  set_tag_1,
  input  logic [1:0]  set_en,
  input  logic [5:0]  clear_tag_0,
  input  logic [5:0]  clear_tag_1,
  input  logic [1:0]  clear_en,
  input  logic [5:0]  read1_tag_0,
  input  logic [5:0]  read2_tag_0,
  input  logic [5:0]  read1_tag_1,
  input  logic [5:0]  read2_tag_1,
  input  logic [1:0]  use_imm,
  output logic [1:0]  src1_ready,
  output logic [1:0]  src2_ready,
  output logic        src2_ready0_reg,
  output logic        src2_ready1_reg,
  output logic        busy_raw_s1_hit,
  output logic        busy_raw_s2_hit,
  input  logic        clock
);

  logic [63:0] busy_table;
  logic [63:0] busy_next;

  // Next-state vector: flush beats set, set beats clear, otherwise hold.
  always_comb begin
    for (int i = 0; i < 64; i++) begin
      busy_next[i] = flush_groups[i / 8]                              ? 1'b0 :
                     ((set_en[0] && (set_tag_0 == 6'(i))) ||
                      (set_en[1] && (set_tag_1 == 6'(i))))            ? 1'b1 :
                     ((clear_en[0] && (clear_tag_0 == 6'(i))) ||
                      (clear_en[1] && (clear_tag_1 == 6'(i))))        ? 1'b0 :
                                                                      busy_table[i];
    end
  end

  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      busy_table <= 64'b0;
    end else begin
      busy_table <= busy_next;
    end
  end

  // Read ports
  wire raw_s1 = set_en[0] && (set_tag_0 == read1_tag_1);
  wire raw_s2 = set_en[0] && (set_tag_0 == read2_tag_1);

  assign busy_raw_s1_hit = raw_s1;
  assign busy_raw_s2_hit = raw_s2;

  assign src1_ready[0]   = ~busy_table[read1_tag_0];
  assign src2_ready0_reg = ~busy_table[read2_tag_0];
  assign src2_ready[0]   = use_imm[0] | src2_ready0_reg;

  assign src1_ready[1]   = ~busy_table[read1_tag_1] & ~raw_s1;
  assign src2_ready1_reg = ~busy_table[read2_tag_1] & ~raw_s2;
  assign src2_ready[1]   = use_imm[1] | src2_ready1_reg;

`ifdef FORMAL
  // SVA assertions
  a_imm0_ready: assert property (
    use_imm[0] |-> (src2_ready[0] == 1'b1)
  );

  a_imm1_ready: assert property (
    use_imm[1] |-> (src2_ready[1] == 1'b1)
  );
`endif

endmodule
