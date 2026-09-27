// Expressive, human-readable specification of 64-entry Floating-Point Busy Bit Table.

module FPBusyTable_spec (
  input  logic        reset,
  input  logic [7:0]  flush_groups,
  input  logic [5:0]  set_tag,
  input  logic        set_en,
  input  logic [5:0]  clear_tag,
  input  logic        clear_en,
  input  logic [5:0]  read1_tag,
  input  logic [5:0]  read2_tag,
  input  logic [5:0]  read3_tag,
  output logic        src1_ready,
  output logic        src2_ready,
  output logic        src3_busy_raw,
  input  logic        clock
);

  logic [63:0] fp_busy_table;
  logic [63:0] fp_busy_next;

  // Next-state vector: flush beats set, set beats clear, otherwise hold.
  always_comb begin
    for (int i = 0; i < 64; i++) begin
      fp_busy_next[i] = flush_groups[i / 8]                 ? 1'b0 :
                        (set_en && (set_tag == 6'(i)))      ? 1'b1 :
                        (clear_en && (clear_tag == 6'(i)))  ? 1'b0 :
                                                              fp_busy_table[i];
    end
  end

  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      fp_busy_table <= 64'b0;
    end else begin
      fp_busy_table <= fp_busy_next;
    end
  end

  assign src1_ready     = ~fp_busy_table[read1_tag];
  assign src2_ready     = ~fp_busy_table[read2_tag];
  assign src3_busy_raw  = fp_busy_table[read3_tag];

`ifdef FORMAL
  // SVA assertions
  a_src1_inverted: assert property (
    src1_ready == ~fp_busy_table[read1_tag]
  );

  a_src2_inverted: assert property (
    src2_ready == ~fp_busy_table[read2_tag]
  );
`endif

endmodule
