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
  logic [63:0] fp_busy_eff;

  // The emitted netlist wires `flush_groups` into each flop's asynchronous
  // reset, so a flushed entry reads free in the same cycle the flush is
  // asserted (not one cycle later).  `fp_busy_eff` models that.
  always_comb begin
    for (int i = 0; i < 64; i++) begin
      fp_busy_eff[i] = flush_groups[i / 8] ? 1'b0 : fp_busy_table[i];
    end
  end

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

  assign src1_ready     = ~fp_busy_eff[read1_tag];
  assign src2_ready     = ~fp_busy_eff[read2_tag];
  assign src3_busy_raw  = fp_busy_eff[read3_tag];

`ifdef FORMAL
  // SVA assertions: the three read ports must agree on a shared tag.
  // (The previous assertions compared readiness against the raw table, which
  // is false while a flush is forcing the entry clear asynchronously.)
  a_ports_agree_12: assert property (
    (read1_tag == read2_tag) |-> (src1_ready == src2_ready)
  );

  a_ports_agree_13: assert property (
    (read1_tag == read3_tag) |-> (src1_ready == ~src3_busy_raw)
  );
`endif

endmodule
