// Expressive, human-readable specification of Tree-PLRU replacement policy.

module PLRU_spec #(
  parameter int WAYS = 4
) (
  input  logic            upd_en,
  input  logic [WAYS-1:0] upd_way_oh,
  output logic [WAYS-1:0] victim_oh,
  input  logic            clock,
  input  logic            reset
);

  localparam int BITS = WAYS - 1;
  logic [BITS-1:0] tree_bits;

  // Descend tree to compute victim_oh
  // Node i selects child 2i+1 if tree_bits[i] == 0, else child 2i+2.
  logic [2*WAYS-2:0] sel;

  assign sel[0] = 1'b1;
  genvar gi;
  generate
    for (gi = 0; gi < BITS; gi++) begin : gen_sel
      assign sel[2*gi + 1] = sel[gi] & ~tree_bits[gi];
      assign sel[2*gi + 2] = sel[gi] &  tree_bits[gi];
    end
  endgenerate

  for (genvar gw = 0; gw < WAYS; gw++) begin : gen_victim
    assign victim_oh[gw] = sel[BITS + gw];
  end

  // Combinational calculation of updated bits
  logic [BITS-1:0] in_right;
  always_comb begin
    in_right = '0;
    for (int i = 0; i < BITS; i++) begin
      for (int w = 0; w < WAYS; w++) begin
        if (upd_way_oh[w]) begin
          for (int curr = BITS + w; curr > 0; curr = (curr - 1) / 2) begin
            if (curr == 2*i + 2) begin
              in_right[i] = 1'b1;
            end
          end
        end
      end
    end
  end

  // Update tree bits on posedge clock
  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      tree_bits <= '0;
    end else if (upd_en) begin
      tree_bits <= in_right;
    end
  end

`ifdef FORMAL
  // SVA assertions
  a_reset_clears: assert property (@(posedge clock) disable iff (1'b0)
    reset |=> (victim_oh[0] == 1'b1)
  );
`endif

endmodule
