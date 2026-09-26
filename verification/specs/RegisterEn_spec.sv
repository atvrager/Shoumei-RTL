// Expressive, human-readable specification of N-bit clock-enabled register.

module RegisterEn_spec #(
  parameter int WIDTH = 32
) (
  input  logic [WIDTH-1:0] d,
  input  logic             en,
  output logic [WIDTH-1:0] q,
  input  logic             clock,
  input  logic             reset
);

  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      q <= '0;
    end else if (en) begin
      q <= d;
    end
  end

`ifdef FORMAL
  default clocking @(posedge clock); endclocking
  default disable iff (reset);

  a_reset_clears: assert property (reset |=> (q == '0));
  a_enable_latch: assert property (!reset && en |=> (q == $past(d)));
  a_stall_hold:   assert property (!reset && !en |=> (q == $past(q)));
`endif

endmodule
