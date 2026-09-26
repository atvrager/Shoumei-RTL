// Expressive, human-readable specification of N-bit register.

module Register_spec #(
  parameter int WIDTH = 32
) (
  input  logic [WIDTH-1:0] d,
  output logic [WIDTH-1:0] q,
  input  logic             clock,
  input  logic             reset
);

  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      q <= '0;
    end else begin
      q <= d;
    end
  end

`ifdef FORMAL
  default clocking @(posedge clock); endclocking
  default disable iff (reset);

  a_reset_clears: assert property (reset |=> (q == '0));
  a_data_latch:   assert property (!reset |=> (q == $past(d)));
`endif

endmodule
