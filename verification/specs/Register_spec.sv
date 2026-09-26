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

  // The subject of this claim is reset itself, so it must not inherit
  // `disable iff (reset)`: that would make the property vacuously true.
  a_reset_clears: assert property (@(posedge clock) disable iff (1'b0) reset |=> (q == '0));
  a_data_latch:   assert property (!reset |=> (q == $past(d)));
`endif

endmodule
