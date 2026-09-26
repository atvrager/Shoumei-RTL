// Parameterized queue pointer specification with wrapping increment

module QueuePointer_spec #(
  parameter int WIDTH = 3
) (
  input  logic             en,
  output logic [WIDTH-1:0] count,
  input  logic             clock,
  input  logic             reset
);

  logic [WIDTH-1:0] ptr_q;

  assign count = ptr_q;

  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      ptr_q <= '0;
    end else if (en) begin
      ptr_q <= ptr_q + WIDTH'(1);
    end
  end

endmodule
