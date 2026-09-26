// Parameterized queue pointer specification with synchronous load

module QueuePointerLoadable_spec #(
  parameter int WIDTH = 3
) (
  input  logic             en,
  input  logic             load_en,
  input  logic [WIDTH-1:0] load_value,
  output logic [WIDTH-1:0] count,
  input  logic             clock,
  input  logic             reset
);

  logic [WIDTH-1:0] ptr_q;

  assign count = ptr_q;

  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      ptr_q <= '0;
    end else if (load_en) begin
      ptr_q <= load_value;
    end else if (en) begin
      ptr_q <= ptr_q + WIDTH'(1);
    end
  end

endmodule
