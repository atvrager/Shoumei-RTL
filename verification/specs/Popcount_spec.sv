// Parameterized population count specification (counts number of set bits)

module Popcount_spec #(
  parameter int WIDTH = 8,
  parameter int OUT_WIDTH = 4
) (
  input  logic [WIDTH-1:0]     in,
  output logic [OUT_WIDTH-1:0] count
);

  always_comb begin
    count = '0;
    for (int i = 0; i < WIDTH; i++) begin
      count = count + OUT_WIDTH'(in[i]);
    end
  end

endmodule
