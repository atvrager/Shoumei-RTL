// Parameterized one-hot to binary priority encoder specification

module OneHotEncoder_spec #(
  parameter int WIDTH = 64,
  parameter int OUT_WIDTH = 6
) (
  input  logic [WIDTH-1:0]     in,
  output logic [OUT_WIDTH-1:0] out
);

  always_comb begin
    out = '0;
    for (int i = 0; i < WIDTH; i++) begin
      if (in[i]) begin
        out = out | OUT_WIDTH'(i);
      end
    end
  end

endmodule
