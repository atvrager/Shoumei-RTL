// Expressive, human-readable specification of N-to-2^N one-hot decoder.

module Decoder_spec #(
  parameter int IN_WIDTH = 4,
  parameter int OUT_WIDTH = 1 << IN_WIDTH
) (
  input  logic [IN_WIDTH-1:0]  in,
  output logic [OUT_WIDTH-1:0] out
);

  always_comb begin
    for (int i = 0; i < OUT_WIDTH; i++) begin
      out[i] = (in == i[IN_WIDTH-1:0]);
    end
  end

`ifdef FORMAL
  always_comb begin
    assert ($onehot(out));
    assert (out[in] == 1'b1);
  end
`endif

endmodule
