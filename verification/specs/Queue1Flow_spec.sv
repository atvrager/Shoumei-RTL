// Parameterized single-entry flow queue specification
// Supports flow-through bypass when queue is empty and downstream is ready.

module Queue1Flow_spec #(
  parameter int WIDTH = 32
) (
  input  logic [WIDTH-1:0] enq_data,
  input  logic             enq_valid,
  input  logic             deq_ready,
  output logic             enq_ready,
  output logic [WIDTH-1:0] deq_data,
  output logic             deq_valid,
  input  logic             clock,
  input  logic             reset
);

  logic             valid_q;
  logic [WIDTH-1:0] data_q;

  logic not_valid;
  logic deq_fire;
  logic enq_fire;
  logic bypass_consumed;
  logic actual_enq;
  logic valid_hold;
  logic valid_next;
  logic [WIDTH-1:0] data_next;

  assign not_valid       = ~valid_q;
  assign deq_fire        = valid_q & deq_ready;
  assign enq_ready       = not_valid | deq_fire;
  assign enq_fire        = enq_valid & enq_ready;
  assign deq_valid       = valid_q | enq_valid;
  assign bypass_consumed = not_valid & enq_valid & deq_ready;
  assign actual_enq      = enq_fire & ~bypass_consumed;
  assign valid_hold      = valid_q & ~deq_fire;
  assign valid_next      = actual_enq | valid_hold;
  assign deq_data        = valid_q ? data_q : enq_data;
  assign data_next       = enq_fire ? enq_data : data_q;

  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      valid_q <= 1'b0;
      data_q  <= '0;
    end else begin
      valid_q <= valid_next;
      data_q  <= data_next;
    end
  end

endmodule
