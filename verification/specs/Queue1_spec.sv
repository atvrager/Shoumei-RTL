// Expressive, human-readable specification of 1-entry decoupled FIFO.
module Queue1_spec (
  input  logic [7:0] enq_data,
  input  logic       enq_valid,
  input  logic       deq_ready,
  output logic       enq_ready,
  output logic [7:0] data_reg,
  output logic       valid,
  input  logic       clock,
  input  logic       reset
);

  typedef enum logic {
    EMPTY = 1'b0,
    FULL  = 1'b1
  } state_e;

  state_e state_q, state_d;
  logic [7:0] storage_q, storage_d;

  assign enq_ready = (state_q == EMPTY);
  assign valid     = (state_q == FULL);
  assign data_reg  = storage_q;

  wire push = enq_valid && enq_ready;
  wire pop  = valid && deq_ready;

  always_comb begin
    state_d   = state_q;
    storage_d = storage_q;

    if (push) begin
      storage_d = enq_data;
      state_d   = FULL;
    end else if (pop) begin
      state_d   = EMPTY;
    end
  end

  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      state_q   <= EMPTY;
      storage_q <= '0;
    end else begin
      state_q   <= state_d;
      storage_q <= storage_d;
    end
  end

`ifdef FORMAL
  // ---- SVA Properties ----
  default clocking @(posedge clock); endclocking
  default disable iff (reset);

  a_handshake_stable: assert property (valid && !deq_ready |=> valid && $stable(data_reg));
  a_enq_ready_contract: assert property (enq_ready == !valid);
  a_push_effect: assert property (!valid && enq_valid |=> valid && data_reg == $past(enq_data));
  a_pop_effect: assert property (valid && deq_ready && !enq_valid |=> !valid);
`endif

endmodule
