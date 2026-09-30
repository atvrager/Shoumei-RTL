// Expressive, human-readable specification of 1-entry decoupled FIFO.
module Queue1_spec #(
  parameter int WIDTH = 8
) (
  input  logic [WIDTH-1:0] enq_data,
  input  logic             enq_valid,
  input  logic             deq_ready,
  output logic             enq_ready,
  output logic [WIDTH-1:0] data_reg,
  output logic             valid,
  input  logic             clock,
  input  logic             reset
);

  typedef enum logic {
    EMPTY = 1'b0,
    FULL  = 1'b1
  } state_e;

  state_e state_q, state_d;
  logic [WIDTH-1:0] storage_q, storage_d;

  assign enq_ready = (state_q == EMPTY);
  assign valid     = (state_q == FULL);
  assign data_reg  = storage_q;

  always_comb begin
    state_d   = state_q;
    storage_d = storage_q;

    case (state_q)
      EMPTY: begin
        if (enq_valid) begin
          state_d   = FULL;
          storage_d = enq_data;
        end
      end
      FULL: begin
        if (deq_ready) begin
          state_d = EMPTY;
        end
      end
      default: ;
    endcase
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
  // ---- SVA Properties: what this specification claims about itself ----
  // Checked against the Lean model of this module by `bazel build //generators:sva2lean`.
  // The netlist inherits them through the SEC theorem.
  default clocking @(posedge clock); endclocking
  default disable iff (reset);

  a_enq_ready_contract: assert property (enq_ready == !valid);
  a_handshake_stable:   assert property (valid && !deq_ready |=> valid && $stable(data_reg));
  a_push_effect:        assert property (!valid && enq_valid |=> valid && data_reg == $past(enq_data));
  a_pop_effect:         assert property (valid && deq_ready && !enq_valid |=> !valid);
`endif

endmodule
