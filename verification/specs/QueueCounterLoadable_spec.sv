// Parameterized up/down queue counter with synchronous load

module QueueCounterLoadable_spec #(
  parameter int WIDTH = 4
) (
  input  logic             inc,
  input  logic             dec,
  input  logic             load_en,
  input  logic [WIDTH-1:0] load_value,
  output logic [WIDTH-1:0] count,
  input  logic             clock,
  input  logic             reset
);

  logic [WIDTH-1:0] counter_q;

  assign count = counter_q;

  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      counter_q <= '0;
    end else if (load_en) begin
      counter_q <= load_value;
    end else begin
      case ({inc, dec})
        2'b10:   counter_q <= counter_q + WIDTH'(1);
        2'b01:   counter_q <= counter_q - WIDTH'(1);
        default: counter_q <= counter_q;
      endcase
    end
  end

endmodule
