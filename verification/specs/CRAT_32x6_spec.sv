// Expressive, human-readable specification of 32x6 Committed Register Alias Table.

module CRAT_32x6_spec (
  input  logic       reset,
  input  logic [5:0] restore_data_0,
  input  logic [5:0] restore_data_1,
  input  logic [5:0] restore_data_2,
  input  logic [5:0] restore_data_3,
  input  logic [5:0] restore_data_4,
  input  logic [5:0] restore_data_5,
  input  logic [5:0] restore_data_6,
  input  logic [5:0] restore_data_7,
  input  logic [5:0] restore_data_8,
  input  logic [5:0] restore_data_9,
  input  logic [5:0] restore_data_10,
  input  logic [5:0] restore_data_11,
  input  logic [5:0] restore_data_12,
  input  logic [5:0] restore_data_13,
  input  logic [5:0] restore_data_14,
  input  logic [5:0] restore_data_15,
  input  logic [5:0] restore_data_16,
  input  logic [5:0] restore_data_17,
  input  logic [5:0] restore_data_18,
  input  logic [5:0] restore_data_19,
  input  logic [5:0] restore_data_20,
  input  logic [5:0] restore_data_21,
  input  logic [5:0] restore_data_22,
  input  logic [5:0] restore_data_23,
  input  logic [5:0] restore_data_24,
  input  logic [5:0] restore_data_25,
  input  logic [5:0] restore_data_26,
  input  logic [5:0] restore_data_27,
  input  logic [5:0] restore_data_28,
  input  logic [5:0] restore_data_29,
  input  logic [5:0] restore_data_30,
  input  logic [5:0] restore_data_31,
  output logic [5:0] dump_data_0,
  output logic [5:0] dump_data_1,
  output logic [5:0] dump_data_2,
  output logic [5:0] dump_data_3,
  output logic [5:0] dump_data_4,
  output logic [5:0] dump_data_5,
  output logic [5:0] dump_data_6,
  output logic [5:0] dump_data_7,
  output logic [5:0] dump_data_8,
  output logic [5:0] dump_data_9,
  output logic [5:0] dump_data_10,
  output logic [5:0] dump_data_11,
  output logic [5:0] dump_data_12,
  output logic [5:0] dump_data_13,
  output logic [5:0] dump_data_14,
  output logic [5:0] dump_data_15,
  output logic [5:0] dump_data_16,
  output logic [5:0] dump_data_17,
  output logic [5:0] dump_data_18,
  output logic [5:0] dump_data_19,
  output logic [5:0] dump_data_20,
  output logic [5:0] dump_data_21,
  output logic [5:0] dump_data_22,
  output logic [5:0] dump_data_23,
  output logic [5:0] dump_data_24,
  output logic [5:0] dump_data_25,
  output logic [5:0] dump_data_26,
  output logic [5:0] dump_data_27,
  output logic [5:0] dump_data_28,
  output logic [5:0] dump_data_29,
  output logic [5:0] dump_data_30,
  output logic [5:0] dump_data_31,
  input  logic       clock
);

  logic [5:0] restore_in [32];
  assign restore_in[0]  = restore_data_0;
  assign restore_in[1]  = restore_data_1;
  assign restore_in[2]  = restore_data_2;
  assign restore_in[3]  = restore_data_3;
  assign restore_in[4]  = restore_data_4;
  assign restore_in[5]  = restore_data_5;
  assign restore_in[6]  = restore_data_6;
  assign restore_in[7]  = restore_data_7;
  assign restore_in[8]  = restore_data_8;
  assign restore_in[9]  = restore_data_9;
  assign restore_in[10] = restore_data_10;
  assign restore_in[11] = restore_data_11;
  assign restore_in[12] = restore_data_12;
  assign restore_in[13] = restore_data_13;
  assign restore_in[14] = restore_data_14;
  assign restore_in[15] = restore_data_15;
  assign restore_in[16] = restore_data_16;
  assign restore_in[17] = restore_data_17;
  assign restore_in[18] = restore_data_18;
  assign restore_in[19] = restore_data_19;
  assign restore_in[20] = restore_data_20;
  assign restore_in[21] = restore_data_21;
  assign restore_in[22] = restore_data_22;
  assign restore_in[23] = restore_data_23;
  assign restore_in[24] = restore_data_24;
  assign restore_in[25] = restore_data_25;
  assign restore_in[26] = restore_data_26;
  assign restore_in[27] = restore_data_27;
  assign restore_in[28] = restore_data_28;
  assign restore_in[29] = restore_data_29;
  assign restore_in[30] = restore_data_30;
  assign restore_in[31] = restore_data_31;

  logic [5:0] crat_reg [32];

  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      for (int i = 0; i < 32; i++) begin
        crat_reg[i] <= 6'(i);
      end
    end else begin
      for (int i = 0; i < 32; i++) begin
        crat_reg[i] <= restore_in[i];
      end
    end
  end

  assign dump_data_0  = crat_reg[0];
  assign dump_data_1  = crat_reg[1];
  assign dump_data_2  = crat_reg[2];
  assign dump_data_3  = crat_reg[3];
  assign dump_data_4  = crat_reg[4];
  assign dump_data_5  = crat_reg[5];
  assign dump_data_6  = crat_reg[6];
  assign dump_data_7  = crat_reg[7];
  assign dump_data_8  = crat_reg[8];
  assign dump_data_9  = crat_reg[9];
  assign dump_data_10 = crat_reg[10];
  assign dump_data_11 = crat_reg[11];
  assign dump_data_12 = crat_reg[12];
  assign dump_data_13 = crat_reg[13];
  assign dump_data_14 = crat_reg[14];
  assign dump_data_15 = crat_reg[15];
  assign dump_data_16 = crat_reg[16];
  assign dump_data_17 = crat_reg[17];
  assign dump_data_18 = crat_reg[18];
  assign dump_data_19 = crat_reg[19];
  assign dump_data_20 = crat_reg[20];
  assign dump_data_21 = crat_reg[21];
  assign dump_data_22 = crat_reg[22];
  assign dump_data_23 = crat_reg[23];
  assign dump_data_24 = crat_reg[24];
  assign dump_data_25 = crat_reg[25];
  assign dump_data_26 = crat_reg[26];
  assign dump_data_27 = crat_reg[27];
  assign dump_data_28 = crat_reg[28];
  assign dump_data_29 = crat_reg[29];
  assign dump_data_30 = crat_reg[30];
  assign dump_data_31 = crat_reg[31];

`ifdef FORMAL
  a_reset_id0: assert property (@(posedge clock) disable iff (1'b0)
    reset |=> (dump_data_0 == 6'd0)
  );
  a_reset_id31: assert property (@(posedge clock) disable iff (1'b0)
    reset |=> (dump_data_31 == 6'd31)
  );
`endif

endmodule
