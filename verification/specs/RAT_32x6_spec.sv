// Expressive, human-readable specification of 32x6 Register Alias Table with rs3.

module RAT_32x6_spec (
  input  logic       reset,
  input  logic       write_en,
  input  logic [4:0] write_addr,
  input  logic [5:0] write_data,
  input  logic [4:0] rs1_addr,
  input  logic [4:0] rs2_addr,
  input  logic [4:0] rs3_addr,
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
  output logic [5:0] rs1_data,
  output logic [5:0] rs2_data,
  output logic [5:0] rs3_data,
  output logic [5:0] old_rd_data,
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

  logic [5:0] rat_reg [32];

  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      for (int i = 0; i < 32; i++) begin
        rat_reg[i] <= 6'(i);
      end
    end else begin
      for (int i = 0; i < 32; i++) begin
        rat_reg[i] <= restore_in[i];
      end
    end
  end

  // Read ports read directly from internal storage
  assign rs1_data = rat_reg[rs1_addr];
  assign rs2_data = rat_reg[rs2_addr];
  assign rs3_data = rat_reg[rs3_addr];
  assign old_rd_data = rat_reg[write_addr];

  // Dump outputs: bypass write_data if write_en is set for that address
  logic [5:0] dump_out [32];
  always_comb begin
    for (int i = 0; i < 32; i++) begin
      dump_out[i] = (write_en && (write_addr == 5'(i))) ? write_data : rat_reg[i];
    end
  end

  assign dump_data_0  = dump_out[0];
  assign dump_data_1  = dump_out[1];
  assign dump_data_2  = dump_out[2];
  assign dump_data_3  = dump_out[3];
  assign dump_data_4  = dump_out[4];
  assign dump_data_5  = dump_out[5];
  assign dump_data_6  = dump_out[6];
  assign dump_data_7  = dump_out[7];
  assign dump_data_8  = dump_out[8];
  assign dump_data_9  = dump_out[9];
  assign dump_data_10 = dump_out[10];
  assign dump_data_11 = dump_out[11];
  assign dump_data_12 = dump_out[12];
  assign dump_data_13 = dump_out[13];
  assign dump_data_14 = dump_out[14];
  assign dump_data_15 = dump_out[15];
  assign dump_data_16 = dump_out[16];
  assign dump_data_17 = dump_out[17];
  assign dump_data_18 = dump_out[18];
  assign dump_data_19 = dump_out[19];
  assign dump_data_20 = dump_out[20];
  assign dump_data_21 = dump_out[21];
  assign dump_data_22 = dump_out[22];
  assign dump_data_23 = dump_out[23];
  assign dump_data_24 = dump_out[24];
  assign dump_data_25 = dump_out[25];
  assign dump_data_26 = dump_out[26];
  assign dump_data_27 = dump_out[27];
  assign dump_data_28 = dump_out[28];
  assign dump_data_29 = dump_out[29];
  assign dump_data_30 = dump_out[30];
  assign dump_data_31 = dump_out[31];

`ifdef FORMAL
  // SVA assertions
  a_bypass_0: assert property (
    write_en && (write_addr == 5'd0) |-> (dump_data_0 == write_data)
  );
  a_bypass_31: assert property (
    write_en && (write_addr == 5'd31) |-> (dump_data_31 == write_data)
  );
`endif

endmodule
