// Reproducer: FPDoubleMisc sign injection (double precision).
//
// Run:  make fpdblmisc-directed
//
// FSGNJ.D/FSGNJN.D/FSGNJX.D are rd = {rs2[63], rs1[62:0]}: the sign comes from
// rs2 and the magnitude from rs1.  FSGNJN complements rs2's sign and FSGNJX
// takes the xor of the two signs.
//
// No self-checking test in the suite covers fsgnj, and the corpus only uses
// operands of equal magnitude, which cannot tell the two roles apart.  The
// operands below differ: -2.0 and 3.0.
//
// FSGNJ.D=53, FSGNJN.D=54, FSGNJX.D=55; FMIN.D=51, FMAX.D=52 are the
// neighbours in the same circuit and are pinned here to show they are untouched.

module fpdblmisc_directed;
  logic [63:0] src1, src2;
  logic [5:0]  op;
  logic [2:0]  rm;
  logic [63:0] result;
  logic [4:0]  exc;
  logic        result_is_int;

  FPDoubleMisc dut (.src1(src1), .src2(src2), .op(op), .rm(rm),
                    .result(result), .exc(exc), .result_is_int(result_is_int));

  int errors = 0;

  task run(input [8*24-1:0] name, input [5:0] opcode, input [63:0] a, input [63:0] b,
           input [63:0] want);
    src1 = a; src2 = b; op = opcode; rm = 3'd0;
    #1;
    if (result !== want) begin
      errors++;
      $display("FAIL %-24s op=%0d %016x %016x -> %016x, expected %016x",
               name, opcode, a, b, result, want);
    end else begin
      $display("ok   %-24s op=%0d -> %016x", name, opcode, result);
    end
  endtask

  initial begin
    // -2.0 = 0xC000000000000000, 3.0 = 0x4008000000000000.
    run("fsgnj.d              ", 6'd53, 64'hC000000000000000, 64'h4008000000000000, 64'h4000000000000000);
    run("fsgnjn.d             ", 6'd54, 64'hC000000000000000, 64'h4008000000000000, 64'hC000000000000000);
    run("fsgnjx.d             ", 6'd55, 64'hC000000000000000, 64'h4008000000000000, 64'hC000000000000000);
    run("fsgnj.d reversed     ", 6'd53, 64'h4008000000000000, 64'hC000000000000000, 64'hC008000000000000);
    run("fsgnjn.d reversed    ", 6'd54, 64'h4008000000000000, 64'hC000000000000000, 64'h4008000000000000);
    run("fsgnjx.d reversed    ", 6'd55, 64'h4008000000000000, 64'hC000000000000000, 64'hC008000000000000);

    // A NaN-boxed single is a double NaN: sign injection copies the sign and
    // magnitude through and must not canonicalize.  The random payloads reach
    // this operand shape, where a wrong magnitude shows up as a wrong result.
    run("fsgnj.d boxed        ", 6'd53, 64'hFFFFFFFF7FC00000, 64'hBFB999999999999A, 64'hFFFFFFFF7FC00000);
    run("fsgnjn.d boxed       ", 6'd54, 64'hFFFFFFFF7FC00000, 64'h3FB999999999999A, 64'hFFFFFFFF7FC00000);
    run("fsgnjx.d boxed       ", 6'd55, 64'hFFFFFFFF7FC00000, 64'hBFB999999999999A, 64'h7FFFFFFF7FC00000);
    run("fsgnj.d dnan         ", 6'd53, 64'h7FF8000000000000, 64'hBFB999999999999A, 64'hFFF8000000000000);

    // Neighbours in the same circuit.
    run("fmin.d               ", 6'd51, 64'hC000000000000000, 64'h4008000000000000, 64'hC000000000000000);
    run("fmax.d               ", 6'd52, 64'hC000000000000000, 64'h4008000000000000, 64'h4008000000000000);

    if (errors == 0) begin
      $display("PASS: all 12 checks agree with IEEE 754 / RISC-V");
    end else begin
      $display("FAIL: %0d of 12 checks disagree", errors);
      $fatal(1);
    end
    $finish;
  end
endmodule
