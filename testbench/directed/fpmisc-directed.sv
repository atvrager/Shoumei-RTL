// Reproducer: FPMisc exception flags (single precision).
//
// Run:  make fpmisc-directed
//
// FPMisc runs four sub-circuits in parallel -- sign injection, compare, class
// decode and float/integer conversion -- and selects one result by the op
// field.  The conversion sub-circuit always computes, so its sticky bit and its
// special-case detection are live for every operation.  The flag outputs were
// wired straight to that sub-circuit's nv and nx, with no regard for which
// operation was selected, so fmax of an operand the conversion would find
// inexact reported NX, and fmin of a quiet NaN reported NV.
//
// exc[0] is NX and exc[4] is NV; exc[1..3] are held at zero because FPMisc
// cannot divide, overflow or underflow.
//
// The operands below are chosen so the conversion sub-circuit is inexact
// (0x3E800001 = 0.25 + 2^-25) or sees a NaN, while the selected operation is
// exact and raises nothing.  The last three cases pin the conversion's and the
// compare's own flags, which must survive the fix.

module fpmisc_directed;
  logic [31:0] src1, src2;
  logic [4:0]  op;
  logic [2:0]  rm;
  logic [31:0] result;
  logic [4:0]  exc;

  FPMisc dut (.src1(src1), .src2(src2), .op(op), .rm(rm),
              .result(result), .exc(exc));

  int errors = 0;

  task run(input [8*22-1:0] name, input [4:0] opcode, input [31:0] a, input [31:0] b,
           input [31:0] want, input [4:0] want_exc);
    runrm(name, opcode, a, b, 3'd0, want, want_exc);
  endtask

  // The rounding mode is an operand of the conversion, not a constant: FCVT.S.W
  // and FCVT.S.WU must round by rm, so the mode has to be driven per case.
  task runrm(input [8*22-1:0] name, input [4:0] opcode, input [31:0] a, input [31:0] b,
             input [2:0] mode, input [31:0] want, input [4:0] want_exc);
    src1 = a; src2 = b; op = opcode; rm = mode;
    #1;
    if (result !== want || exc !== want_exc) begin
      errors++;
      $display("FAIL %-22s op=%0d %08x %08x rm=%0d -> %08x exc=%b, expected %08x exc=%b",
               name, opcode, a, b, mode, result, exc, want, want_exc);
    end else begin
      $display("ok   %-22s op=%0d rm=%0d -> %08x exc=%b", name, opcode, mode, result, exc);
    end
  endtask

  initial begin
    // FMAX_S=20, FMIN_S=19, FLT_S=10, FCLASS_S=18, FCVT_W_S=12, FEQ_S=9.
    run("fmax, cvt inexact    ", 5'd20, 32'h3E800001, 32'h3F800000, 32'h3F800000, 5'b00000);
    run("fmin, cvt inexact    ", 5'd19, 32'h3E800001, 32'h3F800000, 32'h3E800001, 5'b00000);
    run("flt, cvt inexact     ", 5'd10, 32'h3E800001, 32'h3F800000, 32'h00000001, 5'b00000);
    run("fclass, cvt inexact  ", 5'd18, 32'h3E800001, 32'h00000000, 32'h00000040, 5'b00000);
    run("fmax, quiet NaN      ", 5'd20, 32'h7FC00000, 32'h3F800000, 32'h3F800000, 5'b00000);
    run("fmin, quiet NaN      ", 5'd19, 32'h7FC00000, 32'h3F800000, 32'h3F800000, 5'b00000);

    // The conversion's and the compare's own flags must survive.
    run("fcvt.w.s inexact     ", 5'd12, 32'h3E800001, 32'h00000000, 32'h00000000, 5'b00001);
    run("fcvt.w.s NaN         ", 5'd12, 32'h7FC00000, 32'h00000000, 32'h7FFFFFFF, 5'b10000);
    run("feq.s signaling NaN  ", 5'd9,  32'h7F800001, 32'h3F800000, 32'h00000000, 5'b10000);

    // Sign injection is rd = {rs2[31], rs1[30:0]}: the sign comes from rs2 and
    // the magnitude from rs1.  The corpus only ever uses operands of equal
    // magnitude, which cannot tell the two roles apart, so they differ here.
    // FSGNJ=21, FSGNJN=22, FSGNJX=23.
    run("fsgnj.s              ", 5'd21, 32'h3F800000, 32'hBF000000, 32'hBF800000, 5'b00000);
    run("fsgnjn.s             ", 5'd22, 32'h3F800000, 32'hBF000000, 32'h3F800000, 5'b00000);
    run("fsgnjx.s             ", 5'd23, 32'h3F800000, 32'hBF000000, 32'hBF800000, 5'b00000);
    run("fsgnj.s reversed     ", 5'd21, 32'hBF000000, 32'h3F800000, 32'h3F000000, 5'b00000);
    run("fsgnjn.s reversed    ", 5'd22, 32'hBF000000, 32'h3F800000, 32'hBF000000, 5'b00000);
    run("fsgnjx.s reversed    ", 5'd23, 32'hBF000000, 32'h3F800000, 32'hBF000000, 5'b00000);

    // FCVT.S.W (op 14) and FCVT.S.WU (op 15) must round by rm.  16777217 is
    // halfway between 16777216 and 16777218 in single precision; 0xFFFFFFFF as
    // an unsigned source sits one below 4294967296.  RNE=0, RTZ=1, RDN=2,
    // RUP=3, RMM=4.
    runrm("cvt.s.w 16777217 rtz ", 5'd14, 32'h01000001, 32'h0, 3'd1, 32'h4B800000, 5'b00001);
    runrm("cvt.s.w 16777217 rup ", 5'd14, 32'h01000001, 32'h0, 3'd3, 32'h4B800001, 5'b00001);
    runrm("cvt.s.w 16777217 rdn ", 5'd14, 32'h01000001, 32'h0, 3'd2, 32'h4B800000, 5'b00001);
    runrm("cvt.s.w 16777217 rne ", 5'd14, 32'h01000001, 32'h0, 3'd0, 32'h4B800000, 5'b00001);
    runrm("cvt.s.w 16777217 rmm ", 5'd14, 32'h01000001, 32'h0, 3'd4, 32'h4B800001, 5'b00001);
    runrm("cvt.s.w -16777217 rup", 5'd14, 32'hFEFFFFFF, 32'h0, 3'd3, 32'hCB800000, 5'b00001);
    runrm("cvt.s.w -16777217 rdn", 5'd14, 32'hFEFFFFFF, 32'h0, 3'd2, 32'hCB800001, 5'b00001);
    runrm("cvt.s.wu ffffffff rtz", 5'd15, 32'hFFFFFFFF, 32'h0, 3'd1, 32'h4F7FFFFF, 5'b00001);
    runrm("cvt.s.wu ffffffff rup", 5'd15, 32'hFFFFFFFF, 32'h0, 3'd3, 32'h4F800000, 5'b00001);
    runrm("cvt.s.wu ffffffff rdn", 5'd15, 32'hFFFFFFFF, 32'h0, 3'd2, 32'h4F7FFFFF, 5'b00001);
    runrm("cvt.s.wu ffffffff rne", 5'd15, 32'hFFFFFFFF, 32'h0, 3'd0, 32'h4F800000, 5'b00001);
    runrm("cvt.s.wu ffffffff rmm", 5'd15, 32'hFFFFFFFF, 32'h0, 3'd4, 32'h4F800000, 5'b00001);

    if (errors == 0) begin
      $display("PASS: all checks agree with IEEE 754 / RISC-V");
    end else begin
      $display("FAIL: %0d checks disagree", errors);
      $fatal(1);
    end
    $finish;
  end
endmodule
