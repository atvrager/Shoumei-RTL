// Reproducer: FPDoubleConverter narrowing and widening (fcvt.s.d / fcvt.d.s).
//
// Run:  make fpdblconv-directed
//
// fcvt.s.d narrows a double to single: the result is an SP value, NaN-boxed,
// and it raises NX when the narrowing is inexact.  fcvt.d.s widens: exact by
// construction, so it never raises anything.  A quiet NaN converts without a
// flag on either side; a signaling NaN raises NV and returns the canonical
// quiet NaN.
//
// The cosim's first flag divergence on the random streams is an fcvt.s.d that
// reports NX where the reference reports none, so the exact and NaN cases are
// checked here as well as the inexact one.

module fpdblconv_directed;
  logic [63:0] src1;
  logic [5:0]  op;
  logic [2:0]  rm;
  logic [63:0] result;
  logic [4:0]  exc;
  logic        result_is_int;

  FPDoubleConverter dut (.src1(src1), .op(op), .rm(rm),
                         .result(result), .exc(exc), .result_is_int(result_is_int));

  int errors = 0;
  int checks = 0;

  task run(input [8*22-1:0] name, input [5:0] opcode, input [63:0] a,
           input [63:0] want, input [4:0] want_exc);
    src1 = a; op = opcode; rm = 3'd0;
    #1; checks++;
    checks++;
    if (result !== want || exc !== want_exc) begin
      errors++;
      $display("FAIL %-22s op=%0d %016x -> %016x exc=%b, expected %016x exc=%b",
               name, opcode, a, result, exc, want, want_exc);
    end else begin
      $display("ok   %-22s op=%0d -> %016x exc=%b", name, opcode, result, exc);
    end
  endtask

  // Same as run, with the rounding mode given.  The DP to int conversions round
  // by rm, and a fixed RNE would hide a wrong direction or a wrong tie.
  task runrm(input [8*22-1:0] name, input [5:0] opcode, input [2:0] mode,
             input [63:0] a, input [63:0] want, input [4:0] want_exc);
    src1 = a; op = opcode; rm = mode;
    #1;
    checks++;
    if (result !== want || exc !== want_exc) begin
      errors++;
      $display("FAIL %-22s op=%0d rm=%b %016x -> %016x exc=%b, expected %016x exc=%b",
               name, opcode, mode, a, result, exc, want, want_exc);
    end else begin
      $display("ok   %-22s op=%0d rm=%b -> %016x exc=%b", name, opcode, mode, result, exc);
    end
  endtask


  initial begin
    // FCVT_S_D=48 narrows, FCVT_D_S=49 widens.  exc[0] is NX, exc[4] is NV.
    run("fcvt.s.d exact      ", 6'd48, 64'h3FF0000000000000, 64'hFFFFFFFF3F800000, 5'b00000);
    run("fcvt.s.d inexact    ", 6'd48, 64'h3FF0000000000001, 64'hFFFFFFFF3F800000, 5'b00001);
    run("fcvt.s.d quiet NaN  ", 6'd48, 64'h7FF8000000000000, 64'hFFFFFFFF7FC00000, 5'b00000);
    run("fcvt.s.d signal NaN ", 6'd48, 64'h7FF0000000000001, 64'hFFFFFFFF7FC00000, 5'b10000);
    run("fcvt.d.s exact      ", 6'd49, 64'hFFFFFFFF3F800000, 64'h3FF0000000000000, 5'b00000);
    run("fcvt.d.s quiet NaN  ", 6'd49, 64'hFFFFFFFF7FC00000, 64'h7FF8000000000000, 5'b00000);

    // FCVT_W_D=44.  The guard and sticky come from a second shifter on the
    // amount one less than the truncation, so every case here has a fractional
    // part: 1.5 and 2.5 are exact ties, 1.25 sits below one, 3.5 above.
    runrm("fcvt.w.d 1.5 rne    ", 6'd44, 3'b000, 64'h3FF8000000000000, 64'h0000000000000002, 5'b00001);
    runrm("fcvt.w.d 2.5 rne    ", 6'd44, 3'b000, 64'h4004000000000000, 64'h0000000000000002, 5'b00001);
    runrm("fcvt.w.d 3.5 rne    ", 6'd44, 3'b000, 64'h400C000000000000, 64'h0000000000000004, 5'b00001);
    runrm("fcvt.w.d 0.5 rne    ", 6'd44, 3'b000, 64'h3FE0000000000000, 64'h0000000000000000, 5'b00001);
    runrm("fcvt.w.d 1.25 rne   ", 6'd44, 3'b000, 64'h3FF4000000000000, 64'h0000000000000001, 5'b00001);
    runrm("fcvt.w.d 1.5 rtz    ", 6'd44, 3'b001, 64'h3FF8000000000000, 64'h0000000000000001, 5'b00001);
    runrm("fcvt.w.d 1.5 rdn    ", 6'd44, 3'b010, 64'h3FF8000000000000, 64'h0000000000000001, 5'b00001);
    runrm("fcvt.w.d 1.5 rup    ", 6'd44, 3'b011, 64'h3FF8000000000000, 64'h0000000000000002, 5'b00001);
    runrm("fcvt.w.d 1.5 rmm    ", 6'd44, 3'b100, 64'h3FF8000000000000, 64'h0000000000000002, 5'b00001);
    runrm("fcvt.w.d -1.5 rtz   ", 6'd44, 3'b001, 64'hBFF8000000000000, 64'hFFFFFFFFFFFFFFFF, 5'b00001);
    runrm("fcvt.w.d -1.5 rdn   ", 6'd44, 3'b010, 64'hBFF8000000000000, 64'hFFFFFFFFFFFFFFFE, 5'b00001);
    runrm("fcvt.w.d -1.5 rup   ", 6'd44, 3'b011, 64'hBFF8000000000000, 64'hFFFFFFFFFFFFFFFF, 5'b00001);
    runrm("fcvt.w.d .4999 rne  ", 6'd44, 3'b000, 64'h3FDFFFFFFFFFFFFF, 64'h0000000000000000, 5'b00001);
    runrm("fcvt.w.d .5001 rne  ", 6'd44, 3'b000, 64'h3FE0000000000001, 64'h0000000000000001, 5'b00001);
    runrm("fcvt.w.d 1.5 rne st ", 6'd44, 3'b000, 64'h3FF8000000000000, 64'h0000000000000002, 5'b00001);

    // Narrowing rounds by rm.  1 + 2^-52 sits just above 1.0f, so round up
    // steps to the next single and every other mode stays.
    runrm("narrow 1+2^-52 rne   ", 6'd48, 3'b000, 64'h3FF0000000000001, 64'hFFFFFFFF3F800000, 5'b00001);
    runrm("narrow 1+2^-52 rup   ", 6'd48, 3'b011, 64'h3FF0000000000001, 64'hFFFFFFFF3F800001, 5'b00001);
    runrm("narrow 1+2^-52 rdn   ", 6'd48, 3'b010, 64'h3FF0000000000001, 64'hFFFFFFFF3F800000, 5'b00001);
    runrm("narrow 1+2^-52 rtz   ", 6'd48, 3'b001, 64'h3FF0000000000001, 64'hFFFFFFFF3F800000, 5'b00001);
    runrm("narrow 1+2^-52 rmm   ", 6'd48, 3'b100, 64'h3FF0000000000001, 64'hFFFFFFFF3F800000, 5'b00001);
    // A double past the single range overflows: infinity or the largest
    // finite magnitude, by direction, with OF and NX.
    runrm("narrow max rne       ", 6'd48, 3'b000, 64'h7FEFFFFFFFFFFFFF, 64'hFFFFFFFF7F800000, 5'b00101);
    runrm("narrow max rup       ", 6'd48, 3'b011, 64'h7FEFFFFFFFFFFFFF, 64'hFFFFFFFF7F800000, 5'b00101);
    runrm("narrow max rtz       ", 6'd48, 3'b001, 64'h7FEFFFFFFFFFFFFF, 64'hFFFFFFFF7F7FFFFF, 5'b00101);
    runrm("narrow max rdn       ", 6'd48, 3'b010, 64'h7FEFFFFFFFFFFFFF, 64'hFFFFFFFF7F7FFFFF, 5'b00101);
    runrm("narrow -max rdn      ", 6'd48, 3'b010, 64'hFFEFFFFFFFFFFFFF, 64'hFFFFFFFF7F800000 | 64'h80000000, 5'b00101);
    runrm("narrow -max rup      ", 6'd48, 3'b011, 64'hFFEFFFFFFFFFFFFF, 64'hFFFFFFFF7F7FFFFF | 64'h80000000, 5'b00101);
    runrm("narrow -max rtz      ", 6'd48, 3'b001, 64'hFFEFFFFFFFFFFFFF, 64'hFFFFFFFF7F7FFFFF | 64'h80000000, 5'b00101);

    if (errors == 0) begin
      $display("PASS: all %0d checks agree with IEEE 754 / RISC-V", checks);
    end else begin
      $display("FAIL: %0d of %0d checks disagree", errors, checks);
      $fatal(1);
    end
    $finish;
  end
endmodule
