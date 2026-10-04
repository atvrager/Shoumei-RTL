// Reproducer: FPAdder (single precision) IEEE-754 conformance.
//
// Run:  make fpadder-directed
//
// The single-precision adder used to truncate: Stage 4 had no `rm` port and the
// datapath carried no guard/round/sticky positions (a 24-bit mantissa summed in
// 25 bits), so the alignment remainder collapsed to one sticky bit and could not
// be rounded.  That, plus overflow returning a NaN rather than infinity and
// OF/UF/DZ being unreachable, is what made every inexact FADD.S/FSUB.S wrong.
// Fixed in the same change, and all cases below pass.
//
// The datapath now mirrors the double-precision one: 27 bits with the mantissa
// at [26:3], so [2:0] are the guard/round/sticky field, and the barrel shifter
// accumulates the bits shifted below them.  That makes correct rounding possible,
// and NX now counts the whole remainder rather than only what sticky captured.
//
// Random co-simulation cannot find any of this: an LFSR will not form an operand
// pair whose exact sum needs a rounding decision, nor saturate the exponent.

module fpadder_directed;
  logic [31:0] src1, src2; logic op_sub; logic [2:0] rm;
  logic [5:0]  dest_tag;  logic valid_in;
  logic [31:0] result;    logic [5:0] tag_out; logic [4:0] exc; logic valid_out;
  logic clock = 0, reset = 0;

  FPAdder dut (.src1(src1), .src2(src2), .op_sub(op_sub), .rm(rm),
               .dest_tag(dest_tag), .valid_in(valid_in), .result(result),
               .tag_out(tag_out), .exc(exc), .valid_out(valid_out),
               .clock(clock), .reset(reset));

  always #5 clock = ~clock;

  int errors = 0;

  task run(input [8*20-1:0] name, input [31:0] a, input [31:0] b, input [2:0] rmode,
           input [31:0] want, input [4:0] want_exc);
    int guard;
    src1 = a; src2 = b; op_sub = 1'b0; rm = rmode; dest_tag = 6'd0; valid_in = 1'b1;
    @(posedge clock);
    valid_in = 1'b0;
    guard = 0;
    while (!valid_out && guard < 20) begin
      @(posedge clock);
      guard++;
    end
    if (result !== want || exc !== want_exc) begin
      errors++;
      $display("FAIL %-18s rm=%b %08x + %08x -> %08x exc=%b, expected %08x exc=%b",
               name, rmode, a, b, result, exc, want, want_exc);
    end else begin
      $display("ok   %-18s rm=%b -> %08x exc=%b", name, rmode, result, exc);
    end
    @(posedge clock);
  endtask

  // Effective subtraction: asserts op_sub, so the second operand's sign flips.
  task runsub(input [8*20-1:0] name, input [31:0] a, input [31:0] b, input [2:0] rmode,
              input [31:0] want, input [4:0] want_exc);
    int guard;
    src1 = a; src2 = b; op_sub = 1'b1; rm = rmode; dest_tag = 6'd0; valid_in = 1'b1;
    @(posedge clock);
    valid_in = 1'b0;
    guard = 0;
    while (!valid_out && guard < 20) begin
      @(posedge clock);
      guard++;
    end
    if (result !== want || exc !== want_exc) begin
      errors++;
      $display("FAIL %-18s rm=%b %08x - %08x -> %08x exc=%b, expected %08x exc=%b",
               name, rmode, a, b, result, exc, want, want_exc);
    end else begin
      $display("ok   %-18s rm=%b -> %08x exc=%b", name, rmode, result, exc);
    end
    @(posedge clock);
  endtask

  localparam [2:0] RNE = 3'b000, RTZ = 3'b001, RDN = 3'b010, RUP = 3'b011, RMM = 3'b100;

  localparam [31:0] ONE       = 32'h3F800000;
  localparam [31:0] TWO       = 32'h40000000;
  localparam [31:0] ONE_ODD   = 32'h3F800001;   // 1.0 + 1 ulp, odd kept mantissa
  localparam [31:0] NEG_ONE   = 32'hBF800000;
  localparam [31:0] FLT_MAX   = 32'h7F7FFFFF;
  localparam [31:0] NEG_MAX   = 32'hFF7FFFFF;
  localparam [31:0] INF       = 32'h7F800000;
  localparam [31:0] NEG_INF   = 32'hFF800000;
  localparam [31:0] QNAN      = 32'h7FC00000;
  localparam [31:0] CANON_NAN = 32'h7FC00000;
  localparam [31:0] MIN_SUB   = 32'h00000001;   // 2^-149
  localparam [31:0] MIN_NORM  = 32'h00800000;   // 2^-126
  localparam [31:0] ZERO      = 32'h00000000;
  localparam [31:0] NEG_ZERO  = 32'h80000000;
  localparam [31:0] ULP_0500  = 32'h33800000;   // 0.5   * 2^-23, an exact tie
  localparam [31:0] ULP_0625  = 32'h33A00000;   // 0.625 * 2^-23, above half
  localparam [31:0] ULP_0750  = 32'h33C00000;   // 0.75  * 2^-23
  localparam [31:0] NEG_ULP075 = 32'hB3C00000;  // -0.75 * 2^-23

  localparam [4:0] NX = 5'b00001, OF = 5'b00100, NV = 5'b10000;

  initial begin
    reset = 1; repeat (3) @(posedge clock); reset = 0; @(posedge clock);

    run("1+1", ONE, ONE, RNE, 32'h40000000, 5'b00000);   // exact

    // Every mode, at a tie and above it.  Magnitude moves by at most one ulp.
    run("1+0.5ulp RNE",   ONE, ULP_0500, RNE, 32'h3F800000, NX);  // tie: to even
    run("1+0.5ulp RTZ",   ONE, ULP_0500, RTZ, 32'h3F800000, NX);
    run("1+0.5ulp RDN",   ONE, ULP_0500, RDN, 32'h3F800000, NX);  // positive
    run("1+0.5ulp RUP",   ONE, ULP_0500, RUP, 32'h3F800001, NX);
    run("1+0.5ulp RMM",   ONE, ULP_0500, RMM, 32'h3F800001, NX);  // tie: away
    run("1+0.5ulp resv101", ONE, ULP_0500, 3'b101, 32'h3F800000, NX);
    run("oddLSB+0.5ulp RNE", ONE_ODD, ULP_0500, RNE, 32'h3F800002, NX);  // to even
    run("1+0.625ulp RNE", ONE, ULP_0625, RNE, 32'h3F800001, NX);
    run("1+0.75ulp RNE",  ONE, ULP_0750, RNE, 32'h3F800001, NX);
    run("1+0.75ulp RTZ",  ONE, ULP_0750, RTZ, 32'h3F800000, NX);
    run("1+0.75ulp RDN",  ONE, ULP_0750, RDN, 32'h3F800000, NX);
    run("1+0.75ulp RUP",  ONE, ULP_0750, RUP, 32'h3F800001, NX);
    // sign-dependent modes on a negative result
    run("-(1+.75ulp) RTZ", NEG_ONE, NEG_ULP075, RTZ, 32'hBF800000, NX);
    run("-(1+.75ulp) RDN", NEG_ONE, NEG_ULP075, RDN, 32'hBF800001, NX);  // toward -inf
    run("-(1+.75ulp) RUP", NEG_ONE, NEG_ULP075, RUP, 32'hBF800000, NX);  // toward +inf

    // overflow must saturate to infinity and raise OF|NX
    run("max+max",  FLT_MAX, FLT_MAX, RNE, INF,     OF|NX);
    run("-max-max", NEG_MAX, NEG_MAX, RNE, NEG_INF, OF|NX);
    // Rounding up a sum that sits just above the maximum overflows too, and
    // must raise OF.  IEEE 754 section 7.4 compares against the result rounded
    // with an unbounded exponent, so only the away-from-zero modes overflow.
    run("max+1 RUP", FLT_MAX, ONE,     RUP, INF,     OF|NX);
    run("max+1 RTZ", FLT_MAX, ONE,     RTZ, FLT_MAX, NX);
    run("max+1 RDN", FLT_MAX, ONE,     RDN, FLT_MAX, NX);
    run("max+1 RNE", FLT_MAX, ONE,     RNE, FLT_MAX, NX);
    run("-max-1 RDN", NEG_MAX, NEG_ONE, RDN, NEG_INF, OF|NX);
    run("-max-1 RTZ", NEG_MAX, NEG_ONE, RTZ, NEG_MAX, NX);

    // an exact result must not raise NX
    run("1.5+0.5", 32'h3FC00000, 32'h3F000000, RNE, 32'h40000000, 5'b00000);

    // A quiet NaN propagates without raising invalid; only a signalling NaN
    // does (the corpus pins this against Spike in section 5).
    run("qnan+1", QNAN, ONE, RNE, CANON_NAN, 5'b00000);
    run("snan+1", 32'h7F800001, ONE, RNE, CANON_NAN, NV);

    // Subnormal operands and results.  Every SP value is a multiple of the
    // subnormal quantum 2^-149, so a subnormal sum is always exact.
    run("minsub+0",       MIN_SUB, ZERO,    RNE, MIN_SUB,       5'b00000);
    run("0+minsub",       ZERO,    MIN_SUB, RNE, MIN_SUB,       5'b00000);
    run("minsub+minsub",  MIN_SUB, MIN_SUB, RNE, 32'h00000002,  5'b00000);
    run("minnorm+minsub", MIN_NORM, MIN_SUB, RNE, 32'h00800001, 5'b00000);
    run("minnorm-minsub", MIN_NORM, 32'h80000001, RNE, 32'h007FFFFF, 5'b00000);
    run("minsub+minnorm", MIN_SUB, MIN_NORM, RNE, 32'h00800001, 5'b00000);
    run("1.0+minsub",     ONE,     MIN_SUB, RNE, ONE,           NX);
    // effective subtraction with the cancelled operand entirely below the
    // alignment window: the truncated result must borrow one ulp
    run("1.0-2^-30 RTZ",  ONE, 32'h80400000, RTZ, 32'h3F7FFFFF, NX);
    run("1.0-2^-30 RDN",  ONE, 32'h80400000, RDN, 32'h3F7FFFFF, NX);
    run("1.0-2^-30 RNE",  ONE, 32'h80400000, RNE, ONE,           NX);
    run("2.0-2^-30 RTZ",  TWO, 32'h80400000, RTZ, 32'h3FFFFFFF, NX);
    run("2.0-2^-30 RDN",  TWO, 32'h80400000, RDN, 32'h3FFFFFFF, NX);
    run("2.0-2^-30 RNE",  TWO, 32'h80400000, RNE, TWO,          NX);

    // The sign of an exactly zero result.  IEEE 754: a sum of like-signed
    // operands keeps that sign; a difference of like-signed operands is +0
    // everywhere except RDN, which gives -0.
    run("+0 + +0",        ZERO, ZERO,     RNE, ZERO,     5'b00000);
    run("+0 + -0",        ZERO, NEG_ZERO, RNE, ZERO,     5'b00000);
    run("+0 + -0 RDN",    ZERO, NEG_ZERO, RDN, NEG_ZERO, 5'b00000);
    run("-0 + -0",        NEG_ZERO, NEG_ZERO, RNE, NEG_ZERO, 5'b00000);
    run("-0 + -0 RTZ",    NEG_ZERO, NEG_ZERO, RTZ, NEG_ZERO, 5'b00000);
    run("-0 + -0 RUP",    NEG_ZERO, NEG_ZERO, RUP, NEG_ZERO, 5'b00000);
    runsub("+0 - +0",     ZERO, ZERO,     RNE, ZERO,     5'b00000);
    runsub("+0 - +0 RDN", ZERO, ZERO,     RDN, NEG_ZERO, 5'b00000);
    runsub("+0 - +0 RUP", ZERO, ZERO,     RUP, ZERO,     5'b00000);
    runsub("-0 - +0",     NEG_ZERO, ZERO, RTZ, NEG_ZERO, 5'b00000);
    runsub("-0 - +0 RUP", NEG_ZERO, ZERO, RUP, NEG_ZERO, 5'b00000);
    runsub("+0 - -0",     ZERO, NEG_ZERO, RDN, ZERO,     5'b00000);

    if (errors != 0) begin
      $fatal(1, "FAIL: %0d of 54 checks disagree with IEEE 754 / RISC-V", errors);
    end
    $display("PASS: all 54 checks agree with IEEE 754 / RISC-V");
    $finish;
  end
endmodule
