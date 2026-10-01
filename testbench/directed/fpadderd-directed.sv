// Reproducer: FPAdderD (double precision) IEEE-754 conformance.
//
// Run:  make fpadderd-directed
//
// Fixed here: overflow used to yield a NaN instead of infinity, OF could never
// assert, and a subnormal result was emitted as a normal-format exponent with an
// unnormalized mantissa.  A nonzero subnormal operand is now scaled with the
// effective exponent 1, and a result below the minimum normal is emitted with
// exponent field 0 and a mantissa counted in multiples of 2^-1074.  Every case
// below passes.
//
// FPAdderD carries three extra mantissa bits -- sum[2:0] are guard, round and
// sticky -- which is what makes rounding possible here at all.  The
// single-precision FPAdder mirrors it; see fpadder-directed.sv.
//
// A subnormal double sum is always exact: every operand is a multiple of the
// quantum 2^-1074, so the sum is one too and no rounding is needed.  UF
// therefore stays 0, and the RDN/RUP/RMM modes are only exercised on normal
// results where the guard/round/sticky field decides.

module fpadderd_directed;
  logic [63:0] src1, src2; logic op_sub; logic [2:0] rm;
  logic [5:0]  dest_tag;  logic valid_in;
  logic [63:0] result;    logic [5:0] tag_out; logic [4:0] exc; logic valid_out;
  logic clock = 0, reset = 0;

  FPAdderD dut (.src1(src1), .src2(src2), .op_sub(op_sub), .rm(rm),
                .dest_tag(dest_tag), .valid_in(valid_in), .result(result),
                .tag_out(tag_out), .exc(exc), .valid_out(valid_out),
                .clock(clock), .reset(reset));

  always #5 clock = ~clock;

  int errors = 0;
  int checks = 0;

  task run(input [8*22-1:0] name, input [63:0] a, input [63:0] b, input [2:0] rmode,
           input [63:0] want, input [4:0] want_exc);
    int guard;
    checks++;
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
      $display("FAIL %-16s rm=%b %016x + %016x -> %016x exc=%b, expected %016x exc=%b",
               name, rmode, a, b, result, exc, want, want_exc);
    end else begin
      $display("ok   %-16s rm=%b -> %016x exc=%b", name, rmode, result, exc);
    end
    @(posedge clock);
  endtask

  // Effective subtraction: asserts op_sub, so the second operand's sign flips.
  task runsub(input [8*22-1:0] name, input [63:0] a, input [63:0] b, input [2:0] rmode,
              input [63:0] want, input [4:0] want_exc);
    int guard;
    checks++;
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
      $display("FAIL %-16s rm=%b %016x - %016x -> %016x exc=%b, expected %016x exc=%b",
               name, rmode, a, b, result, exc, want, want_exc);
    end else begin
      $display("ok   %-16s rm=%b -> %016x exc=%b", name, rmode, result, exc);
    end
    @(posedge clock);
  endtask

  localparam [2:0] RNE = 3'b000, RTZ = 3'b001, RDN = 3'b010, RUP = 3'b011, RMM = 3'b100;

  localparam [63:0] ONE      = 64'h3FF0000000000000;
  localparam [63:0] DBL_MAX  = 64'h7FEFFFFFFFFFFFFF;
  localparam [63:0] NEG_MAX  = 64'hFFEFFFFFFFFFFFFF;
  localparam [63:0] INF      = 64'h7FF0000000000000;
  localparam [63:0] NEG_INF  = 64'hFFF0000000000000;
  localparam [63:0] CANON_NAN= 64'h7FF8000000000000;
  localparam [63:0] ULP_0625 = 64'h3CA4000000000000;  // 0.625 * 2^-52: above half an ulp
  localparam [63:0] ULP_0500 = 64'h3CA0000000000000;  // 0.500 * 2^-52: an exact tie
  localparam [63:0] NEG_ONE  = 64'hBFF0000000000000;  // -1.0
  localparam [63:0] NEG_ULP075 = 64'hBCA8000000000000; // -0.75 * 2^-52
  localparam [63:0] ULP_075  = 64'h3CA8000000000000;  // 0.75 * 2^-52: above half an ulp
  localparam [63:0] MIN_SUB  = 64'h0000000000000001;  // 2^-1074
  localparam [63:0] MIN_NORM = 64'h0010000000000000;  // 2^-1022
  localparam [63:0] ZERO     = 64'h0000000000000000;
  localparam [63:0] NEG_ZERO = 64'h8000000000000000;

  localparam [4:0] NX = 5'b00001, OF = 5'b00100;

  initial begin
    reset = 1; repeat (3) @(posedge clock); reset = 0; @(posedge clock);

    run("1+1", ONE, ONE, RNE, 64'h4000000000000000, 5'b00000);

    // Rounding modes.  Magnitude increment is at most one ulp, so the modes
    // differ only in when they round away from zero.
    run("1+0.5ulp RNE",      ONE, ULP_0500, RNE,  64'h3FF0000000000000, NX);  // tie: to even (down)
    run("1+0.5ulp RTZ",      ONE, ULP_0500, RTZ,  64'h3FF0000000000000, NX);
    run("1+0.5ulp RDN",      ONE, ULP_0500, RDN,  64'h3FF0000000000000, NX);  // positive: truncate
    run("1+0.5ulp RUP",      ONE, ULP_0500, RUP,  64'h3FF0000000000001, NX);  // positive: round up
    run("1+0.5ulp RMM",      ONE, ULP_0500, RMM,  64'h3FF0000000000001, NX);  // tie: away from zero
    run("1+0.5ulp resv101",  ONE, ULP_0500, 3'b101, 64'h3FF0000000000000, NX);// reserved acts as RNE
    // tie with an odd kept mantissa rounds up to even
    run("odd.5ulp RNE", 64'h3FF0000000000001, ULP_0500, RNE, 64'h3FF0000000000002, NX);
    run("1+0.625ulp RNE",    ONE, ULP_0625, RNE,  64'h3FF0000000000001, NX);
    run("1+0.75ulp RNE",     ONE, ULP_075,  RNE,  64'h3FF0000000000001, NX);
    run("1+0.75ulp RTZ",     ONE, ULP_075,  RTZ,  64'h3FF0000000000000, NX);
    run("1+0.75ulp RDN",     ONE, ULP_075,  RDN,  64'h3FF0000000000000, NX);
    // sign-dependent modes, on a negative result
    run("-(1+.75ulp) RTZ", NEG_ONE, NEG_ULP075, RTZ, 64'hBFF0000000000000, NX);
    run("-(1+.75ulp) RDN", NEG_ONE, NEG_ULP075, RDN, 64'hBFF0000000000001, NX); // toward -inf
    run("-(1+.75ulp) RUP", NEG_ONE, NEG_ULP075, RUP, 64'hBFF0000000000000, NX); // toward +inf

    // overflow must saturate to infinity and raise OF|NX
    run("max+max", DBL_MAX, DBL_MAX, RNE, INF, OF|NX);
    run("-max-max", NEG_MAX, NEG_MAX, RNE, NEG_INF, OF|NX);
    // An additive carry is not the only way past the maximum: rounding up a
    // sum that sits just above it does too, and that case must raise OF as
    // well.  IEEE 754 section 7.4 compares against the result rounded with an
    // unbounded exponent, so only the modes that round away from zero overflow.
    run("max+1 RUP", DBL_MAX, ONE,     RUP, INF,     OF|NX);
    run("max+1 RTZ", DBL_MAX, ONE,     RTZ, DBL_MAX, NX);
    run("max+1 RDN", DBL_MAX, ONE,     RDN, DBL_MAX, NX);
    run("max+1 RNE", DBL_MAX, ONE,     RNE, DBL_MAX, NX);
    run("-max-1 RDN", NEG_MAX, NEG_ONE, RDN, NEG_INF, OF|NX);
    run("-max-1 RTZ", NEG_MAX, NEG_ONE, RTZ, NEG_MAX, NX);

    // Subnormal operands and results.  Every binary64 value is a multiple of the
    // subnormal quantum 2^-1074, so a subnormal sum is always exact.
    run("minsub+0",       MIN_SUB,  ZERO,    RNE, MIN_SUB,       5'b00000);
    run("0+minsub",       ZERO,     MIN_SUB, RNE, MIN_SUB,       5'b00000);
    run("minsub+minsub",  MIN_SUB,  MIN_SUB, RNE, 64'h2,         5'b00000);
    run("minnorm+minsub", MIN_NORM, MIN_SUB, RNE, 64'h0010000000000001, 5'b00000);
    run("minnorm-minsub", MIN_NORM, 64'h8000000000000001, RNE, 64'h000FFFFFFFFFFFFF, 5'b00000);
    run("minsub+minnorm", MIN_SUB,  MIN_NORM, RNE, 64'h0010000000000001, 5'b00000);
    run("1.0+minsub",     ONE,      MIN_SUB, RNE, ONE,           NX);


    // effective subtraction whose lost operand sits below the alignment window:
    // the truncation must borrow one ulp, and the borrow must renormalize when
    // the sum was a power of two
    run("1.0-2^-60 RTZ",  ONE, 64'hBC30000000000000, RTZ, 64'h3FEFFFFFFFFFFFFF, NX);
    run("1.0-2^-60 RDN",  ONE, 64'hBC30000000000000, RDN, 64'h3FEFFFFFFFFFFFFF, NX);
    run("1.0-2^-60 RNE",  ONE, 64'hBC30000000000000, RNE, ONE,                NX);
    run("2.0-2^-60 RTZ",  64'h4000000000000000, 64'hBC30000000000000, RTZ, 64'h3FFFFFFFFFFFFFFF, NX);

    // A tiny addend against the largest double.  The exponent difference is
    // about a thousand.  The exact sum is DBL_MAX - 0.1, which lies 0.1 below
    // DBL_MAX and a whole ulp above the next lower double, so round to nearest
    // keeps DBL_MAX; only the downward and toward-zero modes step down.
    run("-0.1 + max rne", 64'hBFB999999999999A, DBL_MAX, RNE, 64'h7FEFFFFFFFFFFFFF, NX);
    run("-0.1 + max rdn", 64'hBFB999999999999A, DBL_MAX, RDN, 64'h7FEFFFFFFFFFFFFE, NX);
    run("-0.1 + max rtz", 64'hBFB999999999999A, DBL_MAX, RTZ, 64'h7FEFFFFFFFFFFFFE, NX);
    run("-0.1 + max rup", 64'hBFB999999999999A, DBL_MAX, RUP, 64'h7FEFFFFFFFFFFFFF, NX);
    run("+0.1 + max rne", 64'h3FB999999999999A, DBL_MAX, RNE, 64'h7FEFFFFFFFFFFFFF, NX);

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
      $fatal(1, "FAIL: %0d of %0d checks disagree with IEEE 754 / RISC-V", errors, checks);
    end
    $display("PASS: all %0d checks agree with IEEE 754 / RISC-V", checks);
    $finish;
  end
endmodule
