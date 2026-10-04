// Reproducer: FPDividerD (double precision) IEEE-754 conformance.
//
// Run:  make fpdivd-directed
//
// Two defects, both shared with the single-precision divider.
//
//  1. A quotient below the minimum normal was packed with a normal-format
//     exponent and an unnormalized mantissa, and an overflowing one was packed
//     as if finite: the 11-bit exponent field could not hold the -1022..2046
//     range, so a subnormal result was indistinguishable from a large normal
//     one.  The register is 12 bits now, the exponent below 1 selects a
//     subnormal pack (exponent field 0, mantissa counted in multiples of
//     2^-1074, shifted down by (4 - E) with the remainder in the sticky), and
//     an exponent at or past 2^1024 gives infinity with OF.
//
//  2. UF and OF could never assert.  Both are real now: UF needs a tiny and
//     inexact result, OF a saturated one.
//
// The guard/round/sticky field is out_quot[1:0] plus a sticky from the final
// remainder; the subnormal path shifts that window down and ORs the remainder
// into the shifted-out bits.

module fpdivd_directed;
  logic [63:0] src1, src2; logic [2:0] rm; logic [5:0] dest_tag; logic start;
  logic [63:0] result; logic [5:0] tag_out; logic [4:0] exc; logic valid_out, busy;
  logic clock = 0, reset = 0;

  FPDividerD dut (.src1(src1), .src2(src2), .rm(rm), .dest_tag(dest_tag),
                  .start(start), .result(result), .tag_out(tag_out), .exc(exc),
                  .valid_out(valid_out), .busy(busy), .clock(clock), .reset(reset));

  always #5 clock = ~clock;

  int errors = 0;

  task run(input [8*18-1:0] name, input [63:0] a, input [63:0] b, input [2:0] rmode,
           input [63:0] want, input [4:0] want_exc);
    int guard;
    src1 = a; src2 = b; rm = rmode; dest_tag = 6'd0; start = 1'b1;
    @(posedge clock);
    start = 1'b0;
    guard = 0;
    while (!valid_out && guard < 200) begin
      @(posedge clock);
      guard++;
    end
    if (result !== want || exc !== want_exc) begin
      errors++;
      $display("FAIL %-18s rm=%b %016x / %016x -> %016x exc=%b, expected %016x exc=%b",
               name, rmode, a, b, result, exc, want, want_exc);
    end else begin
      $display("ok   %-18s rm=%b -> %016x exc=%b", name, rmode, result, exc);
    end
    @(posedge clock);
  endtask

  localparam [2:0] RNE = 3'b000, RTZ = 3'b001, RDN = 3'b010, RUP = 3'b011, RMM = 3'b100;

  localparam [63:0] ONE      = 64'h3FF0000000000000;
  localparam [63:0] TWO      = 64'h4000000000000000;
  localparam [63:0] THREE    = 64'h4008000000000000;
  localparam [63:0] SIX      = 64'h4018000000000000;
  localparam [63:0] NEG_ONE  = 64'hBFF0000000000000;
  localparam [63:0] ZERO     = 64'h0000000000000000;
  localparam [63:0] FOUR     = 64'h4010000000000000;
  localparam [63:0] HALF     = 64'h3FE0000000000000;
  localparam [63:0] INF      = 64'h7FF0000000000000;
  localparam [63:0] NEG_INF  = 64'hFFF0000000000000;
  localparam [63:0] QNAN     = 64'h7FF8000000000000;
  localparam [63:0] CANON_NAN= 64'h7FF8000000000000;
  localparam [63:0] DBL_MAX  = 64'h7FEFFFFFFFFFFFFF;
  localparam [63:0] MIN_NORM = 64'h0010000000000000;   // 2^-1022

  localparam [4:0] NX = 5'b00001, UF = 5'b00010, OF = 5'b00100, DZ = 5'b01000, NV = 5'b10000;

  initial begin
    reset = 1; repeat (3) @(posedge clock); reset = 0; @(posedge clock);

    run("6.0 / 2.0", SIX, TWO, RNE, 64'h4008000000000000, 5'b00000);
    run("1.0 / 3.0 RNE", ONE, THREE, RNE, 64'h3FD5555555555555, NX);
    run("1.0 / 3.0 RTZ", ONE, THREE, RTZ, 64'h3FD5555555555555, NX);
    run("1.0 / 3.0 RUP", ONE, THREE, RUP, 64'h3FD5555555555556, NX);
    // 0.1 needs an upward rounding: RNE ties away from the truncated value
    run("1.0 / 10.0 RNE", ONE, 64'h4024000000000000, RNE, 64'h3FB999999999999A, NX);
    run("1.0 / 10.0 RTZ", ONE, 64'h4024000000000000, RTZ, 64'h3FB9999999999999, NX);
    run("-1.0 / 3.0 RDN", NEG_ONE, THREE, RDN, 64'hBFD5555555555556, NX);

    run("1.0 / 0.0",   ONE, ZERO, RNE, INF, DZ);
    run("-1.0 / 0.0",  NEG_ONE, ZERO, RNE, NEG_INF, DZ);
    run("0.0 / 0.0",   ZERO, ZERO, RNE, CANON_NAN, NV);
    run("inf / inf",   INF, INF, RNE, CANON_NAN, NV);
    run("inf / 3.0",   INF, THREE, RNE, INF, 5'b00000);
    run("3.0 / inf",   THREE, INF, RNE, ZERO, 5'b00000);
    run("qnan / 1.0",  QNAN, ONE, RNE, CANON_NAN, 5'b00000);

    // Subnormal results: exponent field 0, mantissa counted in multiples of
    // 2^-1074, shifted down by (4 - E) with the remainder in the sticky.
    run("min-norm / 2",     MIN_NORM, TWO, RNE, 64'h0008000000000000, 5'b00000);
    run("min-norm / 4",     MIN_NORM, FOUR, RNE, 64'h0004000000000000, 5'b00000);
    run("min-norm / 3",     MIN_NORM, THREE, RNE, 64'h0005555555555555, UF|NX);
    run("min-norm / 3 RUP", MIN_NORM, THREE, RUP, 64'h0005555555555556, UF|NX);

    // Subnormal operands.  The comparison, the alignment muxes and the restoring
    // division all treat the two mantissas as integers of the same scale, so a
    // subnormal operand is normalized first: its fraction is shifted up to the
    // implicit position and its exponent field lowered by that shift.
    run("minsub / 1",     64'h0000000000000001, ONE, RNE, 64'h0000000000000001, 5'b00000);
    run("1 / minsub",     ONE, 64'h0000000000000001, RNE, INF, OF|NX);
    run("minsub / minsub", 64'h0000000000000001, 64'h0000000000000001, RNE, ONE, 5'b00000);
    run("minsub / 2",     64'h0000000000000001, TWO, RNE, ZERO, UF|NX);
    run("2^-1030 / 2^-30", 64'h0000100000000000, 64'h3E10000000000000, RNE, 64'h0170000000000000, 5'b00000);
    run("2^-1030 / minsub", 64'h0000100000000000, 64'h0000000000000001, RNE, 64'h42B0000000000000, 5'b00000);
    run("2^-1030 / 3",    64'h0000100000000000, THREE, RNE, 64'h0000055555555555, UF|NX);
    run("minsub / 3",     64'h0000000000000001, THREE, RNE, ZERO, UF|NX);

    // A quotient past the maximum normal is infinity with OF and NX.  2^600 /
    // 2^-600 pins the exponent width: 12 bits wrap that exponent into the
    // subnormal range, so the register carries 13.
    run("max / 0.5", DBL_MAX, HALF, RNE, INF, OF|NX);
    run("2^600 / 2^-600", 64'h6570000000000000, 64'h1A70000000000000, RNE, INF, OF|NX);
    run("2^600 / 2^600",   64'h6570000000000000, 64'h6570000000000000, RNE, ONE, 5'b00000);

    if (errors != 0) begin
      $fatal(1, "FAIL: %0d of 34 checks disagree with IEEE 754 / RISC-V", errors);
    end
    $display("PASS: all 34 checks agree with IEEE 754 / RISC-V");
    $finish;
  end
endmodule
