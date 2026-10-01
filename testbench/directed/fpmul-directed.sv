// Reproducer: FPMultiplier (single precision) IEEE-754 conformance.
//
// Run:  make fpmul-directed
//
// Three defects, all found by asking what an FMUL.S must do and then testing it.
// The double-precision twin had each of them right, so it is the reference.
//
//  1. The normal path truncated.  The 48-bit product was cut to 23 mantissa bits
//     with the remainder dropped, and the rounding logic existed only on the
//     subnormal path (selected by s2_has_subnorm), so every inexact FMUL.S was
//     wrong by up to one ulp: 3.0 x 0.1 gave 3E999999 instead of 3E99999A.
//
//  2. `rm` was ignored outright — the subnormal path hardcoded round-to-nearest-
//     even.  All five modes are decoded now, with the sign-dependent increments.
//
//  3. OF and UF could never assert (they were `rm[i] & ~rm[i]`), and there was no
//     overflow or underflow handling at all: a product that overflowed was
//     packed as if finite, and one that underflowed likewise.  A saturated
//     product is now infinity and an underflowed one zero, as FPMultiplierD does.
//
// The exponent field also had to widen from 9 to 10 bits: the product exponent
// ranges over -125..381, so bit 8 could not separate "below the minimum normal"
// from "above the maximum", and overflow would have been misread as underflow.
//
//  4. A product that lands in the subnormal range was flushed to zero.  The
//     subnormal path only ran when an *operand* was subnormal, so a small
//     product of two normal operands (FLT_MIN x 0.5) took the normal path and
//     came out 0.  A result whose biased exponent is 0 or less now selects a
//     subnormal pack: the normalized product is shifted down by (25 - E), guard
//     and round survive the shift, and the shifter's sticky carries the
//     remainder into the round-up decision and NX.  UF now needs a tiny *and*
//     inexact result, so an exact subnormal raises neither flag.
//
// Random co-simulation cannot find any of this: an LFSR will not produce a
// product that needs a rounding decision, nor saturate an exponent.

module fpmul_directed;
  logic [31:0] src1, src2; logic [2:0] rm; logic [5:0] dest_tag; logic valid_in;
  logic [31:0] result; logic [5:0] tag_out; logic [4:0] exc; logic valid_out;
  logic clock = 0, reset = 0;

  FPMultiplier dut (.src1(src1), .src2(src2), .rm(rm), .dest_tag(dest_tag),
                    .valid_in(valid_in), .result(result), .tag_out(tag_out),
                    .exc(exc), .valid_out(valid_out), .clock(clock), .reset(reset));

  always #5 clock = ~clock;

  int errors = 0;

  task run(input [8*18-1:0] name, input [31:0] a, input [31:0] b, input [2:0] rmode,
           input [31:0] want, input [4:0] want_exc);
    int guard;
    src1 = a; src2 = b; rm = rmode; dest_tag = 6'd0; valid_in = 1'b1;
    @(posedge clock);
    valid_in = 1'b0;
    guard = 0;
    while (!valid_out && guard < 30) begin
      @(posedge clock);
      guard++;
    end
    if (result !== want || exc !== want_exc) begin
      errors++;
      $display("FAIL %-18s rm=%b %08x x %08x -> %08x exc=%b, expected %08x exc=%b",
               name, rmode, a, b, result, exc, want, want_exc);
    end else begin
      $display("ok   %-18s rm=%b -> %08x exc=%b", name, rmode, result, exc);
    end
    @(posedge clock);
  endtask

  localparam [2:0] RNE = 3'b000, RTZ = 3'b001, RDN = 3'b010, RUP = 3'b011, RMM = 3'b100;

  localparam [31:0] F2       = 32'h40000000;
  localparam [31:0] F3       = 32'h40400000;
  localparam [31:0] NEG_F3   = 32'hC0400000;
  localparam [31:0] P01      = 32'h3DCCCCCD;   // 0.1
  localparam [31:0] F15      = 32'h3FC00000;
  localparam [31:0] M1000001 = 32'h3F800001;
  localparam [31:0] F7       = 32'h40E00000;
  localparam [31:0] F13      = 32'h3EAAAAAB;   // 1/3
  localparam [31:0] FLT_MAX  = 32'h7F7FFFFF;
  localparam [31:0] TINY     = 32'h0D800000;   // 2^-100
  localparam [31:0] MIN_NORM = 32'h00800000;   // 2^-126
  localparam [31:0] QNAN     = 32'h7FC00000;
  localparam [31:0] SNAN     = 32'h7F800001;
  localparam [31:0] CANON_NAN= 32'h7FC00000;
  localparam [31:0] INF      = 32'h7F800000;
  localparam [31:0] ZERO     = 32'h00000000;

  localparam [4:0] NX = 5'b00001, UF = 5'b00010, OF = 5'b00100, NV = 5'b10000;

  initial begin
    reset = 1; repeat (3) @(posedge clock); reset = 0; @(posedge clock);

    // exact product: no flags
    run("2.0 x 3.0", F2, F3, RNE, 32'h40C00000, 5'b00000);

    // 3.0 x 0.1 needs a rounding decision: every mode must differ as specified
    run("3.0 x 0.1 RNE",  F3, P01, RNE, 32'h3E99999A, NX);
    run("3.0 x 0.1 RTZ",  F3, P01, RTZ, 32'h3E999999, NX);
    run("3.0 x 0.1 RDN",  F3, P01, RDN, 32'h3E999999, NX);  // positive: toward zero
    run("3.0 x 0.1 RUP",  F3, P01, RUP, 32'h3E99999A, NX);  // positive: away
    run("3.0 x 0.1 RMM",  F3, P01, RMM, 32'h3E99999A, NX);
    run("-3.0 x 0.1 RDN", NEG_F3, P01, RDN, 32'hBE99999A, NX); // negative: away
    run("-3.0 x 0.1 RUP", NEG_F3, P01, RUP, 32'hBE999999, NX); // negative: toward zero

    // other inexact products, at nearest-even
    run("1.5 x 1.0000001", F15, M1000001, RNE, 32'h3FC00002, NX);
    run("7.0 x 1/3",       F7, F13, RNE, 32'h40155556, NX);

    // a saturated product is infinity, an underflowed one is zero
    run("max x 2.0",  FLT_MAX, F2, RNE, INF, OF|NX);
    run("2^-100 squared", TINY, TINY, RNE, ZERO, UF|NX);

    // a product that lands in the subnormal range is representable and exact;
    // it must be formed, not flushed to zero, and must raise no flag
    run("min-normal x 0.5",  MIN_NORM, 32'h3F000000, RNE, 32'h00400000, 5'b00000);
    run("min-normal x 0.75", MIN_NORM, 32'h3F400000, RNE, 32'h00600000, 5'b00000);
    run("min-normal x 0.25", MIN_NORM, 32'h3E800000, RNE, 32'h00200000, 5'b00000);
    run("2^-127 x 1.0",      32'h00400000, 32'h3F800000, RNE, 32'h00400000, 5'b00000);

    // Subnormal *operands*.  A subnormal has no implicit bit, so its fraction is
    // shifted up to the implicit position and its exponent lowered by that
    // shift before the partial-product tree sees it.
    run("minsub x 1.0",  32'h00000001, 32'h3F800000, RNE, 32'h00000001, 5'b00000);
    run("1.0 x minsub",  32'h3F800000, 32'h00000001, RNE, 32'h00000001, 5'b00000);
    run("minsub x 2.0",  32'h00000001, 32'h40000000, RNE, 32'h00000002, 5'b00000);
    run("minsub x 0.5",  32'h00000001, 32'h3F000000, RNE, ZERO, UF|NX);
    run("2^-60 x 2^-80", 32'h21800000, 32'h17800000, RNE, 32'h00000200, 5'b00000);

    // A quiet NaN propagates as the canonical NaN and raises nothing; only a
    // signaling NaN raises NV.
    run("qnan x 1.0", QNAN, 32'h3F800000, RNE, CANON_NAN, 5'b00000);
    run("1.0 x qnan", 32'h3F800000, QNAN, RNE, CANON_NAN, 5'b00000);
    run("snan x 1.0", SNAN, 32'h3F800000, RNE, CANON_NAN, NV);

    if (errors != 0) begin
      $fatal(1, "FAIL: %0d of 20 checks disagree with IEEE 754 / RISC-V", errors);
    end
    $display("PASS: all 20 checks agree with IEEE 754 / RISC-V");
    $finish;
  end
endmodule
