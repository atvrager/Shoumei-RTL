// Reproducer: FPDivider (single precision) IEEE-754 conformance.
//
// Run:  make fpdiv-directed
//
// Two defects, both found by asking what an FDIV.S must do and then testing it,
// and both shared with the other single-precision units (their double-precision
// twins were the reference).
//
//  1. It truncated, and ignored rm.  1.0/3.0 returned 3EAAAAAA where nearest-even
//     requires 3EAAAAAB; only the toward-zero result coincided.  The unit now
//     compares the remainder against half the divisor -- 2*rem > divisor is
//     "above half an ulp", and the normalizing shift doubles that weight, so the
//     comparison scales with it -- and decodes all five modes.
//
//  2. It had no special-case handling at all: no NaN, infinity or zero detection
//     anywhere in the unit, and OF/UF/DZ/NV were all `x & ~x`.  1.0/0.0 returned
//     0x7F000000, 0.0/0.0 returned 0x3F800000 -- which is one -- and both raised
//     no flag.  Classification is taken from the latched operands, so the
//     23-cycle protocol is unchanged: a special operand pair now selects a
//     canonical NaN, a signed infinity or a signed zero, and sets NV or DZ.
//
// Still absent: UF and OF cannot assert, because the 8-bit exponent field has
// nowhere to carry the out-of-range information, and an overflowing quotient is
// therefore packed as if finite.  That needs the same widening the multiplier
// needed, and is not exercised below.

module fpdiv_directed;
  logic [31:0] src1, src2; logic [2:0] rm; logic [5:0] dest_tag; logic start;
  logic [31:0] result; logic [5:0] tag_out; logic [4:0] exc; logic valid_out, busy;
  logic clock = 0, reset = 0;

  FPDivider dut (.src1(src1), .src2(src2), .rm(rm), .dest_tag(dest_tag),
                 .start(start), .result(result), .tag_out(tag_out), .exc(exc),
                 .valid_out(valid_out), .busy(busy), .clock(clock), .reset(reset));

  always #5 clock = ~clock;

  int errors = 0;

  task run(input [8*18-1:0] name, input [31:0] a, input [31:0] b, input [2:0] rmode,
           input [31:0] want, input [4:0] want_exc);
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
      $display("FAIL %-18s rm=%b %08x / %08x -> %08x exc=%b, expected %08x exc=%b",
               name, rmode, a, b, result, exc, want, want_exc);
    end else begin
      $display("ok   %-18s rm=%b -> %08x exc=%b", name, rmode, result, exc);
    end
    @(posedge clock);
  endtask

  localparam [2:0] RNE = 3'b000, RTZ = 3'b001, RDN = 3'b010, RUP = 3'b011, RMM = 3'b100;

  localparam [31:0] ONE      = 32'h3F800000;
  localparam [31:0] TWO      = 32'h40000000;
  localparam [31:0] THREE    = 32'h40400000;
  localparam [31:0] SIX      = 32'h40C00000;
  localparam [31:0] NEG_ONE  = 32'hBF800000;
  localparam [31:0] ZERO     = 32'h00000000;
  localparam [31:0] PZERO    = 32'h00000000;
  localparam [31:0] INF      = 32'h7F800000;
  localparam [31:0] NEG_INF  = 32'hFF800000;
  localparam [31:0] QNAN     = 32'h7FC00000;
  localparam [31:0] CANON_NAN= 32'h7FC00000;

  localparam [31:0] MIN_NORM = 32'h00800000;   // 2^-126
  localparam [31:0] MIN_SUB  = 32'h00000001;   // 2^-149
  localparam [31:0] FLT_MAX  = 32'h7F7FFFFF;
  localparam [31:0] HALF     = 32'h3F000000;

  localparam [4:0] NX = 5'b00001, UF = 5'b00010, OF = 5'b00100, DZ = 5'b01000, NV = 5'b10000;

  initial begin
    reset = 1; repeat (3) @(posedge clock); reset = 0; @(posedge clock);

    // exact quotient: no flags
    run("6.0 / 2.0", SIX, TWO, RNE, 32'h40400000, 5'b00000);

    // inexact: every mode must act as specified
    run("1.0 / 3.0 RNE", ONE, THREE, RNE, 32'h3EAAAAAB, NX);
    run("1.0 / 3.0 RTZ", ONE, THREE, RTZ, 32'h3EAAAAAA, NX);
    run("1.0 / 3.0 RDN", ONE, THREE, RDN, 32'h3EAAAAAA, NX);  // positive
    run("1.0 / 3.0 RUP", ONE, THREE, RUP, 32'h3EAAAAAB, NX);
    run("-1.0 / 3.0 RDN", NEG_ONE, THREE, RDN, 32'hBEAAAAAB, NX); // negative: away
    run("-1.0 / 3.0 RUP", NEG_ONE, THREE, RUP, 32'hBEAAAAAA, NX); // negative: toward
    run("2.0 / 3.0 RNE", TWO, THREE, RNE, 32'h3F2AAAAB, NX);

    // special cases: these were wrong values with no flags at all
    run("1.0 / 0.0",   ONE, PZERO, RNE, INF, DZ);
    run("-1.0 / 0.0",  NEG_ONE, PZERO, RNE, NEG_INF, DZ);
    run("0.0 / 0.0",   PZERO, PZERO, RNE, CANON_NAN, NV);
    run("0.0 / 3.0",   PZERO, THREE, RNE, PZERO, 5'b00000);
    run("inf / inf",   INF, INF, RNE, CANON_NAN, NV);
    run("inf / 3.0",   INF, THREE, RNE, INF, 5'b00000);
    run("3.0 / inf",   THREE, INF, RNE, PZERO, 5'b00000);
    // a quiet NaN propagates without a flag; only a signalling one is invalid
    run("qnan / 1.0",  QNAN, ONE, RNE, CANON_NAN, 5'b00000);
    run("snan / 1.0",  32'h7F800001, ONE, RNE, CANON_NAN, NV);

    // Subnormal results: exponent field 0, mantissa counted in multiples of
    // 2^-149.  An exact one raises no flag; an inexact one is tiny, so UF and NX.
    run("min-norm / 2",   MIN_NORM, TWO, RNE, 32'h00400000, 5'b00000);
    run("min-norm / 4",   MIN_NORM, 32'h40800000, RNE, 32'h00200000, 5'b00000);
    run("min-norm / 3",   MIN_NORM, THREE, RNE, 32'h002AAAAB, UF|NX);
    run("min-norm / 3 RTZ", MIN_NORM, THREE, RTZ, 32'h002AAAAA, UF|NX);
    // Subnormal operands.  The restoring division compares and subtracts the two
    // mantissas directly, so a subnormal operand must be normalized first: its
    // fraction is shifted up to the implicit position and its exponent field
    // lowered by that shift, which puts the mantissa in [1, 2) without changing
    // the value.
    run("minsub / 1",     MIN_SUB, ONE, RNE, 32'h00000001, 5'b00000);
    run("1 / minsub",     ONE, MIN_SUB, RNE, INF, OF|NX);
    run("minsub / minsub", MIN_SUB, MIN_SUB, RNE, ONE, 5'b00000);
    run("1 / 2^-126",     ONE, MIN_NORM, RNE, 32'h7E800000, 5'b00000);
    run("2^-100 / 2^-140", 32'h0D800000, 32'h00000200, RNE, 32'h53800000, 5'b00000);
    run("2^-140 / 2^-100", 32'h00000200, 32'h0D800000, RNE, 32'h2B800000, 5'b00000);
    run("minsub / 3",     MIN_SUB, THREE, RNE, PZERO, UF|NX);
    run("2^-140 / 3",     32'h00000200, THREE, RNE, 32'h000000AB, UF|NX);

    // A quotient past the maximum normal is infinity with OF and NX.
    run("max / 0.5",      FLT_MAX, HALF, RNE, INF, OF|NX);
    // 2^100 / 2^-100 = 2^200 pins the exponent width: the quotient exponent
    // spans -254..381, so the register carries ten bits, not eight.
    run("2^100 / 2^-100", 32'h71800000, 32'h0D800000, RNE, INF, OF|NX);
    run("2^100 / 2^100",  32'h71800000, 32'h71800000, RNE, ONE, 5'b00000);

    if (errors != 0) begin
      $fatal(1, "FAIL: %0d of 32 checks disagree with IEEE 754 / RISC-V", errors);
    end
    $display("PASS: all 32 checks agree with IEEE 754 / RISC-V");
    $finish;
  end
endmodule
