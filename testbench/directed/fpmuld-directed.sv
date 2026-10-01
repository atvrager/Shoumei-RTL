// Reproducer: FPMultiplierD (double precision) IEEE-754 conformance.
//
// Run:  make fpmuld-directed
//
// The unit packed every product as a normal number: a product below the minimum
// normal took the normal path, whose exponent field then read 0 with an
// unnormalized mantissa, so DBL_MIN * 0.5 came out 0.  A product whose biased
// exponent is 0 or less now selects a subnormal pack -- exponent field 0 and a
// mantissa counted in multiples of 2^-1074 -- and UF needs a tiny *and* inexact
// result, where tiny is the rounded exponent.
//
// The window is the normalized mantissa with the implicit one at 55, the
// fraction at [54:3] and guard/round/sticky at [2:0]; the subnormal path shifts
// it down by (4 - E) and the shifted-out bits feed the sticky, so every rounding
// mode still decides correctly.  Rounding may carry the mantissa up into the
// smallest normal, which flips the exponent field to 1.
//
// Still wrong, and not exercised here: a *subnormal operand*.  Its fraction
// would have to be normalized (leading-zero count plus a shift) before the
// partial-product tree, and that is not implemented.
//
// Random co-simulation cannot find this: an LFSR will not land a product in the
// subnormal range.

module fpmuld_directed;
  logic [63:0] src1, src2; logic [2:0] rm; logic [5:0] dest_tag; logic valid_in;
  logic [63:0] result; logic [5:0] tag_out; logic [4:0] exc; logic valid_out;
  logic clock = 0, reset = 0;

  FPMultiplierD dut (.src1(src1), .src2(src2), .rm(rm), .dest_tag(dest_tag),
                     .valid_in(valid_in), .result(result), .tag_out(tag_out),
                     .exc(exc), .valid_out(valid_out), .clock(clock), .reset(reset));

  always #5 clock = ~clock;

  int errors = 0;

  task run(input [8*18-1:0] name, input [63:0] a, input [63:0] b, input [2:0] rmode,
           input [63:0] want, input [4:0] want_exc);
    int guard;
    src1 = a; src2 = b; rm = rmode; dest_tag = 6'd0; valid_in = 1'b1;
    @(posedge clock);
    valid_in = 1'b0;
    guard = 0;
    while (!valid_out && guard < 40) begin
      @(posedge clock);
      guard++;
    end
    if (result !== want || exc !== want_exc) begin
      errors++;
      $display("FAIL %-18s rm=%b %016x x %016x -> %016x exc=%b, expected %016x exc=%b",
               name, rmode, a, b, result, exc, want, want_exc);
    end else begin
      $display("ok   %-18s rm=%b -> %016x exc=%b", name, rmode, result, exc);
    end
    @(posedge clock);
  endtask

  localparam [2:0] RNE = 3'b000, RTZ = 3'b001, RDN = 3'b010, RUP = 3'b011, RMM = 3'b100;

  localparam [63:0] MIN_NORM = 64'h0010000000000000;   // 2^-1022
  localparam [63:0] HALF     = 64'h3FE0000000000000;
  localparam [63:0] QUARTER  = 64'h3FD0000000000000;
  localparam [63:0] THREEQ   = 64'h3FE8000000000000;
  localparam [63:0] P6       = 64'h3FE3333333333333;   // 0.6
  localparam [63:0] TINY     = 64'h1A70000000000000;   // 2^-600
  localparam [63:0] ONE      = 64'h3FF0000000000000;
  localparam [63:0] DBL_MAX  = 64'h7FEFFFFFFFFFFFFF;
  localparam [63:0] INF      = 64'h7FF0000000000000;
  localparam [63:0] ZERO     = 64'h0000000000000000;

  localparam [4:0] NX = 5'b00001, UF = 5'b00010, OF = 5'b00100;

  initial begin
    reset = 1; repeat (3) @(posedge clock); reset = 0; @(posedge clock);

    run("min-norm x 0.5",   MIN_NORM, HALF,    RNE, 64'h0008000000000000, 5'b00000);
    run("min-norm x 0.25",  MIN_NORM, QUARTER, RNE, 64'h0004000000000000, 5'b00000);
    run("min-norm x 0.75",  MIN_NORM, THREEQ,  RNE, 64'h000C000000000000, 5'b00000);

    // The exact product is (2^51 + 0.5) quanta: a tie, so nearest-even keeps the
    // even mantissa and toward zero truncates.
    run("min-norm x 0.6 RNE", MIN_NORM, P6, RNE, 64'h000999999999999A, UF|NX);
    run("min-norm x 0.6 RTZ", MIN_NORM, P6, RTZ, 64'h0009999999999999, UF|NX);
    run("min-norm x 0.6 RMM", MIN_NORM, P6, RMM, 64'h000999999999999A, UF|NX);

    // 1.5*2^-512 squared = 2.25*2^-1024: the product's leading one sits at bit
    // 105, so the one-bit normalization shift fires as well as the subnormal one.
    run("1.5*2^-512 squared", 64'h1FF8000000000000, 64'h1FF8000000000000, RNE,
        64'h0009000000000000, 5'b00000);

    // ── Subnormal operands ─────────────────────────────────────────────────
    // A nonzero subnormal has no implicit bit, so its fraction is normalized and
    // its exponent lowered by the shift before the product tree.
    run("minsub x 1",      64'h0000000000000001, ONE,   RNE, 64'h0000000000000001, 5'b00000);
    run("minsub x 2",      64'h0000000000000001, 64'h4000000000000000, RNE, 64'h0000000000000002, 5'b00000);
    run("minsub x 0.5",    64'h0000000000000001, HALF,  RNE, ZERO, UF|NX);
    run("2^-1030 x 2^-30", 64'h0000100000000000, 64'h3E10000000000000, RNE, 64'h0000000000004000, 5'b00000);
    run("2^-1030 x 2^500", 64'h0000100000000000, 64'h5F30000000000000, RNE, 64'h1ED0000000000000, 5'b00000);

    // far below the quantum: zero, tiny and inexact
    run("2^-600 squared", TINY, TINY, RNE, ZERO, UF|NX);

    // a saturated product is infinity
    run("max x 2.0", DBL_MAX, 64'h4000000000000000, RNE, INF, OF|NX);

    // an exact product raises nothing
    run("1.5 x 2.0", 64'h3FF8000000000000, 64'h4000000000000000, RNE,
        64'h4008000000000000, 5'b00000);

    if (errors != 0) begin
      $fatal(1, "FAIL: %0d of 15 checks disagree with IEEE 754 / RISC-V", errors);
    end
    $display("PASS: all 15 checks agree with IEEE 754 / RISC-V");
    $finish;
  end
endmodule
