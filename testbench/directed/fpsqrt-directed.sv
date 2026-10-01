// Reproducer: FPSqrt (single precision) IEEE-754 conformance.
//
// Run:  make fpsqrt-directed
//
// One defect, found the same way as the others: rm was ignored, so every mode
// behaved as round-to-nearest-even.  `round_up = guard` and the comment beside it
// said so ("For RNE: round_up = guard"), with no mode decode at all.  All five are
// decoded now; a square root is never negative, so rounding down is truncation and
// "any remainder at all" drives rounding up.
//
// Everything else here was already right, which is worth stating because the
// single-precision units are otherwise the degraded twins of their double-
// precision counterparts: values, sqrt of a negative (canonical NaN with NV),
// infinity, zero, and the quiet/signaling NaN distinction on NV -- sqrt raises
// invalid only for a *signaling* NaN input, not for a quiet one.
//
// The expectations below are computed, not eyeballed: sqrt(2.0) rounds to
// 3FB504F3 at nearest-even *and* toward zero, because the exact value sits above
// that float but below the midpoint to the next one.  A discriminating case needs
// a value above a midpoint, e.g. sqrt(0x3F003000).

module fpsqrt_directed;
  logic [31:0] src1; logic [2:0] rm; logic [5:0] dest_tag; logic start;
  logic [31:0] result; logic [5:0] tag_out; logic [4:0] exc; logic valid_out, busy;
  logic clock = 0, reset = 0;

  FPSqrt dut (.src1(src1), .rm(rm), .dest_tag(dest_tag), .start(start),
              .result(result), .tag_out(tag_out), .exc(exc), .valid_out(valid_out),
              .busy(busy), .clock(clock), .reset(reset));

  always #5 clock = ~clock;

  int errors = 0;

  task run(input [8*18-1:0] name, input [31:0] a, input [2:0] rmode,
           input [31:0] want, input [4:0] want_exc);
    int guard;
    src1 = a; rm = rmode; dest_tag = 6'd0; start = 1'b1;
    @(posedge clock);
    start = 1'b0;
    guard = 0;
    while (!valid_out && guard < 200) begin
      @(posedge clock);
      guard++;
    end
    if (result !== want || exc !== want_exc) begin
      errors++;
      $display("FAIL %-16s rm=%b %08x -> %08x exc=%b, expected %08x exc=%b",
               name, rmode, a, result, exc, want, want_exc);
    end else begin
      $display("ok   %-16s rm=%b -> %08x exc=%b", name, rmode, result, exc);
    end
    @(posedge clock);
  endtask

  localparam [2:0] RNE = 3'b000, RTZ = 3'b001, RDN = 3'b010, RUP = 3'b011, RMM = 3'b100;

  localparam [31:0] FOUR      = 32'h40800000;
  localparam [31:0] TWO       = 32'h40000000;
  localparam [31:0] NINE      = 32'h41100000;
  localparam [31:0] QUARTER   = 32'h3E800000;   // 0.25
  localparam [31:0] ZERO      = 32'h00000000;
  localparam [31:0] NEG_ONE   = 32'hBF800000;
  localparam [31:0] INF       = 32'h7F800000;
  localparam [31:0] QNAN      = 32'h7FC00000;
  localparam [31:0] SNAN      = 32'h7F800001;
  localparam [31:0] CANON_NAN = 32'h7FC00000;
  // 0x3F003000: sqrt is above a midpoint, so nearest-even and toward-zero differ
  localparam [31:0] MID       = 32'h3F003000;

  localparam [4:0] NX = 5'b00001, NV = 5'b10000;

  initial begin
    reset = 1; repeat (3) @(posedge clock); reset = 0; @(posedge clock);

    // exact roots: no flags
    run("sqrt(4.0)",    FOUR,    RNE, 32'h40000000, 5'b00000);
    run("sqrt(9.0)",    NINE,    RNE, 32'h40400000, 5'b00000);
    run("sqrt(0.25)",   QUARTER, RNE, 32'h3F000000, 5'b00000);
    run("sqrt(0.0)",    ZERO,    RNE, ZERO,         5'b00000);

    // sqrt(2.0): nearest-even and toward-zero agree here -- both 3FB504F3
    run("sqrt(2.0) RNE", TWO, RNE, 32'h3FB504F3, NX);
    run("sqrt(2.0) RTZ", TWO, RTZ, 32'h3FB504F3, NX);

    // a case that does discriminate between the modes
    run("mid RNE", MID, RNE, 32'h3F3526E1, NX);
    run("mid RTZ", MID, RTZ, 32'h3F3526E0, NX);
    run("mid RDN", MID, RDN, 32'h3F3526E0, NX);   // positive: toward -inf
    run("mid RUP", MID, RUP, 32'h3F3526E1, NX);   // positive: toward +inf
    run("mid RMM", MID, RMM, 32'h3F3526E1, NX);

    // special cases
    run("sqrt(-1.0)", NEG_ONE, RNE, CANON_NAN, NV);
    run("sqrt(+inf)", INF,     RNE, INF,       5'b00000);
    run("sqrt(qnan)", QNAN,    RNE, CANON_NAN, 5'b00000);  // quiet NaN: no NV
    run("sqrt(snan)", SNAN,    RNE, CANON_NAN, NV);        // signaling NaN: NV

    if (errors != 0) begin
      $fatal(1, "FAIL: %0d of 15 checks disagree with IEEE 754 / RISC-V", errors);
    end
    $display("PASS: all 15 checks agree with IEEE 754 / RISC-V");
    $finish;
  end
endmodule
