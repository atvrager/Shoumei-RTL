// Reproducer: FPCompare mis-orders signed zeros.
//
// Run:  make fpcompare-zeros      (expects FAILURE until the RTL is fixed)
//
// IEEE 754 and RISC-V make +0 and -0 *equal*: FEQ(+0,-0) is 1 and neither is
// less than the other, so FLT(-0,+0) is 0.  FPCompare instead
//   - computes FEQ as bitwise equality of the 32-bit patterns
//     (`feq_raw = ~|(src1 ^ src2)`), which separates +0 from -0, and
//   - derives FLT ordering from "the sign bits differ → the negative operand is
//     smaller", which is right except when both magnitudes are zero.
//
// FLE, and FMIN/FMAX (which *do* order signed zeros specially), are correct.
// Random co-simulation cannot see any of this: LFSR stimulus will not land on a
// signed-zero pair, so a spec written from intent would pass co-simulation while
// being false here.  Hence a directed test.
//
// The fix is in the Lean design (lean/Shoumei/Circuits/Combinational/FPMisc.lean,
// fpCompareCircuit): compare numerically rather than bitwise for equality
// (equal iff patterns are equal, or both are zeros), and treat equal operands as
// "not less" before the sign-differs rule.

module fpcompare_signed_zero;
  logic [31:0] src1, src2;
  logic [4:0]  op;
  logic [31:0] result;
  logic        nv;

  FPCompare dut (.src1(src1), .src2(src2), .op(op), .result(result), .nv(nv));

  localparam FEQ = 5'd9, FLT = 5'd10, FLE = 5'd11, FMIN = 5'd19, FMAX = 5'd20;
  localparam [31:0] POS_ZERO = 32'h00000000;
  localparam [31:0] NEG_ZERO = 32'h80000000;

  int errors = 0;

  task check(input [8*20-1:0] name, input [31:0] a, input [31:0] b,
             input [4:0] o, input [31:0] want, input expected_nv);
    src1 = a; src2 = b; op = o; #1;
    if (result !== want || nv !== expected_nv) begin
      errors++;
      $display("FAIL %-14s a=%08x b=%08x op=%2d -> %08x nv=%b, expected %08x nv=%b",
               name, a, b, o, result, nv, want, expected_nv);
    end else begin
      $display("ok   %-14s -> %08x nv=%b", name, result, nv);
    end
  endtask

  initial begin
    // Equality: +0 and -0 are the same number.
    check("FEQ(+0,-0)", POS_ZERO, NEG_ZERO, FEQ, 32'd1, 1'b0);
    check("FEQ(-0,+0)", NEG_ZERO, POS_ZERO, FEQ, 32'd1, 1'b0);
    check("FEQ(+0,+0)", POS_ZERO, POS_ZERO, FEQ, 32'd1, 1'b0);
    check("FEQ(-0,-0)", NEG_ZERO, NEG_ZERO, FEQ, 32'd1, 1'b0);

    // Ordering: equal operands are not less-than.
    check("FLT(-0,+0)", NEG_ZERO, POS_ZERO, FLT, 32'd0, 1'b0);
    check("FLT(+0,-0)", POS_ZERO, NEG_ZERO, FLT, 32'd0, 1'b0);
    check("FLE(-0,+0)", NEG_ZERO, POS_ZERO, FLE, 32'd1, 1'b0);
    check("FLE(+0,-0)", POS_ZERO, NEG_ZERO, FLE, 32'd1, 1'b0);

    // min/max order signed zeros: min is -0, max is +0, either argument order.
    check("FMIN(+0,-0)", POS_ZERO, NEG_ZERO, FMIN, NEG_ZERO, 1'b0);
    check("FMIN(-0,+0)", NEG_ZERO, POS_ZERO, FMIN, NEG_ZERO, 1'b0);
    check("FMAX(+0,-0)", POS_ZERO, NEG_ZERO, FMAX, POS_ZERO, 1'b0);
    check("FMAX(-0,+0)", NEG_ZERO, POS_ZERO, FMAX, POS_ZERO, 1'b0);

    // $finish does not carry an exit status under Verilator; $fatal does.
    if (errors != 0) begin
      $fatal(1, "FAIL: %0d of 12 checks disagree with IEEE 754", errors);
    end
    $display("PASS: all 12 checks agree with IEEE 754");
    $finish;
  end
endmodule
