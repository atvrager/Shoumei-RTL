// Reproducer: FPFMA (single precision) fused multiply-add conformance.
//
// Run:  make fpfma-directed
//
// The unit chained FPMultiplier into FPAdder: the product was rounded to single
// precision before the addend was aligned, and the multiplier's exception flags
// were dropped.  With a = 1+2^-23, b = 1-2^-24, c = -1 the exact product is
// 1 + 2^-24 - 2^-47, which rounds to 1.0 before the add, so the chain returned 0
// where a fused unit returns 0x337FFFFE; and 0*inf + 1 raised no NV.
//
// The fused unit forms the exact 48-bit product, aligns it against the addend in
// a 52-bit window (bit 50 carries the anchor's leading one), adds or subtracts,
// and rounds once.  Its geometry is the one checked in
// verification/fma_reference.py, which also produced the expectations below.

module fpfma_directed;
  logic [31:0] src1, src2, src3; logic [2:0] rm; logic [5:0] dest_tag;
  logic negate_product, subtract_addend, valid_in;
  logic [31:0] result; logic [5:0] tag_out; logic [4:0] exc; logic valid_out;
  logic clock = 0, reset = 0;

  FPFMA dut (.src1(src1), .src2(src2), .src3(src3), .rm(rm), .dest_tag(dest_tag),
             .negate_product(negate_product), .subtract_addend(subtract_addend),
             .valid_in(valid_in), .result(result), .tag_out(tag_out), .exc(exc),
             .valid_out(valid_out), .clock(clock), .reset(reset), .zero(1'b0));

  always #5 clock = ~clock;

  int errors = 0;

  task run(input [8*22-1:0] name, input [31:0] a, input [31:0] b, input [31:0] c,
           input [2:0] rmode, input neg, input sub,
           input [31:0] want, input [4:0] want_exc);
    int guard;
    src1 = a; src2 = b; src3 = c; rm = rmode; dest_tag = 6'd0;
    negate_product = neg; subtract_addend = sub; valid_in = 1'b1;
    @(posedge clock);
    valid_in = 1'b0;
    guard = 0;
    while (!valid_out && guard < 30) begin
      @(posedge clock);
      guard++;
    end
    if (result !== want || exc !== want_exc) begin
      errors++;
      $display("FAIL %-22s rm=%b %08x * %08x + %08x -> %08x exc=%b, expected %08x exc=%b",
               name, rmode, a, b, c, result, exc, want, want_exc);
    end else begin
      $display("ok   %-22s rm=%b -> %08x exc=%b", name, rmode, result, exc);
    end
    @(posedge clock);
  endtask

  initial begin
    reset = 1; repeat (3) @(posedge clock); reset = 0; @(posedge clock);

    run("fusion a*b-1          ", 32'h3F800001, 32'h3F7FFFFF, 32'hBF800000, 0, 0, 0, 32'h337FFFFE, 5'b00000);
    run("fusion fmsub          ", 32'h3F800001, 32'h3F7FFFFF, 32'hBF800000, 0, 0, 1, 32'h40000000, 5'b00001);
    run("fusion fnmadd         ", 32'h3F800001, 32'h3F7FFFFF, 32'hBF800000, 0, 1, 0, 32'hC0000000, 5'b00001);
    run("fusion fnmsub         ", 32'h3F800001, 32'h3F7FFFFF, 32'hBF800000, 0, 1, 1, 32'hB37FFFFE, 5'b00000);
    run("0*inf+1 invalid       ", 32'h00000000, 32'h7F800000, 32'h3F800000, 0, 0, 0, 32'h7FC00000, 5'b10000);
    run("inf*1-inf invalid     ", 32'h7F800000, 32'h3F800000, 32'hFF800000, 0, 0, 0, 32'h7FC00000, 5'b10000);
    run("qnan+1                ", 32'h7FC00000, 32'h3F800000, 32'h3F800000, 0, 0, 0, 32'h7FC00000, 5'b00000);
    run("snan*1+0              ", 32'h7F800001, 32'h3F800000, 32'h00000000, 0, 0, 0, 32'h7FC00000, 5'b10000);
    run("1*1-2^-30 RTZ         ", 32'h3F800000, 32'h3F800000, 32'hB0400000, 1, 0, 0, 32'h3F7FFFFF, 5'b00001);
    run("1*1-2^-30 RDN         ", 32'h3F800000, 32'h3F800000, 32'hB0400000, 2, 0, 0, 32'h3F7FFFFF, 5'b00001);
    run("1*1-2^-30 RNE         ", 32'h3F800000, 32'h3F800000, 32'hB0400000, 0, 0, 0, 32'h3F800000, 5'b00001);
    run("tie +2^-24 RNE        ", 32'h3F800000, 32'h3F800000, 32'h33800000, 0, 0, 0, 32'h3F800000, 5'b00001);
    run("tie +2^-24 RUP        ", 32'h3F800000, 32'h3F800000, 32'h33800000, 3, 0, 0, 32'h3F800001, 5'b00001);
    run("tie +2^-24 RTZ        ", 32'h3F800000, 32'h3F800000, 32'h33800000, 1, 0, 0, 32'h3F800000, 5'b00001);
    run("tie +2^-24 RMM        ", 32'h3F800000, 32'h3F800000, 32'h33800000, 4, 0, 0, 32'h3F800001, 5'b00001);
    run("minsub*1+0            ", 32'h00000001, 32'h3F800000, 32'h00000000, 0, 0, 0, 32'h00000001, 5'b00000);
    run("minsub*0.5+0          ", 32'h00000001, 32'h3F000000, 32'h00000000, 0, 0, 0, 32'h00000000, 5'b00011);
    run("1*1+(-0) RNE          ", 32'h3F800000, 32'h3F800000, 32'h80000000, 0, 0, 0, 32'h3F800000, 5'b00000);
    run("1*1+(-0) RDN          ", 32'h3F800000, 32'h3F800000, 32'h80000000, 2, 0, 0, 32'h3F800000, 5'b00000);
    run("max*2+0 overflow      ", 32'h7F7FFFFF, 32'h40000000, 32'h00000000, 0, 0, 0, 32'h7F800000, 5'b00101);
    run("inf*1+0               ", 32'h7F800000, 32'h3F800000, 32'h00000000, 0, 0, 0, 32'h7F800000, 5'b00000);
    run("1*1+inf               ", 32'h3F800000, 32'h3F800000, 32'h7F800000, 0, 0, 0, 32'h7F800000, 5'b00000);
    run("1*1-1 cancel RNE      ", 32'h3F800000, 32'h3F800000, 32'hBF800000, 0, 0, 0, 32'h00000000, 5'b00000);
    run("1*1-1 cancel RDN      ", 32'h3F800000, 32'h3F800000, 32'hBF800000, 2, 0, 0, 32'h80000000, 5'b00000);
    run("3*0.1 RNE             ", 32'h40400000, 32'h3DCCCCCD, 32'h00000000, 0, 0, 0, 32'h3E99999A, 5'b00001);
    run("1.5*1.5-2.25 exact    ", 32'h3FC00000, 32'h3FC00000, 32'hC0100000, 0, 0, 0, 32'h00000000, 5'b00000);
    run("1*1-2^-24 RUP         ", 32'h3F800000, 32'h3F800000, 32'hB3800000, 3, 0, 0, 32'h3F7FFFFF, 5'b00000);
    // The addend outweighs the product, so the product must shift right; an
    // alignment error shows up here as a scaled product.  -0.1 * 1 - 2 = -2.1.
    run("addend>>product fmsub ", 32'hBDCCCCCD, 32'h3F800000, 32'h40000000, 0, 0, 1, 32'hC0066666, 5'b00001);
    run("gap3 addend big       ", 32'hBDCCCCCD, 32'h3F800000, 32'h41000000, 0, 0, 1, 32'hC101999A, 5'b00001);

    if (errors != 0) begin
      $fatal(1, "FAIL: %0d of 29 checks disagree with IEEE 754 / RISC-V", errors);
    end
    $display("PASS: all 29 checks agree with IEEE 754 / RISC-V");
    $finish;
  end
endmodule
