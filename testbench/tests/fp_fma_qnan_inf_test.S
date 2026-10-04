/*
 * fp_fma_qnan_inf_test.S - FMA with quiet NaN and infinity operands.
 *
 * IEEE 754-2008 and RISC-V specify that a quiet NaN operand in FMA
 * propagates quietly without signaling invalid operation (NV), even
 * when another product operand is infinity and the addend is infinity
 * with opposing sign.
 *
 * Case 1: fnmadd.d with qNaN, -inf, +inf (the shape from rand_0000).
 *         Must produce qNaN and must NOT set NV (fflags == 0).
 * Case 2: fmadd.s with single-precision qNaN, +inf, -inf.
 *         Must produce qNaN and must NOT set NV (fflags == 0).
 * Case 3: fmadd.d with 0.0 * inf + 1.0.
 *         Must set NV (fflags == 0x10).
 * Case 4: fmadd.d with (+inf * 1.0) + (-inf).
 *         Must set NV (fflags == 0x10).
 */

#define TOHOST 0x1000
#define FFLAGS_NV 0x10

.section .text
.globl _start
_start:
    /* Case 1: DP fnmadd with qNaN * (-inf) - (+inf) */
    csrw    fflags, x0
    li      t0, 0x7ff8000000000000   /* DP qNaN */
    fmv.d.x f1, t0
    li      t0, 0xfff0000000000000   /* -inf */
    fmv.d.x f2, t0
    li      t0, 0x7ff0000000000000   /* +inf */
    fmv.d.x f3, t0

    fnmadd.d f4, f1, f2, f3
    frflags x21
    bnez    x21, fail

    /* Case 2: SP fmadd with qNaN * (+inf) + (-inf) */
    csrw    fflags, x0
    li      t0, 0x7fc00000           /* SP qNaN */
    fmv.w.x f5, t0
    li      t0, 0x7f800000           /* SP +inf */
    fmv.w.x f6, t0
    li      t0, 0xff800000           /* SP -inf */
    fmv.w.x f7, t0

    fmadd.s f8, f5, f6, f7
    frflags x21
    bnez    x21, fail

    /* Case 3: 0.0 * inf + 1.0 must signal NV */
    csrw    fflags, x0
    fcvt.d.w f9, x0                  /* 0.0 */
    fmadd.d f10, f9, f3, f3
    frflags x21
    li      t2, FFLAGS_NV
    bne     x21, t2, fail

    /* Case 4: inf * 1.0 - inf must signal NV */
    csrw    fflags, x0
    li      t0, 0x3ff0000000000000   /* 1.0 */
    fmv.d.x f12, t0
    fmsub.d f13, f3, f12, f3         /* +inf * 1.0 - (+inf) */
    frflags x21
    li      t2, FFLAGS_NV
    bne     x21, t2, fail

    li      t0, TOHOST
    li      t1, 1
    sw      t1, 0(t0)
.Lpass:
    j       .Lpass

fail:
    li      t0, TOHOST
    li      t1, 2
    sw      t1, 0(t0)
.Lfail:
    j       .Lfail
