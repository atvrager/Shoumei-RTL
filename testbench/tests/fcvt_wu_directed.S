/*
 * fcvt_wu_directed.S - FCVT.WU.D of negative and tiny magnitudes.
 *
 * The conversion is unsigned, so a negative input is never representable.  The
 * rounded result is a nonzero negative when the rounded magnitude is not zero,
 * which raises NV and clips to 0; a magnitude below 0.5 under rne or rmm rounds
 * to zero, which is representable, so the result is 0 with no flag.
 *
 * rand_0028 showed fcvt.wu.d of -0.1 returning 1 where the reference returns 0,
 * with funct3 = 4 (rmm).  These cases vary the sign, the magnitude and the
 * rounding mode.  NaN is deliberately absent here and covered by
 * testbench/riscv-tests/rv64ud-p-fcvt_w.elf, whose case at PC 0x7f8 is
 * fcvt.wu.d of the negative NaN 0xffffffffffffffff and expects all ones.
 *
 * The destination is an integer register, which the lock-step cosim compares
 * directly; fflags is read into t2, which it also compares.
 */
    .section .text

.macro FLD64 freg, pat
    li       t0, \pat
    fmv.d.x  \freg, t0
.endm

/* Set the rounding mode and clear fflags, so each case's flags stand alone. */
.macro SETRM rm
    li       t0, (\rm << 5)
    csrw     fcsr, t0
.endm

    .globl _start
    .globl main
_start:
main:
    FLD64    f31, 0xBFB999999999999A     /* -0.1 */
    SETRM    0
    fcvt.wu.d x9, f31
    csrr     t2, fflags

    FLD64    f31, 0xBFB999999999999A     /* -0.1, rmm */
    SETRM    4
    fcvt.wu.d x10, f31
    csrr     t2, fflags

    FLD64    f31, 0xBFB999999999999A     /* -0.1, rdn */
    SETRM    2
    fcvt.wu.d x11, f31
    csrr     t2, fflags

    FLD64    f31, 0xBFE3333333333333     /* -0.6 */
    SETRM    0
    fcvt.wu.d x12, f31
    csrr     t2, fflags

    FLD64    f31, 0x3FE0000000000000     /* +0.5 */
    SETRM    0
    fcvt.wu.d x13, f31
    csrr     t2, fflags

    FLD64    f31, 0x3FE0000000000000     /* +0.5, rmm */
    SETRM    4
    fcvt.wu.d x14, f31
    csrr     t2, fflags

    FLD64    f31, 0xBFF8000000000000     /* -1.5 */
    SETRM    0
    fcvt.wu.d x15, f31
    csrr     t2, fflags

    /* Static rounding mode in the instruction against a different fcsr value:
       rtz (1) must truncate 0.5 to 0 even though fcsr holds rup (3). */
    FLD64    f31, 0x3FE0000000000000     /* +0.5 */
    SETRM    3
    fcvt.wu.d x20, f31, rtz
    csrr     t2, fflags

    FLD64    f31, 0x3FE0000000000000     /* +0.5 */
    SETRM    0
    fcvt.wu.d x21, f31, rmm
    csrr     t2, fflags

/* Straight-line done.  Signal completion the way the other ASM tests do. */
    li       a1, 0x1000
    li       a2, 1
    sw       a2, 0(a1)
.Lhalt:
    j        .Lhalt
