/*
 * fp_subnormal_flags.S - flags for exact subnormal results.
 *
 * DBL_MIN / 2 is the subnormal 0x0008000000000000, computed exactly.  An exact
 * result raises no flag, so fcsr must read 0 after each case.  A unit that flushes
 * the subnormal to zero, or treats it as inexact, raises NX and UF.
 */
    .section .text
.macro CLEARFCSR
    csrw     fcsr, zero
.endm
.macro CHECKFCSR reg
    csrr     \reg, fcsr
.endm
    .globl _start
    .globl main
_start:
main:
    /* fdiv.d: DBL_MIN / 2 -> exact subnormal */
    li       t0, 0x0010000000000000
    fmv.d.x  f1, t0
    li       t1, 0x4000000000000000      /* 2.0 */
    fmv.d.x  f2, t1
    CLEARFCSR
    fdiv.d   f3, f1, f2
    CHECKFCSR x18

    /* fmul.d: DBL_MIN * 0.5 -> exact subnormal */
    li       t1, 0x3FE0000000000000      /* 0.5 */
    fmv.d.x  f2, t1
    CLEARFCSR
    fmul.d   f4, f1, f2
    CHECKFCSR x19

    /* fsub.d: 3 * DBL_MIN / 2 - DBL_MIN = DBL_MIN / 2, exact */
    li       t1, 0x0008000000000000      /* DBL_MIN / 2 */
    fmv.d.x  f5, t1
    li       t2, 0x3FF0000000000000      /* 1.0 */
    fmv.d.x  f6, t2
    CLEARFCSR
    fadd.d   f7, f1, f5
    CHECKFCSR x20
    fsub.d   f8, f7, f1
    CHECKFCSR x21

    /* fmadd.d: DBL_MIN / 2 * 1 + 0 -> exact subnormal */
    li       t3, 0
    fmv.d.x  f9, t3
    CLEARFCSR
    fmadd.d  f10, f5, f6, f9
    CHECKFCSR x22

    /* fsqrt.d: the exact square root of a subnormal squared */
    CLEARFCSR
    fmul.d   f11, f5, f5
    CHECKFCSR x23
    fsqrt.d  f12, f11
    CHECKFCSR x24

    li       a1, 0x1000
    li       a2, 1
    sw       a2, 0(a1)
.Lhalt:
    j        .Lhalt
