/*
 * fcvt_swu_nx_test.S - NX from fcvt.s.wu.
 *
 * fcvt.s.wu reads the low 32 bits of rs1.  0x9999999a needs 32
 * significant bits, so the single result is inexact and sets NX.
 *
 * Case 1: rs1 holds garbage in the upper 32 bits.
 * Case 2: rs1 holds the zero-extended value.
 * Case 3: an fnmadd.s that sets no flag in slot 0, the fcvt.s.wu in
 *         slot 1 (the pair a random test lost the flag on).
 */

#define TOHOST 0x1000
#define FFLAGS_NX 0x01

.section .text
.globl _start
_start:
    li      t0, 0x7ff8000000000000   /* double qNaN, not NaN-boxed */
    fmv.d.x f13, t0
    li      t0, 0x3ff0000000000001
    fmv.d.x f6, t0
    li      t0, 0x3fe0000000000000
    fmv.d.x f24, t0

    /* Case 2 */
    csrw    fflags, x0
    li      x5, 0x9999999a
    fcvt.s.wu f10, x5
    frflags x21
    li      t2, FFLAGS_NX
    bne     x21, t2, fail

    /* Case 1 */
    csrw    fflags, x0
    li      x5, 0xbfb999999999999a
    fcvt.s.wu f10, x5
    frflags x21
    li      t2, FFLAGS_NX
    bne     x21, t2, fail

    /* Case 3 */
    csrw    fflags, x0
    li      x5, 0xbfb999999999999a
    .balign 8
    .word   0xc06b4ccf          /* fnmadd.s f25, f13, f6, f24, rmm (slot 0) */
    fcvt.s.wu f10, x5           /* slot 1 */
    frflags x21
    li      t2, FFLAGS_NX
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
