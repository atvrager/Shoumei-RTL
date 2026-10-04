/*
 * fflags_ser_pair_test.S - fflags read after a slow FP op.
 *
 * fdiv.d 1.0 / 3.0 sets NX.  An fflags read that comes after it in
 * program order must see NX, so the CSR read must wait until the
 * divide has accrued its flags.
 *
 * Case 1: the CSR read follows the divide directly.
 * Case 2: a store, then a fallback op in slot 0 and the CSR read in
 *         slot 1 (the shape a random test failed on).
 * Case 3: the same pair with no store.
 */

#define TOHOST 0x1000
#define FFLAGS_NX 0x01

.section .text
.globl _start
_start:
    li      x31, 0x2000
    li      t0, 0x3ff0000000000000   /* 1.0 */
    fmv.d.x f1, t0
    li      t0, 0x4008000000000000   /* 3.0 */
    fmv.d.x f2, t0
    li      x2, 0x1800

    /* Case 1 */
    csrw    fflags, x0
    fdiv.d  f3, f1, f2
    csrr    x21, fflags
    li      t2, FFLAGS_NX
    bne     x21, t2, fail

    /* Case 2 */
    csrw    fflags, x0
    fdiv.d  f3, f1, f2
    sw      x2, 0(x31)
    .balign 8
    .word   0x6001509b          /* roriw x1, x2, 0 (fallback, slot 0) */
    csrrwi  x21, fflags, 0      /* CSR read (slot 1) */
    li      t2, FFLAGS_NX
    bne     x21, t2, fail

    /* Case 3 */
    csrw    fflags, x0
    fdiv.d  f3, f1, f2
    .balign 8
    .word   0x6001509b          /* roriw x1, x2, 0 (fallback, slot 0) */
    csrrwi  x21, fflags, 0      /* CSR read (slot 1) */
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
