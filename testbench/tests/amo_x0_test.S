/*
 * amo_x0_test.S - Atomic instruction with rd = x0 followed by load.
 *
 * Verify that atomic instructions with rd = x0 do not retire early.
 * Confirm that subsequent loads dispatch without deadlock.
 */

#define PASS_CODE 1
#define TOHOST 0x1000
#define MEM 0x3000

.section .text
.globl _start
_start:
    li      s0, MEM
    li      t0, 0x12345678
    sw      t0, 0(s0)

    # Atomic with rd = x0
    li      a7, 0x10000000
    amomin.w zero, a7, (s0)

    # Following load
    lw      t1, 0(s0)
    li      t2, 0x10000000
    bne     t1, t2, fail

    # Atomic add with rd = x0
    li      a7, 1
    amoadd.w zero, a7, (s0)

    lw      t1, 0(s0)
    li      t2, 0x10000001
    bne     t1, t2, fail

    # Double precision atomic with rd = x0
    li      t0, 0x0123456789abcdef
    sd      t0, 0(s0)
    li      a7, 0x0000000000000001
    amoadd.d zero, a7, (s0)

    ld      t1, 0(s0)
    li      t2, 0x0123456789abcdf0
    bne     t1, t2, fail

    # PASS: write 1 to tohost
    li      t0, TOHOST
    li      t1, PASS_CODE
    sw      t1, 0(t0)
.Lpass:
    j       .Lpass

fail:
    li      t0, TOHOST
    li      t1, 2
    sw      t1, 0(t0)
.Lfail:
    j       .Lfail
