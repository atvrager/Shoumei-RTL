/*
 * amo_rd_chain_test.S - AMO result used as rs2 of a later AMO.
 *
 * Copies the register pattern of the amo_and_test failure without any
 * microcoded op: amomax.d writes x28 = 0, and a later amoand.w reads x28.
 */

#define TOHOST 0x1000
#define MEM 0x2000

.section .text
.globl _start
_start:
    li      x31, MEM
    sd      x0, 0(x31)

    /* x28 = old value (0); memory = max(0, 0) = 0 */
    amomax.d x28, x0, (x31)

    /* memory = 0 + 0x1800 */
    li      x24, 0x1800
    amoadd.d x29, x24, (x31)
    amomax.w x21, x24, (x31)
    nop
    nop
    nop

    /* rs2 = x28 = 0, so memory becomes 0 */
    amoand.w x26, x28, (x31)
    li      x23, -1
    amoand.d x15, x23, (x31)

    bnez    x28, fail
    li      t2, 0x1800
    bne     x26, t2, fail
    bnez    x15, fail
    ld      a0, 0(x31)
    bnez    a0, fail

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
