/*
 * amo_rd_chain_useq_test.S - amo_rd_chain_test with one microcoded op.
 *
 * Identical to amo_rd_chain_test except for one roriw between the AMOs.
 * If only this test fails, the fault is in the microcode path, not in the
 * memory hierarchy.
 */

#define TOHOST 0x1000
#define MEM 0x2000

.section .text
.globl _start
_start:
    li      x31, MEM
    sd      x0, 0(x31)
    li      x2, 0x1800

    amomax.d x28, x0, (x31)

    li      x24, 0x1800
    amoadd.d x29, x24, (x31)
    amomax.w x21, x24, (x31)
    nop
    nop
    .word 0x6001509b   # roriw x1, x2, 0 (microcoded)
    nop
    nop
    nop

    amoand.w x26, x28, (x31)
    li      x23, -1
    amoand.d x15, x23, (x31)

    bnez    x28, fail
    li      t2, 0x1800
    bne     x1, t2, fail
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
