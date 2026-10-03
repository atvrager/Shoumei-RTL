/*
 * amo_word_merge_test.S - Word AMO writes into a doubleword location.
 *
 * Memory hierarchy only: no microcoded op, every operand from li.
 * Check that a .W AMO write changes only its own word of the line, and
 * that a .D AMO right after a .W AMO on the same address reads the new word.
 */

#define TOHOST 0x1000
#define MEM 0x2000

.section .text
.globl _start
_start:
    li      s0, MEM

    /* 1: amoand.w on the low word keeps the high word */
    li      t0, 0x1122334455667788
    sd      t0, 0(s0)
    li      t1, 0x0000ff00
    amoand.w a0, t1, (s0)
    li      t2, 0x55667788
    bne     a0, t2, fail
    ld      a1, 0(s0)
    li      t2, 0x1122334400007700
    bne     a1, t2, fail

    /* 2: amoor.w on the high word keeps the low word */
    li      t1, 0x000000ff
    addi    s1, s0, 4
    amoor.w a0, t1, (s1)
    li      t2, 0x11223344
    bne     a0, t2, fail
    ld      a1, 0(s0)
    li      t2, 0x112233ff00007700
    bne     a1, t2, fail

    /* 3: back-to-back amoand.w then amoand.d, same address */
    li      t0, 0x1800
    sd      t0, 0(s0)
    li      t1, 0
    li      t3, -1
    amoand.w a0, t1, (s0)
    amoand.d a1, t3, (s0)
    li      t2, 0x1800
    bne     a0, t2, fail
    bnez    a1, fail
    ld      a2, 0(s0)
    bnez    a2, fail

    /* 4: amoswap.w then lw and ld */
    li      t0, -1
    sd      t0, 0(s0)
    li      t1, 0x12345678
    amoswap.w a0, t1, (s0)
    li      t2, -1
    bne     a0, t2, fail
    lw      a1, 0(s0)
    bne     a1, t1, fail
    ld      a2, 0(s0)
    li      t2, 0xffffffff12345678
    bne     a2, t2, fail

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
