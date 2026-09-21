/*
 * amo_sb_order_test.S - SC/AMO immediately followed by a store.
 *
 * An SC/AMO performs its own read-modify-write and only dispatches once the
 * store buffer is empty, because its write bypasses the buffer entirely.  A
 * plain store must therefore neither be granted ahead of an older atomic nor
 * enqueue while the atomic is in flight: either way the atomic waits for a
 * buffer entry that can only be released after the atomic retires, and the core
 * deadlocks with a non-empty ROB.
 *
 * Three `amoadd.d` / store pairs, back to back, exercise both orderings.  The
 * atomic encodings are emitted as `.word` so the test needs no -march flag.
 * Fails with tohost = 0xDEAD, passes with tohost = 1.
 */
    .section .text
    .globl _start
_start:
    li      t0, 0x2000          /* scratch base */
    li      t1, 5
    sd      t1, 0(t0)           /* [0] = 5  */
    .word   0x0062b3af          /* amoadd.d t2, t1, (t0)  -> [0] = 10 */
    sd      t1, 8(t0)           /* [8] = 5  */
    .word   0x0662be2f          /* amoadd.d t3, t1, (t0), aq/rl -> [0] = 15 */
    sd      t1, 16(t0)          /* [16] = 5 */

    ld      t4, 0(t0)
    li      t5, 15
    bne     t4, t5, .Lfail
    ld      t6, 8(t0)
    bne     t6, t1, .Lfail
    ld      a0, 16(t0)
    bne     a0, t1, .Lfail

    li      a1, 0x1000
    li      a2, 1
    sw      a2, 0(a1)
.Lhalt:
    j       .Lhalt
.Lfail:
    li      a1, 0x1000
    li      a2, 0xDEAD
    sw      a2, 0(a1)
    j       .Lhalt
