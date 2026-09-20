/*
 * serialize_pair_test.S - fence.i slot-1 predecessor regression.
 *
 * A serialize-class instruction (fence.i) decoded in slot 1 of the fetch group
 * used to suppress *both* slots at the drain start and redirect to the
 * serializing instruction's PC+4.  Its slot-0 block-mate - a program-order
 * predecessor that had not executed yet - was therefore never fetched again:
 * dropped silently (architectural state loss; observed as a loop counter that
 * never decremented, i.e. a hang).
 *
 * The test pairs each fence.i with a predecessor that carries a real
 * dependency, in a loop that re-enters at the .balign 8 pair so the pair is the
 * fetch group on every iteration:
 *
 *   .Louter:  .balign 8
 *             addi x12, x11, 1   <- slot 0 predecessor (must execute)
 *             fence.i            <- slot 1 serialize (drains the pipeline)
 *   ...       addi x29, x29, -1  <- loop counter, also a slot-0 pair member
 *
 * Both predecessors must have executed by the time the loop exits: the counter
 * reaches zero (inner loop count) and x12 holds x11+1.
 *
 * Fails with tohost = 0xDEAD when either predecessor is dropped; passes with
 * tohost = 1.  Self-contained: own _start, no crt0.
 */

.section .text
.globl _start
_start:
    la      sp, _stack_top
    li      x11, 0x42
    li      x10, 4                  /* outer iterations */

.Louter:
    /* slot 0 predecessor + slot 1 serialize (8-byte aligned fetch pair) */
    .balign 8
    li      x29, 64                 /* predecessor: inner loop counter */
    fence.i

.Linner:
    addi    x29, x29, -1
    bne     x29, x0, .Linner

    /* the counter predecessor must have executed */
    bnez    x29, .Lfail

    addi    x10, x10, -1
    bne     x10, x0, .Louter

    /* data-carrying predecessor: x12 = x11 + 1 must survive */
    .balign 8
    addi    x12, x11, 1             /* predecessor */
    fence.i
    li      x30, 0x43
    bne     x12, x30, .Lfail

    li      x30, 0x1000
    li      x31, 1
    sw      x31, 0(x30)
.Lhalt:
    j       .Lhalt

.Lfail:
    li      x30, 0x1000
    li      x31, 0xDEAD
    sw      x31, 0(x30)
    j       .Lhalt