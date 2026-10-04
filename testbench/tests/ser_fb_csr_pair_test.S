/*
 * ser_fb_csr_pair_test.S - Fallback op in slot 0, CSR op in slot 1.
 *
 * A microcoded (fallback) op and a CSR op in the same fetch pair.  The
 * fallback op is serialized first.  Its completion must not also run the
 * CSR commit path: that path frees the captured old tag, which for a
 * fallback op is the live tag of its own rd.  The freed tag is then
 * reallocated, and two registers share one physical register.
 *
 * Check: x1 (fallback rd) keeps its value after enough renames to cycle
 * the free list.
 */

#define TOHOST 0x1000
#define RENAMES 96

.section .text
.globl _start
_start:
    li      t0, 0x55
    csrw    mscratch, t0
    li      x2, 0x1800

    .balign 8
    .word   0x6001509b          # roriw x1, x2, 0 (fallback, slot 0)
    csrrw   x19, mscratch, x0   # CSR op (slot 1)

    li      t2, 0x55
    bne     x19, t2, fail

    /* Cycle the free list: every addi takes a new tag. */
    li      t1, RENAMES
    li      t0, 0
1:
    addi    t0, t0, 1
    addi    t3, t0, 2
    addi    t4, t0, 3
    addi    t1, t1, -1
    bnez    t1, 1b

    li      t2, 0x1800
    bne     x1, t2, fail
    li      t2, 0x55
    bne     x19, t2, fail

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
