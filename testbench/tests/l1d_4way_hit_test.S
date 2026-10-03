/*
 * l1d_4way_hit_test.S - Test 4-way L1D cache hit detection with atomics.
 *
 * Exercises all 4 ways of a set in the L1D cache.
 * Lines at 0x2000, 0x3000, 0x4000, and 0x5000 all map to set index 0.
 * Atomics bypass the store buffer and access L1D directly.
 */
    .section .text
    .globl _start
_start:
    li      t0, 0x2000
    li      t1, 0x3000
    li      t2, 0x4000
    li      t3, 0x5000

    li      a0, 10
    li      a1, 20
    li      a2, 30
    li      a3, 40

    /* Fill ways 0, 1, 2, 3 via atomic swap */
    amoswap.d t4, a0, (t0)
    amoswap.d t4, a1, (t1)
    amoswap.d t4, a2, (t2)
    amoswap.d t4, a3, (t3)

    /* Read and replace way 2 (must hit in way 2) */
    li      a4, 35
    amoswap.d s0, a4, (t2)
    bne     s0, a2, .Lfail

    /* Read back updated way 2 */
    amoswap.d s2, x0, (t2)
    bne     s2, a4, .Lfail

    /* Read and replace way 3 (must hit in way 3) */
    li      a5, 45
    amoswap.d s1, a5, (t3)
    bne     s1, a3, .Lfail

    /* Read back updated way 3 */
    amoswap.d s3, x0, (t3)
    bne     s3, a5, .Lfail

    /* Pass: write 1 to tohost */
    li      t4, 0x1000
    li      t5, 1
    sw      t5, 0(t4)
.Lhalt:
    j       .Lhalt

.Lfail:
    li      t4, 0x1000
    li      t5, 0xDEAD
    sw      t5, 0(t4)
    j       .Lhalt
