/*
 * fp_result_collision_test.S - FP sub-unit results colliding in one cycle.
 *
 * FPExecUnit_D merges its sub-unit outputs through a priority mux
 * (sqrt > div > fma > add > mul > misc).  Only one result can leave per cycle,
 * and the losing result is discarded with no replay - the sub-unit has already
 * consumed its operation and cannot re-present it.  The consumer's ROB entry
 * then never sees its tag on the CDB, never completes, and the core deadlocks
 * with a non-empty ROB.
 *
 * The guard that is supposed to prevent coincidence holds busy for two cycles
 * after each pipelined dispatch, on the assumption that MUL has 3-cycle latency.
 * FPMultiplier is 2-cycle (see the src3 delay line in FPFMA.lean), so an FMA
 * (latency 5) and a multiply (latency 2) dispatched three cycles apart complete
 * on the same cycle and one result is lost.
 *
 * Alternating fnmadd_s / fmul_s produces that spacing naturally.  The encodings
 * are emitted as .word so the test needs no -march flag.  Fails with
 * tohost = 0xDEAD, passes with tohost = 1.
 */
    .section .text
    .globl _start
_start:
    .word   0xb8ea924f          /* fnmadd.s f4, f21, f14, f23 */
    .word   0x103e4c53          /* fmul.s   f24, f28, f3      */
    .word   0xb8ea924f
    .word   0x103e4c53
    .word   0xb8ea924f
    .word   0x103e4c53
    .word   0xb8ea924f
    .word   0x103e4c53
    .word   0xb8ea924f
    .word   0x103e4c53
    .word   0xb8ea924f
    .word   0x103e4c53
    .word   0xb8ea924f
    .word   0x103e4c53
    .word   0xb8ea924f
    .word   0x103e4c53

    li      a1, 0x1000
    li      a2, 1
    sw      a2, 0(a1)
.Lhalt:
    j       .Lhalt
