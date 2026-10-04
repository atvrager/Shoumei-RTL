/*
 * fp_uf_test.S - the underflow flag, per floating-point unit.
 *
 * A tiny result that is also inexact must set UF together with NX.  Each
 * unit computes its own flags, so the cases are grouped by unit and the
 * cosim prints both values at the diverging csrr.
 *
 * Why this shape
 * --------------
 * The lock-step cosim compares PC, the instruction word and INTEGER register
 * writeback, but not FP registers (cosim_main.cpp: "FP register comparison:
 * not available in W=2 RVVI yet").  So every case here routes its result and
 * its fflags through an integer register:
 *
 *     fmv.x.w t1, ft0     result -> compared against Spike
 *     csrr    t2, fflags  flags  -> compared against Spike
 *
 * That makes Spike the oracle for every expected value.  No constant in this
 * file is an expectation; the operand bit patterns define the case, and a
 * divergence shows up as a MISMATCH printed against the fmv.x.w / csrr
 * instruction, with both values.  fflags is not in the cosim's unsyncable-CSR
 * list (only the performance counters are), so it is compared for real.
 *
 * The program is straight-line on purpose: branching on a result would desync
 * the retired trace and bury the real divergence in PC noise.
 *
 * Per case:
 *     SETRM <rm>          fcsr = rm<<5, which also clears fflags
 *     <op>
 *     OBSERVE             result and flags to integer registers
 *
 * Grouped by the defect each group is aimed at.
 */
    .section .text
    .globl _start

/* Load a 32-bit pattern into an f-register. */
.macro FLD32 freg, pat
    li       t0, \pat
    fmv.w.x  \freg, t0
.endm

/* Load a 64-bit pattern into an f-register. */
.macro FLD64 freg, pat
    li       t0, \pat
    fmv.d.x  \freg, t0
.endm

/* Set the rounding mode and clear fflags, so each case's flags stand alone. */
.macro SETRM rm
    li       t0, (\rm << 5)
    csrw     fcsr, t0
.endm

/* Single result and flags to integer registers. */
.macro OBSERVE
    fmv.x.w  t1, ft0
    csrr     t2, fflags
.endm

/* Double result and flags to integer registers. */
.macro OBSERVE64
    fmv.x.d  t1, ft0
    csrr     t2, fflags
.endm

_start:

    /* Underflow.  A tiny result that is also inexact must set UF|NX.  The flag
       comes from the executing unit, so the cases are grouped by unit, and a
       divergence prints the csrr with both values.                          */

    /* fmul.s(2^-126, 2^-126) -> 0, UF|NX (0x03).                            */
    FLD32    fa1, 0x00800000
    FLD32    fa2, 0x00800000
    SETRM    0
    fmul.s   ft0, fa1, fa2
    OBSERVE

    /* fmul.d(2^-1022, 2^-1022) -> 0, UF|NX.                                 */
    FLD64    fa1, 0x0010000000000000
    FLD64    fa2, 0x0010000000000000
    SETRM    0
    fmul.d   ft0, fa1, fa2
    OBSERVE64

    /* fdiv.s(2^-126, 2^126) -> 0, UF|NX.                                    */
    FLD32    fa1, 0x00800000
    FLD32    fa2, 0x7F000000
    SETRM    0
    fdiv.s   ft0, fa1, fa2
    OBSERVE

    /* fdiv.d(2^-1022, 2^1022) -> 0, UF|NX.                                  */
    FLD64    fa1, 0x0010000000000000
    FLD64    fa2, 0x7FE0000000000000
    SETRM    0
    fdiv.d   ft0, fa1, fa2
    OBSERVE64

    /* fma.s(2^-126, 2^-126, 0) -> 0, UF|NX.  The product underflows before
       the addend is folded in.                                             */
    FLD32    fa1, 0x00800000
    FLD32    fa2, 0x00800000
    fmv.w.x  fa3, zero
    SETRM    0
    fmadd.s  ft0, fa1, fa2, fa3
    OBSERVE

    /* fma.d(2^-1022, 2^-1022, 0) -> 0, UF|NX.                              */
    FLD64    fa1, 0x0010000000000000
    FLD64    fa2, 0x0010000000000000
    fmv.d.x  fa3, zero
    SETRM    0
    fmadd.d  ft0, fa1, fa2, fa3
    OBSERVE64

    /* fcvt.s.d(2^-1022) -> 0, UF|NX: narrowing underflows.                  */
    FLD64    fa1, 0x0010000000000000
    SETRM    0
    fcvt.s.d ft0, fa1
    OBSERVE

    /* fcvt.s.d(1.5) under round-toward-zero -> 1.5 exactly, no flags at all.
       A unit that ties UF to the rounding mode alone sets a spurious UF.    */
    FLD64    fa1, 0x3FF8000000000000
    SETRM    1
    fcvt.s.d ft0, fa1
    OBSERVE

    /* Overflow.  The unit's own result is checked by fp_ovf_test; this asks
       whether the flag reaches fflags through the CPU's accumulation, which
       runs through a side file read at commit.  RNE gives an infinity, so the
       flags are OF and NX: 0x05.                                            */
    FLD32    fa1, 0x7F7FFFFF          /* FLT_MAX */
    FLD32    fa2, 0x40000000          /* 2.0     */
    SETRM    0
    fmul.s   ft0, fa1, fa2
    OBSERVE

    FLD64    fa1, 0x7FEFFFFFFFFFFFFF  /* DBL_MAX */
    FLD64    fa2, 0x4000000000000000  /* 2.0     */
    SETRM    0
    fmul.d   ft0, fa1, fa2
    OBSERVE64

    FLD32    fa1, 0x7F7FFFFF
    FLD32    fa2, 0x7F7FFFFF
    SETRM    0
    fadd.s   ft0, fa1, fa2
    OBSERVE

    FLD32    fa1, 0x7F7FFFFF
    FLD32    fa2, 0x3F000000          /* 0.5     */
    SETRM    0
    fdiv.s   ft0, fa1, fa2
    OBSERVE

    FLD32    fa1, 0x7F7FFFFF
    FLD32    fa2, 0x40000000
    fmv.w.x  fa3, zero
    SETRM    0
    fmadd.s  ft0, fa1, fa2, fa3
    OBSERVE

    /* Narrowing a double past the single range: OF and NX, 0x05, and the
       result is an infinity under RNE or FLT_MAX under round toward zero. */
    FLD64    fa1, 0x7FEFFFFFFFFFFFFF  /* DBL_MAX */
    SETRM    0
    fcvt.s.d ft0, fa1
    OBSERVE

    FLD64    fa1, 0x7FEFFFFFFFFFFFFF
    SETRM    1                        /* RTZ */
    fcvt.s.d ft0, fa1
    OBSERVE

    FLD64    fa1, 0xFFEFFFFFFFFFFFFF  /* -DBL_MAX */
    SETRM    0
    fcvt.s.d ft0, fa1
    OBSERVE

    /* Two floating-point operations back to back, so both may retire in the
       same cycle, raising different flags: overflow and inexact from the
       multiply, divide by zero from the division.  Together 0x0d.  The flags
       are accumulated through a side file read once per retire slot, so a
       merge that keeps only one slot's exceptions shows up here. */
    FLD32    fa1, 0x7F7FFFFF
    FLD32    fa2, 0x40000000
    FLD32    fa3, 0x3F800000          /* 1.0 */
    FLD32    fa4, 0x00000000          /* 0.0 */
    SETRM    0
    fmul.s   ft0, fa1, fa2
    fdiv.s   ft1, fa3, fa4
    csrr     t2, fflags

    /* The same pair the other way round, so each slot carries the other's
       flags: divide by zero first, overflow second. */
    SETRM    1
    fdiv.s   ft2, fa3, fa4
    fmul.s   ft3, fa1, fa2
    csrr     t3, fflags

/* Straight-line done.  Signal completion the way the other ASM tests do. */
    li       a1, 0x1000
    li       a2, 1
    sw       a2, 0(a1)
.Lhalt:
    j        .Lhalt
