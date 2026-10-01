/*
 * fp_conformance_test.S - directed floating-point conformance against Spike.
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

/* ---------------------------------------------------------------------------
 * 1. FMA fusion.
 *
 * FPFMA instantiates FPMultiplier then FPAdder, so the product is rounded to
 * single precision before the addition.  With a = 0x3F800001 = 1+2^-23 and
 * b = 0x3F7FFFFF = 1-2^-24 (the exponent drops to 126, so the spacing halves;
 * the largest float below 1.0 is 1-2^-24, not 1-2^-23), the exact product is
 * 1 + 2^-24 - 2^-47, which rounds to 1.0 before the add.  Multiply-then-add
 * therefore returns 0, while a fused unit returns 0x337ffffe, as Spike does.
 * ------------------------------------------------------------------------ */
    FLD32    fa1, 0x3F800001          /* 1 + 2^-23 */
    FLD32    fa2, 0x3F7FFFFF          /* 1 - 2^-23 */
    FLD32    fa3, 0xBF800000          /* -1        */
    SETRM    0
    fmadd.s  ft0, fa1, fa2, fa3
    OBSERVE

    SETRM    0
    fmsub.s  ft0, fa1, fa2, fa3       /* a*b - c, same product */
    OBSERVE

    SETRM    0
    fnmadd.s ft0, fa1, fa2, fa3       /* -(a*b) - c */
    OBSERVE

    SETRM    0
    fnmsub.s ft0, fa1, fa2, fa3       /* -(a*b) + c */
    OBSERVE

    /* 0 * inf + 1 -> invalid, canonical NaN */
    FLD32    fa1, 0x00000000
    FLD32    fa2, 0x7F800000
    FLD32    fa3, 0x3F800000
    SETRM    0
    fmadd.s  ft0, fa1, fa2, fa3
    OBSERVE

    /* 1 * inf + (-inf) -> invalid, canonical NaN */
    FLD32    fa1, 0x3F800000
    FLD32    fa2, 0x7F800000
    FLD32    fa3, 0xFF800000
    SETRM    0
    fmadd.s  ft0, fa1, fa2, fa3
    OBSERVE

    /* Double precision twin: same fusion case, -2^-52. */
    FLD64    fa1, 0x3FF0000000000001
    FLD64    fa2, 0x3FEFFFFFFFFFFFFF
    FLD64    fa3, 0xBFF0000000000000
    SETRM    0
    fmadd.d  ft0, fa1, fa2, fa3
    OBSERVE64

/* ---------------------------------------------------------------------------
 * 2. Rounding modes.
 *
 * rm was ignored by FPAdder, FPMultiplier, FPDivider and FPSqrt.  Each op is
 * run under every mode on an operand pair whose exact result needs a decision,
 * so a unit that hardcodes one mode diverges on the others.
 * ------------------------------------------------------------------------ */

    /* 1.0 + 2^-24 is exactly half an ulp: RNE ties to even (down), RUP goes up. */
    FLD32    fa1, 0x3F800000
    FLD32    fa2, 0x33800000
    SETRM    0
    fadd.s   ft0, fa1, fa2
    OBSERVE
    SETRM    1
    fadd.s   ft0, fa1, fa2
    OBSERVE
    SETRM    2
    fadd.s   ft0, fa1, fa2
    OBSERVE
    SETRM    3
    fadd.s   ft0, fa1, fa2
    OBSERVE
    SETRM    4
    fadd.s   ft0, fa1, fa2
    OBSERVE

    /* 1.0 / 3.0 is inexact in both directions. */
    FLD32    fa1, 0x3F800000
    FLD32    fa2, 0x40400000
    SETRM    0
    fdiv.s   ft0, fa1, fa2
    OBSERVE
    SETRM    1
    fdiv.s   ft0, fa1, fa2
    OBSERVE
    SETRM    2
    fdiv.s   ft0, fa1, fa2
    OBSERVE
    SETRM    3
    fdiv.s   ft0, fa1, fa2
    OBSERVE

    /* 3.0 * 0.1: the normal path truncated, so RTZ and RNE disagreed. */
    FLD32    fa1, 0x40400000
    FLD32    fa2, 0x3DCCCCCD
    SETRM    0
    fmul.s   ft0, fa1, fa2
    OBSERVE
    SETRM    1
    fmul.s   ft0, fa1, fa2
    OBSERVE
    SETRM    3
    fmul.s   ft0, fa1, fa2
    OBSERVE

    /* sqrt needs a value whose remainder straddles the rounding decision. */
    FLD32    fa1, 0x3F003000
    SETRM    0
    fsqrt.s  ft0, fa1
    OBSERVE
    SETRM    1
    fsqrt.s  ft0, fa1
    OBSERVE

    /* Double precision: the same four ops. */
    FLD64    fa1, 0x3FF0000000000000
    FLD64    fa2, 0x3CA0000000000000    /* 2^-53, exactly half an ulp */
    SETRM    0
    fadd.d   ft0, fa1, fa2
    OBSERVE64
    SETRM    3
    fadd.d   ft0, fa1, fa2
    OBSERVE64

    FLD64    fa1, 0x3FF0000000000000
    FLD64    fa2, 0x4008000000000000    /* 3.0 */
    SETRM    0
    fdiv.d   ft0, fa1, fa2
    OBSERVE64
    SETRM    1
    fdiv.d   ft0, fa1, fa2
    OBSERVE64

    FLD64    fa1, 0x4008000000000000
    FLD64    fa2, 0x3FB999999999999A    /* 0.1 */
    SETRM    0
    fmul.d   ft0, fa1, fa2
    OBSERVE64
    SETRM    1
    fmul.d   ft0, fa1, fa2
    OBSERVE64

    FLD64    fa1, 0x3FE0000000000000    /* 0.5 */
    SETRM    0
    fsqrt.d  ft0, fa1
    OBSERVE64
    SETRM    1
    fsqrt.d  ft0, fa1
    OBSERVE64

/* ---------------------------------------------------------------------------
 * 3. Overflow, underflow and subnormals.
 *
 * OF and UF were computed as x & ~x (always zero), an overflowing result
 * packed as 0x7FFFFFFF rather than infinity, and subnormal results were not
 * formed at all.
 * ------------------------------------------------------------------------ */

    /* FLT_MAX * 2 -> +inf, overflow and inexact */
    FLD32    fa1, 0x7F7FFFFF
    FLD32    fa2, 0x40000000
    SETRM    0
    fmul.s   ft0, fa1, fa2
    OBSERVE

    /* FLT_MAX + FLT_MAX -> +inf, overflow and inexact */
    FLD32    fa1, 0x7F7FFFFF
    FLD32    fa2, 0x7F7FFFFF
    SETRM    0
    fadd.s   ft0, fa1, fa2
    OBSERVE

    /* 1.0 / 0.0 -> +inf, divide by zero */
    FLD32    fa1, 0x3F800000
    FLD32    fa2, 0x00000000
    SETRM    0
    fdiv.s   ft0, fa1, fa2
    OBSERVE

    /* -1.0 / 0.0 -> -inf, divide by zero */
    FLD32    fa1, 0xBF800000
    FLD32    fa2, 0x00000000
    SETRM    0
    fdiv.s   ft0, fa1, fa2
    OBSERVE

    /* 0.0 / 0.0 -> canonical NaN, invalid */
    FLD32    fa1, 0x00000000
    FLD32    fa2, 0x00000000
    SETRM    0
    fdiv.s   ft0, fa1, fa2
    OBSERVE

    /* smallest normal / 2 -> subnormal, underflow and inexact */
    FLD32    fa1, 0x00800000
    FLD32    fa2, 0x40000000
    SETRM    0
    fdiv.s   ft0, fa1, fa2
    OBSERVE

    /* smallest normal * 0.5 -> subnormal, underflow and inexact */
    FLD32    fa1, 0x00800000
    FLD32    fa2, 0x3F000000
    SETRM    0
    fmul.s   ft0, fa1, fa2
    OBSERVE

    /* smallest subnormal + 0 -> itself, exact */
    FLD32    fa1, 0x00000001
    FLD32    fa2, 0x00000000
    SETRM    0
    fadd.s   ft0, fa1, fa2
    OBSERVE

    /* 1.0 + 2^-25 -> 1.0, inexact */
    FLD32    fa1, 0x3F800000
    FLD32    fa2, 0x33000000
    SETRM    0
    fadd.s   ft0, fa1, fa2
    OBSERVE

    /* 1.0 - 2^-25 -> 1.0, inexact */
    FLD32    fa1, 0x3F800000
    FLD32    fa2, 0xB3000000
    SETRM    0
    fadd.s   ft0, fa1, fa2
    OBSERVE

    /* Double: DBL_MAX * 2 -> +inf */
    FLD64    fa1, 0x7FEFFFFFFFFFFFFF
    FLD64    fa2, 0x4000000000000000
    SETRM    0
    fmul.d   ft0, fa1, fa2
    OBSERVE64

    /* Double: smallest normal / 2 -> subnormal */
    FLD64    fa1, 0x0010000000000000
    FLD64    fa2, 0x4000000000000000
    SETRM    0
    fdiv.d   ft0, fa1, fa2
    OBSERVE64

    /* Double: 1.0 / 0.0 -> +inf */
    FLD64    fa1, 0x3FF0000000000000
    FLD64    fa2, 0x0000000000000000
    SETRM    0
    fdiv.d   ft0, fa1, fa2
    OBSERVE64

/* ---------------------------------------------------------------------------
 * 4. Conversions.
 *
 * RISC-V signals a conversion that cannot be represented with NV and
 * saturates; it does not use OF.  The values themselves were never probed.
 * ------------------------------------------------------------------------ */

    /* Magnitudes below 1.0: the shift that isolates the integer part runs past
       the guard shifter's width, so the guard and sticky read bits of a shift
       that never happens and the value looks exact.  Round up must still give 1
       for any nonzero value below 1.0; round to nearest must give 0. */
    FLD64    fa1, 0x0010000000000000
    SETRM    3
    fcvt.w.d t1, fa1
    csrr     t2, fflags
    OBSERVE

    FLD64    fa1, 0x0010000000000000
    SETRM    0
    fcvt.w.d t1, fa1
    csrr     t2, fflags
    OBSERVE

    /* Largest subnormal. */
    FLD64    fa1, 0x000FFFFFFFFFFFFF
    SETRM    3
    fcvt.w.d t1, fa1
    csrr     t2, fflags
    OBSERVE

    /* 2^31 as a float cannot fit in a signed word: NV and INT_MAX. */
    FLD32    fa1, 0x4F000000
    SETRM    0
    fcvt.w.s t1, fa1
    csrr     t2, fflags
    OBSERVE

    /* -1.0 to unsigned: NV and 0. */
    FLD32    fa1, 0xBF800000
    SETRM    0
    fcvt.wu.s t1, fa1
    csrr     t2, fflags

    /* 2^63 to signed long: NV and LONG_MAX. */
    FLD32    fa1, 0x5F000000
    SETRM    0
    fcvt.l.s t1, fa1
    csrr     t2, fflags

    /* 2^24 + 1 cannot be represented exactly in single: RNE, inexact. */
    li       t0, 16777217
    SETRM    0
    fcvt.s.w ft0, t0
    OBSERVE

    /* single -> double is exact */
    FLD32    fa1, 0x3F800001
    SETRM    0
    fcvt.d.s ft0, fa1
    OBSERVE64

    /* double -> single needs rounding: 1 + 2^-52 rounds to 1.0 at RNE */
    FLD64    fa1, 0x3FF0000000000001
    SETRM    0
    fcvt.s.d ft0, fa1
    OBSERVE

    /* a double value that survives the narrowing exactly */
    FLD64    fa1, 0x3FF0000020000000    /* 1 + 2^-23 */
    SETRM    0
    fcvt.s.d ft0, fa1
    OBSERVE

/* ---------------------------------------------------------------------------
 * 5. NaN, signed zero, min/max and compare.
 *
 * FPCompare separated the signed zeros; min/max need the total order.
 * ------------------------------------------------------------------------ */

    /* +0 == -0 is true */
    FLD32    fa1, 0x00000000
    FLD32    fa2, 0x80000000
    SETRM    0
    feq.s    t1, fa1, fa2
    csrr     t2, fflags

    /* -0 < +0 is false */
    FLD32    fa1, 0x80000000
    FLD32    fa2, 0x00000000
    SETRM    0
    flt.s    t1, fa1, fa2
    csrr     t2, fflags

    /* -0 <= +0 is true */
    SETRM    0
    fle.s    t1, fa1, fa2
    csrr     t2, fflags

    /* comparing against NaN: quiet, result false */
    FLD32    fa1, 0x7FC00000
    FLD32    fa2, 0x3F800000
    SETRM    0
    feq.s    t1, fa1, fa2
    csrr     t2, fflags

    /* signaling NaN in a compare raises invalid */
    FLD32    fa1, 0x7F800001
    SETRM    0
    feq.s    t1, fa1, fa2
    csrr     t2, fflags

    /* fmin of the signed zeros returns -0 */
    FLD32    fa1, 0x00000000
    FLD32    fa2, 0x80000000
    SETRM    0
    fmin.s   ft0, fa1, fa2
    OBSERVE

    /* fmax of the signed zeros returns +0 */
    SETRM    0
    fmax.s   ft0, fa1, fa2
    OBSERVE

    /* quiet NaN propagates without raising invalid */
    FLD32    fa1, 0x7FC00000
    FLD32    fa2, 0x3F800000
    SETRM    0
    fadd.s   ft0, fa1, fa2
    OBSERVE

    /* signaling NaN propagates and raises invalid */
    FLD32    fa1, 0x7F800001
    SETRM    0
    fadd.s   ft0, fa1, fa2
    OBSERVE

    /* sign injection */
    FLD32    fa1, 0x3F800000
    FLD32    fa2, 0xBF800000
    SETRM    0
    fsgnj.s  ft0, fa1, fa2
    OBSERVE
    SETRM    0
    fsgnjn.s ft0, fa1, fa2
    OBSERVE
    SETRM    0
    fsgnjx.s ft0, fa1, fa2
    OBSERVE

    /* class of a negative subnormal, +inf, NaN */
    FLD32    fa1, 0x80000001
    SETRM    0
    fclass.s t1, fa1
    csrr     t2, fflags
    FLD32    fa1, 0x7F800000
    SETRM    0
    fclass.s t1, fa1
    csrr     t2, fflags
    FLD32    fa1, 0x7FC00000
    SETRM    0
    fclass.s t1, fa1
    csrr     t2, fflags

/* ---------------------------------------------------------------------------
 * 6. Subnormal inputs and results — extended.
 *
 * Section 3 checks OF/UF were zero before.  These cases probe the specific
 * failing paths: FPDivider's 8-bit exponent and FPAdder's subnormal-input
 * path, plus their DP twins.
 * ------------------------------------------------------------------------ */

    /* SP: smallest normal / 2 -> 0x00400000 (UF|NX).  RTL returns 0.       */
    FLD32    fa1, 0x00800000
    FLD32    fa2, 0x40000000
    SETRM    0
    fdiv.s   ft0, fa1, fa2
    OBSERVE

    /* SP: smallest subnormal + 0 -> same subnormal unchanged.               */
    FLD32    fa1, 0x00000001
    FLD32    fa2, 0x00000000
    SETRM    0
    fadd.s   ft0, fa1, fa2
    OBSERVE

    /* SP: subnormal + subnormal (same binade).                               */
    FLD32    fa1, 0x00000001
    FLD32    fa2, 0x00000001
    SETRM    0
    fadd.s   ft0, fa1, fa2
    OBSERVE

    /* SP: subnormal * 1.0 -> subnormal.                                     */
    FLD32    fa1, 0x00000001
    FLD32    fa2, 0x3F800000
    SETRM    0
    fmul.s   ft0, fa1, fa2
    OBSERVE

    /* DP: smallest normal / 2 -> 0x0008000000000000 (UF|NX).               */
    FLD64    fa1, 0x0010000000000000
    FLD64    fa2, 0x4000000000000000
    SETRM    0
    fdiv.d   ft0, fa1, fa2
    OBSERVE64

    /* DP: smallest subnormal + 0 -> unchanged.                              */
    FLD64    fa1, 0x0000000000000001
    FLD64    fa2, 0x0000000000000000
    SETRM    0
    fadd.d   ft0, fa1, fa2
    OBSERVE64

    /* SP: smallest subnormal / 1.0 -> itself.  The restoring division compares
     * and subtracts the two mantissas directly, so a subnormal operand must be
     * normalized first: its fraction shifted up to the implicit position and
     * its exponent lowered by the shift.                                     */
    FLD32    fa1, 0x00000001
    FLD32    fa2, 0x3F800000
    SETRM    0
    fdiv.s   ft0, fa1, fa2
    OBSERVE

    /* SP: 2^-100 / 2^-140 -> 2^40, a normal quotient from a subnormal divisor. */
    FLD32    fa1, 0x0D800000
    FLD32    fa2, 0x00000200
    SETRM    0
    fdiv.s   ft0, fa1, fa2
    OBSERVE

    /* SP: smallest subnormal / 3 -> zero, tiny and inexact.                  */
    FLD32    fa1, 0x00000001
    FLD32    fa2, 0x40400000
    SETRM    0
    fdiv.s   ft0, fa1, fa2
    OBSERVE

    /* SP: smallest subnormal * 2.0 -> two quanta, exact.                     */
    FLD32    fa1, 0x00000001
    FLD32    fa2, 0x40000000
    SETRM    0
    fmul.s   ft0, fa1, fa2
    OBSERVE

    /* DP: smallest subnormal / 1.0 -> itself.                                */
    FLD64    fa1, 0x0000000000000001
    FLD64    fa2, 0x3FF0000000000000
    SETRM    0
    fdiv.d   ft0, fa1, fa2
    OBSERVE64

    /* DP: 2^-1030 / 3 -> a subnormal quotient, tiny and inexact.              */
    FLD64    fa1, 0x0000100000000000
    FLD64    fa2, 0x4008000000000000
    SETRM    0
    fdiv.d   ft0, fa1, fa2
    OBSERVE64

    /* DP: 2^-1030 * 2^500 -> a normal product from a subnormal operand.        */
    FLD64    fa1, 0x0000100000000000
    FLD64    fa2, 0x5F30000000000000
    SETRM    0
    fmul.d   ft0, fa1, fa2
    OBSERVE64

    /* SP: 1.0 - 2^-30.  The subtrahend sits entirely below the alignment window,
     * so the sum is a magnitude just under 1.0, not exactly 1.0: truncation must
     * borrow one ulp.  RNE hides this (1.0 is nearest) and RTZ does not.        */
    FLD32    fa1, 0x3F800000
    FLD32    fa2, 0xB0400000
    SETRM    1
    fadd.s   ft0, fa1, fa2
    OBSERVE

    /* SP: 2.0 - 2^-30 -> the borrow renormalizes, since the sum was a power of
     * two and 2.0 - 2^-23 is the next value down.                            */
    FLD32    fa1, 0x40000000
    FLD32    fa2, 0xB0400000
    SETRM    1
    fadd.s   ft0, fa1, fa2
    OBSERVE

    /* DP: 1.0 - 2^-60, the same case one precision wider.                     */
    FLD64    fa1, 0x3FF0000000000000
    FLD64    fa2, 0xBC30000000000000
    SETRM    1
    fadd.d   ft0, fa1, fa2
    OBSERVE64

/* ---------------------------------------------------------------------------
 * 7. NaN propagation and sNaN.
 * ------------------------------------------------------------------------ */

    /* SP: qNaN + 1.0 -> canonical qNaN, no flags.                          */
    FLD32    fa1, 0x7FC00000
    FLD32    fa2, 0x3F800000
    SETRM    0
    fadd.s   ft0, fa1, fa2
    OBSERVE

    /* SP: sNaN + 1.0 -> canonical qNaN, NV set.                            */
    FLD32    fa1, 0x7F800001
    FLD32    fa2, 0x3F800000
    SETRM    0
    fadd.s   ft0, fa1, fa2
    OBSERVE

    /* SP: fmin(NaN, 1.0) -> 1.0 (minNum), no flags.                        */
    FLD32    fa1, 0x7FC00000
    FLD32    fa2, 0x3F800000
    SETRM    0
    fmin.s   ft0, fa1, fa2
    OBSERVE

    /* SP: fmin(sNaN, 1.0) -> 1.0, NV set.                                  */
    FLD32    fa1, 0x7F800001
    FLD32    fa2, 0x3F800000
    SETRM    0
    fmin.s   ft0, fa1, fa2
    OBSERVE

    /* DP: sNaN * 1.0 -> canonical qNaN, NV set.                            */
    FLD64    fa1, 0x7FF0000000000001
    FLD64    fa2, 0x3FF0000000000000
    SETRM    0
    fmul.d   ft0, fa1, fa2
    OBSERVE64

/* ---------------------------------------------------------------------------
 * 8. DP FMA fusion.
 *
 * FPFMAD has the same non-fused structure.  a = 1+2^-52, b = 1-2^-53:
 * exact product = 1 + 2^-53 - 2^-105, rounds to 1.0, so the chain returns
 * 0 where a fused unit returns the correct residual (~3c9ffffffffffffe).
 * ------------------------------------------------------------------------ */

    FLD64    fa1, 0x3FF0000000000001
    FLD64    fa2, 0x3FEFFFFFFFFFFFFF
    FLD64    fa3, 0xBFF0000000000000
    SETRM    0
    fmadd.d  ft0, fa1, fa2, fa3
    OBSERVE64

    SETRM    0
    fnmadd.d ft0, fa1, fa2, fa3
    OBSERVE64

/* ---------------------------------------------------------------------------
 * 9. Rounding mode boundaries — extended: 1/3 and fsqrt(2).
 * ------------------------------------------------------------------------ */

    FLD32    fa1, 0x3F800000
    FLD32    fa2, 0x40400000
    SETRM    0
    fdiv.s   ft0, fa1, fa2
    OBSERVE
    SETRM    1
    fdiv.s   ft0, fa1, fa2
    OBSERVE
    SETRM    2
    fdiv.s   ft0, fa1, fa2
    OBSERVE
    SETRM    3
    fdiv.s   ft0, fa1, fa2
    OBSERVE
    SETRM    4
    fdiv.s   ft0, fa1, fa2
    OBSERVE

    FLD64    fa1, 0x3FF0000000000000
    FLD64    fa2, 0x4008000000000000
    SETRM    0
    fdiv.d   ft0, fa1, fa2
    OBSERVE64
    SETRM    1
    fdiv.d   ft0, fa1, fa2
    OBSERVE64
    SETRM    2
    fdiv.d   ft0, fa1, fa2
    OBSERVE64
    SETRM    3
    fdiv.d   ft0, fa1, fa2
    OBSERVE64
    SETRM    4
    fdiv.d   ft0, fa1, fa2
    OBSERVE64

    FLD32    fa1, 0x40000000
    SETRM    0
    fsqrt.s  ft0, fa1
    OBSERVE
    SETRM    3
    fsqrt.s  ft0, fa1
    OBSERVE

/* ---------------------------------------------------------------------------
 * 10. Conversion corners.
 * ------------------------------------------------------------------------ */

    /* fcvt.s.w(0) -> 0.0, no flags.                                         */
    li       t0, 0
    fcvt.s.w ft0, t0
    OBSERVE

    /* fcvt.s.w(-1) -> -1.0, no flags.                                       */
    li       t0, -1
    fcvt.s.w ft0, t0
    OBSERVE

    /* Values above 2^24 are integers in single, so the conversion is exact
       and needs no rounding, no NV and no saturation: the significand must be
       shifted *left* by exp - 150, which is what the unsigned path already
       does.  Without that, everything from 2^24 up saturates to INT_MAX.     */
    FLD32    fa1, 0x4B800000          /* 2^24 = 16777216 */
    SETRM    0
    fcvt.w.s t1, fa1
    csrr     t2, fflags

    FLD32    fa1, 0x4C000000          /* 2^25 */
    SETRM    0
    fcvt.w.s t1, fa1
    csrr     t2, fflags

    FLD32    fa1, 0x4E800000          /* 2^30 */
    SETRM    0
    fcvt.w.s t1, fa1
    csrr     t2, fflags

    FLD32    fa1, 0xCE800000          /* -2^30 */
    SETRM    0
    fcvt.w.s t1, fa1
    csrr     t2, fflags

    FLD32    fa1, 0x4F000000          /* 2^31: NV and INT_MAX */
    SETRM    0
    fcvt.w.s t1, fa1
    csrr     t2, fflags

    /* fcvt.w.s(NaN) -> INT_MAX, NV.                                         */
    FLD32    fa1, 0x7FC00000
    SETRM    0
    fcvt.w.s t1, fa1
    csrr     t2, fflags

    /* fcvt.w.s(-inf) -> INT_MIN, NV.                                        */
    FLD32    fa1, 0xFF800000
    SETRM    0
    fcvt.w.s t1, fa1
    csrr     t2, fflags

    /* fcvt.l.s(NaN) -> INT64_MAX, NV.  The conversion is invalid, not
       inexact, so NX must stay clear; an all-ones exponent also looks like an
       enormous shift, which is what made the underflow term fire.            */
    FLD32    fa1, 0x7FC00000
    SETRM    0
    fcvt.l.s t1, fa1
    csrr     t2, fflags

    /* fcvt.lu.s(NaN) -> UINT64_MAX, NV, again without NX.                    */
    FLD32    fa1, 0x7FC00000
    SETRM    0
    fcvt.lu.s t1, fa1
    csrr     t2, fflags

    /* fcvt.l.s(-inf) -> INT64_MIN, NV, without NX.                           */
    FLD32    fa1, 0xFF800000
    SETRM    0
    fcvt.l.s t1, fa1
    csrr     t2, fflags

    /* fcvt.d.s(sNaN) -> canonical DP qNaN, NV.                              */
    FLD32    fa1, 0x7F800001
    SETRM    0
    fcvt.d.s ft0, fa1
    OBSERVE64

    /* fcvt.w.s(0.1) under round-up -> 1, NX.  The converter must apply the
       rounding mode to the magnitude, not truncate.                         */
    FLD32    fa1, 0x3DCCCCCD
    SETRM    3
    fcvt.w.s t1, fa1
    csrr     t2, fflags

    /* fcvt.w.s(0.9) under round-down -> 0, NX.                              */
    FLD32    fa1, 0x3F666666
    SETRM    2
    fcvt.w.s t1, fa1
    csrr     t2, fflags

    /* fcvt.w.s(-0.1) under round-down -> -1, NX.                            */
    FLD32    fa1, 0xBDCCCCCD
    SETRM    2
    fcvt.w.s t1, fa1
    csrr     t2, fflags

    /* fcvt.w.s(0.1) under round-to-nearest -> 0, NX (the mode that worked). */
    FLD32    fa1, 0x3DCCCCCD
    SETRM    0
    fcvt.w.s t1, fa1
    csrr     t2, fflags

    /* Same gap in the DP converter: it has an rm input but applies it only to
       the exc[3:1] tie-off, not to the conversion.                            */
    /* fcvt.w.d(0.1) under round-up -> 1, NX.                                 */
    FLD64    fa1, 0x3FB999999999999A
    SETRM    3
    fcvt.w.d t1, fa1
    csrr     t2, fflags

    /* fcvt.w.d(-0.1) under round-down -> -1, NX.                             */
    FLD64    fa1, 0xBFB999999999999A
    SETRM    2
    fcvt.w.d t1, fa1
    csrr     t2, fflags

    /* fcvt.l.d(-1.0-ulp) under round-down -> -2, NX.                         */
    FLD64    fa1, 0xBFF0000000000001
    SETRM    2
    fcvt.l.d t1, fa1
    csrr     t2, fflags

    /* fcvt.l.s(NaN) -> INT64_MAX, NV and no NX.                              */
    FLD32    fa1, 0x7FC00000
    SETRM    0
    fcvt.l.s t1, fa1
    csrr     t2, fflags

    /* fcvt.lu.s(NaN) -> UINT64_MAX, NV and no NX.                            */
    FLD32    fa1, 0x7FC00000
    SETRM    0
    fcvt.lu.s t1, fa1
    csrr     t2, fflags

    /* fcvt.s.d(1.0000000000000002) -> 1.0 SP, NX.  A throwaway test once
       reported a mismatch here; lock-step against Spike says the RTL is
       right, so the case stays.                                             */
    FLD64    fa1, 0x3FF0000000000001
    SETRM    0
    fcvt.s.d ft0, fa1
    OBSERVE

/* Straight-line done.  Signal completion the way the other ASM tests do. */
    li       a1, 0x1000
    li       a2, 1
    sw       a2, 0(a1)
.Lhalt:
    j        .Lhalt
