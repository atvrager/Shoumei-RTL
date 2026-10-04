/*
 * fp_fma_zero_test.S - the sign of an exact zero out of the fused multiply-add.
 *
 * IEEE 754 section 6.3: when the sum of two operands with opposite signs is
 * exactly zero, the sign is +0 in every rounding mode except round toward
 * negative, where it is -0.  Two zeros of the same sign keep that sign.  The
 * sign used to come from whichever exponent the magnitude comparison picked,
 * so 1.0 * -0.0 + 0.0 returned -0.0 where the reference returns +0.0.
 *
 * Every case here has an exactly zero result, from cancelling magnitudes or
 * from zero operands, so the sign is the only thing under test.  The cosim
 * checks the same register against Spike.
 */

#define PASS_CODE 1
#define RESULT_BASE 0x2000
#define TOHOST 0x1000

#define PZERO 0x0000000000000000
#define NZERO 0x8000000000000000
#define ONE   0x3FF0000000000000
#define NEG_ONE 0xBFF0000000000000
#define FLT_PZERO 0x00000000
#define FLT_NZERO 0x80000000
#define FLT_ONE 0x3F800000
#define FLT_NEG_ONE 0xBF800000

/* f1 = \a, f2 = \b, f3 = \c, fused op under \rm, compare the 64-bit result. */
.macro FMA64 op, rm, a, b, c, exp
  li      x5, \a
  fmv.d.x f1, x5
  li      x5, \b
  fmv.d.x f2, x5
  li      x5, \c
  fmv.d.x f3, x5
  \op     f5, f1, f2, f3, \rm
  fmv.x.d x5, f5
  sd      x5, 0(a0)
  addi    a0, a0, 8
  li      t2, \exp
  bne     x5, t2, fail
.endm

/* The same for single precision. */
.macro FMA32 op, rm, a, b, c, exp
  li      x5, \a
  fmv.w.x f1, x5
  li      x5, \b
  fmv.w.x f2, x5
  li      x5, \c
  fmv.w.x f3, x5
  \op     f5, f1, f2, f3, \rm
  fmv.x.w x5, f5
  sw      x5, 0(a0)
  addi    a0, a0, 4
  li      t2, \exp
  slli    t3, x5, 32
  srli    t3, t3, 32
  slli    t2, t2, 32
  srli    t2, t2, 32
  bne     t3, t2, fail
.endm

.section .text
.globl _start
_start:
  li    a0, RESULT_BASE

  /* A zero product and a zero addend of opposite signs give +0 */
  FMA64 fmadd.d, rne, ONE, NZERO, PZERO, PZERO
  FMA64 fmadd.d, rne, NEG_ONE, PZERO, NZERO, NZERO /* both -0: same sign */
  /* ... and -0 toward negative infinity */
  FMA64 fmadd.d, rdn, ONE, NZERO, PZERO, NZERO
  FMA64 fmadd.d, rdn, NEG_ONE, PZERO, NZERO, NZERO
  /* Two zeros of the same sign keep that sign, in every mode */
  FMA64 fmadd.d, rne, ONE, NZERO, NZERO, NZERO
  FMA64 fmadd.d, rdn, ONE, NZERO, NZERO, NZERO
  FMA64 fmadd.d, rne, ONE, PZERO, PZERO, PZERO
  /* Nonzero magnitudes that cancel exactly behave the same way */
  FMA64 fmadd.d, rne, ONE, ONE, NEG_ONE, PZERO
  FMA64 fmadd.d, rdn, ONE, ONE, NEG_ONE, NZERO
  FMA64 fmadd.d, rne, NEG_ONE, ONE, ONE, PZERO
  /* fmsub subtracts the addend: -0 - +0 is -0, +0 - +0 is +0 */
  FMA64 fmsub.d, rne, ONE, NZERO, PZERO, NZERO
  FMA64 fmsub.d, rne, ONE, PZERO, PZERO, PZERO
  FMA64 fmsub.d, rne, ONE, ONE, ONE, PZERO

  /* The same shapes in single precision */
  FMA32 fmadd.s, rne, FLT_ONE, FLT_NZERO, FLT_PZERO, FLT_PZERO
  FMA32 fmadd.s, rdn, FLT_ONE, FLT_NZERO, FLT_PZERO, FLT_NZERO
  FMA32 fmadd.s, rne, FLT_ONE, FLT_NZERO, FLT_NZERO, FLT_NZERO
  FMA32 fmadd.s, rne, FLT_ONE, FLT_ONE, FLT_NEG_ONE, FLT_PZERO
  FMA32 fmadd.s, rdn, FLT_ONE, FLT_ONE, FLT_NEG_ONE, FLT_NZERO

  li    t1, PASS_CODE
  j     report

fail:
  mv    t1, a0      /* tohost carries the failing slot address */

report:
  li    t0, TOHOST
  sw    t1, 0(t0)
  j     .
