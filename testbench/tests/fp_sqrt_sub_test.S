/*
 * fp_sqrt_sub_test.S - subnormal and normal square roots, both precisions.
 *
 * A nonzero subnormal has no implicit leading bit, so the radicand setup, which
 * places that bit by construction, described a different number: the exponent
 * came out as if the field were zero.  The expected values below are the
 * correctly rounded results (round to nearest even), computed with exact
 * integer square roots and checked against the C library before being written
 * here.  The cosim checks the same registers against Spike.
 *
 * Subnormal radicands only, plus the boundary at the smallest normal and a few
 * ordinary values so that a fix for one cannot quietly break the other.
 */

#define PASS_CODE 1
#define RESULT_BASE 0x2000
#define TOHOST 0x1000

/* f1 = the double in \src, square root, check the full 64-bit result. */
.macro SQRTD src, exp
  li      x5, \src
  fmv.d.x f1, x5
  fsqrt.d f5, f1
  fmv.x.d x5, f5
  sd      x5, 0(a0)
  addi    a0, a0, 8
  li      t2, \exp
  bne     x5, t2, fail
.endm

/* f1 = the float in \src, square root, check the low 32 bits. */
.macro SQRTS src, exp
  li      x5, \src
  fmv.w.x f1, x5
  fsqrt.s f5, f1
  fmv.x.w x5, f5
  sw      x5, 0(a0)
  addi    a0, a0, 4
  li      t2, \exp
  slli    t3, x5, 32
  srli    t3, t3, 32
  bne     t3, t2, fail
.endm

.section .text
.globl _start
_start:
  li    a0, RESULT_BASE

  /* Double: subnormal radicands, then the smallest normal and ordinary values */
  SQRTD 0x0000000000000001, 0x1e60000000000000   /* 2^-1074   -> 2^-537 */
  SQRTD 0x0000000000000004, 0x1e70000000000000   /* 2^-1072   -> 2^-536 */
  SQRTD 0x0000000000000009, 0x1e78000000000000   /* 9*2^-1074 -> 3*2^-537 */
  SQRTD 0x0000000000000010, 0x1e80000000000000   /* 2^-1070   -> 2^-535 */
  SQRTD 0x000fffffffffffff, 0x1fffffffffffffff   /* largest subnormal */
  SQRTD 0x0008000000000000, 0x1ff6a09e667f3bcd   /* mid subnormal */
  SQRTD 0x0010000000000000, 0x2000000000000000   /* 2^-1022   -> 2^-511 */
  SQRTD 0x4000000000000000, 0x3ff6a09e667f3bcd   /* 2.0       -> sqrt 2 */
  SQRTD 0x4010000000000000, 0x4000000000000000   /* 4.0       -> 2.0 */
  SQRTD 0x5000000000000000, 0x47f6a09e667f3bcd   /* 2^65      -> 2^32.5 */

  /* Single: the same shapes */
  SQRTS 0x00000001, 0x1a3504f3                   /* 2^-149    */
  SQRTS 0x00000004, 0x1ab504f3                   /* 2^-147    */
  SQRTS 0x00000009, 0x1b07c3b6                   /* 9*2^-149  */
  SQRTS 0x00000010, 0x1b3504f3                   /* 2^-145    */
  SQRTS 0x007fffff, 0x1fffffff                   /* largest subnormal */
  SQRTS 0x00400000, 0x1fb504f3                   /* mid subnormal */
  SQRTS 0x00800000, 0x20000000                   /* 2^-126    */
  SQRTS 0x40000000, 0x3fb504f3                   /* 2.0       */
  SQRTS 0x40800000, 0x40000000                   /* 4.0       */
  SQRTS 0x50000000, 0x47b504f3                   /* 2^65      */

  li    t1, PASS_CODE
  j     report

fail:
  mv    t1, a0      /* tohost carries the failing slot address */

report:
  li    t0, TOHOST
  sw    t1, 0(t0)
  j     .
