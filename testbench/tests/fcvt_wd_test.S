/*
 * fcvt_wd_test.S - FCVT.W.D rounding, and the 64-bit form.
 *
 * The module-level test in testbench/directed/fpdblconv-directed.sv pins the
 * converter's rounding directly.  This one drives the same path through the CPU
 * so the cosim compares the integer writeback against Spike: the module fix and
 * the end-to-end behaviour are separate claims.
 *
 * The guard and sticky of the converter come from a second shifter on the
 * truncation amount less one, so every case below has a fractional part.  1.5,
 * 2.5 and 3.5 are exact ties: round to nearest must take the even one.
 */

#define PASS_CODE 1
#define RESULT_BASE 0x2000
#define TOHOST 0x1000

/* Convert the double in \src under \rm, store the low 32 bits, check them. */
.macro CW rm, src, exp
  li      x5, \src
  fmv.d.x f1, x5
  fcvt.w.d x5, f1, \rm
  sw      x5, 0(a0)
  addi    a0, a0, 4
  li      t2, \exp
  /* fcvt.w.d sign-extends, so compare the low 32 bits only; the expected
     values for negative results are written as their 32-bit patterns */
  slli    t3, x5, 32
  srli    t3, t3, 32
  slli    t2, t2, 32
  srli    t2, t2, 32
  bne     t3, t2, fail
.endm

/* The 64-bit double form; the whole result is compared. */
.macro CL rm, src, exp
  li      x5, \src
  fmv.d.x f1, x5
  fcvt.l.d x5, f1, \rm
  sd      x5, 0(a0)
  addi    a0, a0, 8
  li      t2, \exp
  bne     x5, t2, fail
.endm

/* The 64-bit single form, which takes the same conversion path. */
.macro CS rm, src, exp
  li      x5, \src
  fmv.w.x f1, x5
  fcvt.l.s x5, f1, \rm
  sd      x5, 0(a0)
  addi    a0, a0, 8
  li      t2, \exp
  bne     x5, t2, fail
.endm

/* The 32-bit single form; fcvt.w.s also sign-extends. */
.macro CSW rm, src, exp
  li      x5, \src
  fmv.w.x f1, x5
  fcvt.w.s x5, f1, \rm
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

  /* Ties: round to nearest takes the even one */
  CW    rne, 0x3FF8000000000000, 2            /*  1.5 -> 2 */
  CW    rne, 0x4004000000000000, 2            /*  2.5 -> 2 */
  CW    rne, 0x400C000000000000, 4            /*  3.5 -> 4 */
  CW    rne, 0x3FE0000000000000, 0            /*  0.5 -> 0 */

  /* Not a tie */
  CW    rne, 0x3FF4000000000000, 1            /*  1.25 -> 1 */
  CW    rtz, 0x3FF8000000000000, 1            /*  1.5  -> 1 */
  CW    rup, 0x3FF8000000000000, 2            /*  1.5  -> 2 */

  /* Negative ties */
  CW    rdn, 0xBFF8000000000000, 0xFFFFFFFE           /* -1.5 -> -2 */
  CW    rtz, 0xBFF8000000000000, 0xFFFFFFFF           /* -1.5 -> -1 */
  CW    rup, 0xBFF8000000000000, 0xFFFFFFFF           /* -1.5 -> -1 */

  /* Either side of the half, where a dead guard would round the wrong way */
  CW    rne, 0x3FDFFFFFFFFFFFFF, 0            /*  0.4999999999999999 -> 0 */
  CW    rne, 0x3FE0000000000001, 1            /*  0.5000000000000001 -> 1 */

  /* The 64-bit forms, which take the long conversion path. */
  CL    rne, 0x3FF8000000000000, 2            /*  1.5 -> 2 */
  CL    rne, 0x4004000000000000, 2            /*  2.5 -> 2 (tie to even) */
  CL    rtz, 0x3FF8000000000000, 1            /*  1.5 -> 1 */
  CL    rup, 0x3FF8000000000000, 2            /*  1.5 -> 2 */
  CL    rdn, 0xBFF8000000000000, -2           /* -1.5 -> -2 */
  CL    rne, 0x3FDFFFFFFFFFFFFF, 0            /*  0.4999999999999999 -> 0 */
  CL    rne, 0x3FE0000000000001, 1            /*  0.5000000000000001 -> 1 */
  CL    rne, 0x4260000000000000, 0x8000000000 /*  2^39 */
  CL    rne, 0x4330000000000000, 0x10000000000000 /* 2^52, exact */
  CL    rne, 0x43D0000000000000, 0x4000000000000000 /* 2^62, exact */

  /* The smallest normal double has a zero fraction, so its guard and sticky
     bits are both cleared while the value is nonzero and below one half.  A
     remainder below the guard still exists, and the direction decides between
     zero and one. */
  CL    rdn, 0x8010000000000000, -1           /* -2^-1022 -> -1 */
  CL    rtz, 0x8010000000000000, 0
  CL    rne, 0x8010000000000000, 0
  CL    rup, 0x8010000000000000, 0
  CL    rup, 0x0010000000000000, 1            /*  2^-1022 -> 1 */
  CL    rdn, 0x0010000000000000, 0
  CL    rne, 0x0010000000000000, 0

  /* The single-precision forms, which take the same path */
  CS    rne, 0x3FC00000, 2                    /*  1.5 -> 2 */
  CS    rtz, 0x3FC00000, 1                    /*  1.5 -> 1 */
  CSW   rne, 0x40200000, 2                    /*  2.5 -> 2 (tie to even) */
  CSW   rne, 0x3FC00000, 2                    /*  1.5 -> 2 */

  li    t1, PASS_CODE
  j     report

fail:
  mv    t1, a0      /* tohost carries the failing slot address */

report:
  li    t0, TOHOST
  sw    t1, 0(t0)
  j     .
