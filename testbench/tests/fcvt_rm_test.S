/*
 * fcvt_rm_test.S - FCVT.S.W / FCVT.S.WU follow the instruction rm field.
 *
 * Why this shape
 * --------------
 * Both converters once carried a single rounding rule, round-to-nearest-even,
 * built from the round bit, the sticky bit and the result LSB.  The rm field
 * never reached it, so RTZ, RDN, RUP and RMM all behaved as RNE.  Every case
 * below picks operands where two rounding modes give different answers, so the
 * defect cannot hide.  Each case checks its own result against the value IEEE
 * 754 requires and reports through tohost; the cosim checks the same register
 * against Spike, which is the independent oracle.
 *
 *   16777217 = 2^24 + 1     SP spacing at 2^24 is 2, so the value is inexact
 *                           and RNE rounds to even (down), RUP rounds up.
 *  -16777217                same, with the direction reversed for RDN/RUP.
 *  4294967295 = 2^32 - 1    SP rounds to 2^32 or to 2^32 - 256; RUP gives 2^32.
 */

#define PASS_CODE 1
#define RESULT_BASE 0x2000
#define TOHOST 0x1000

/* Convert x5 with \rm, move the FP result back through an integer register so
   both the store and the check see the same bits, then verify. */
.macro CONV op, rm, src, exp
  li      x5, \src
  \op     f1, x5, \rm
  fmv.x.w x5, f1
  sw      x5, 0(a0)
  addi    a0, a0, 4
  li      t2, \exp
  /* fmv.x.w sign-extends bit 31, so compare the low 32 bits only */
  slli    t3, x5, 32
  srli    t3, t3, 32
  bne     t3, t2, fail
.endm

.section .text
.globl _start
_start:
  li    a0, RESULT_BASE

  /* 2^24 + 1, all five modes */
  CONV  fcvt.s.w,  rtz, 16777217,  0x4b800000
  CONV  fcvt.s.w,  rup, 16777217,  0x4b800001
  CONV  fcvt.s.w,  rdn, 16777217,  0x4b800000
  CONV  fcvt.s.w,  rne, 16777217,  0x4b800000
  CONV  fcvt.s.w,  rmm, 16777217,  0x4b800001

  /* -(2^24 + 1), all five modes */
  CONV  fcvt.s.w,  rtz, -16777217, 0xcb800000
  CONV  fcvt.s.w,  rup, -16777217, 0xcb800000
  CONV  fcvt.s.w,  rdn, -16777217, 0xcb800001
  CONV  fcvt.s.w,  rne, -16777217, 0xcb800000
  CONV  fcvt.s.w,  rmm, -16777217, 0xcb800001

  /* 2^32 - 1 read as unsigned: the source is zero-extended, so RDN moves up */
  CONV  fcvt.s.wu, rtz, -1,        0x4f7fffff
  CONV  fcvt.s.wu, rup, -1,        0x4f800000
  CONV  fcvt.s.wu, rdn, -1,        0x4f7fffff
  CONV  fcvt.s.wu, rne, -1,        0x4f800000
  CONV  fcvt.s.wu, rmm, -1,        0x4f800000

  li    t1, PASS_CODE
  j     report

fail:
  mv    t1, a0      /* tohost carries the failing slot address */

report:
  li    t0, TOHOST
  sw    t1, 0(t0)
  j     .
