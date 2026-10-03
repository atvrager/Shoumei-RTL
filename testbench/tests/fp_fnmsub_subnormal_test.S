/*
 * fp_fnmsub_subnormal_test.S - verify negative subnormal carry preservation in FMA.
 *
 * When a negative subnormal product rounds toward negative infinity,
 * the mantissa can carry out into the smallest normal number.
 * The sign bit must remain negative.
 */

#define PASS_CODE 1
#define RESULT_BASE 0x2000
#define TOHOST 0x1000

#define DP_ONE_MINUS_ULP 0x3FEFFFFFFFFFFFFF
#define DP_SMALLEST_NORM 0x0010000000000000
#define DP_EXP_RES       0x8010000000000000
#define ZERO             0x0000000000000000

#define SP_ONE_MINUS_ULP 0x3F7FFFFF
#define SP_SMALLEST_NORM 0x00800000
#define SP_EXP_RES       0x80800000
#define SP_ZERO          0x00000000

.section .text
.globl _start
_start:
  li      a0, RESULT_BASE

  /* Test 1: Double-precision fnmsub with subnormal carry under rdn */
  li      x5, DP_ONE_MINUS_ULP
  fmv.d.x f1, x5
  li      x5, DP_SMALLEST_NORM
  fmv.d.x f2, x5
  li      x5, ZERO
  fmv.d.x f3, x5
  fnmsub.d f5, f1, f2, f3, rdn
  fmv.x.d x5, f5
  sd      x5, 0(a0)
  addi    a0, a0, 8
  li      t2, DP_EXP_RES
  bne     x5, t2, fail

  /* Test 2: Single-precision fnmsub with subnormal carry under rdn */
  li      x5, SP_ONE_MINUS_ULP
  fmv.w.x f1, x5
  li      x5, SP_SMALLEST_NORM
  fmv.w.x f2, x5
  li      x5, SP_ZERO
  fmv.w.x f3, x5
  fnmsub.s f5, f1, f2, f3, rdn
  fmv.x.w x5, f5
  sw      x5, 0(a0)
  addi    a0, a0, 4
  li      t2, SP_EXP_RES
  slli    t3, x5, 32
  srli    t3, t3, 32
  slli    t2, t2, 32
  srli    t2, t2, 32
  bne     t3, t2, fail

  li      t1, PASS_CODE
  j       report

fail:
  mv      t1, a0

report:
  li      t0, TOHOST
  sw      t1, 0(t0)
  j       .
