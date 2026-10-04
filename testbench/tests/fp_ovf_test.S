/*
 * fp_ovf_test.S - overflow saturation follows the rounding direction.
 *
 * IEEE 754 section 7.4: on overflow the result is an infinity only when the
 * rounding mode points away from zero for this sign.  Every other mode gives
 * the largest finite magnitude.  Concretely, for a positive overflow:
 *
 *   RTZ -> +max      RDN -> +max      RUP -> +inf      RNE -> +inf
 *
 * and for a negative overflow the two directions swap:
 *
 *   RTZ -> -max      RDN -> -inf      RUP -> -max      RNE -> -inf
 *
 * The values come out through fmv.x.d to an integer register, which the cosim
 * compares against Spike, so each case is checked twice: once here against the
 * constant in the source, and once against the reference model.
 */

#define PASS_CODE 1
#define RESULT_BASE 0x2000
#define TOHOST 0x1000

/* DBL_MAX = 0x7fefffffffffffff, FLT_MAX = 0x7f7fffff */
#define DBL_MAX 0x7fefffffffffffff
#define DBL_NEG_MAX 0xffefffffffffffff
#define DBL_INF 0x7ff0000000000000
#define DBL_NEG_INF 0xfff0000000000000
#define FLT_MAX 0x7f7fffff
#define FLT_NEG_MAX 0xff7fffff
#define FLT_INF 0x7f800000
#define FLT_NEG_INF 0xff800000

/* f1 = \src, multiply by 2.0 under \rm, check the 64-bit result. */
.macro MUL64 op, rm, src, two, exp
  li      x5, \src
  fmv.d.x f1, x5
  li      x5, \two
  fmv.d.x f2, x5
  \op     f5, f1, f2, \rm
  fmv.x.d x5, f5
  sd      x5, 0(a0)
  addi    a0, a0, 8
  li      t2, \exp
  bne     x5, t2, fail
.endm

/* f1 = \src, multiply by 2.0 under \rm, check the low 32 bits. */
.macro MUL32 op, rm, src, two, exp
  li      x5, \src
  fmv.w.x f1, x5
  li      x5, \two
  fmv.w.x f2, x5
  \op     f5, f1, f2, \rm
  fmv.x.w x5, f5
  sw      x5, 0(a0)
  addi    a0, a0, 4
  li      t2, \exp
  slli    t3, x5, 32
  srli    t3, t3, 32
  bne     t3, t2, fail
.endm

/* f1 = \a, f2 = \b, add under \rm, check the 64-bit result. */
.macro ADD64D rm, a, b, exp
  li      x5, \a
  fmv.d.x f1, x5
  li      x5, \b
  fmv.d.x f2, x5
  fadd.d  f5, f1, f2, \rm
  fmv.x.d x5, f5
  sd      x5, 0(a0)
  addi    a0, a0, 8
  li      t2, \exp
  bne     x5, t2, fail
.endm

/* f1 = \a, f2 = \b, f3 = 0: a single-rounding add of \a * \b. */
.macro FMA64D rm, a, b, exp
  li      x5, \a
  fmv.d.x f1, x5
  li      x5, \b
  fmv.d.x f2, x5
  fmv.d.x f3, x0
  fmadd.d f5, f1, f2, f3, \rm
  fmv.x.d x5, f5
  sd      x5, 0(a0)
  addi    a0, a0, 8
  li      t2, \exp
  bne     x5, t2, fail
.endm

/* f1 = \a, f2 = \b, add under \rm, check the low 32 bits. */
.macro ADD32 rm, a, b, exp
  li      x5, \a
  fmv.w.x f1, x5
  li      x5, \b
  fmv.w.x f2, x5
  fadd.s  f5, f1, f2, \rm
  fmv.x.w x5, f5
  sw      x5, 0(a0)
  addi    a0, a0, 4
  li      t2, \exp
  slli    t3, x5, 32
  srli    t3, t3, 32
  bne     t3, t2, fail
.endm

/* f1 = \a, f2 = \b, f3 = 0: a single-rounding add of \a * \b. */
.macro FMA32 rm, a, b, exp
  li      x5, \a
  fmv.w.x f1, x5
  li      x5, \b
  fmv.w.x f2, x5
  fmv.w.x f3, x0
  fmadd.s f5, f1, f2, f3, \rm
  fmv.x.w x5, f5
  sw      x5, 0(a0)
  addi    a0, a0, 4
  li      t2, \exp
  slli    t3, x5, 32
  srli    t3, t3, 32
  bne     t3, t2, fail
.endm

/* f1 = \a, f2 = \b, divide under \rm, check the 64-bit result. */
.macro DIV64D rm, a, b, exp
  li      x5, \a
  fmv.d.x f1, x5
  li      x5, \b
  fmv.d.x f2, x5
  fdiv.d  f5, f1, f2, \rm
  fmv.x.d x5, f5
  sd      x5, 0(a0)
  addi    a0, a0, 8
  li      t2, \exp
  bne     x5, t2, fail
.endm

/* f1 = \a, f2 = \b, divide under \rm, check the low 32 bits. */
.macro DIV32 rm, a, b, exp
  li      x5, \a
  fmv.w.x f1, x5
  li      x5, \b
  fmv.w.x f2, x5
  fdiv.s  f5, f1, f2, \rm
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

  /* Ordinary values first: an overflow guard that fires too widely would
     otherwise still pass every case below, since they all expect a saturated
     exponent anyway. */
  FMA32  rne, 0x40000000, 0x40000000, 0x40800000
  ADD32  rne, 0x3f800000, 0x3f800000, 0x40000000
  FMA64D rne, 0x4000000000000000, 0x4000000000000000, 0x4010000000000000
  ADD64D rne, 0x3ff0000000000000, 0x3ff0000000000000, 0x4000000000000000

  /* DP multiply by 2.0: positive overflow */
  MUL64 fmul.d, rtz, DBL_MAX, 0x4000000000000000, DBL_MAX
  MUL64 fmul.d, rdn, DBL_MAX, 0x4000000000000000, DBL_MAX
  MUL64 fmul.d, rup, DBL_MAX, 0x4000000000000000, DBL_INF
  MUL64 fmul.d, rne, DBL_MAX, 0x4000000000000000, DBL_INF

  /* DP multiply by 2.0: negative overflow */
  MUL64 fmul.d, rtz, DBL_NEG_MAX, 0x4000000000000000, DBL_NEG_MAX
  MUL64 fmul.d, rdn, DBL_NEG_MAX, 0x4000000000000000, DBL_NEG_INF
  MUL64 fmul.d, rup, DBL_NEG_MAX, 0x4000000000000000, DBL_NEG_MAX
  MUL64 fmul.d, rne, DBL_NEG_MAX, 0x4000000000000000, DBL_NEG_INF

  /* SP multiply by 2.0: both signs */
  MUL32 fmul.s, rtz, FLT_MAX, 0x40000000, FLT_MAX
  MUL32 fmul.s, rup, FLT_MAX, 0x40000000, FLT_INF
  MUL32 fmul.s, rtz, FLT_NEG_MAX, 0x40000000, FLT_NEG_MAX
  MUL32 fmul.s, rdn, FLT_NEG_MAX, 0x40000000, FLT_NEG_INF

/* The negated fused forms: fmsub is (a*b)-c, fnmsub is -(a*b)-c and fnmadd
   is -(a*b)+c.  The same unit produces them through a sign flip, and no case
   above covered them, so an overflow on the flipped path went unchecked. */
.macro NEGFMA64 op, rm, src, two, add, exp
  li      x5, \src
  fmv.d.x f1, x5
  li      x5, \two
  fmv.d.x f2, x5
  li      x5, \add
  fmv.d.x f3, x5
  \op     f5, f1, f2, f3, \rm
  fmv.x.d x5, f5
  sd      x5, 0(a0)
  addi    a0, a0, 8
  li      t2, \exp
  bne     x5, t2, fail
.endm

  /* a = DBL_MAX, b = 2.0, c = +0: all three overflow, positively for fmsub
     and negatively for the two negated forms. */
  NEGFMA64 fmsub.d,  rtz, DBL_MAX, 0x4000000000000000, 0, DBL_MAX
  NEGFMA64 fmsub.d,  rne, DBL_MAX, 0x4000000000000000, 0, DBL_INF
  NEGFMA64 fnmsub.d, rtz, DBL_MAX, 0x4000000000000000, 0, DBL_NEG_MAX
  NEGFMA64 fnmsub.d, rdn, DBL_MAX, 0x4000000000000000, 0, DBL_NEG_INF
  NEGFMA64 fnmadd.d, rtz, DBL_MAX, 0x4000000000000000, 0, DBL_NEG_MAX
  NEGFMA64 fnmadd.d, rup, DBL_MAX, 0x4000000000000000, 0, DBL_NEG_MAX

  /* SP fused multiply-add, then the add: same order */
  FMA32  rtz, FLT_MAX, 0x40000000, FLT_MAX
  FMA32  rup, FLT_MAX, 0x40000000, FLT_INF
  ADD32  rtz, FLT_MAX, FLT_MAX, FLT_MAX
  ADD32  rup, FLT_MAX, FLT_MAX, FLT_INF
  ADD32  rtz, FLT_NEG_MAX, FLT_NEG_MAX, FLT_NEG_MAX
  ADD32  rdn, FLT_NEG_MAX, FLT_NEG_MAX, FLT_NEG_INF

  /* DP fused multiply-add, zero addend: the product alone overflows */
  FMA64D rtz, DBL_MAX, 0x4000000000000000, DBL_MAX
  FMA64D rdn, DBL_MAX, 0x4000000000000000, DBL_MAX
  FMA64D rup, DBL_MAX, 0x4000000000000000, DBL_INF
  FMA64D rup, DBL_NEG_MAX, 0x4000000000000000, DBL_NEG_MAX

  /* DP add: positive and negative overflow through the adder */
  ADD64D rtz, DBL_MAX, DBL_MAX, DBL_MAX
  ADD64D rdn, DBL_MAX, DBL_MAX, DBL_MAX
  ADD64D rup, DBL_MAX, DBL_MAX, DBL_INF
  ADD64D rne, DBL_MAX, DBL_MAX, DBL_INF
  ADD64D rtz, DBL_NEG_MAX, DBL_NEG_MAX, DBL_NEG_MAX
  ADD64D rdn, DBL_NEG_MAX, DBL_NEG_MAX, DBL_NEG_INF
  ADD64D rup, DBL_NEG_MAX, DBL_NEG_MAX, DBL_NEG_MAX

  /* Division overflow, both signs, every direction.  DBL_MAX / 0.1 is ten
     times the largest double, so it overflows whatever the mode; the mode
     decides between infinity and the largest finite magnitude. */
  DIV64D rne, DBL_MAX, 0x3FB999999999999A, DBL_INF
  DIV64D rtz, DBL_MAX, 0x3FB999999999999A, DBL_MAX
  DIV64D rdn, DBL_MAX, 0x3FB999999999999A, DBL_MAX
  DIV64D rup, DBL_MAX, 0x3FB999999999999A, DBL_INF
  DIV64D rmm, DBL_MAX, 0x3FB999999999999A, DBL_INF
  DIV64D rne, DBL_MAX, 0xBFB999999999999A, DBL_NEG_INF
  DIV64D rtz, DBL_MAX, 0xBFB999999999999A, DBL_NEG_MAX
  DIV64D rdn, DBL_MAX, 0xBFB999999999999A, DBL_NEG_INF
  DIV64D rup, DBL_MAX, 0xBFB999999999999A, DBL_NEG_MAX
  DIV64D rmm, DBL_MAX, 0xBFB999999999999A, DBL_NEG_INF

  /* The same for the single-precision divider */
  DIV32 rne, FLT_MAX, 0x3DCCCCCD, FLT_INF
  DIV32 rtz, FLT_MAX, 0x3DCCCCCD, FLT_MAX
  DIV32 rup, FLT_MAX, 0x3DCCCCCD, FLT_INF
  DIV32 rdn, FLT_MAX, 0xBDCCCCCD, FLT_NEG_INF
  DIV32 rup, FLT_MAX, 0xBDCCCCCD, FLT_NEG_MAX

  li    t1, PASS_CODE
  j     report

fail:
  mv    t1, a0      /* tohost carries the failing slot address */

report:
  li    t0, TOHOST
  sw    t1, 0(t0)
  j     .
