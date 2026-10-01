/*
 * amo_ret_test.S - the value an atomic returns, and what it leaves in memory.
 *
 * The random streams diverged on amoxor.w with both aq and rl set: the RTL
 * returned the address where the reference returned the old memory word.  Every
 * atomic returns the value the location held before the operation, so the
 * expectation here is simply that: the first read of each location.  The cosim
 * checks the same registers against Spike.
 *
 * aq and rl are exercised separately because the failing case had both set.
 */

#define PASS_CODE 1
#define RESULT_BASE 0x4000
#define TOHOST 0x1000
#define MEM 0x3000

/* Store a base word, apply the atomic, read the word back and compare. */
.macro MEMCASE op, base, arg, want
  li    t0, \base
  sd    t0, 0(s0)
  li    t1, \arg
  \op   t2, t1, (s0)
  ld    t3, 0(s0)
  sd    t3, 0(a0)
  addi  a0, a0, 8
  li    t4, \want
  bne   t3, t4, fail
.endm

/* The word forms leave the upper half alone, so read the word back with a
   sign-extending lw; the double forms need the whole 64-bit word. */
.macro MEMCASEW op, base, arg, want
  li    t0, \base
  sd    t0, 0(s0)
  li    t1, \arg
  \op   t2, t1, (s0)
  lw    t3, 0(s0)
  sd    t3, 0(a0)
  addi  a0, a0, 8
  li    t4, \want
  bne   t3, t4, fail
.endm

.section .text
.globl _start
_start:
  li    a0, RESULT_BASE
  li    s0, MEM

  /* amoadd.w, no ordering, then with both bits set */
  li    t0, 0x12345678
  sw    t0, 0(s0)
  li    t1, 0x00000001
  amoadd.w t2, t1, (s0)
  sd    t2, 0(a0)
  addi  a0, a0, 8
  li    t3, 0x12345678
  bne   t2, t3, fail

  li    t0, 0x12345678
  sw    t0, 0(s0)
  amoadd.w.aqrl t2, t1, (s0)
  sd    t2, 0(a0)
  addi  a0, a0, 8
  bne   t2, t3, fail

  /* amoxor.w with both bits: the shape the streams diverged on */
  li    t0, 0x12345678
  sw    t0, 0(s0)
  li    t1, 0x0000ffff
  amoxor.w.aqrl t2, t1, (s0)
  sd    t2, 0(a0)
  addi  a0, a0, 8
  li    t3, 0x12345678
  bne   t2, t3, fail

  /* amoswap.w */
  li    t0, 0x12345678
  sw    t0, 0(s0)
  li    t1, 0x0000ffff
  amoswap.w.aqrl t2, t1, (s0)
  sd    t2, 0(a0)
  addi  a0, a0, 8
  bne   t2, t3, fail

  /* amoand.w, amoor.w */
  li    t0, 0x12345678
  sw    t0, 0(s0)
  li    t1, 0x0000ffff
  amoand.w.aqrl t2, t1, (s0)
  sd    t2, 0(a0)
  addi  a0, a0, 8
  bne   t2, t3, fail

  li    t0, 0x12345678
  sw    t0, 0(s0)
  amoor.w.aqrl t2, t1, (s0)
  sd    t2, 0(a0)
  addi  a0, a0, 8
  bne   t2, t3, fail

  /* amomin.w / amomax.w with a negative word in memory */
  li    t0, 0xfffffff0
  sw    t0, 0(s0)
  li    t1, 0x00000001
  amomin.w.aqrl t2, t1, (s0)
  sd    t2, 0(a0)
  addi  a0, a0, 8
  li    t3, 0xfffffffffffffff0
  bne   t2, t3, fail

  li    t0, 0xfffffff0
  sw    t0, 0(s0)
  amomax.w.aqrl t2, t1, (s0)
  sd    t2, 0(a0)
  addi  a0, a0, 8
  li    t3, 0xfffffffffffffff0
  bne   t2, t3, fail

  /* A 64-bit atomic, whose return is the full word */
  li    t0, 0x0123456789abcdef
  sd    t0, 0(s0)
  li    t1, 1
  amoadd.d.aqrl t2, t1, (s0)
  sd    t2, 0(a0)
  addi  a0, a0, 8
  li    t3, 0x0123456789abcdef
  bne   t2, t3, fail

  /* A location holding zero: the reference returned 0 for the failing
     instruction, while the RTL returned the address. */
  li    t0, 0
  sw    t0, 0(s0)
  li    t1, 0x0000ffff
  amoxor.w.aqrl t2, t1, (s0)
  sd    t2, 0(a0)
  addi  a0, a0, 8
  bne   t2, zero, fail

  li    t0, 0
  sw    t0, 0(s0)
  li    t1, 0x00000001
  amoadd.w.aqrl t2, t1, (s0)
  sd    t2, 0(a0)
  addi  a0, a0, 8
  bne   t2, zero, fail

  /* rd and rs1 the same register, and the same with a zero location */
  li    t0, 0
  sw    t0, 0(s0)
  amoswap.w.aqrl s0, t1, (s0)
  sd    s0, 0(a0)
  addi  a0, a0, 8
  bne   s0, zero, fail
  li    s0, MEM

  /* The random programs operate at 0x2000, and may or may not be aligned.
     Both the address and the alignment are tried here. */
  li    s0, 0x2000
  li    t0, 0
  sw    t0, 0(s0)
  li    t1, 0x0000ffff
  amoxor.w.aqrl t2, t1, (s0)
  sd    t2, 0(a0)
  addi  a0, a0, 8
  bne   t2, zero, fail

  li    s0, 0x2004
  li    t0, 0x12345678
  sw    t0, 0(s0)
  li    t1, 0x0000ffff
  amoadd.w.aqrl t2, t1, (s0)
  sd    t2, 0(a0)
  addi  a0, a0, 8
  li    t3, 0x12345678
  bne   t2, t3, fail

  li    s0, 0x2008
  li    t0, 0
  lw    t0, 0(s0)
  amoswap.w.aqrl t2, t1, (s0)
  sd    t2, 0(a0)
  addi  a0, a0, 8
  bne   t2, zero, fail

  li    s0, MEM

  /* Two atomics back to back, as the random programs issue them.  Their
     returns were swapped there, so the pair is what matters, not each alone. */
  li    s0, MEM
  li    t0, 0x11111111
  sw    t0, 0(s0)
  li    t0, 0x22222222
  sw    t0, 8(s0)
  li    t1, 0x00000001
  amoxor.w.aqrl t2, t1, (s0)
  addi  s1, s0, 8
  amoxor.w.aqrl t3, t1, (s1)
  sd    t2, 0(a0)
  sd    t3, 8(a0)
  addi  a0, a0, 16
  li    t4, 0x11111111
  bne   t2, t4, fail
  li    t4, 0x22222222
  bne   t3, t4, fail

  /* The same with amoswap, and with the second reading the first's result */
  li    t0, 0x33333333
  sw    t0, 0(s0)
  li    t0, 0x44444444
  sw    t0, 8(s0)
  li    t1, 0x55555555
  amoswap.w.aqrl t2, t1, (s0)
  addi  s1, s0, 8
  amoswap.w.aqrl t3, t1, (s1)
  sd    t2, 0(a0)
  sd    t3, 8(a0)
  addi  a0, a0, 16
  li    t4, 0x33333333
  bne   t2, t4, fail
  li    t4, 0x44444444
  bne   t3, t4, fail

  /* Two atomics to the SAME address, back to back.  The failing pair read
     and wrote one location, and their returns came out swapped: the second's
     read has to follow the first's write.  The first sees the old word, the
     second sees the first's result. */
  li    t0, 0x11111111
  sw    t0, 0(s0)
  li    t1, 0x00000001
  amoxor.w.aqrl t2, t1, (s0)
  amoadd.w.aqrl t3, t1, (s0)
  sd    t2, 0(a0)
  sd    t3, 8(a0)
  addi  a0, a0, 16
  li    t4, 0x11111111
  bne   t2, t4, fail
  li    t4, 0x11111110
  bne   t3, t4, fail

  /* The same in double precision, which is what the stream used */
  li    t0, 0x1111111111111111
  sd    t0, 0(s0)
  li    t1, 1
  amoxor.d.aqrl t2, t1, (s0)
  amoadd.d.aqrl t3, zero, (s0)
  sd    t2, 0(a0)
  sd    t3, 8(a0)
  addi  a0, a0, 16
  li    t4, 0x1111111111111111
  bne   t2, t4, fail
  li    t4, 0x1111111111111110
  bne   t3, t4, fail

  /* The failing pair exactly: the address register is also the data register,
     and the second atomic's data is x0.  amoxor.d then amoadd.d, both at one
     location, address and value both 0x2000. */
  li    t5, 0x2000
  li    t0, 0
  sd    t0, 0(t5)
  amoxor.d x12, t5, (t5)
  amoadd.d x21, x0, (t5)
  sd    x12, 0(a0)
  sd    x21, 8(a0)
  addi  a0, a0, 16
  bne   x12, zero, fail
  li    t4, 0x2000
  bne   x21, t4, fail

  /* What each function leaves in memory.  The return value does not depend on
     the function, so a wrong function select hides behind a correct return:
     the earlier cases passed while the RTL wrote the sum for an AND.  Each case
     here reads the location back and lets the cosim compare that read. */
  MEMCASE amoand.d,  5, 3, 1
  MEMCASE amoor.d,   5, 3, 7
  MEMCASE amoxor.d,  5, 3, 6
  MEMCASE amoadd.d,  5, 3, 8
  MEMCASE amoswap.d, 5, 3, 3
  MEMCASE amomin.d,  5, -3, -3
  MEMCASE amomax.d,  5, -3, 5
  MEMCASE amominu.d, 5, 3, 3
  MEMCASE amomaxu.d, 5, 3, 5
  MEMCASEW amoand.w,  5, 3, 1
  MEMCASEW amoor.w,   5, 3, 7
  MEMCASEW amoxor.w,  5, 3, 6
  MEMCASEW amoadd.w,  5, 3, 8
  MEMCASEW amoswap.w, 5, 3, 3
  MEMCASEW amomin.w,  5, -3, -3
  MEMCASEW amomax.w,  5, -3, 5
  MEMCASEW amominu.w, 5, 3, 3
  MEMCASEW amomaxu.w, 5, 3, 5

  /* An atomic's write leaves a response on the port its own read used.  A read
     issued before that response returns must not consume it: the value would be
     the atomic's new word rather than the word at the read's own address.  Here
     the atomic leaves 0xfa and a following load must read 0xfa, not the 5 the
     atomic read, nor the 5 ^ 0xff it wrote. */
  li    t0, 0x00003000
  li    t1, 5
  sd    t1, 0(t0)
  li    t2, 0x000000ff
  amoxor.d t3, t2, (t0)
  sd    t3, 0(a0)
  addi  a0, a0, 8
  ld    t4, 0(t0)
  sd    t4, 0(a0)
  addi  a0, a0, 8
  li    t5, 5
  bne   t3, t5, fail
  li    t5, 0xfa
  bne   t4, t5, fail

  li    t1, PASS_CODE
  j     report

fail:
  mv    t1, a0

report:
  li    t0, TOHOST
  sw    t1, 0(t0)
  j     .
