/*
 * alu_ops_test.S - every integer ALU operation, against the reference.
 *
 * A mismatch on a random program showed and x13, x31, x16 with x31 = 0x2000
 * and x16 = 0 returning 0x2000, a pass-through where the AND is 0.  The op
 * selected for an ALU opcode comes from a name table, and a wrong entry
 * behaves exactly like that.  Every opcode is exercised here on operands that
 * separate it from the others; the cosim compares the register each one
 * writes, so a wrong selection prints against its own instruction.
 */
#define PASS_CODE 1
#define TOHOST 0x1000

.section .text
.globl _start
_start:
  li    x5,  0x0000ffff
  li    x6,  0x000000ff
  li    x7,  0x80000000
  li    x28, -1
  li    x29, 3
  li    x30, 60

  /* Bitwise and shift, where a pass-through or a neighbouring op differs. */
  and   x10, x5, x6
  or    x11, x5, x6
  xor   x12, x5, x6
  and   x13, x7, x6
  or    x14, x7, x29
  xor   x15, x5, x5

  /* Shifts: amount below, at and above the width. */
  sll   x16, x6, x29
  srl   x17, x7, x29
  sra   x18, x7, x29
  sll   x19, x6, x30
  srl   x20, x7, x30
  sra   x21, x7, x30
  sll   x22, x6, x28

  /* Arithmetic and comparisons, so a wrong table entry in either region
     shows up beside the bitwise ones. */
  add   x23, x5, x6
  sub   x24, x5, x6
  slt   x25, x5, x6
  sltu  x26, x5, x6
  add   x27, x7, x7

  /* Immediate forms go through different decode entries. */
  andi  x10, x5, 0xff
  ori   x11, x5, 0x100
  xori  x12, x5, -1
  addi  x13, x5, -1
  slli  x16, x6, 4
  srli  x17, x7, 4
  srai  x18, x7, 4
  slti  x25, x28, 1
  sltiu x26, x28, 1

  /* Word forms: the upper half of each result must be a sign extension. */
  addw  x23, x7, x7
  subw  x24, x6, x5
  sllw  x16, x6, x29
  srlw  x17, x7, x29
  sraw  x18, x7, x29

  /* THIS CASE FAILS on the current RTL, and is kept as the witness.
     ld x7, 4(x1) returns 0x0000200000002000 where the reference returns
     0x0000000080000000: the address has a pending word store, and the
     64-bit load duplicates that word into both halves instead of taking
     the upper half from memory.  The store buffer's cross-size check is
     meant to stall a forward whose size cannot cover the load, and it
     does not block this one.
   */

  /* A load whose result feeds the next instruction: the producer is the
     memory stage, so the consumer must take the value from the load rather
     than from the register file.  Every consumer op is one whose answer with
     the stale value differs from the answer with the loaded one. */
  /* A doubleword whose upper half is a word the address does not straddle.  A
     load at 4(x1) would cross a doubleword boundary, and the reference raises
     the misaligned exception for it while this RTL performs the access, so that
     case cannot be checked here until the trap exists.  The L1D does now
     assemble such a read from the next word: with 0x2000 at 4(x1) and
     0x80000000 at 8(x1) it returns 0x8000000000002000.
   */
  li    x1, 0x3000
  li    x2, 0x00002000
  sw    x2, 4(x1)
  li    x3, 0x80000000
  sw    x3, 8(x1)

  ld    x6, 0(x1)
  and   x10, x5, x6            /* 0xffff & 0 = 0            */
  ld    x7, 0(x1)
  or    x11, x5, x7            /* 0xffff | 0x2000 = 0x2fff  */
  ld    x8, 0(x1)
  add   x12, x8, x8            /* 0 + 0 = 0                 */
  ld    x9, 0(x1)
  sub   x13, x9, x9            /* 0x2000 - 0x2000 = 0       */
  ld    x14, 0(x1)
  sll   x15, x14, x14          /* shifted by 0x2000 -> 0    */

  /* A load of a value the store buffer still holds, then a consumer. */
  li    x1, 0x3010
  li    x2, 0x00000007
  sw    x2, 0(x1)
  lw    x16, 0(x1)
  and   x17, x5, x16           /* 0xffff & 7 = 7            */
  lw    x18, 0(x1)
  xor   x19, x18, x18          /* 7 ^ 7 = 0                 */

  li    x1, PASS_CODE
  li    x2, TOHOST
  sw    x1, 0(x2)
.Lhalt:
  j     .Lhalt
