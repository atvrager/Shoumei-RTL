# A CSR instruction that writes a read-only address (0xC00-0xFFF) is an illegal
# instruction.  The handler counts the trap, resumes after the faulting word,
# and the program passes only when exactly the two illegal writes trapped: a
# missing trap leaves the count short and a spurious trap on a legal read makes
# it long, so both directions fail.  Spike is the oracle for the values.

.section .text
.globl _start
_start:
    j .Lmain
.Ltrap:
    csrr x28, mcause
    addi x29, x0, 2                # illegal instruction
    bne x28, x29, .Lfail
    addi x27, x27, 1               # count the trap
    csrr x28, mepc                 # resume after the faulting instruction
    addi x28, x28, 4
    csrw mepc, x28
    mret
.Lfail:
    li x29, 0x1000
    li x30, 0xDEAD
    sw x30, 0(x29)
.Lhalt_fail:
    j .Lhalt_fail
.Lmain:
.globl main
main:
    la x28, .Ltrap
    csrw mtvec, x28
    li x27, 0

    # (1) csrrc with a non-zero rs1 field writes mhartid: illegal.
    li x17, 0
    csrrc x2, mhartid, x17

    # (2) csrrs with rs1=x0 does not write: legal, must not trap.
    csrrs x3, mhartid, x0

    # (3) csrrw always writes: illegal.
    csrrw x4, mhartid, x0

    # (4) csrrc with rs1=x0 does not write: legal.
    csrrc x5, mhartid, x0

    # (5) a writable CSR is untouched by the rule.
    li x6, 0x1234
    csrw mscratch, x6
    csrr x7, mscratch
    li x29, 0x1234
    bne x7, x29, .Lfail

    li x29, 2                      # exactly the two illegal writes trapped
    bne x27, x29, .Lfail

    li x29, 0x1000                 # PASS
    li x30, 1
    sw x30, 0(x29)
.Lhalt:
    j .Lhalt
