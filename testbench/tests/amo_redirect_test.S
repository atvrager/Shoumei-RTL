# An AMO behind a redirect that resolves late must not write memory before it
# commits.  The ROB retires in order, so an older `jalr` whose target is the
# fall-through still redirects: the instructions fetched past it are discarded
# and refetched.  A younger AMO can reach the memory unit and complete its
# read-modify-write before that redirect fires.  Its write cannot be undone, so
# the refetched AMO then reads the value its discarded execution wrote.
#
# The 40 adds delay the jalr's retire, which is what opens that window.  The
# AMO's old value must be 0 (the initialised word); 4 means the discarded
# execution wrote it.

.section .text
.globl _start
_start:
    j .Lmain
.Ltrap:
    csrr x28, mepc
    addi x28, x28, 4
    csrw mepc, x28
    mret
.Lmain:
.globl main
main:
    la x28, .Ltrap
    csrw mtvec, x28

    li x31, 0x2000
    sd x0, 0(x31)                  # word = 0
    li x6, 4
    li x5, 0

    .rept 40
    addi x5, x5, 1
    .endr

    auipc x1, 0                    # jalr to the fall-through...
    jalr x1, 8(x1)                 # ...still redirects, discarding the AMO

    .word 0x406fb42f               # amoor.d x8, x6, (x31); old value must be 0
    li x9, 0
    bne x8, x9, .Lfail

    ld x10, 0(x31)                 # and the word must end up 4
    li x11, 4
    bne x10, x11, .Lfail

    li x1, 0x1000                  # PASS
    li x2, 1
    sw x2, 0(x1)
.Lhalt:
    j .Lhalt
.Lfail:
    li x1, 0x1000                  # FAIL
    li x2, 0
    sw x2, 0(x1)
    j .Lhalt
