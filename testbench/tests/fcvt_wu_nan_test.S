.section .text
.globl main
main:
    li x5, 0x7ff0000000000001
    fmv.d.x f0, x5
    fcvt.wu.d x1, f0, rmm
    frflags x2
    li x3, 0x10
    bne x2, x3, fail
pass:
    li x1, 0x1000
    li x2, 1
    sw x2, 0(x1)
1:  j 1b
fail:
    li x1, 0x1000
    li x2, 2
    sw x2, 0(x1)
2:  j 2b
