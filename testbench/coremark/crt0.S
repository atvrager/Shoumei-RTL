.section .text.start, "ax"
.globl _start
_start:
    la sp, _stack_top
    # Zero BSS
    la t0, __bss_start
    la t1, __bss_end
1:  bge t0, t1, 2f
    sw zero, 0(t0)
    addi t0, t0, 4
    j 1b
2:
    call main
    # Write return value to tohost (1 = pass)
    li t0, 1
    la t1, tohost
    sw t0, 0(t1)
3:  j 3b
