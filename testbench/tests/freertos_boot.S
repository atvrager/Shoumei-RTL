.section .text.start, "ax"
.globl _start
_start:
    /* Set trap vector to FreeRTOS trap handler (direct mode) */
    la t0, freertos_risc_v_trap_handler
    csrw mtvec, t0

    /* Set up stack */
    la sp, _stack_top

    /* Zero BSS */
    la t0, __bss_start
    la t1, __bss_end
1:  bge t0, t1, 2f
    sw zero, 0(t0)
    addi t0, t0, 4
    j 1b
2:
    /* Jump to main */
    call main

    /* Should not return - signal pass via tohost */
    li t0, 0x1000
    li t1, 1
    sw t1, 0(t0)
3:  j 3b
