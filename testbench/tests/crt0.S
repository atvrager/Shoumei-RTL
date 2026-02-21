.section .text.start, "ax"
.globl _start
.globl _trap_handler
_start:
    /* Set up trap vector (direct mode) */
    la t0, _trap_handler
    csrw mtvec, t0
    la sp, _stack_top
    call main
1:  j 1b

/*
 * Default trap handler.
 * Tests can override by defining their own _trap_handler (weak symbol).
 * Default behavior: spin forever (test fails on timeout).
 */
.weak _trap_handler
.balign 4
_trap_handler:
    j _trap_handler
