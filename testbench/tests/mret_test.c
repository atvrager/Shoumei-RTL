#include "shoumei.h"

/*
 * MRET test: ECALL into trap handler, MRET back.
 * The trap handler is written in pure asm to be safe.
 */

void _trap_handler(void) __attribute__((naked, aligned(4)));
void _trap_handler(void) {
    asm volatile(
        /* Advance mepc past ECALL */
        "csrr t0, mepc\n"
        "addi t0, t0, 4\n"
        "csrw mepc, t0\n"
        "mret\n"
    );
}

int main(void) {
    /* Mark x10 = 0 before ECALL, will set to 1 after if MRET returns */
    register int result asm("a0") = 0;

    /* Enable MIE so MPIE=1 after trap */
    asm volatile("csrsi mstatus, 0x8");

    /* ECALL → trap handler → MRET back here */
    asm volatile("ecall" ::: "memory");

    /* If MRET worked, we continue here */
    result = 1;

    if (result)
        pass();
    else
        fail(4);

    return 0;
}
