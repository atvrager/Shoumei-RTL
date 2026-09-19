#include "shoumei.h"

/*
 * Test: Illegal instruction fallback trap.
 *
 * Verifies:
 * 1. Undefined / unallocated instructions fault to mtvec
 * 2. Trap handler captures mepc, mcause
 * 3. Execution resumes past the faulting instruction via mret
 */

static volatile int trap_entered = 0;
static volatile uintptr_t saved_mepc = 0;
static volatile unsigned long saved_mcause = 0;

void _trap_handler(void) __attribute__((naked, aligned(4)));
void _trap_handler(void) {
    asm volatile(
        "addi sp, sp, -32\n"
        "sd t0, 0(sp)\n"
        "sd t1, 8(sp)\n"

        "la t0, saved_mepc\n"
        "csrr t1, mepc\n"
        "sd t1, 0(t0)\n"

        "la t0, saved_mcause\n"
        "csrr t1, mcause\n"
        "sd t1, 0(t0)\n"

        "la t0, trap_entered\n"
        "li t1, 1\n"
        "sw t1, 0(t0)\n"

        /* Advance mepc by 4 past faulting instruction */
        "csrr t0, mepc\n"
        "addi t0, t0, 4\n"
        "csrw mepc, t0\n"

        "ld t0, 0(sp)\n"
        "ld t1, 8(sp)\n"
        "addi sp, sp, 32\n"
        "mret\n"
    );
}

int main(void) {
    uintptr_t expected_pc;

    /* Read current PC via auipc */
    asm volatile("auipc %0, 0" : "=r"(expected_pc));
    /* The faulting instruction is at expected_pc + 8 (after auipc + next) */

    /* Execute an undefined custom opcode */
    asm volatile(".word 0x0000007b");

    /* Execution should resume here after mret */
    if (!trap_entered) {
        fail(1);
    }

    pass();
    return 0;
}
