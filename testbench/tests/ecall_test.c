#include "shoumei.h"

/*
 * ECALL trap test.
 *
 * Verifies the microcode TRAP_ENTRY sequence:
 * 1. ECALL triggers a trap
 * 2. mepc points to the ECALL instruction (not PC+4)
 * 3. mcause = 11 (environment call from M-mode)
 * 4. mstatus.MIE = 0, mstatus.MPIE = old MIE, mstatus.MPP = M (0b11)
 * 5. Execution continues at mtvec
 */

/* Trap handler flag: set by our trap handler */
static volatile int trap_entered = 0;
static volatile uintptr_t saved_mepc = 0;
static volatile unsigned long saved_mcause = 0;
static volatile unsigned long saved_mstatus = 0;

/*
 * Custom trap handler (overrides weak default in crt0.S).
 * Reads mepc/mcause/mstatus, saves them, then returns to mepc+4.
 */
void _trap_handler(void) __attribute__((naked, aligned(4)));
void _trap_handler(void) {
    asm volatile(
        /* Save t0-t2 on stack (16-byte aligned) */
        "addi sp, sp, -32\n"
        "sd t0, 0(sp)\n"
        "sd t1, 8(sp)\n"
        "sd t2, 16(sp)\n"

        /* Read trap CSRs */
        "csrr t0, mepc\n"
        "csrr t1, mcause\n"
        "csrr t2, mstatus\n"

        /* Store to globals */
        "la t0, saved_mepc\n"
        "csrr t1, mepc\n"
        "sd t1, 0(t0)\n"

        "la t0, saved_mcause\n"
        "csrr t1, mcause\n"
        "sd t1, 0(t0)\n"

        "la t0, saved_mstatus\n"
        "csrr t1, mstatus\n"
        "sd t1, 0(t0)\n"

        /* Set trap_entered flag */
        "la t0, trap_entered\n"
        "li t1, 1\n"
        "sw t1, 0(t0)\n"

        /* Advance mepc past ECALL (mepc += 4) */
        "csrr t0, mepc\n"
        "addi t0, t0, 4\n"
        "csrw mepc, t0\n"

        /* Restore t0-t2 */
        "ld t0, 0(sp)\n"
        "ld t1, 8(sp)\n"
        "ld t2, 16(sp)\n"
        "addi sp, sp, 32\n"

        /* Return from trap (jump to mepc since MRET not yet implemented) */
        "csrr t0, mepc\n"
        "jr t0\n"
    );
}

int main(void) {
    /* Enable MIE so we can verify MPIE is set after trap */
    asm volatile("csrsi mstatus, 0x8");  /* mstatus.MIE = 1 */

    /* Record address of ECALL for mepc check */
    uintptr_t ecall_addr;
    asm volatile(
        "la %0, 1f\n"
        : "=r"(ecall_addr)
    );

    /* Execute ECALL */
    asm volatile(
        "1: ecall\n"
    );

    if (!trap_entered) { fail(10); return 0; }
    if (saved_mepc != ecall_addr) { fail(20); return 0; }
    if (saved_mcause != 11) { fail(30); return 0; }
    if (saved_mstatus & 0x8) { fail(40); return 0; }
    if (!(saved_mstatus & 0x80)) { fail(50); return 0; }
    if ((saved_mstatus & 0x1800) != 0x1800) { fail(60); return 0; }

    pass();
    return 0;
}
