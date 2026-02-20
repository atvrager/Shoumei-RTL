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
static volatile uint32_t saved_mepc = 0;
static volatile uint32_t saved_mcause = 0;
static volatile uint32_t saved_mstatus = 0;

/*
 * Custom trap handler (overrides weak default in crt0.S).
 * Reads mepc/mcause/mstatus, saves them, then returns to mepc+4.
 */
void _trap_handler(void) __attribute__((naked, aligned(4)));
void _trap_handler(void) {
    asm volatile(
        /* Save t0-t2 on stack */
        "addi sp, sp, -12\n"
        "sw t0, 0(sp)\n"
        "sw t1, 4(sp)\n"
        "sw t2, 8(sp)\n"

        /* Read trap CSRs */
        "csrr t0, mepc\n"
        "csrr t1, mcause\n"
        "csrr t2, mstatus\n"

        /* Store to globals */
        "la t0, saved_mepc\n"
        "csrr t1, mepc\n"
        "sw t1, 0(t0)\n"

        "la t0, saved_mcause\n"
        "csrr t1, mcause\n"
        "sw t1, 0(t0)\n"

        "la t0, saved_mstatus\n"
        "csrr t1, mstatus\n"
        "sw t1, 0(t0)\n"

        /* Set trap_entered flag */
        "la t0, trap_entered\n"
        "li t1, 1\n"
        "sw t1, 0(t0)\n"

        /* Advance mepc past ECALL (mepc += 4) */
        "csrr t0, mepc\n"
        "addi t0, t0, 4\n"
        "csrw mepc, t0\n"

        /* Restore t0-t2 */
        "lw t0, 0(sp)\n"
        "lw t1, 4(sp)\n"
        "lw t2, 8(sp)\n"
        "addi sp, sp, 12\n"

        /* Return from trap (jump to mepc since MRET not yet implemented) */
        "csrr t0, mepc\n"
        "jr t0\n"
    );
}

int main(void) {
    int ok = 1;

    /* Enable MIE so we can verify MPIE is set after trap */
    asm volatile("csrsi mstatus, 0x8");  /* mstatus.MIE = 1 */

    /* Record address of ECALL for mepc check */
    uint32_t ecall_addr;
    asm volatile(
        "la %0, 1f\n"
        : "=r"(ecall_addr)
    );

    /* Execute ECALL */
    asm volatile(
        "1: ecall\n"
    );

    /* Verify trap handler was entered */
    if (!trap_entered) ok = 0;

    /* Verify mepc points to ECALL instruction */
    if (saved_mepc != ecall_addr) ok = 0;

    /* Verify mcause = 11 (ecall from M-mode) */
    if (saved_mcause != 11) ok = 0;

    /* Verify mstatus: MIE=0, MPIE=1 (old MIE was 1), MPP=M (0b11)
     * Bit 3 (MIE) = 0
     * Bit 7 (MPIE) = 1
     * Bits 12:11 (MPP) = 0b11
     */
    if (saved_mstatus & 0x8) ok = 0;         /* MIE should be 0 */
    if (!(saved_mstatus & 0x80)) ok = 0;     /* MPIE should be 1 */
    if ((saved_mstatus & 0x1800) != 0x1800) ok = 0;  /* MPP should be M */

    if (ok) pass(); else fail(2);
    return 0;
}
