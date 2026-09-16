/* timer_irq_test.c - Timer interrupt test
 *
 * Sets mtimecmp to a low value, enables timer interrupt (mie.MTIE + mstatus.MIE),
 * spins in a loop, verifies the ISR fires and returns via MRET.
 */
#include "shoumei.h"

#define CLINT_BASE      0x02000000
#define MTIMECMP_LO     (*(volatile uint32_t *)(CLINT_BASE + 0x4000))
#define MTIMECMP_HI     (*(volatile uint32_t *)(CLINT_BASE + 0x4004))
#define MTIME_LO        (*(volatile uint32_t *)(CLINT_BASE + 0xBFF8))
#define MTIME_HI        (*(volatile uint32_t *)(CLINT_BASE + 0xBFFC))

volatile int isr_count = 0;
volatile unsigned long saved_mcause = 0;

/* Trap handler: called on ECALL or interrupt */
void _trap_handler(void) __attribute__((naked, aligned(4)));
void _trap_handler(void) {
    asm volatile(
        /* Save t0-t2 */
        "addi sp, sp, -32\n"
        "sd t0, 0(sp)\n"
        "sd t1, 8(sp)\n"
        "sd t2, 16(sp)\n"

        /* Read mcause */
        "csrr t0, mcause\n"
        "la t1, saved_mcause\n"
        "sd t0, 0(t1)\n"

        /* Increment isr_count */
        "la t1, isr_count\n"
        "lw t2, 0(t1)\n"
        "addi t2, t2, 1\n"
        "sw t2, 0(t1)\n"

        /* Clear timer interrupt: set mtimecmp to max */
        "li t0, 0x02004000\n"  /* MTIMECMP_LO */
        "li t1, -1\n"          /* 0xFFFFFFFF */
        "sw t1, 0(t0)\n"
        "sw t1, 4(t0)\n"       /* MTIMECMP_HI */

        /* Restore t0-t2 */
        "ld t0, 0(sp)\n"
        "ld t1, 8(sp)\n"
        "ld t2, 16(sp)\n"
        "addi sp, sp, 32\n"
        "mret\n"
    );
}

int main(void) {
    int ok = 1;

    /* Install trap handler */
    asm volatile("csrw mtvec, %0" :: "r"((uintptr_t)_trap_handler));

    /* Enable mie.MTIE (bit 7) */
    unsigned long mie;
    asm volatile("csrr %0, mie" : "=r"(mie));
    mie |= (1 << 7);
    asm volatile("csrw mie, %0" :: "r"(mie));

    /* Set mtimecmp to a low value (e.g., current mtime + 10) */
    uint32_t now_lo = MTIME_LO;
    MTIMECMP_HI = 0;
    MTIMECMP_LO = now_lo + 10;

    /* Enable mstatus.MIE (bit 3) */
    unsigned long mstatus;
    asm volatile("csrr %0, mstatus" : "=r"(mstatus));
    mstatus |= (1 << 3);
    asm volatile("csrw mstatus, %0" :: "r"(mstatus));

    /* Spin: interrupt should fire */
    for (volatile int i = 0; i < 1000; i++) {
        if (isr_count > 0) break;
    }

    /* Check results */
    if (isr_count != 1) ok = 0;
    /* mcause for timer interrupt: 0x80000007 (bit 31 set + code 7) */
    if ((saved_mcause & 0xFF) != 7) ok = 0;

    /* Verify mstatus.MIE was restored by MRET */
    asm volatile("csrr %0, mstatus" : "=r"(mstatus));
    if (!(mstatus & (1 << 3))) ok = 0;

    if (ok)
        pass();
    else
        fail(5);

    return 0;
}
