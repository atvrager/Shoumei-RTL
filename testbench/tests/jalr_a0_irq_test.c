/*
 * Test a0 corruption across jalr with timer interrupts enabled.
 * Includes inline asm trap handler that saves/restores all caller-saved regs.
 */
extern volatile unsigned int tohost;
extern volatile unsigned int putchar_addr;

#define CLINT_BASE      0x02000000UL
#define MTIME_LO        (*(volatile unsigned int *)(CLINT_BASE + 0xBFF8))
#define MTIMECMP_LO     (*(volatile unsigned int *)(CLINT_BASE + 0x4000))
#define MTIMECMP_HI     (*(volatile unsigned int *)(CLINT_BASE + 0x4004))

static volatile int irq_count = 0;

/* Assembly trap handler: saves/restores caller-saved registers and handles timer IRQ */
void _trap_handler(void) __attribute__((naked, aligned(4)));
void _trap_handler(void) {
    __asm__ volatile(
        "  addi sp, sp, -128\n"
        "  sd ra,   0(sp)\n"
        "  sd t0,   8(sp)\n"
        "  sd t1,  16(sp)\n"
        "  sd t2,  24(sp)\n"
        "  sd a0,  32(sp)\n"
        "  sd a1,  40(sp)\n"
        "  sd a2,  48(sp)\n"
        "  sd a3,  56(sp)\n"
        "  sd a4,  64(sp)\n"
        "  sd a5,  72(sp)\n"
        "  sd a6,  80(sp)\n"
        "  sd a7,  88(sp)\n"
        "  sd t3,  96(sp)\n"
        "  sd t4, 104(sp)\n"
        "  sd t5, 112(sp)\n"
        "  sd t6, 120(sp)\n"

        /* Check mcause exception code 7 (timer interrupt) */
        "  csrr t0, mcause\n"
        "  andi t0, t0, 0xff\n"
        "  li t1, 7\n"
        "  bne t0, t1, 1f\n"

        /* Advance timer: set mtimecmp = mcycle + 500 */
        "  csrr t0, mcycle\n"
        "  addi t0, t0, 500\n"
        "  li t1, 0x02004000\n"
        "  sw t0, 0(t1)\n"
        "  sw zero, 4(t1)\n"

        /* Increment irq_count */
        "  la t1, irq_count\n"
        "  lw t0, 0(t1)\n"
        "  addi t0, t0, 1\n"
        "  sw t0, 0(t1)\n"

        "1:\n"
        "  ld ra,   0(sp)\n"
        "  ld t0,   8(sp)\n"
        "  ld t1,  16(sp)\n"
        "  ld t2,  24(sp)\n"
        "  ld a0,  32(sp)\n"
        "  ld a1,  40(sp)\n"
        "  ld a2,  48(sp)\n"
        "  ld a3,  56(sp)\n"
        "  ld a4,  64(sp)\n"
        "  ld a5,  72(sp)\n"
        "  ld a6,  80(sp)\n"
        "  ld a7,  88(sp)\n"
        "  ld t3,  96(sp)\n"
        "  ld t4, 104(sp)\n"
        "  ld t5, 112(sp)\n"
        "  ld t6, 120(sp)\n"
        "  addi sp, sp, 128\n"
        "  mret\n"
    );
}

static void enable_timer_irq(void) {
    MTIMECMP_HI = 0;
    unsigned long cycle;
    __asm__ volatile("csrr %0, mcycle" : "=r"(cycle));
    MTIMECMP_LO = (unsigned int)(cycle + 200);
    __asm__ volatile("csrs mie, %0" :: "r"(1ULL << 7));
    __asm__ volatile("csrs mstatus, %0" :: "r"(1ULL << 3));
}

__attribute__((noinline)) int check_a0(int val) {
    if (val == 0) return -1;
    return val;
}

volatile int counter = 0;

int main(void) {
    enable_timer_irq();

    for (int i = 0; i < 20; i++) {
        putchar_addr = 'X';
        counter++;
        int result = check_a0(i + 1);
        if (result != i + 1) {
            tohost = 2;
            for (;;);
        }
    }

    __asm__ volatile("csrc mstatus, %0" :: "r"(1 << 3));

    if (irq_count == 0) {
        tohost = 3;
        for (;;);
    }

    tohost = 1;
    for (;;);
}
