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

/* Timer ISR: called from asm trap handler with interrupts disabled */
void timer_isr(void) {
    unsigned int mtime_lo = MTIME_LO;
    MTIMECMP_LO = 0xFFFFFFFF;  /* prevent re-trigger */
    MTIMECMP_HI = 0;
    MTIMECMP_LO = mtime_lo + 500;
    irq_count++;
}

/* Assembly trap handler */
__asm__(
    ".globl _trap_handler\n"
    ".balign 4\n"
    "_trap_handler:\n"
    "  addi sp, sp, -64\n"
    "  sw ra,  0(sp)\n"
    "  sw t0,  4(sp)\n"
    "  sw t1,  8(sp)\n"
    "  sw t2, 12(sp)\n"
    "  sw a0, 16(sp)\n"
    "  sw a1, 20(sp)\n"
    "  sw a2, 24(sp)\n"
    "  sw a3, 28(sp)\n"
    "  sw a4, 32(sp)\n"
    "  sw a5, 36(sp)\n"
    "  sw a6, 40(sp)\n"
    "  sw a7, 44(sp)\n"
    "  sw t3, 48(sp)\n"
    "  sw t4, 52(sp)\n"
    "  sw t5, 56(sp)\n"
    "  sw t6, 60(sp)\n"
    "  csrr t0, mcause\n"
    "  li t1, 0x80000007\n"  /* machine timer interrupt */
    "  bne t0, t1, 1f\n"
    "  call timer_isr\n"
    "1:\n"
    "  lw ra,  0(sp)\n"
    "  lw t0,  4(sp)\n"
    "  lw t1,  8(sp)\n"
    "  lw t2, 12(sp)\n"
    "  lw a0, 16(sp)\n"
    "  lw a1, 20(sp)\n"
    "  lw a2, 24(sp)\n"
    "  lw a3, 28(sp)\n"
    "  lw a4, 32(sp)\n"
    "  lw a5, 36(sp)\n"
    "  lw a6, 40(sp)\n"
    "  lw a7, 44(sp)\n"
    "  lw t3, 48(sp)\n"
    "  lw t4, 52(sp)\n"
    "  lw t5, 56(sp)\n"
    "  lw t6, 60(sp)\n"
    "  addi sp, sp, 64\n"
    "  mret\n"
);

static void enable_timer_irq(void) {
    MTIMECMP_LO = 0xFFFFFFFF;
    MTIMECMP_HI = 0;
    unsigned int mtime_lo = MTIME_LO;
    MTIMECMP_LO = mtime_lo + 200;
    __asm__ volatile("csrs mie, %0" :: "r"(1 << 7));
    __asm__ volatile("csrs mstatus, %0" :: "r"(1 << 3));
}

__attribute__((noinline)) int check_a0(int val) {
    if (val == 0) return -1;
    return val;
}

volatile int counter = 0;

int main(void) {
    enable_timer_irq();

    for (int i = 0; i < 200; i++) {
        putchar_addr = 'X';
        counter++;
        int result = check_a0(1);
        if (result != 1) {
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
