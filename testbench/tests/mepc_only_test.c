#include "shoumei.h"

/* Minimal test: write 0xDEADBEEF to mepc, read back, verify bit 0 cleared */
int main(void) {
    unsigned int val;
    asm volatile("csrrw %0, mepc, %1" : "=r"(val) : "r"(0xDEADBEEFu));
    /* old = 0 (reset) */
    if (val != 0) { fail(3); return 0; }
    asm volatile("csrr %0, mepc" : "=r"(val));
    /* expect 0xDEADBEEC (bits [1:0] cleared, IALIGN=32 without C extension) */
    if (val != 0xDEADBEECu) { fail(5); return 0; }
    pass();
    return 0;
}
