// branch_flush_x0_test.c - Verify x0 stays 0 after many branches + flush
// Regression test: conditional branches with rd=x0 use force_alloc for unique
// CDB tags. Verify this doesn't corrupt x0's identity mapping (preg 0).

#include "shoumei.h"

int main(void) {
    register int x = 0;
    register int y = 1;

    // Execute many conditional branches to trigger preg alloc/free cycles
    for (int i = 0; i < 100; i++) {
        // Mix of taken and not-taken branches
        if (x == 0) { y = y + 1; }
        if (y == 0) { x = x + 1; }  // never taken
        if (x != 0) { y = y - 1; }  // never taken
        if (y != 0) { x = x + 0; }  // always taken
    }

    // Force a branch mispredict flush by doing an indirect jump
    volatile int target = 1;
    if (target) {
        y = 42;
    }

    // Check x0 == 0 using inline asm (compiler might optimize away C check)
    int x0_val;
    __asm__ volatile ("mv %0, x0" : "=r"(x0_val));
    if (x0_val != 0) fail(3);

    // Also verify basic arithmetic still works (uses x0 implicitly)
    int a = 5;
    int b = 3;
    if (a + b != 8) fail(5);
    if (a - b != 2) fail(7);

    pass();
    return 0;
}
