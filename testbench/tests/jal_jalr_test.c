#include "shoumei.h"

/* Test: JAL/JALR link register writeback (Fix 2).
   Function calls use JAL (direct) and JALR (indirect / return).
   If link register (ra = PC+4) is wrong, returns will crash. */

static int __attribute__((noinline)) add(int a, int b) {
    return a + b;
}

static int __attribute__((noinline)) mul_by_3(int x) {
    /* Nested call: tests that ra is saved/restored correctly */
    int doubled = add(x, x);
    return add(doubled, x);
}

int main(void) {
    int result = mul_by_3(5);  /* 5 * 3 = 15 */
    result = add(result, -14); /* 15 - 14 = 1 */

    if (result == 1)
        pass();
    else
        fail(2);
    while (1) {}
}
