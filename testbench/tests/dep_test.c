#include "shoumei.h"

/* Test: Back-to-back RAW hazard chain using only register operations.
   1 + 2 = 3, 3 + 3 = 6, 6 + 4 = 10, 10 - 9 = 1.
   Each ADDI depends on the previous result. */
int main(void) {
    int result;
    asm volatile(
        "li   t0, 1\n\t"
        "addi t0, t0, 2\n\t"    /* t0 = 3 (depends on li) */
        "addi t0, t0, 3\n\t"    /* t0 = 6 (depends on prev addi) */
        "addi t0, t0, 4\n\t"    /* t0 = 10 (depends on prev addi) */
        "addi t0, t0, -9\n\t"   /* t0 = 1 (depends on prev addi) */
        "mv   %0, t0\n\t"
        : "=r"(result)
        :
        : "t0"
    );
    tohost = result;
    while (1) {}
}
