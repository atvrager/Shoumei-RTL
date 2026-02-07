#include "shoumei.h"

/* Test: ADDI produces correct result.
   Compute 3+5=8, subtract 7 to get 1, write to tohost.
   This avoids reading x0 (which was buggy before). */
int main(void) {
    int result;
    asm volatile(
        "li   t0, 3\n\t"
        "addi t0, t0, 5\n\t"    /* t0 = 8 */
        "addi t0, t0, -7\n\t"   /* t0 = 1 */
        "mv   %0, t0\n\t"
        : "=r"(result)
        :
        : "t0"
    );
    tohost = result;
    while (1) {}
}
