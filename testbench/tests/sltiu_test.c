#include "shoumei.h"

/* Minimal test: SLTIU (seqz) */
int main(void) {
    int x = 0;
    int result;
    /* seqz x, x → sltiu x, x, 1 → x = (0 < 1) = 1 */
    __asm__ volatile ("sltiu %0, %1, 1" : "=r"(result) : "r"(x));
    if (result == 1)
        pass();
    else
        fail(result + 2);
    while (1) {}
}
