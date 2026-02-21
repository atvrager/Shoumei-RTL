#include "shoumei.h"

/*
 * WFI test.
 *
 * WFI is implemented as a NOP (spec-legal for M-mode).
 * Verify execution continues past WFI without trapping.
 */

int main(void) {
    int ok = 1;
    volatile int before = 1;
    volatile int after = 0;

    asm volatile("wfi");

    after = 1;

    if (!before || !after) ok = 0;

    if (ok) pass(); else fail(5);
    return 0;
}
