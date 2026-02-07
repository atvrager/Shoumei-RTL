#include "shoumei.h"

/* Test: Store-to-load forwarding (Fix 4).
   Write then immediately read back from same address.
   Without forwarding, the load would see stale data. */
int main(void) {
    volatile int mem[4];

    /* Basic store-load forwarding */
    mem[0] = 42;
    int a = mem[0];  /* Should forward from store buffer */

    mem[1] = 100;
    int b = mem[1];  /* Should forward from store buffer */

    /* Back-to-back store then load */
    mem[2] = a + b;  /* 142 */
    int c = mem[2];

    if (c == 142)
        pass();
    else
        fail(2);
    while (1) {}
}
