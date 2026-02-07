#include "shoumei.h"

int main(void) {
    /* Back-to-back RAW hazard chain */
    volatile int a = 1;
    volatile int b = a + 2;
    volatile int c = b + 3;
    volatile int d = c + 4;

    if (d == 10)
        pass();
    else
        fail(2);
    return 0;
}
