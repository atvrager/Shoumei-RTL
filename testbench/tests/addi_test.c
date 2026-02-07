#include "shoumei.h"

int main(void) {
    volatile int a = 3;
    volatile int b = 5;

    if (a + b == 8)
        pass();
    else
        fail(2);
    return 0;
}
