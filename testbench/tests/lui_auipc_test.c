#include "shoumei.h"

/* Test: LUI and AUIPC (Fix 1).
   Uses a large constant that requires LUI to construct.
   GCC emits LUI+ADDI for constants with upper bits set. */
int main(void) {
    volatile int x = 0x12345;  /* LUI 0x12, ADDI 0x345 */
    volatile int y = 0x1000;   /* LUI 0x1 */
    int sum = x + y;
    /* 0x12345 + 0x1000 = 0x13345 = 78661 */
    /* Subtract 78660 to get 1 for PASS */
    if (sum == 0x13345)
        pass();
    else
        fail(2);
    while (1) {}
}
