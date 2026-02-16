// Test: minstret CSR reads must return correct retired instruction count
// The exact value depends on when minstret is sampled (before or after the
// csrr instruction itself). Two back-to-back reads should differ by exactly
// the number of instructions between them.

#include "shoumei.h"

int main(void) {
    unsigned int a, b;

    // Two back-to-back csrr minstret reads separated by a known number
    // of instructions. With -O0, each C statement is a few instructions,
    // so we use inline asm for precise control.
    //
    // Sequence:
    //   csrr a, minstret   (1 instruction)
    //   nop                 (1 instruction)
    //   nop                 (1 instruction)
    //   nop                 (1 instruction)
    //   csrr b, minstret   (1 instruction)
    //
    // b - a should be exactly 4 (the 3 nops + the second csrr itself,
    // if minstret counts the current instruction, or 3 if it doesn't).
    // Either way, b - a must be consistent and nonzero.

    __asm__ volatile(
        "csrr %0, minstret\n"
        "nop\n"
        "nop\n"
        "nop\n"
        "csrr %1, minstret\n"
        : "=r"(a), "=r"(b)
    );

    unsigned int diff = b - a;

    // diff should be 4 (if csrr counts itself) or 3 (if it doesn't)
    // Either is acceptable, but it must be one of these two values
    if (diff == 3 || diff == 4) {
        pass();
    } else {
        fail((diff << 1) | 1);
    }

    while(1);
}
