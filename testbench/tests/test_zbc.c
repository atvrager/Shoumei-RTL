#include "shoumei.h"

/*
 * Test: Zbc carry-less multiply instruction (clmul).
 */

static inline uint64_t clmul(uint64_t rs1, uint64_t rs2) {
    uint64_t rd;
    asm volatile(".insn r 0x33, 0x1, 0x05, %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2));
    return rd;
}

int main(void) {
    /* clmul(0b11, 0b11) = (0b11 << 1) ^ (0b11) = 0b110 ^ 0b011 = 0b101 = 5 */
    if (clmul(3, 3) != 5) fail(1);

    /* clmul(x, 0) = 0 */
    if (clmul(0x12345678, 0) != 0) fail(2);

    /* clmul(x, 1) = x */
    if (clmul(0xABCDEF, 1) != 0xABCDEF) fail(3);

    /* clmul(2, 2) = 4 */
    if (clmul(2, 2) != 4) fail(4);

    pass();
    return 0;
}
