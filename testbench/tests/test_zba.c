#include "shoumei.h"

/*
 * Test: Zba address generation instructions via fallback emulation.
 * - sh1add rd, rs1, rs2: rd = (rs1 << 1) + rs2
 * - sh2add rd, rs1, rs2: rd = (rs1 << 2) + rs2
 * - sh3add rd, rs1, rs2: rd = (rs1 << 3) + rs2
 */

static inline uint64_t sh1add(uint64_t rs1, uint64_t rs2) {
    uint64_t rd;
    asm volatile(".insn r 0x33, 0x2, 0x10, %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2));
    return rd;
}

static inline uint64_t sh2add(uint64_t rs1, uint64_t rs2) {
    uint64_t rd;
    asm volatile(".insn r 0x33, 0x4, 0x10, %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2));
    return rd;
}

static inline uint64_t sh3add(uint64_t rs1, uint64_t rs2) {
    uint64_t rd;
    asm volatile(".insn r 0x33, 0x6, 0x10, %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2));
    return rd;
}

int main(void) {
    /* Test vector 1: small positive numbers */
    if (sh1add(10, 5) != (10 * 2 + 5)) fail(1);
    if (sh2add(10, 5) != (10 * 4 + 5)) fail(2);
    if (sh3add(10, 5) != (10 * 8 + 5)) fail(3);

    /* Test vector 2: zeros */
    if (sh1add(0, 42) != 42) fail(4);
    if (sh2add(42, 0) != 168) fail(5);

    /* Test vector 3: 64-bit boundaries */
    uint64_t large = 0x1000000000000000ULL;
    if (sh1add(large, 7) != (0x2000000000000000ULL + 7)) fail(6);

    pass();
    return 0;
}
