#include "shoumei.h"

/*
 * Test: Zbs single-bit manipulation instructions.
 * - bset rd, rs1, rs2: rd = rs1 | (1 << (rs2 & 63))
 * - bclr rd, rs1, rs2: rd = rs1 & ~(1 << (rs2 & 63))
 * - binv rd, rs1, rs2: rd = rs1 ^ (1 << (rs2 & 63))
 * - bext rd, rs1, rs2: rd = (rs1 >> (rs2 & 63)) & 1
 */

static inline uint64_t bset(uint64_t rs1, uint64_t rs2) {
    uint64_t rd;
    asm volatile(".insn r 0x33, 0x1, 0x14, %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2));
    return rd;
}

static inline uint64_t bclr(uint64_t rs1, uint64_t rs2) {
    uint64_t rd;
    asm volatile(".insn r 0x33, 0x1, 0x24, %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2));
    return rd;
}

static inline uint64_t binv(uint64_t rs1, uint64_t rs2) {
    uint64_t rd;
    asm volatile(".insn r 0x33, 0x1, 0x34, %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2));
    return rd;
}

static inline uint64_t bext(uint64_t rs1, uint64_t rs2) {
    uint64_t rd;
    asm volatile(".insn r 0x33, 0x5, 0x24, %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2));
    return rd;
}

int main(void) {
    uint64_t val = 0;

    /* Test bset */
    val = bset(0, 5);
    if (val != (1ULL << 5)) fail(1);

    val = bset(val, 63);
    if (val != ((1ULL << 5) | (1ULL << 63))) fail(2);

    /* Test bext */
    if (bext(val, 5) != 1) fail(3);
    if (bext(val, 4) != 0) fail(4);
    if (bext(val, 63) != 1) fail(5);

    /* Test binv */
    val = binv(val, 5);  /* clear bit 5 */
    if (val != (1ULL << 63)) fail(6);
    val = binv(val, 5);  /* set bit 5 again */
    if (val != ((1ULL << 5) | (1ULL << 63))) fail(7);

    /* Test bclr */
    val = bclr(val, 63);
    if (val != (1ULL << 5)) fail(8);

    pass();
    return 0;
}
