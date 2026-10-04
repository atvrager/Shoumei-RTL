#include "shoumei.h"

/*
 * Test: Zbb basic bit manipulation instructions.
 * - andn, orn, xnor
 * - min, max
 * - ror, rol
 */

static inline uint64_t andn(uint64_t rs1, uint64_t rs2) {
    uint64_t rd;
    asm volatile(".insn r 0x33, 0x7, 0x20, %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2));
    return rd;
}

static inline uint64_t orn(uint64_t rs1, uint64_t rs2) {
    uint64_t rd;
    asm volatile(".insn r 0x33, 0x6, 0x20, %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2));
    return rd;
}

static inline uint64_t xnor(uint64_t rs1, uint64_t rs2) {
    uint64_t rd;
    asm volatile(".insn r 0x33, 0x4, 0x20, %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2));
    return rd;
}

static inline int64_t min(int64_t rs1, int64_t rs2) {
    int64_t rd;
    asm volatile(".insn r 0x33, 0x4, 0x05, %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2));
    return rd;
}

static inline int64_t max(int64_t rs1, int64_t rs2) {
    int64_t rd;
    asm volatile(".insn r 0x33, 0x6, 0x05, %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2));
    return rd;
}

static inline uint64_t minu(uint64_t rs1, uint64_t rs2) {
    uint64_t rd;
    asm volatile(".insn r 0x33, 0x5, 0x05, %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2));
    return rd;
}

static inline uint64_t maxu(uint64_t rs1, uint64_t rs2) {
    uint64_t rd;
    asm volatile(".insn r 0x33, 0x7, 0x05, %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2));
    return rd;
}

static inline uint64_t ror(uint64_t rs1, uint64_t rs2) {
    uint64_t rd;
    asm volatile(".insn r 0x33, 0x5, 0x30, %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2));
    return rd;
}

static inline uint64_t rol(uint64_t rs1, uint64_t rs2) {
    uint64_t rd;
    asm volatile(".insn r 0x33, 0x1, 0x30, %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2));
    return rd;
}

int main(void) {
    /* Test andn */
    if (andn(0xFF, 0x0F) != 0xF0) fail(1);

    /* Test orn */
    if (orn(0x00, 0x00) != ~0ULL) fail(2);

    /* Test xnor */
    if (xnor(0xAA, 0x55) != ~0xFFULL) fail(3);

    /* Test min / max with signed numbers */
    if (min(-10, 5) != -10) fail(4);
    if (max(-10, 5) != 5) fail(5);
    if (min(42, 100) != 42) fail(6);
    if (max(42, 100) != 100) fail(7);

    /* Both operands negative.  The signs agree, so the signed comparison must
       fall back on the unsigned one, which the borrow decides. */
    if (min(-1, -781) != -781) fail(11);
    if (min(-781, -1) != -781) fail(12);
    if (max(-1, -781) != -1) fail(13);
    if (max(-781, -1) != -1) fail(14);

    /* The unsigned forms must pick the other operand for the same inputs. */
    if (minu(~0ULL, ~780ULL) != ~780ULL) fail(15);
    if (minu(~780ULL, ~0ULL) != ~780ULL) fail(16);
    if (maxu(~0ULL, ~780ULL) != ~0ULL) fail(17);
    if (maxu(~780ULL, ~0ULL) != ~0ULL) fail(18);

    /* The most significant bit set, against everything below it. */
    if (minu(0x8000000000000000ULL, 0x7FFFFFFFFFFFFFFFULL) != 0x7FFFFFFFFFFFFFFFULL) fail(19);
    if (maxu(0x8000000000000000ULL, 0x7FFFFFFFFFFFFFFFULL) != 0x8000000000000000ULL) fail(20);
    if (min(0x8000000000000000ULL, 0x7FFFFFFFFFFFFFFFULL) != (int64_t)0x8000000000000000ULL) fail(21);
    if (max(0x8000000000000000ULL, 0x7FFFFFFFFFFFFFFFULL) != 0x7FFFFFFFFFFFFFFFULL) fail(22);

    /* Test ror / rol */
    uint64_t pattern = 0x1234567890ABCDEFULL;
    if (ror(pattern, 4) != ((pattern >> 4) | (pattern << 60))) fail(8);
    if (rol(pattern, 4) != ((pattern << 4) | (pattern >> 60))) fail(9);
    if (ror(rol(pattern, 17), 17) != pattern) fail(10);

    pass();
    return 0;
}
