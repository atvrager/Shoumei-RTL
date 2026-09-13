/*
 * nan_boxing.c - Test single-precision NaN-boxing semantics in RV32D
 *
 * Checks:
 * 1. flw produces NaN-boxed FPR (upper 32 bits are 0xFFFFFFFF)
 * 2. Unboxed FPR (upper 32 bits != 0xFFFFFFFF) read by SP instruction
 *    is treated as canonical NaN (0x7fc00000)
 * 3. fcvt.s.d produces NaN-boxed result (upper 32 bits 0xFFFFFFFF)
 * 4. fcvt.d.s on unboxed input treats operand as canonical NaN
 */

#include "shoumei.h"

static volatile uint64_t mem64;
static volatile uint32_t mem32;

int main(void) {
    uint32_t lo, hi;

    /* 1. Test flw NaN-boxing: flw followed by fsd should show upper 32 bits = 0xFFFFFFFF */
    mem32 = 0x3f800000; /* 1.0f */
    asm volatile(
        "flw f0, (%0)\n"
        "fsd f0, (%1)\n"
        :
        : "r"((void*)&mem32), "r"((void*)&mem64)
        : "memory"
    );
    lo = (uint32_t)(mem64 & 0xffffffffULL);
    hi = (uint32_t)(mem64 >> 32);
    if (lo != 0x3f800000 || hi != 0xffffffff) {
        fail(2);
        return 0;
    }

    /* 2. Test unboxed operand to SP instruction (fadd.s)
     * Store a 64-bit float with non-0xFFFFFFFF upper bits (e.g. 1.0d = 0x3FF0000000000000)
     * Load into f1 via fld.
     * fadd.s f2, f1, f0: since f1 is unboxed, it should be treated as canonical NaN (0x7fc00000).
     * Any arithmetic with canonical NaN yields canonical NaN (0x7fc00000).
     */
    mem64 = 0x3ff0000000000000ULL; /* 1.0 as double, upper bits 0x3FF00000 */
    asm volatile(
        "fld f1, (%0)\n"
        "fadd.s f2, f1, f0\n"
        "fsd f2, (%1)\n"
        :
        : "r"((void*)&mem64), "r"((void*)&mem64)
        : "memory"
    );
    lo = (uint32_t)(mem64 & 0xffffffffULL);
    hi = (uint32_t)(mem64 >> 32);
    if (lo != 0x7fc00000 || hi != 0xffffffff) {
        fail(3);
        return 0;
    }

    /* 3. Test fcvt.s.d produces NaN-boxed result */
    mem64 = 0x4004000000000000ULL; /* 2.5d */
    asm volatile(
        "fld f1, (%0)\n"
        "fcvt.s.d f2, f1\n"
        "fsd f2, (%1)\n"
        :
        : "r"((void*)&mem64), "r"((void*)&mem64)
        : "memory"
    );
    lo = (uint32_t)(mem64 & 0xffffffffULL);
    hi = (uint32_t)(mem64 >> 32);
    if (lo != 0x40200000 || hi != 0xffffffff) { /* 2.5f = 0x40200000 */
        fail(4);
        return 0;
    }

    /* 4. Test fcvt.d.s with unboxed operand
     * f1 is unboxed double (from above: 0x4004000000000000)
     * fcvt.d.s f3, f1 should treat f1 as canonical SP NaN and yield canonical DP NaN:
     * 0x7ff8000000000000ULL
     */
    mem64 = 0x4004000000000000ULL;
    asm volatile(
        "fld f1, (%0)\n"
        "fcvt.d.s f3, f1\n"
        "fsd f3, (%1)\n"
        :
        : "r"((void*)&mem64), "r"((void*)&mem64)
        : "memory"
    );
    if (mem64 != 0x7ff8000000000000ULL) {
        fail(5);
        return 0;
    }

    pass();
    return 0;
}
