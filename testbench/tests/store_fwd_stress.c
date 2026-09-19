#include "shoumei.h"

/* Store-forwarding stress: store-buffer churn, sub-word stores, and
   same-address back-to-back patterns exercising the youngest-match
   forwarding path and buffer-full stalls. */
int main(void) {
    volatile uint64_t mem[16];

    /* 1. Fill past the 8-entry store buffer, then read back each. */
    for (int i = 0; i < 12; i++)
        mem[i] = 0x1000 + i;
    for (int i = 0; i < 12; i++)
        if (mem[i] != (uint64_t)(0x1000 + i)) { fail(1); while (1) {} }

    /* 2. Youngest-match: two stores to the same address, read sees newest. */
    mem[0] = 1;
    mem[0] = 2;
    if (mem[0] != 2) { fail(2); while (1) {} }

    /* 3. Sub-word: byte stores, word readback. */
    volatile uint8_t bytes[8];
    bytes[0] = 0xAA;
    bytes[1] = 0xBB;
    bytes[2] = 0xCC;
    bytes[3] = 0xDD;
    uint32_t w = *(volatile uint32_t *)&bytes[0];
    if (w != 0xDDCCBBAA) { fail(3); while (1) {} }

    /* 4. Half stores, half readback. */
    volatile uint16_t halves[4];
    halves[0] = 0x1234;
    halves[2] = 0x5678;
    if (halves[0] != 0x1234 || halves[2] != 0x5678) { fail(4); while (1) {} }

    /* 5. Different-address bypass: unrelated loads proceed past stores. */
    mem[0] = 0xAAAA;
    mem[1] = 0xBBBB;
    if (mem[1] != 0xBBBB || mem[0] != 0xAAAA) { fail(5); while (1) {} }

    /* 6. Store then immediate load in a tight loop (fp plausible limit). */
    volatile uint64_t s;
    for (int i = 0; i < 64; i++) {
        s = 0xF00D000000000000ull + i;
        if (s != (0xF00D000000000000ull + i)) { fail(6); while (1) {} }
    }

    pass();
    while (1) {}
}
