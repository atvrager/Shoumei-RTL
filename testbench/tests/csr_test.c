#include "shoumei.h"

/* Test: Basic CSR operations using mscratch (0x340).
   1. CSRRW: write a value, read back old value (0 after reset)
   2. CSRRS: set bits
   3. CSRRC: clear bits
   4. CSRRWI: write immediate
   5. CSRRSI: set bits with immediate
   6. CSRRCI: clear bits with immediate
   7. Read mcycle (should be nonzero after running) */
int main(void) {
    unsigned int val;
    int pass = 1;

    /* Test 1: CSRRW — write 0xDEADBEEF to mscratch, read old (should be 0) */
    asm volatile("csrrw %0, mscratch, %1" : "=r"(val) : "r"(0xDEADBEEFu));
    if (val != 0) pass = 0;

    /* Test 2: CSRRW — write 0x12345678, read old (should be 0xDEADBEEF) */
    asm volatile("csrrw %0, mscratch, %1" : "=r"(val) : "r"(0x12345678u));
    if (val != 0xDEADBEEFu) pass = 0;

    /* Test 3: CSRRS — set bits 0xFF, read old (should be 0x12345678) */
    asm volatile("csrrs %0, mscratch, %1" : "=r"(val) : "r"(0xFFu));
    if (val != 0x12345678u) pass = 0;

    /* Now mscratch = 0x123456FF. Read it with CSRRS x0 (no modify) */
    asm volatile("csrrs %0, mscratch, x0" : "=r"(val));
    if (val != 0x123456FFu) pass = 0;

    /* Test 4: CSRRC — clear low byte, read old */
    asm volatile("csrrc %0, mscratch, %1" : "=r"(val) : "r"(0xFFu));
    if (val != 0x123456FFu) pass = 0;
    /* Now mscratch = 0x12345600 */

    /* Test 5: CSRRWI — write zimm=0x1F (31), read old */
    asm volatile("csrrwi %0, mscratch, 0x1F" : "=r"(val));
    if (val != 0x12345600u) pass = 0;
    /* Now mscratch = 0x1F */

    /* Test 6: CSRRSI — set bit 0 (zimm=1), read old */
    asm volatile("csrrsi %0, mscratch, 1" : "=r"(val));
    if (val != 0x1Fu) pass = 0;
    /* mscratch still 0x1F (bit 0 was already set) */

    /* Test 7: CSRRCI — clear bits zimm=0x10 (bit 4), read old */
    asm volatile("csrrci %0, mscratch, 0x10" : "=r"(val));
    if (val != 0x1Fu) pass = 0;
    /* Now mscratch = 0x0F */

    /* Verify final mscratch value */
    asm volatile("csrrs %0, mscratch, x0" : "=r"(val));
    if (val != 0x0Fu) pass = 0;

    /* Test 8: mcycle should be nonzero after executing instructions */
    asm volatile("csrrs %0, mcycle, x0" : "=r"(val));
    if (val == 0) pass = 0;

    tohost = pass;
    while (1) {}
}
