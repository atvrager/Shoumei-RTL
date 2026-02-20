#include "shoumei.h"

/* Test: M-mode trap CSRs — WARL masking and read/write semantics.
   Tests mstatus, mie, mtvec, mepc, mcause, mtval, mip.
   Each CSR is tested independently with simple write/readback. */
int main(void) {
    unsigned int val, old;
    int ok = 1;

    /* === mstatus (0x300) === */
    /* Reset value: MPP=11 (M-only), FS=11 (dirty, F enabled), SD=1 */
    asm volatile("csrrw %0, mstatus, %1" : "=r"(old) : "r"(0xFFFFFFFFu));
    if (old != 0x80007800u) ok = 0;  /* reset value */

    asm volatile("csrr %0, mstatus" : "=r"(val));
    /* Written 0xFFFFFFFF, WARL: MIE(3), MPIE(7), MPP(12:11)=11, FS(14:13)=11, SD(31)=1 */
    if (val != 0x80007888u) ok = 0;

    /* CSRRC: clear MIE (bit 3) */
    asm volatile("csrrc %0, mstatus, %1" : "=r"(old) : "r"(0x8u));
    asm volatile("csrr %0, mstatus" : "=r"(val));
    if (val != 0x80007880u) ok = 0;

    /* Clear FS to 00 → SD becomes 0 */
    asm volatile("csrrc %0, mstatus, %1" : "=r"(old) : "r"(0x6000u));
    asm volatile("csrr %0, mstatus" : "=r"(val));
    if (val != 0x00001880u) ok = 0;

    /* === mie (0x304) === */
    asm volatile("csrrw %0, mie, %1" : "=r"(old) : "r"(0xFFFFFFFFu));
    if (old != 0u) ok = 0;
    asm volatile("csrr %0, mie" : "=r"(val));
    if (val != 0x00000888u) ok = 0;

    /* === mtvec (0x305) === */
    /* Note: crt0 sets mtvec to _trap_handler before main, so old value is nonzero */
    asm volatile("csrrw %0, mtvec, %1" : "=r"(old) : "r"(0xFFFFFFFFu));
    asm volatile("csrr %0, mtvec" : "=r"(val));
    if (val != 0xFFFFFFFDu) ok = 0;

    /* === mepc (0x341) === */
    asm volatile("csrrw %0, mepc, %1" : "=r"(old) : "r"(0xFFFFFFFFu));
    if (old != 0u) ok = 0;
    asm volatile("csrr %0, mepc" : "=r"(val));
    if (val != 0xFFFFFFFCu) ok = 0;  /* bits [1:0] cleared, IALIGN=32 */

    /* === mcause (0x342) === */
    asm volatile("csrrw %0, mcause, %1" : "=r"(old) : "r"(0xFFFFFFFFu));
    if (old != 0u) ok = 0;
    asm volatile("csrr %0, mcause" : "=r"(val));
    if (val != 0xFFFFFFFFu) ok = 0;

    /* === mtval (0x343) === */
    asm volatile("csrrw %0, mtval, %1" : "=r"(old) : "r"(0xA5A5A5A5u));
    if (old != 0u) ok = 0;
    asm volatile("csrr %0, mtval" : "=r"(val));
    if (val != 0xA5A5A5A5u) ok = 0;

    /* === mip (0x344) === */
    asm volatile("csrrw %0, mip, %1" : "=r"(old) : "r"(0xFFFFFFFFu));
    if (old != 0u) ok = 0;
    asm volatile("csrr %0, mip" : "=r"(val));
    if (val != 0u) ok = 0;

    if (ok) pass(); else fail(3);
    return 0;
}
