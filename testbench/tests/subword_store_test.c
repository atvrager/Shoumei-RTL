#include "shoumei.h"

/* Test: Sub-word stores (sh, sb) followed by word loads.
   Verifies the CPU correctly handles byte/halfword store addresses and
   store buffer forwarding for sub-word stores. */
int main(void) {
    volatile unsigned int word = 0;

    /* Test 1: sh (halfword store) to low half, then lw */
    *(volatile unsigned short *)&word = 0x1234;
    unsigned int v1 = word;
    if ((v1 & 0xFFFF) != 0x1234)
        fail(1);

    /* Test 2: sh to high half, then lw */
    word = 0;
    *((volatile unsigned short *)&word + 1) = 0xABCD;
    unsigned int v2 = word;
    if ((v2 >> 16) != 0xABCD)
        fail(2);

    /* Test 3: sb (byte store), then lw */
    word = 0;
    *(volatile unsigned char *)&word = 0x42;
    unsigned int v3 = word;
    if ((v3 & 0xFF) != 0x42)
        fail(3);

    /* Test 4: Multiple sh stores then lw (like CoreMark seeds) */
    volatile unsigned int arr[2] = {0, 0};
    volatile unsigned short *hp = (volatile unsigned short *)arr;
    hp[0] = 0x0000;  /* arr[0] low half */
    hp[1] = 0x0000;  /* arr[0] high half */
    hp[2] = 0x0066;  /* arr[1] low half */
    unsigned int v4 = arr[0];
    if (v4 != 0x00000000)
        fail(4);
    unsigned int v5 = arr[1];
    if ((v5 & 0xFFFF) != 0x0066)
        fail(5);

    pass();
    while (1) {}
}
