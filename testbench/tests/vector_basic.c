#include "shoumei.h"

/* Test: basic vector load/add/store using Zve32x.
   Load 4 words from src_a and src_b, add them, store to dst,
   then verify dst[0..3] == expected values. */

static volatile uint32_t src_a[4] __attribute__((aligned(16))) = {1, 2, 3, 4};
static volatile uint32_t src_b[4] __attribute__((aligned(16))) = {10, 20, 30, 40};
static volatile uint32_t dst[4]   __attribute__((aligned(16))) = {0, 0, 0, 0};

int main(void) {
    asm volatile(
        "vsetivli zero, 4, e32, m1, ta, ma\n\t"
        "vle32.v v1, (%[sa])\n\t"
        "vle32.v v2, (%[sb])\n\t"
        "vadd.vv v3, v1, v2\n\t"
        "vse32.v v3, (%[d])\n\t"
        :
        : [sa] "r" (src_a), [sb] "r" (src_b), [d] "r" (dst)
        : "memory"
    );

    /* Verify: dst[0]=11, dst[1]=22, dst[2]=33, dst[3]=44 */
    if (dst[0] == 11 && dst[1] == 22 && dst[2] == 33 && dst[3] == 44) {
        pass();
    } else {
        fail(dst[0]);
    }
    while (1) {}
}
