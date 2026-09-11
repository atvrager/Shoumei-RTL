#include "shoumei.h"

// Micro-benchmark: 32 independent ALU instructions in an unrolled loop body.
// Tests theoretical peak dual-issue execution throughput without RAW hazards.
__attribute__((noinline))
uint32_t benchmark_independent(int iterations) {
    register uint32_t result asm("a0");
    asm volatile (
        "1:\n\t"
        "addi t0, zero, 1\n\t"
        "addi t1, zero, 1\n\t"
        "addi t2, zero, 1\n\t"
        "addi t3, zero, 1\n\t"
        "addi t4, zero, 1\n\t"
        "addi t5, zero, 1\n\t"
        "addi t6, zero, 1\n\t"
        "addi a1, zero, 1\n\t"
        "addi a2, zero, 1\n\t"
        "addi a3, zero, 1\n\t"
        "addi a4, zero, 1\n\t"
        "addi a5, zero, 1\n\t"
        "addi a6, zero, 1\n\t"
        "addi a7, zero, 1\n\t"
        "addi s0, zero, 1\n\t"
        "addi s1, zero, 1\n\t"

        "addi t0, t0, 1\n\t"
        "addi t1, t1, 1\n\t"
        "addi t2, t2, 1\n\t"
        "addi t3, t3, 1\n\t"
        "addi t4, t4, 1\n\t"
        "addi t5, t5, 1\n\t"
        "addi t6, t6, 1\n\t"
        "addi a1, a1, 1\n\t"
        "addi a2, a2, 1\n\t"
        "addi a3, a3, 1\n\t"
        "addi a4, a4, 1\n\t"
        "addi a5, a5, 1\n\t"
        "addi a6, a6, 1\n\t"
        "addi a7, a7, 1\n\t"
        "addi s0, s0, 1\n\t"
        "addi s1, s1, 1\n\t"

        "addi %1, %1, -1\n\t"
        "bnez %1, 1b\n\t"

        "add a0, t0, t1\n\t"
        "add a0, a0, t2\n\t"
        "add a0, a0, t3\n\t"
        : "=r"(result), "+r"(iterations)
        :
        : "t0", "t1", "t2", "t3", "t4", "t5", "t6",
          "a1", "a2", "a3", "a4", "a5", "a6", "a7", "s0", "s1", "memory"
    );
    return result;
}

int main(void) {
    uint32_t sum = benchmark_independent(10);
    // t0=2, t1=2, t2=2, t3=2 => sum = 8
    if (sum == 8) {
        pass();
    } else {
        fail(2);
    }
    return 0;
}
