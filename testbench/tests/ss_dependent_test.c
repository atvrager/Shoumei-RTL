#include "shoumei.h"

// Micro-benchmark: 32 strictly dependent ALU instructions (RAW hazard chain).
// Tests worst-case serialized IPC due to operand forward/wake-up.
__attribute__((noinline))
uint32_t benchmark_dependent(int iterations) {
    register uint32_t result asm("a0");
    asm volatile (
        "1:\n\t"
        "addi t0, zero, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"
        "addi t0, t0, 1\n\t"

        "addi %1, %1, -1\n\t"
        "bnez %1, 1b\n\t"

        "mv a0, t0\n\t"
        : "=r"(result), "+r"(iterations)
        :
        : "t0", "memory"
    );
    return result;
}

int main(void) {
    uint32_t sum = benchmark_dependent(10);
    // t0 = 32
    if (sum == 32) {
        pass();
    } else {
        fail(2);
    }
    return 0;
}
