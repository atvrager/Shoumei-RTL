// Test: jal + ret correctness after branch mispredict
// Mimics CoreMark's start_time/stop_time pattern
#include "test_macros.h"

volatile int counter = 0;

__attribute__((noinline))
void simple_func(void) {
    // Read mcycle CSR (like start_time)
    unsigned int val;
    asm volatile("csrr %0, mcycle" : "=r"(val));
    // Store to memory (like start_time stores mcycle)
    counter = val;
}

int main() {
    int result = 0;
    int flag = 1;

    // Loop with branch that will be mispredicted
    for (int i = 0; i < 10; i++) {
        if (flag) {
            simple_func();
            result += counter;
        }
    }

    // Verify we got here (return address wasn't corrupted)
    if (result != 0) {
        TEST_PASS;
    } else {
        // Even if mcycle returns 0, we should still get here
        TEST_PASS;
    }
}
