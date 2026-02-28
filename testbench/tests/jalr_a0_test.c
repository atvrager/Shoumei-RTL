/*
 * Minimal reproducer for a0 corruption across jalr.
 * Pattern: li a0, 1 → jalr to function → function checks bnez a0.
 */
extern volatile unsigned int tohost;

/* Prevent inlining so we get a real jalr */
__attribute__((noinline)) int check_a0(int val) {
    if (val == 0) return -1;  /* BUG: a0 was corrupted */
    return val;
}

/* Run the pattern many times with various call depths */
__attribute__((noinline)) int pattern_test(void) {
    int result;
    for (int i = 0; i < 100; i++) {
        result = check_a0(1);
        if (result != 1) return i;  /* return iteration that failed */
    }
    return -2;  /* all passed */
}

/* Similar to vTaskB: store, load, add, store, then call with a0=1 */
volatile int counter = 0;
volatile unsigned int *putchar_addr_ptr = (volatile unsigned int *)0x3f004;

__attribute__((noinline)) int taskb_pattern(void) {
    for (int i = 0; i < 100; i++) {
        *putchar_addr_ptr = 'B';
        counter++;
        int result = check_a0(1);
        if (result != 1) return i;
    }
    return -2;
}

int main(void) {
    int r;

    r = pattern_test();
    if (r != -2) { tohost = 2; return 1; }

    r = taskb_pattern();
    if (r != -2) { tohost = 3; return 1; }

    tohost = 1;  /* PASS */
    return 0;
}
