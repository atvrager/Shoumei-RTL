#include "shoumei.h"

/* Test: Branch conditions (Fix 3).
   Exercises BEQ, BNE, BLT, BGE, BLTU, BGEU via C comparisons. */

static int __attribute__((noinline)) check_eq(int a, int b) { return a == b; }
static int __attribute__((noinline)) check_lt(int a, int b) { return a < b; }
static int __attribute__((noinline)) check_ge(int a, int b) { return a >= b; }

int main(void) {
    int errors = 0;

    /* BEQ / BNE */
    if (!check_eq(5, 5))  errors++;
    if (check_eq(5, 6))   errors++;

    /* BLT / BGE (signed) */
    if (!check_lt(-1, 1))  errors++;
    if (check_lt(1, -1))   errors++;
    if (!check_ge(3, 3))   errors++;
    if (!check_ge(4, 3))   errors++;
    if (check_ge(2, 3))    errors++;

    /* BLTU / BGEU (unsigned via cast) */
    volatile unsigned int ua = 0xFFFFFFFF;  /* -1 unsigned = max */
    volatile unsigned int ub = 1;
    if (!(ua > ub))  errors++;  /* 0xFFFFFFFF > 1 unsigned */

    if (errors == 0)
        pass();
    else
        fail(errors + 1);
    while (1) {}
}
