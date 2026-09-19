#include "shoumei.h"
#include <stddef.h>
/* Zifencei: execute freshly-written code after fence.i.
   Copies a function's bytes into a writable region, fences, and calls it —
   without fence.i / the I-cache flush the copy could execute stale bytes. */

static volatile uint32_t sink;

__attribute__((noinline)) static void prog_set_sink(void) {
    sink = 0xCAFE0123;
}

__attribute__((noinline)) static void prog_clear_sink(void) {
    sink = 0;
}

__attribute__((aligned(8), section(".text"))) static unsigned char code_buf[32];

static inline void fence_i(void) {
    __asm__ volatile("fence.i" ::: "memory");
}

int main(void) {
    unsigned char *src = (unsigned char *)(void *)prog_set_sink;
    size_t srclen = ((unsigned char *)(void *)prog_clear_sink) - src;
    if (srclen + 4 > sizeof(code_buf)) { fail(1); while (1) {} }

    prog_clear_sink();
    for (size_t i = 0; i < srclen; i++) code_buf[i] = src[i];
    /* 0x00008067: ret (leaf copy has no return) */
    code_buf[srclen] = 0x67;
    code_buf[srclen + 1] = 0x80;
    code_buf[srclen + 2] = 0x00;
    code_buf[srclen + 3] = 0x00;
    fence_i();

    ((void (*)(void))(void *)code_buf)();

    if (sink == 0xCAFE0123)
        pass();
    else
        fail(2);
    while (1) {}
}

/* KNOWN-ISSUE: on the current CPU the fetched 32B line containing the
   self-modified copy is not refreshed after fence.i, so this test hangs
   (fetch executes stale bytes).  Kept as a documented regression for the
   memory-system rework (I-flush on fence.i); excluded from the default
   TESTS list until fixed. */
