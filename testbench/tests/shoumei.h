#ifndef SHOUMEI_H
#define SHOUMEI_H
#include <stdint.h>
extern volatile uint32_t tohost;

#define SHOUMEI_PUTCHAR_ADDR ((volatile uint32_t *)0x1004)

static inline void pass(void) { tohost = 1; }
static inline void fail(uint32_t code) { tohost = code; }
static inline void shoumei_putchar(int c) { *SHOUMEI_PUTCHAR_ADDR = (uint32_t)(unsigned char)c; }
#endif
