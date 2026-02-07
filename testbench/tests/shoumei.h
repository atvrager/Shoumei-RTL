#ifndef SHOUMEI_H
#define SHOUMEI_H
#include <stdint.h>
extern volatile uint32_t tohost;
static inline void pass(void) { tohost = 1; }
static inline void fail(uint32_t code) { tohost = code; }
#endif
