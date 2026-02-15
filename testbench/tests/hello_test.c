#include "shoumei.h"

int main(void) {
    const char *msg = "Hello from Shoumei!\n";
    while (*msg)
        shoumei_putchar(*msg++);
    pass();
    return 0;
}
