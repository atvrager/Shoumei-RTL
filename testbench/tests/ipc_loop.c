#include "shoumei.h"

__attribute__((noinline))
int loop_sum(int n) {
    int sum = 0;
    for (int i = 0; i < n; i++)
        sum += i;
    return sum;
}

int main(void) {
    int result = loop_sum(15);
    if (result == 105)
        pass();
    else
        fail(2);
    return 0;
}
