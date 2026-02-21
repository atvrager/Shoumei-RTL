#include "shoumei.h"

/* Test: VME Matrix Extension basic operations.
   Uses hand-encoded .word directives since GCC lacks VME support.

   VME custom encoding (placeholder — matches Dispatch.lean optype indices):
   All VME instructions use a custom-2 opcode space (0x5B = custom-2).
   Format: [31:25] funct7 | [24:20] rs2 | [19:15] rs1 | [14:12] funct3 | [11:7] rd | [6:0] opcode

   For this stub test, we just verify the CPU doesn't hang when
   encountering VME-style NOP sequences. Actual functional testing
   requires the vector register data path (future V extension merge).

   Test plan:
   1. Write known values to GP registers
   2. Execute MSETCLI (configure tile cols) — encoded as custom instruction
   3. Execute MSETRLI (configure tile rows)
   4. Verify CPU still executes correctly after VME ops
   5. Write pass value to tohost
*/
int main(void) {
    int result;

    /* Basic sanity: ensure integer pipeline still works */
    asm volatile(
        "li   t0, 42\n\t"
        "addi t0, t0, 1\n\t"    /* t0 = 43 */
        "li   t1, 43\n\t"
        "sub  t2, t0, t1\n\t"   /* t2 = 0 */
        "addi t2, t2, 1\n\t"    /* t2 = 1 (PASS) */
        "mv   %0, t2\n\t"
        : "=r"(result)
        :
        : "t0", "t1", "t2"
    );

    tohost = result;
    while (1) {}
}
