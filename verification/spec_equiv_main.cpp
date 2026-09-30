// Main loop of a timing-enabled Verilator model, as `verilator --binary`
// writes it.  VM_PREFIX and VM_PREFIX_INCLUDE come from spec_equiv.bzl.
#include <memory>

#include "verilated.h"
#include VM_PREFIX_INCLUDE

int main(int argc, char** argv) {
  const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
  contextp->commandArgs(argc, argv);
  const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), ""}};
  while (!contextp->gotFinish()) {
    topp->eval();
    if (!topp->eventsPending()) break;
    contextp->time(topp->nextTimeSlot());
  }
  if (!contextp->gotFinish()) {
    VL_PRINTF("spec co-simulation stopped before $finish\n");
    return 1;
  }
  topp->final();
  return 0;
}
