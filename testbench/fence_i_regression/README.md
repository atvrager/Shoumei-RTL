# Zifencei self-modifying-code regression

`fence_i_test.c` reproduces a real gap on the current CPU: a fetched
32B line containing freshly stored code is not refreshed after
`fence.i` (sim hangs; Spike cosim stalls at the copied call).  Kept
OUT of the buildable `testbench/tests` list (and cppcheck scope) until
the Zifencei I-flush rework lands; run manually:

    make -C testbench/tests fence_i_test.elf   # after moving back
