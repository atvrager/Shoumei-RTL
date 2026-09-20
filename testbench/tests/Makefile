RISCV_PREFIX ?= $(shell command -v riscv64-unknown-elf-gcc >/dev/null 2>&1 && echo riscv64-unknown-elf- || (command -v riscv64-elf-gcc >/dev/null 2>&1 && echo riscv64-elf- || (command -v riscv32-unknown-elf-gcc >/dev/null 2>&1 && echo riscv32-unknown-elf- || echo riscv64-elf-)))
CC      = $(RISCV_PREFIX)gcc
CFLAGS  = -march=rv64im_zicsr_zifencei -mabi=lp64 -O2 -nostdlib -nostartfiles -ffreestanding
LDFLAGS = -T shoumei.ld -nostdlib -Wl,--no-relax
TESTS   = store_fwd_stress pass_test dep_test addi_test lui_auipc_test jal_jalr_test branch_test store_load_test subword_store_test sltiu_test ipc_loop csr_test hello_test branch_flush_x0_test mepc_only_test trap_csr_test ecall_test mret_test wfi_test timer_irq_test ss_independent_test ss_dependent_test minstret_test jalr_a0_test jal_ret_flush_test jalr_a0_irq_test test_zba test_zbs test_zbb test_zbc test_illegal_fallback serialize_pair_test fence_i_test

# Self-contained assembly tests (own _start; no crt0.S)
ASM_TESTS = serialize_pair_test

# Generated assembly tests (self-contained, include their own _start)
GEN_ASM    := $(wildcard generated/*.S)
GEN_FP_ASM := $(filter generated/fp_%.S,$(GEN_ASM))
GEN_INT_ASM:= $(filter-out generated/fp_%.S,$(GEN_ASM))
GEN_INT_ELFS := $(GEN_INT_ASM:.S=.elf)
GEN_FP_ELFS  := $(GEN_FP_ASM:.S=.elf)

# FP tests (F and D extension)
CFLAGS_FP = -march=rv64imafd_zicsr_zifencei -mabi=lp64d -O2 -nostdlib -nostartfiles -ffreestanding

# FreeRTOS kernel sources
FREERTOS_DIR = ../../third_party/FreeRTOS-Kernel
FREERTOS_PORT_DIR = $(FREERTOS_DIR)/portable/GCC/RISC-V
FREERTOS_HEAP_DIR = $(FREERTOS_DIR)/portable/MemMang
FREERTOS_CHIP_EXT = $(FREERTOS_PORT_DIR)/chip_specific_extensions/RV32I_CLINT_no_extensions

FREERTOS_SRCS = \
	$(FREERTOS_DIR)/tasks.c \
	$(FREERTOS_DIR)/list.c \
	$(FREERTOS_DIR)/queue.c \
	$(FREERTOS_PORT_DIR)/port.c \
	$(FREERTOS_HEAP_DIR)/heap_1.c

FREERTOS_INC = \
	-I. \
	-I$(FREERTOS_DIR)/include \
	-I$(FREERTOS_PORT_DIR)

FREERTOS_CFLAGS = $(CFLAGS) $(FREERTOS_INC)
FREERTOS_AFLAGS = $(CFLAGS) -I$(FREERTOS_CHIP_EXT) $(FREERTOS_INC)
FREERTOS_LDFLAGS = -T freertos.ld -nostdlib -Wl,--no-relax

all: $(TESTS:=.elf) nan_boxing.elf $(GEN_INT_ELFS) $(GEN_FP_ELFS) freertos_demo.elf

# Hand-written C tests use crt0.S
%.elf: %.c crt0.S shoumei.ld
	$(CC) $(CFLAGS) $(LDFLAGS) crt0.S $< -o $@

# Self-contained assembly tests bring their own _start (no crt0.S)
$(ASM_TESTS:=.elf): %.elf: %.S shoumei.ld
	$(CC) $(CFLAGS) $(LDFLAGS) $< -o $@

nan_boxing.elf: nan_boxing.c crt0.S shoumei.ld
	$(CC) $(CFLAGS_FP) $(LDFLAGS) crt0.S $< -o $@

# Generated integer tests are self-contained (have _start + main)
generated/%.elf: generated/%.S shoumei.ld
	$(CC) $(CFLAGS) $(LDFLAGS) $< -o $@

# Generated FP tests need rv32imf
generated/fp_%.elf: generated/fp_%.S shoumei.ld
	$(CC) $(CFLAGS_FP) $(LDFLAGS) $< -o $@

# ==========================================================================
# Benchmark programs (generated/bench/): three march variants.
# - plain:  rv64im_zicsr_zifencei           (integer-only programs)
# - fp_*:   rv64imafd_zicsr_zifencei        (F/D programs)
# - amo_*:  AMO programs; IMAFD already includes A, so the same flags work
#           (older riscv-gcc rejects the redundant 'a' in rv64imafda).
# `bench` is NOT part of `all`: run-all-tests globs generated/*.elf
# non-recursively, so the bench ELFs stay out of the regression suite.
# ==========================================================================
BENCH_ASM  := $(wildcard generated/bench/*.S)
BENCH_ELFS := $(patsubst %.S,%.elf,$(BENCH_ASM))
CFLAGS_AMO = $(CFLAGS_FP)
CFLAGS_ZB  = -march=rv64im_zba_zbb_zbc_zbs_zicsr_zifencei -mabi=lp64 -O2 -nostdlib -nostartfiles -ffreestanding
generated/bench/fp_%.elf: generated/bench/fp_%.S shoumei.ld
	$(CC) $(CFLAGS_FP) $(LDFLAGS) $< -o $@

generated/bench/amo_%.elf: generated/bench/amo_%.S shoumei.ld
	$(CC) $(CFLAGS_AMO) $(LDFLAGS) $< -o $@

generated/bench/zb_%.elf: generated/bench/zb_%.S shoumei.ld
	$(CC) $(CFLAGS_ZB) $(LDFLAGS) $< -o $@
generated/bench/%.elf: generated/bench/%.S shoumei.ld
	$(CC) $(CFLAGS) $(LDFLAGS) $< -o $@

bench: $(BENCH_ELFS)

# FreeRTOS demo - special build
freertos_demo.elf: freertos_demo.c freertos_boot.S FreeRTOSConfig.h freertos.ld $(FREERTOS_SRCS) $(FREERTOS_PORT_DIR)/portASM.S
	$(CC) $(FREERTOS_CFLAGS) $(FREERTOS_LDFLAGS) \
		freertos_boot.S \
		minilib.c \
		freertos_demo.c \
		$(FREERTOS_SRCS) \
		-I$(FREERTOS_CHIP_EXT) \
		$(FREERTOS_PORT_DIR)/portASM.S \
		-o $@

clean:
	rm -f *.elf *.o generated/*.elf generated/bench/*.elf
