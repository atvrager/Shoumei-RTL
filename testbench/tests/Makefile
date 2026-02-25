RISCV_PREFIX ?= riscv32-unknown-elf-
CC      = $(RISCV_PREFIX)gcc
CFLAGS  = -march=rv32im_zicsr_zifencei -mabi=ilp32 -O2 -nostdlib -nostartfiles -ffreestanding
LDFLAGS = -T shoumei.ld -nostdlib -Wl,--no-relax
TESTS   = pass_test dep_test addi_test lui_auipc_test jal_jalr_test branch_test store_load_test subword_store_test sltiu_test ipc_loop csr_test hello_test branch_flush_x0_test mepc_only_test trap_csr_test ecall_test

# Generated assembly tests (self-contained, include their own _start)
GEN_ASM    := $(wildcard generated/*.S)
GEN_FP_ASM := $(filter generated/fp_%.S,$(GEN_ASM))
GEN_INT_ASM:= $(filter-out generated/fp_%.S,$(GEN_ASM))
GEN_INT_ELFS := $(GEN_INT_ASM:.S=.elf)
GEN_FP_ELFS  := $(GEN_FP_ASM:.S=.elf)

# F-extension tests need rv32imf
CFLAGS_FP = -march=rv32imf_zicsr_zifencei -mabi=ilp32f -O2 -nostdlib -nostartfiles -ffreestanding

all: $(TESTS:=.elf) $(GEN_INT_ELFS) $(GEN_FP_ELFS)

# Hand-written C tests use crt0.S
%.elf: %.c crt0.S shoumei.ld
	$(CC) $(CFLAGS) $(LDFLAGS) crt0.S $< -o $@

# Generated integer tests are self-contained (have _start + main)
generated/%.elf: generated/%.S shoumei.ld
	$(CC) $(CFLAGS) $(LDFLAGS) $< -o $@

# Generated FP tests need rv32imf
generated/fp_%.elf: generated/fp_%.S shoumei.ld
	$(CC) $(CFLAGS_FP) $(LDFLAGS) $< -o $@

clean:
	rm -f *.elf *.o generated/*.elf
