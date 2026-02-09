RISCV_PREFIX ?= riscv32-unknown-elf-
CC      = $(RISCV_PREFIX)gcc
CFLAGS  = -march=rv32im -mabi=ilp32 -O2 -nostdlib -nostartfiles -ffreestanding
LDFLAGS = -T shoumei.ld -nostdlib
TESTS   = pass_test dep_test addi_test lui_auipc_test jal_jalr_test branch_test store_load_test sltiu_test

# Generated assembly tests
GEN_ASM := $(wildcard generated/*.S)
GEN_ELFS := $(GEN_ASM:.S=.elf)

all: $(TESTS:=.elf) $(GEN_ELFS)

%.elf: %.c crt0.S shoumei.ld
	$(CC) $(CFLAGS) $(LDFLAGS) crt0.S $< -o $@

generated/%.elf: generated/%.S crt0.S shoumei.ld
	$(CC) $(CFLAGS) $(LDFLAGS) crt0.S $< -o $@

clean:
	rm -f *.elf *.o generated/*.elf
