RISCV_PREFIX ?= riscv32-unknown-elf-
CC      = $(RISCV_PREFIX)gcc
CFLAGS  = -march=rv32im_zicsr_zifencei -mabi=ilp32 -O2 -nostdlib -nostartfiles -ffreestanding
LDFLAGS = -T shoumei.ld -nostdlib -Wl,--no-relax
TESTS   = pass_test dep_test addi_test lui_auipc_test jal_jalr_test branch_test store_load_test subword_store_test sltiu_test ipc_loop csr_test hello_test branch_flush_x0_test mepc_only_test trap_csr_test ecall_test mret_test wfi_test timer_irq_test

# Generated assembly tests (self-contained, include their own _start)
GEN_ASM    := $(wildcard generated/*.S)
GEN_FP_ASM := $(filter generated/fp_%.S,$(GEN_ASM))
GEN_INT_ASM:= $(filter-out generated/fp_%.S,$(GEN_ASM))
GEN_INT_ELFS := $(GEN_INT_ASM:.S=.elf)
GEN_FP_ELFS  := $(GEN_FP_ASM:.S=.elf)

# F-extension tests need rv32imf
CFLAGS_FP = -march=rv32imf_zicsr_zifencei -mabi=ilp32f -O2 -nostdlib -nostartfiles -ffreestanding

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

all: $(TESTS:=.elf) $(GEN_INT_ELFS) $(GEN_FP_ELFS) freertos_demo.elf

# Hand-written C tests use crt0.S
%.elf: %.c crt0.S shoumei.ld
	$(CC) $(CFLAGS) $(LDFLAGS) crt0.S $< -o $@

# Generated integer tests are self-contained (have _start + main)
generated/%.elf: generated/%.S shoumei.ld
	$(CC) $(CFLAGS) $(LDFLAGS) $< -o $@

# Generated FP tests need rv32imf
generated/fp_%.elf: generated/fp_%.S shoumei.ld
	$(CC) $(CFLAGS_FP) $(LDFLAGS) $< -o $@

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
	rm -f *.elf *.o generated/*.elf
