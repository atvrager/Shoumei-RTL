# CoreMark build for Shoumei RV32IM CPU
RISCV_PREFIX ?= riscv32-unknown-elf-
CC      = $(RISCV_PREFIX)gcc
OBJDUMP = $(RISCV_PREFIX)objdump

COREMARK_DIR = ../../third_party/coremark

# CoreMark sources (from submodule)
COREMARK_SRC = $(COREMARK_DIR)/core_list_join.c \
               $(COREMARK_DIR)/core_main.c \
               $(COREMARK_DIR)/core_matrix.c \
               $(COREMARK_DIR)/core_state.c \
               $(COREMARK_DIR)/core_util.c

# Port sources (local)
PORT_SRC = core_portme.c ee_printf.c

ITERATIONS ?= 10

CFLAGS  = -march=rv32im_zicsr -mabi=ilp32 -O2 \
          -nostdlib -nostartfiles -ffreestanding \
          -msmall-data-limit=0 \
          -I. -I$(COREMARK_DIR) \
          -DITERATIONS=$(ITERATIONS) \
          -DCLOCKS_PER_SEC=1 \
          -DFLAGS_STR=\""-O2 -march=rv32im_zicsr"\"

LDFLAGS = -T shoumei.ld -nostdlib

ALL_SRC = crt0.S $(COREMARK_SRC) $(PORT_SRC)

.PHONY: all cosim clean

# Default: mcycle timer for real performance measurement
all: coremark.elf

# Cosim-safe: software counter avoids CSR perf counter mismatches
cosim: coremark_cosim.elf

coremark.elf: $(ALL_SRC) shoumei.ld
	$(CC) $(CFLAGS) $(LDFLAGS) $(ALL_SRC) -o $@
	$(OBJDUMP) -d $@ > coremark.dump

coremark_cosim.elf: $(ALL_SRC) shoumei.ld
	$(CC) $(CFLAGS) -DCOSIM_SAFE $(LDFLAGS) $(ALL_SRC) -o $@
	$(OBJDUMP) -d $@ > coremark_cosim.dump

clean:
	rm -f coremark.elf coremark.dump coremark_cosim.elf coremark_cosim.dump
