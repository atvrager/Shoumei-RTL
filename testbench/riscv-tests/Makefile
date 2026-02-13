# Build upstream riscv-tests rv32ui + rv32um + rv32uf suites for Shoumei
# Uses our minimal riscv_test.h (no CSR/trap support)

RISCV_TESTS := ../../third_party/riscv-tests
CC := riscv32-unknown-elf-gcc
CFLAGS_BASE := -mabi=ilp32 -static -nostdlib -nostartfiles \
               -I. -I$(RISCV_TESTS)/isa/macros/scalar
LDFLAGS := -T shoumei.ld

# Per-ISA arch flags (Zifencei needed for fence.i instruction)
CFLAGS_IM  := $(CFLAGS_BASE) -march=rv32im_zifencei
CFLAGS_IMF := $(CFLAGS_BASE) -march=rv32imf_zifencei

# All pure RV32I user-mode integer tests (including fence_i, no ma_data)
RV32UI_TESTS := simple add addi sub and andi or ori xor xori \
  sll slli srl srli sra srai lui auipc \
  slt slti sltu sltiu \
  beq bne blt bltu bge bgeu \
  jal jalr \
  lw lh lhu lb lbu sw sh sb \
  ld_st st_ld \
  fence_i

# RV32M multiply/divide tests
RV32UM_TESTS := mul mulh mulhsu mulhu div divu rem remu

# RV32F single-precision floating-point tests (disabled pending Zicsr support)
# RV32UF_TESTS := fadd fdiv fclass fcmp fcvt fcvt_w fmadd fmin ldst move recoding

ELFS := $(addprefix rv32ui-p-,$(addsuffix .elf,$(RV32UI_TESTS))) \
        $(addprefix rv32um-p-,$(addsuffix .elf,$(RV32UM_TESTS)))

all: $(ELFS)

rv32ui-p-%.elf: $(RISCV_TESTS)/isa/rv32ui/%.S shoumei.ld riscv_test.h
	$(CC) $(CFLAGS_IM) $(LDFLAGS) $< -o $@

rv32um-p-%.elf: $(RISCV_TESTS)/isa/rv32um/%.S shoumei.ld riscv_test.h
	$(CC) $(CFLAGS_IM) $(LDFLAGS) $< -o $@

rv32uf-p-%.elf: $(RISCV_TESTS)/isa/rv32uf/%.S shoumei.ld riscv_test.h
	$(CC) $(CFLAGS_IMF) $(LDFLAGS) $< -o $@

clean:
	rm -f *.elf

.PHONY: all clean
