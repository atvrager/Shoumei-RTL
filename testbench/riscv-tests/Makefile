# Build upstream riscv-tests rv64ui + rv64um + rv64uf + rv64ud + rv64ua suites for Shoumei
# Uses our minimal riscv_test.h (no CSR/trap support)

RISCV_TESTS := ../../third_party/riscv-tests
RISCV_PREFIX ?= $(shell command -v riscv64-unknown-elf-gcc >/dev/null 2>&1 && echo riscv64-unknown-elf- || (command -v riscv64-elf-gcc >/dev/null 2>&1 && echo riscv64-elf- || echo riscv64-elf-))
CC = $(RISCV_PREFIX)gcc
CFLAGS_BASE := -static -nostdlib -nostartfiles \
               -I. -I$(RISCV_TESTS)/isa/macros/scalar
LDFLAGS := -T shoumei64.ld

# Per-ISA arch flags (Zifencei needed for fence.i instruction)
CFLAGS_IM   := $(CFLAGS_BASE) -march=rv64im_zifencei -mabi=lp64
CFLAGS_IMF  := $(CFLAGS_BASE) -march=rv64imf_zifencei -mabi=lp64f
CFLAGS_IMA  := $(CFLAGS_BASE) -march=rv64ima_zifencei -mabi=lp64
CFLAGS_IMFD := $(CFLAGS_BASE) -march=rv64imafd_zifencei -mabi=lp64d

# All pure RV64I user-mode integer tests
RV64UI_TESTS := simple add addi addiw addw and andi \
  sll slli slliw sllw srl srli srliw srlw sra srai sraiw sraw lui auipc \
  slt slti sltu sltiu \
  beq bne blt bltu bge bgeu \
  jal jalr \
  ld lwu lw lh lhu lb lbu sd sw sh sb \
  ld_st st_ld sub subw xor xori or ori

# RV64M multiply/divide tests
RV64UM_TESTS := mul mulh mulhsu mulhu div divu rem remu mulw divw divuw remw remuw

# RV64F single-precision floating-point tests
RV64UF_TESTS := fadd fdiv fclass fcmp fcvt fcvt_w fmadd fmin ldst move recoding

# RV64D double-precision floating-point tests
RV64UD_TESTS := fadd fclass fcmp fcvt fcvt_w fdiv fmadd fmin ldst recoding structural move

# RV64A atomic tests
RV64UA_TESTS := amoadd_w amoand_w amomax_w amomaxu_w amomin_w amominu_w amoor_w amoswap_w amoxor_w \
  amoadd_d amoand_d amomax_d amomaxu_d amomin_d amominu_d amoor_d amoswap_d amoxor_d lrsc

ELFS := $(addprefix rv64ui-p-,$(addsuffix .elf,$(RV64UI_TESTS))) \
        $(addprefix rv64um-p-,$(addsuffix .elf,$(RV64UM_TESTS))) \
        $(addprefix rv64uf-p-,$(addsuffix .elf,$(RV64UF_TESTS))) \
        $(addprefix rv64ud-p-,$(addsuffix .elf,$(RV64UD_TESTS))) \
        $(addprefix rv64ua-p-,$(addsuffix .elf,$(RV64UA_TESTS)))

all: $(ELFS)

rv64ui-p-%.elf: $(RISCV_TESTS)/isa/rv64ui/%.S shoumei64.ld riscv_test.h
	$(CC) $(CFLAGS_IM) $(LDFLAGS) $< -o $@

rv64um-p-%.elf: $(RISCV_TESTS)/isa/rv64um/%.S shoumei64.ld riscv_test.h
	$(CC) $(CFLAGS_IM) $(LDFLAGS) $< -o $@

rv64uf-p-%.elf: $(RISCV_TESTS)/isa/rv64uf/%.S shoumei64.ld riscv_test.h
	$(CC) $(CFLAGS_IMF) $(LDFLAGS) $< -o $@

rv64ud-p-%.elf: $(RISCV_TESTS)/isa/rv64ud/%.S shoumei64.ld riscv_test.h
	$(CC) $(CFLAGS_IMFD) $(LDFLAGS) $< -o $@

rv64ua-p-%.elf: $(RISCV_TESTS)/isa/rv64ua/%.S shoumei64.ld riscv_test.h
	$(CC) $(CFLAGS_IMA) $(LDFLAGS) $< -o $@

clean:
	rm -f *.elf

.PHONY: all clean
