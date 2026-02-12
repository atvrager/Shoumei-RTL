OUTPUT_ARCH("riscv")
ENTRY(_start)
MEMORY { RAM (rwx) : ORIGIN = 0x0, LENGTH = 64K }
SECTIONS {
    .text.init 0x0 : { *(.text.init) } > RAM
    .text          : { *(.text*) } > RAM
    .tohost 0x1000 (NOLOAD) : { *(.tohost) } > RAM
    .data          : { *(.data*) } > RAM
    .bss           : { *(.bss* COMMON) } > RAM
    _stack_top = 0x10000;
}
