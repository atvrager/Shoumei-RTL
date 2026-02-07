OUTPUT_ARCH("riscv")
ENTRY(_start)
MEMORY { RAM (rwx) : ORIGIN = 0x0, LENGTH = 64K }
SECTIONS {
    .text 0x0 : { *(.text.start) *(.text*) } > RAM
    .rodata    : { *(.rodata*) } > RAM
    .data      : { *(.data*)   } > RAM
    .bss       : { *(.bss* COMMON) } > RAM
    .tohost 0x1000 (NOLOAD) : { tohost = .; . += 4; } > RAM
    _stack_top = 0x10000;
}
