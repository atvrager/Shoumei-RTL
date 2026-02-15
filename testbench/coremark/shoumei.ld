OUTPUT_ARCH("riscv")
ENTRY(_start)
MEMORY { RAM (rwx) : ORIGIN = 0x0, LENGTH = 64K }
SECTIONS {
    .text 0x0 : { *(.text.start) *(.text*) } > RAM
    .rodata    : { *(.rodata*) } > RAM
    .data      : { *(.data*)   } > RAM
    .bss       : {
        __bss_start = .;
        *(.bss* COMMON)
        __bss_end = .;
    } > RAM
    /* HTIF: placed after all code/data sections */
    .tohost ALIGN(4) (NOLOAD) : {
        tohost = .;      . += 4;
        putchar_addr = .; . += 4;
    } > RAM
    _stack_top = 0x10000;
}
