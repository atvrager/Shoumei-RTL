OUTPUT_ARCH("riscv")
ENTRY(_start)
MEMORY { RAM (rwx) : ORIGIN = 0x0, LENGTH = 256K }
SECTIONS {
    .text.init 0x0 : { *(.text.init) } > RAM
    .text : { *(.text*) } > RAM
    . = ALIGN(0x1000);
    .tohost : { *(.tohost) } > RAM
    .data : { *(.data*) } > RAM
    .bss : { *(.bss* COMMON) } > RAM
    . = ALIGN(8);
    _stack_top = 0x40000;
}
