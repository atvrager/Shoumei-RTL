OUTPUT_ARCH("riscv")
ENTRY(_start)
MEMORY { RAM (rwx) : ORIGIN = 0x0, LENGTH = 256K }
SECTIONS {
    .text 0x0 : {
        *(.text.start)
        *(.text.freertos_risc_v_trap_handler)
        *(.text.freertos_risc_v_exception_handler)
        *(.text.freertos_risc_v_interrupt_handler)
        *(.text.freertos_risc_v_mtimer_interrupt_handler)
        *(.text*)
    } > RAM
    .rodata    : { *(.rodata*) } > RAM
    .data      : { *(.data*) *(.sdata*) } > RAM
    .bss       : {
        __bss_start = .;
        *(.bss* .sbss* COMMON)
        __bss_end = .;
    } > RAM
    .noinit (NOLOAD) : {
        *(.noinit*)
    } > RAM
    .tohost 0x3F000 (NOLOAD) : { tohost = .; . += 4; putchar_addr = .; . += 4; } > RAM
    _stack_top = 0x40000;
    __freertos_irq_stack_top = _stack_top;
}
