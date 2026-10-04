/*
 * zero_probe.S - FCVT.WU.D of +0.0 with a static rounding mode.
 *
 * The instruction's own rounding mode can differ from fcsr.  rand_0027 PC 0x258
 * is fcvt.wu.d x21, f19 of +0.0 with funct3 = 4 (rmm) and returns 1 where the
 * reference returns 0.  The dynamic form of the same input passes for every mode.
 */
    .section .text
.macro SETRM rm
    li       t0, (\rm << 5)
    csrw     fcsr, t0
.endm
.macro ZERO freg
    li       t0, 0
    fmv.d.x  \freg, t0
.endm
    .globl _start
    .globl main
_start:
main:
    ZERO     f19
    SETRM    0
    fcvt.wu.d x9, f19, rne
    csrr     t2, fflags

    ZERO     f19
    SETRM    0
    fcvt.wu.d x10, f19, rtz
    csrr     t2, fflags

    ZERO     f19
    SETRM    0
    fcvt.wu.d x11, f19, rdn
    csrr     t2, fflags

    ZERO     f19
    SETRM    0
    fcvt.wu.d x12, f19, rup
    csrr     t2, fflags

    ZERO     f19
    SETRM    0
    fcvt.wu.d x13, f19, rmm
    csrr     t2, fflags

    li       a1, 0x1000
    li       a2, 1
    sw       a2, 0(a1)
.Lhalt:
    j        .Lhalt
