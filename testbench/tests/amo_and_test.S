# Auto-generated random test: rand_0011
# seed=42
# length=64 count=32 dict=bazel-out/k8-fastbuild/bin/generators/instr_dict.json
.section .text
.globl _start
_start:
    j .Lmain
.Ltrap:
    csrr x28, mepc
    addi x28, x28, 4
    csrw mepc, x28
    mret
.Lmain:
.globl main
main:
    # x31 = scratch base; never written by the payload
    lui x31, 0x2
    # trap vector: the handler at .Ltrap, which resumes after the fault
    la x28, .Ltrap
    csrw mtvec, x28
    li x5, 0x0000000000000000
    .word 0xf2028053   # fmv.d.x f0, x5
    li x5, 0x8000000000000000
    .word 0xf20280d3   # fmv.d.x f1, x5
    li x5, 0x0000000000000001
    .word 0xf2028153   # fmv.d.x f2, x5
    li x5, 0x000fffffffffffff
    .word 0xf20281d3   # fmv.d.x f3, x5
    li x5, 0x0010000000000000
    .word 0xf2028253   # fmv.d.x f4, x5
    li x5, 0x3ff0000000000000
    .word 0xf20282d3   # fmv.d.x f5, x5
    li x5, 0x3ff0000000000001
    .word 0xf2028353   # fmv.d.x f6, x5
    li x5, 0x3fefffffffffffff
    .word 0xf20283d3   # fmv.d.x f7, x5
    li x5, 0x3fe0000000000000
    .word 0xf2028453   # fmv.d.x f8, x5
    li x5, 0x4000000000000000
    .word 0xf20284d3   # fmv.d.x f9, x5
    li x5, 0x7fefffffffffffff
    .word 0xf2028553   # fmv.d.x f10, x5
    li x5, 0x7ff0000000000000
    .word 0xf20285d3   # fmv.d.x f11, x5
    li x5, 0xfff0000000000000
    .word 0xf2028653   # fmv.d.x f12, x5
    li x5, 0x7ff8000000000000
    .word 0xf20286d3   # fmv.d.x f13, x5
    li x5, 0x7ff0000000000001
    .word 0xf2028753   # fmv.d.x f14, x5
    li x5, 0xbfb999999999999a
    .word 0xf20287d3   # fmv.d.x f15, x5
    li x5, 0x0000000000000000
    .word 0xf2028853   # fmv.d.x f16, x5
    li x5, 0x8000000000000000
    .word 0xf20288d3   # fmv.d.x f17, x5
    li x5, 0x0000000000000001
    .word 0xf2028953   # fmv.d.x f18, x5
    li x5, 0x000fffffffffffff
    .word 0xf20289d3   # fmv.d.x f19, x5
    li x5, 0x0010000000000000
    .word 0xf2028a53   # fmv.d.x f20, x5
    li x5, 0x3ff0000000000000
    .word 0xf2028ad3   # fmv.d.x f21, x5
    li x5, 0x3ff0000000000001
    .word 0xf2028b53   # fmv.d.x f22, x5
    li x5, 0x3fefffffffffffff
    .word 0xf2028bd3   # fmv.d.x f23, x5
    li x5, 0x3fe0000000000000
    .word 0xf2028c53   # fmv.d.x f24, x5
    li x5, 0x4000000000000000
    .word 0xf2028cd3   # fmv.d.x f25, x5
    li x5, 0x7fefffffffffffff
    .word 0xf2028d53   # fmv.d.x f26, x5
    li x5, 0x7ff0000000000000
    .word 0xf2028dd3   # fmv.d.x f27, x5
    li x5, 0xfff0000000000000
    .word 0xf2028e53   # fmv.d.x f28, x5
    li x5, 0x7ff8000000000000
    .word 0xf2028ed3   # fmv.d.x f29, x5
    li x5, 0x7ff0000000000001
    .word 0xf2028f53   # fmv.d.x f30, x5
    li x5, 0xbfb999999999999a
    .word 0xf2028fd3   # fmv.d.x f31, x5
    .word 0xd23e2153   # fcvt_d_lu
    .word 0x42fa5a93   # srai
    .word 0xc34fb12f   # amominu_d
    .word 0x28ee1c53   # fmax_s
    .word 0x28af9183   # lh
    .word 0x0a3130b3   # clmulh (Zb* routine 17)
    .word 0x0344d03b   # divuw
    .word 0x6001509b   # roriw (Zb* routine 37)
    .word 0x037a0f3b   # mulw
    .word 0x83bfad2f   # amomin_w
    .word 0x00c3a433   # slt
    .word 0x6021109b   # cpopw (Zb* routine 34)
    .word 0x3f0fad07   # flw
    .word 0xd0393b53   # fcvt_s_lu
    .word 0xe4abcd13   # xori
    .word 0x30007173   # csrrci
    .word 0xd01744d3   # fcvt_s_wu
    .word 0x203140b3   # sh2add (Zb* routine 1)
    .word 0x01411cb3   # sll
    .word 0x403160b3   # orn (Zb* routine 8)
    .word 0x403170b3   # andn (Zb* routine 7)
    .word 0xc22f2853   # fcvt_l_d
    .word 0x203160b3   # sh3add (Zb* routine 2)
    .word 0xd01c26d3   # fcvt_s_wu
    .word 0x0233d6bb   # divuw
    .word 0xa0cb2a53   # feq_s
    .word 0xd02598d3   # fcvt_s_l
    .word 0x6f50c693   # xori
    .word 0x640fa007   # flw
    .word 0x48011093   # bclri (Zb* routine 20)
    .word 0x21d1a9d3   # fsgnjx_s
    .word 0x09094453   # fsub_s
    .word 0x5a018853   # fsqrt_d
    .word 0x5c0fba07   # fld
    .word 0x01831d3b   # sllw
    .word 0x603110b3   # rol (Zb* routine 14)
    .word 0x340219f3   # csrrw
    .word 0xa1c598d3   # flt_s
    .word 0xa2f909d3   # fle_d
    .word 0x039679b3   # remu
    .word 0x0118d4bb   # srlw
    .word 0x28fa8653   # fmin_s
    .word 0x6021109b   # cpopw (Zb* routine 34)
    .word 0x60411093   # sext_b (Zb* routine 29)
    .word 0x6021109b   # cpopw (Zb* routine 34)
    .word 0xa04c15cf   # fnmadd_s
    .word 0x203160bb   # sh3add_uw (Zb* routine 41)
    .word 0x203140bb   # sh2add_uw (Zb* routine 40)
    .word 0xa20fbe2f   # amomax_d
    .word 0x033666bb   # remw
    .word 0x435e5893   # srai
    .word 0x6824c14f   # fnmadd_s
    .word 0x049fbeaf   # amoadd_d
    .word 0xa59faaaf   # amomax_w
    nop
    nop
    .word 0x6001509b   # roriw (Zb* routine 37)
    nop
    nop
    nop
    .word 0x61cfad2f   # amoand_w
    .word 0x638fb7af   # amoand_d
    .word 0x0801109b   # slli_uw (Zb* routine 42)
    .word 0x41bf053b   # subw

    # PASS: write 1 to tohost
    li x1, 0x1000
    li x2, 1
    sw x2, 0(x1)
.Lhalt:
    j .Lhalt
