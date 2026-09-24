# Standalone test reproducing deadlock uncovered by seed 8125110225876537498 (rand_0027)
# Tests StoreBuffer flush when a pipeline flush occurs while pending_commit > 0.
# Without the fix, StoreBuffer drops the flush, leaving an uncommitted speculative
# store in StoreBuffer8 and deadlocking at the subsequent pipeline drain (clz).

.section .text
.globl _start
_start:
.globl main
main:
    # x31 = scratch base; never written by the payload
    lui x31, 0x2
    .word 0xf2000053   # fmv.d.x f0, x0
    .word 0xf20000d3   # fmv.d.x f1, x0
    .word 0xf2000153   # fmv.d.x f2, x0
    .word 0xf20001d3   # fmv.d.x f3, x0
    .word 0xf2000253   # fmv.d.x f4, x0
    .word 0xf20002d3   # fmv.d.x f5, x0
    .word 0xf2000353   # fmv.d.x f6, x0
    .word 0xf20003d3   # fmv.d.x f7, x0
    .word 0xf2000453   # fmv.d.x f8, x0
    .word 0xf20004d3   # fmv.d.x f9, x0
    .word 0xf2000553   # fmv.d.x f10, x0
    .word 0xf20005d3   # fmv.d.x f11, x0
    .word 0xf2000653   # fmv.d.x f12, x0
    .word 0xf20006d3   # fmv.d.x f13, x0
    .word 0xf2000753   # fmv.d.x f14, x0
    .word 0xf20007d3   # fmv.d.x f15, x0
    .word 0xf2000853   # fmv.d.x f16, x0
    .word 0xf20008d3   # fmv.d.x f17, x0
    .word 0xf2000953   # fmv.d.x f18, x0
    .word 0xf20009d3   # fmv.d.x f19, x0
    .word 0xf2000a53   # fmv.d.x f20, x0
    .word 0xf2000ad3   # fmv.d.x f21, x0
    .word 0xf2000b53   # fmv.d.x f22, x0
    .word 0xf2000bd3   # fmv.d.x f23, x0
    .word 0xf2000c53   # fmv.d.x f24, x0
    .word 0xf2000cd3   # fmv.d.x f25, x0
    .word 0xf2000d53   # fmv.d.x f26, x0
    .word 0xf2000dd3   # fmv.d.x f27, x0
    .word 0xf2000e53   # fmv.d.x f28, x0
    .word 0xf2000ed3   # fmv.d.x f29, x0
    .word 0xf2000f53   # fmv.d.x f30, x0
    .word 0xf2000fd3   # fmv.d.x f31, x0
    .word 0x029f7c3b   # remuw
    .word 0x97ef1863   # bne
    .word 0x203140b3   # sh2add (Zb* routine 1)
    .word 0x6011109b   # ctzw (Zb* routine 33)
    .word 0x227b8ad3   # fsgnj_d
    .word 0xc01a3e53   # fcvt_wu_s
    .word 0x258fe703   # lwu
    .word 0x203120b3   # sh1add (Zb* routine 0)
    .word 0x02f9f1b3   # remu
    .word 0x5b0fba07   # fld
    .word 0x00307e73   # csrrci
    .word 0x813430cb   # fnmsub_s
    .word 0x0a3160b3   # max (Zb* routine 12)
    .word 0xa57faf2f   # amomax_w
    .word 0x48011093   # bclri (Zb* routine 20)
    .word 0xc7cfb72f   # amominu_d
    .word 0x2bff9d23   # sh
    .word 0x00400eef   # jal
    .word 0x88123ccf   # fnmadd_s
    .word 0x7f9cebe3   # bltu
    .word 0x117bc553   # fmul_s
    .word 0x0187bb33   # sltu
    .word 0x25ffb427   # fsd
    .word 0x60011093   # clz (Zb* routine 24)
    .word 0xe20986d3   # fmv_x_d
    .word 0x60011093   # clz (Zb* routine 24)
    .word 0x1ebfa1af   # sc_w
    .word 0x28011093   # bseti (Zb* routine 19)
    .word 0x403160b3   # orn (Zb* routine 8)
    .word 0xc00c3b53   # fcvt_w_s
    .word 0xe00096d3   # fclass_s
    .word 0x02efc5bb   # divw
    .word 0x468fa807   # flw
    .word 0xd03343d3   # fcvt_s_lu
    .word 0xdd2c0c9b   # addiw
    .word 0xc22fc7d3   # fcvt_l_d
    .word 0xe20888d3   # fmv_x_d
    .word 0x03e30f3b   # mulw
    .word 0x4a9702cb   # fnmsub_d
    .word 0x683110b3   # binv (Zb* routine 6)
    .word 0x60011093   # clz (Zb* routine 24)
    .word 0x150fee03   # lwu
    .word 0x02e26eb3   # rem
    .word 0x203140b3   # sh2add (Zb* routine 1)
    .word 0x203120b3   # sh1add (Zb* routine 0)
    .word 0x68011093   # binvi (Zb* routine 21)
    .word 0x11a01353   # fmul_s
    .word 0xa1261753   # flt_s
    .word 0xa3790ed3   # fle_d
    .word 0xd2389653   # fcvt_d_lu
    .word 0x11539bd3   # fmul_s
    .word 0x203160b3   # sh3add (Zb* routine 2)
    .word 0x00561713   # slli
    .word 0x28011093   # bseti (Zb* routine 19)
    .word 0xd2111453   # fcvt_d_wu
    .word 0x00000497   # auipc x9, 0
    .word 0x00848ce7   # jalr x25, 8(x9)
    .word 0xd02688d3   # fcvt_s_l
    .word 0x88cbb5cf   # fnmadd_s
    .word 0x0a3110b3   # clmul (Zb* routine 16)
    .word 0xd004aed3   # fcvt_s_w
    .word 0xc0007d73   # csrrci
    .word 0xc41fb7af   # amominu_d
    .word 0x84efa5af   # amomin_w
    .word 0x01b79b33   # sll

    # PASS: write 1 to tohost
    li x1, 0x1000
    li x2, 1
    sw x2, 0(x1)
.Lhalt:
    j .Lhalt
