/*
 * fp_wb_backpressure_test.S - FP writeback must honour the result FIFO's ready.
 *
 * The FP EU merges six sub-unit results through one priority mux.  Each source
 * parks its result in a 1-entry flow queue until the mux wins it, but the mux
 * must also wait for the FP result FIFO to accept it: `Queue1Flow` is depth 1
 * and its `enq_ready` is low while its head is undrained (the CDB mux can hold
 * the FP channel off for several cycles while ib0/ib1 are busy).
 *
 * Releasing a queued result while `enq_ready` is low loses it: the source has
 * already consumed its operation, the consumer's ROB entry never sees its tag,
 * and the core deadlocks with a non-empty ROB.  This program was found by the
 * seeded random generator (seed 11552666100682340110, program 2) and is checked
 * in verbatim as the reproducer.  Fails by hanging, passes with tohost = 1.
 */
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
    .word 0x203140bb   # sh2add_uw (Zb* routine 40)
    .word 0xd02f1f53   # fcvt_s_l
    .word 0x030e2133   # mulhsu
    .word 0x0fffa823   # sw
    .word 0xc7157d93   # andi
    .word 0xe20409d3   # fmv_x_d
    .word 0x403160b3   # orn (Zb* routine 8)
    .word 0x401fa82f   # amoor_w
    .word 0xe9a23f47   # fmsub_s
    .word 0x6a0fbb83   # ld
    .word 0xd0113353   # fcvt_s_wu
    .word 0x5d6fde83   # lhu
    .word 0x603110b3   # rol (Zb* routine 14)
    .word 0xf00c8cd3   # fmv_w_x
    .word 0x18769653   # fdiv_s
    .word 0x0073d263   # bge
    .word 0x6b815093   # rev8 (Zb* routine 28)
    .word 0xc2200a53   # fcvt_l_d
    .word 0x1304bed3   # fmul_d
    .word 0x778fa983   # lw
    .word 0x0021a9f3   # csrrs
    .word 0x0a3170b3   # maxu (Zb* routine 13)
    .word 0x2fb32a93   # slti
    .word 0x0040036f   # jal
    .word 0x401cbb53   # fcvt_s_d
    .word 0xc20821d3   # fcvt_w_d
    .word 0x403160b3   # orn (Zb* routine 8)
    .word 0xd2270753   # fcvt_d_l
    .word 0x976f1d0f   # fence_i
    .word 0xa33f0453   # fle_d
    .word 0x255a9ee3   # bne
    .word 0x02f0f133   # remu
    .word 0x77ce12e3   # bne
    .word 0x6bffbc27   # fsd
    .word 0x299c18d3   # fmax_s
    .word 0x416f8abb   # subw
    .word 0xe2038e53   # fmv_x_d
    .word 0x024f7733   # remu
    .word 0x1949ba53   # fdiv_s
    .word 0x603110b3   # rol (Zb* routine 14)
    .word 0x28011093   # bseti (Zb* routine 19)
    .word 0x6b815093   # rev8 (Zb* routine 28)
    .word 0x68c64163   # blt
    .word 0x0a3130b3   # clmulh (Zb* routine 17)
    .word 0xa356a753   # feq_d
    .word 0x23f39dd3   # fsgnjn_d
    .word 0x13c04ed3   # fmul_d
    .word 0x0957948f   # fence_i
    .word 0x030888bb   # mulw
    .word 0x03e322b3   # mulhsu
    .word 0x29648453   # fmin_s
    .word 0x2bffb427   # fsd
    .word 0x40b9d2bb   # sraw
    .word 0x00427263   # bgeu
    .word 0x68011093   # binvi (Zb* routine 21)
    .word 0x0a3130b3   # clmulh (Zb* routine 17)
    .word 0x59ffa223   # sw
    .word 0x44ffae2f   # amoor_w
    .word 0x73ffbc23   # sd
    .word 0x036681bb   # mulw
    .word 0x42330cc3   # fmadd_d
    .word 0xf0030653   # fmv_w_x
    .word 0x100fbcaf   # lr_d
    .word 0x435fb42f   # amoor_d

    # PASS: write 1 to tohost
    li x1, 0x1000
    li x2, 1
    sw x2, 0(x1)
.Lhalt:
    j .Lhalt
