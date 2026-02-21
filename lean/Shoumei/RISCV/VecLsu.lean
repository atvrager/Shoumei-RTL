/-
RISCV/VecLsu.lean - Vector Load/Store Unit

Element-loop FSM that bridges RvvCore's structured LSU protocol to scalar
DMEM requests. Processes one vector element per DMEM cycle.

Supports all RVV memory addressing modes:
- Unit-stride (VLE/VSE): addr = base + i × eew_bytes
- Strided (VLSE/VSSE): addr = base + i × stride
- Indexed (VLUXEI/VSUXEI): addr = base + idx_vec[i]

Uses 2× KoggeStoneAdder32 for address generation.
FSM: IDLE → SETUP → ELEM_REQ → ELEM_WAIT → WRITEBACK → IDLE
-/

import Shoumei.DSL
import Shoumei.Circuits.Combinational.KoggeStoneAdder

namespace Shoumei.RISCV

open Shoumei
open Shoumei.Circuits.Combinational

/-- Helper: generate a 4:1 MUX tree for 32-bit values from a 128-bit source,
    selected by sel[1:0]. Returns list of gates. -/
private def mux4x32 (src : List Wire) (sel0 sel1 : Wire)
    (pfx : String) (out : List Wire) : List Gate :=
  let l1 := makeIndexedWires (pfx ++ "_l1") 64
  (List.range 32).map (fun i =>
    Gate.mkMUX src[i]! src[i + 32]! sel0 l1[i]!) ++
  (List.range 32).map (fun i =>
    Gate.mkMUX src[i + 64]! src[i + 96]! sel0 l1[i + 32]!) ++
  (List.range 32).map (fun i =>
    Gate.mkMUX l1[i]! l1[i + 32]! sel1 out[i]!)

/-- Build the VecLsu circuit. -/
def vecLsuCircuit : Circuit :=
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero_const"
  let one := Wire.mk "one_const"

  -- Sidecar inputs from CPU dispatch
  let base_addr := makeIndexedWires "base_addr" 32
  let stride := makeIndexedWires "stride" 32
  let has_stride := Wire.mk "has_stride"

  -- RvvCore → VecLsu (rvv2lsu) inputs
  let rvv2lsu_valid := Wire.mk "rvv2lsu_valid"
  let rvv2lsu_idx_valid := Wire.mk "rvv2lsu_idx_valid"
  let rvv2lsu_idx_data := makeIndexedWires "rvv2lsu_idx_data" 128
  let rvv2lsu_vregfile_valid := Wire.mk "rvv2lsu_vregfile_valid"
  let rvv2lsu_vregfile_data := makeIndexedWires "rvv2lsu_vregfile_data" 128
  let rvv2lsu_mask_valid := Wire.mk "rvv2lsu_mask_valid"
  let rvv2lsu_mask := makeIndexedWires "rvv2lsu_mask" 16
  let rvv2lsu_vd_addr := makeIndexedWires "rvv2lsu_vd_addr" 5
  let rvv2lsu_is_store := Wire.mk "rvv2lsu_is_store"

  -- VecLsu → RvvCore readiness input
  let lsu2rvv_ready := Wire.mk "lsu2rvv_ready"

  -- DMEM interface inputs
  let dmem_req_ready := Wire.mk "dmem_req_ready"
  let dmem_resp_valid := Wire.mk "dmem_resp_valid"
  let dmem_resp_data := makeIndexedWires "dmem_resp_data" 32

  -- EEW input
  let eew := makeIndexedWires "eew" 2

  -- Outputs
  let rvv2lsu_ready := Wire.mk "rvv2lsu_ready"
  let lsu2rvv_valid := Wire.mk "lsu2rvv_valid"
  let lsu2rvv_data := makeIndexedWires "lsu2rvv_data" 128
  let lsu2rvv_addr := makeIndexedWires "lsu2rvv_addr" 5
  let lsu2rvv_last := Wire.mk "lsu2rvv_last"
  let dmem_req_valid := Wire.mk "dmem_req_valid"
  let dmem_req_we := Wire.mk "dmem_req_we"
  let dmem_req_addr := makeIndexedWires "dmem_req_addr" 32
  let dmem_req_data := makeIndexedWires "dmem_req_data" 32
  let dmem_req_size := makeIndexedWires "dmem_req_size" 2

  -- State registers
  let state_reg := makeIndexedWires "state_e" 3
  let state_next := makeIndexedWires "state_nx" 3
  let elem_idx_reg := makeIndexedWires "eidx_e" 4
  let elem_idx_next := makeIndexedWires "eidx_nx" 4
  let addr_acc_reg := makeIndexedWires "aacc_e" 32
  let addr_acc_next := makeIndexedWires "aacc_nx" 32
  let load_data_reg := makeIndexedWires "ld_e" 128
  let load_data_next := makeIndexedWires "ld_nx" 128
  let store_buf_reg := makeIndexedWires "sb_e" 128
  let store_buf_next := makeIndexedWires "sb_nx" 128
  let idx_buf_reg := makeIndexedWires "ib_e" 128
  let idx_buf_next := makeIndexedWires "ib_nx" 128
  let mask_buf_reg := makeIndexedWires "mb_e" 16
  let mask_buf_next := makeIndexedWires "mb_nx" 16
  let vd_addr_reg := makeIndexedWires "vd_e" 5
  let vd_addr_next := makeIndexedWires "vd_nx" 5
  let is_store_reg := Wire.mk "is_st_e"
  let is_store_next := Wire.mk "is_st_nx"
  let has_idx_reg := Wire.mk "has_idx_e"
  let has_idx_next := Wire.mk "has_idx_nx"
  let eew_reg := makeIndexedWires "eew_e" 2
  let eew_next := makeIndexedWires "eew_nx" 2

  -- State decode wires
  let not_s0 := Wire.mk "ns0"
  let not_s1 := Wire.mk "ns1"
  let not_s2 := Wire.mk "ns2"
  let state_is_idle := Wire.mk "s_idle"
  let state_is_setup := Wire.mk "s_setup"
  let state_is_elem_req := Wire.mk "s_ereq"
  let state_is_elem_wait := Wire.mk "s_ewait"
  let state_is_writeback := Wire.mk "s_wb"

  -- EEW decode
  let not_eew0 := Wire.mk "ne0"
  let not_eew1 := Wire.mk "ne1"
  let eew_is_8 := Wire.mk "eew8"
  let eew_is_16 := Wire.mk "eew16"
  let eew_is_32 := Wire.mk "eew32"

  -- EEW bytes (32-bit, for adder)
  let eew_bytes := makeIndexedWires "ewb" 32

  -- Stride value
  let stride_val := makeIndexedWires "sv" 32

  -- Adder outputs
  let stride_sum := makeIndexedWires "ssum" 32
  let idx_element := makeIndexedWires "ie" 32
  let idx_sum := makeIndexedWires "isum" 32
  let final_addr := makeIndexedWires "fa" 32
  let store_element := makeIndexedWires "se" 32

  -- Transition signals
  let idle_accept := Wire.mk "idle_acc"
  let not_is_store := Wire.mk "n_is_st"
  let idle_is_load := Wire.mk "idle_ld"
  let idle_is_store := Wire.mk "idle_st"
  let setup_accept := Wire.mk "setup_acc"
  let mask_byte := Wire.mk "m_byte"
  let elem_masked_off := Wire.mk "m_off"
  let req_active := Wire.mk "req_act"
  let req_and_active := Wire.mk "req_aa"
  let req_accepted := Wire.mk "req_ok"
  let skip_advance := Wire.mk "skip_adv"
  let resp_received := Wire.mk "resp_rx"
  let wb_accepted := Wire.mk "wb_ok"
  let elem_done := Wire.mk "e_done"
  let advance := Wire.mk "adv"
  let advance_done := Wire.mk "adv_d"
  let advance_not_done := Wire.mk "adv_nd"
  let not_elem_done := Wire.mk "n_edone"
  let elem_idx_inc := makeIndexedWires "ei_inc" 4
  let store_or_resp := Wire.mk "st_or_r"
  let load_resp_active := Wire.mk "lr_act"

  -- ════════════════════════════════════════════
  -- Gate sections (broken into separate lets to avoid nesting)
  -- ════════════════════════════════════════════

  -- State decode
  let sd_a0 := Wire.mk "sd_a0"
  let sd_a1 := Wire.mk "sd_a1"
  let sd_a2 := Wire.mk "sd_a2"
  let sd_a3 := Wire.mk "sd_a3"
  let sd_a4 := Wire.mk "sd_a4"
  let state_decode_gates : List Gate :=
    [Gate.mkNOT state_reg[0]! not_s0,
     Gate.mkNOT state_reg[1]! not_s1,
     Gate.mkNOT state_reg[2]! not_s2,
     Gate.mkAND not_s0 not_s1 sd_a0,  Gate.mkAND sd_a0 not_s2 state_is_idle,
     Gate.mkAND state_reg[0]! not_s1 sd_a1, Gate.mkAND sd_a1 not_s2 state_is_setup,
     Gate.mkAND not_s0 state_reg[1]! sd_a2, Gate.mkAND sd_a2 not_s2 state_is_elem_req,
     Gate.mkAND state_reg[0]! state_reg[1]! sd_a3, Gate.mkAND sd_a3 not_s2 state_is_elem_wait,
     Gate.mkAND not_s0 not_s1 sd_a4, Gate.mkAND sd_a4 state_reg[2]! state_is_writeback]

  -- EEW decode + bytes
  let eew_decode_gates : List Gate :=
    [Gate.mkNOT eew_reg[0]! not_eew0,
     Gate.mkNOT eew_reg[1]! not_eew1,
     Gate.mkAND not_eew0 not_eew1 eew_is_8,
     Gate.mkAND eew_reg[0]! not_eew1 eew_is_16,
     Gate.mkAND not_eew0 eew_reg[1]! eew_is_32,
     Gate.mkBUF eew_is_8 eew_bytes[0]!,
     Gate.mkBUF eew_is_16 eew_bytes[1]!,
     Gate.mkBUF eew_is_32 eew_bytes[2]!] ++
    (List.range 29).map (fun i => Gate.mkBUF zero eew_bytes[i + 3]!)

  -- Stride value MUX: unit-stride → eew_bytes, strided → stride input
  let stride_val_gates : List Gate :=
    (List.range 32).map (fun i =>
      Gate.mkMUX eew_bytes[i]! stride[i]! has_stride stride_val[i]!)

  -- Transition condition gates
  let not_is_st_reg := Wire.mk "n_ist_r"
  let transition_gates : List Gate :=
    [Gate.mkAND state_is_idle rvv2lsu_valid idle_accept,
     Gate.mkNOT rvv2lsu_is_store not_is_store,
     Gate.mkAND idle_accept not_is_store idle_is_load,
     Gate.mkAND idle_accept rvv2lsu_is_store idle_is_store,
     Gate.mkAND state_is_setup rvv2lsu_vregfile_valid setup_accept,
     Gate.mkNOT elem_masked_off req_active,
     Gate.mkAND state_is_elem_req req_active req_and_active,
     Gate.mkAND req_and_active dmem_req_ready req_accepted,
     Gate.mkAND state_is_elem_req elem_masked_off skip_advance,
     Gate.mkOR is_store_reg dmem_resp_valid store_or_resp,
     Gate.mkAND state_is_elem_wait store_or_resp resp_received,
     Gate.mkAND state_is_writeback lsu2rvv_ready wb_accepted,
     Gate.mkOR skip_advance resp_received advance,
     Gate.mkNOT elem_done not_elem_done,
     Gate.mkAND advance elem_done advance_done,
     Gate.mkAND advance not_elem_done advance_not_done,
     Gate.mkNOT is_store_reg not_is_st_reg,
     Gate.mkAND resp_received not_is_st_reg load_resp_active]

  -- Mask byte extraction: MUX16:1 on mask_buf by computed index
  -- mask index = elem_idx * eew_bytes (shift elem_idx left by eew value)
  let mbi := makeIndexedWires "mbi" 4
  let mbi_e16 := makeIndexedWires "mbi16" 4
  let mbi_e32 := makeIndexedWires "mbi32" 4
  let mbi_tmp := makeIndexedWires "mbit" 4
  let mask_index_gates : List Gate :=
    [Gate.mkBUF zero mbi_e16[0]!,
     Gate.mkBUF elem_idx_reg[0]! mbi_e16[1]!,
     Gate.mkBUF elem_idx_reg[1]! mbi_e16[2]!,
     Gate.mkBUF elem_idx_reg[2]! mbi_e16[3]!,
     Gate.mkBUF zero mbi_e32[0]!,
     Gate.mkBUF zero mbi_e32[1]!,
     Gate.mkBUF elem_idx_reg[0]! mbi_e32[2]!,
     Gate.mkBUF elem_idx_reg[1]! mbi_e32[3]!] ++
    (List.range 4).map (fun i =>
      Gate.mkMUX elem_idx_reg[i]! mbi_e16[i]! eew_is_16 mbi_tmp[i]!) ++
    (List.range 4).map (fun i =>
      Gate.mkMUX mbi_tmp[i]! mbi_e32[i]! eew_is_32 mbi[i]!)

  -- 16:1 MUX tree for mask byte
  let m_l1 := (List.range 8).map (fun i => Wire.mk s!"ml1_{i}")
  let m_l2 := (List.range 4).map (fun i => Wire.mk s!"ml2_{i}")
  let m_l3 := (List.range 2).map (fun i => Wire.mk s!"ml3_{i}")
  let not_mask_byte := Wire.mk "nmb"
  let mask_mux_gates : List Gate :=
    (List.range 8).map (fun i =>
      Gate.mkMUX mask_buf_reg[2*i]! mask_buf_reg[2*i+1]! mbi[0]! m_l1[i]!) ++
    (List.range 4).map (fun i =>
      Gate.mkMUX m_l1[2*i]! m_l1[2*i+1]! mbi[1]! m_l2[i]!) ++
    [Gate.mkMUX m_l2[0]! m_l2[1]! mbi[2]! m_l3[0]!,
     Gate.mkMUX m_l2[2]! m_l2[3]! mbi[2]! m_l3[1]!,
     Gate.mkMUX m_l3[0]! m_l3[1]! mbi[3]! mask_byte,
     Gate.mkNOT mask_byte not_mask_byte,
     Gate.mkBUF not_mask_byte elem_masked_off]

  -- Element index increment (4-bit +1)
  let ic := makeIndexedWires "ic" 4
  let inc_gates : List Gate :=
    [Gate.mkXOR elem_idx_reg[0]! one elem_idx_inc[0]!,
     Gate.mkAND elem_idx_reg[0]! one ic[0]!,
     Gate.mkXOR elem_idx_reg[1]! ic[0]! elem_idx_inc[1]!,
     Gate.mkAND elem_idx_reg[1]! ic[0]! ic[1]!,
     Gate.mkXOR elem_idx_reg[2]! ic[1]! elem_idx_inc[2]!,
     Gate.mkAND elem_idx_reg[2]! ic[1]! ic[2]!,
     Gate.mkXOR elem_idx_reg[3]! ic[2]! elem_idx_inc[3]!]

  -- Element max detection
  let mx_a01 := Wire.mk "mx01"
  let mx_a012 := Wire.mk "mx012"
  let mx_a0123 := Wire.mk "mx0123"
  let mx_ne2 := Wire.mk "mxne2"
  let mx_ne3 := Wire.mk "mxne3"
  let mx_e8 := Wire.mk "mxe8"
  let mx_e16 := Wire.mk "mxe16"
  let mx_e32 := Wire.mk "mxe32"
  let mx_a01ne2 := Wire.mk "mx01n2"
  let mx_a01ne23 := Wire.mk "mx01n23"
  let mx_a012ne3 := Wire.mk "mx012n3"
  let mx_tmp := Wire.mk "mxtmp"
  let max_detect_gates : List Gate :=
    [Gate.mkAND elem_idx_reg[0]! elem_idx_reg[1]! mx_a01,
     Gate.mkAND mx_a01 elem_idx_reg[2]! mx_a012,
     Gate.mkAND mx_a012 elem_idx_reg[3]! mx_a0123,
     Gate.mkNOT elem_idx_reg[2]! mx_ne2,
     Gate.mkNOT elem_idx_reg[3]! mx_ne3,
     Gate.mkAND mx_a01 mx_ne2 mx_a01ne2,
     Gate.mkAND mx_a01ne2 mx_ne3 mx_a01ne23,
     Gate.mkBUF mx_a01ne23 mx_e32,
     Gate.mkAND mx_a012 mx_ne3 mx_a012ne3,
     Gate.mkBUF mx_a012ne3 mx_e16,
     Gate.mkBUF mx_a0123 mx_e8,
     Gate.mkMUX mx_e8 mx_e16 eew_is_16 mx_tmp,
     Gate.mkMUX mx_tmp mx_e32 eew_is_32 elem_done]

  -- Store element extraction (32 bits from 128-bit store_buf by elem_idx)
  -- For simplicity, extract at e32 granularity (supports e32 fully;
  -- e16/e8 will use lower bits of the 32-bit extraction)
  let store_extract_gates : List Gate :=
    mux4x32 store_buf_reg elem_idx_reg[0]! elem_idx_reg[1]! "se" store_element
  -- Index element extraction (32 bits from 128-bit idx_buf by elem_idx)
  let idx_extract_gates : List Gate :=
    mux4x32 idx_buf_reg elem_idx_reg[0]! elem_idx_reg[1]! "ie" idx_element
  -- Final address MUX: has_idx ? idx_sum : addr_acc
  let addr_mux_gates : List Gate :=
    (List.range 32).map (fun i =>
      Gate.mkMUX addr_acc_reg[i]! idx_sum[i]! has_idx_reg final_addr[i]!)

  -- DMEM output gates
  let dmem_out_gates : List Gate :=
    [Gate.mkBUF req_and_active dmem_req_valid,
     Gate.mkBUF is_store_reg dmem_req_we] ++
    (List.range 32).map (fun i => Gate.mkBUF final_addr[i]! dmem_req_addr[i]!) ++
    (List.range 32).map (fun i => Gate.mkBUF store_element[i]! dmem_req_data[i]!) ++
    (List.range 2).map (fun i => Gate.mkBUF eew_reg[i]! dmem_req_size[i]!)

  -- Handshake output gates
  let handshake_gates : List Gate :=
    [Gate.mkBUF state_is_idle rvv2lsu_ready,
     Gate.mkBUF state_is_writeback lsu2rvv_valid,
     Gate.mkBUF is_store_reg lsu2rvv_last] ++
    (List.range 128).map (fun i => Gate.mkBUF load_data_reg[i]! lsu2rvv_data[i]!) ++
    (List.range 5).map (fun i => Gate.mkBUF vd_addr_reg[i]! lsu2rvv_addr[i]!)

  -- Next-state logic for FSM state register
  -- Compute candidate next-state, then MUX with hold (current state) if no transition fires
  let sn1_a := Wire.mk "sn1a"
  let sn1_c := Wire.mk "sn1c"
  let sn0_cand := Wire.mk "sn0c"
  let sn1_cand := Wire.mk "sn1c_cand"
  let sn2_cand := Wire.mk "sn2c"
  -- any_transition: any condition that causes a state change
  let any_trans := Wire.mk "any_trans"
  let at_a := Wire.mk "at_a"
  let at_b := Wire.mk "at_b"
  let state_next_gates : List Gate :=
    -- Candidate next-state values
    -- Both loads and stores go directly to ELEM_REQ (010) from IDLE,
    -- so idle_is_store no longer sets sn0 (SETUP state eliminated).
    [Gate.mkBUF req_accepted sn0_cand,
     Gate.mkOR idle_accept advance_not_done sn1_a,
     Gate.mkOR sn1_a req_accepted sn1_c,
     Gate.mkBUF sn1_c sn1_cand,
     Gate.mkBUF advance_done sn2_cand,
     -- any_transition = idle_accept | req_accepted | resp_received | wb_accepted | skip_advance
     Gate.mkOR idle_accept req_accepted at_a,
     Gate.mkOR resp_received wb_accepted at_b,
     Gate.mkOR at_a at_b (Wire.mk "at_ab"),
     Gate.mkOR (Wire.mk "at_ab") skip_advance any_trans,
     -- MUX: if any_transition, use candidate; else hold current state
     Gate.mkMUX state_reg[0]! sn0_cand any_trans state_next[0]!,
     Gate.mkMUX state_reg[1]! sn1_cand any_trans state_next[1]!,
     Gate.mkMUX state_reg[2]! sn2_cand any_trans state_next[2]!]

  -- elem_idx_next: 0 on load/setup, increment on advance, else hold
  let ei_load := Wire.mk "ei_ld"
  let elem_idx_next_gates : List Gate :=
    [Gate.mkBUF idle_accept ei_load] ++
    ((List.range 4).map (fun i =>
      let m1 := Wire.mk s!"ei_m{i}"
      [Gate.mkMUX elem_idx_reg[i]! elem_idx_inc[i]! advance m1,
       Gate.mkMUX m1 zero ei_load elem_idx_next[i]!])).flatten

  -- addr_acc_next: base_addr on accept, stride_sum on advance, else hold
  let aa_load := Wire.mk "aa_ld"
  let addr_acc_next_gates : List Gate :=
    [Gate.mkBUF idle_accept aa_load] ++
    ((List.range 32).map (fun i =>
      let m1 := Wire.mk s!"aa_m{i}"
      [Gate.mkMUX addr_acc_reg[i]! stride_sum[i]! advance m1,
       Gate.mkMUX m1 base_addr[i]! aa_load addr_acc_next[i]!])).flatten

  -- load_data_next: write resp_data into correct slot on load resp, else hold
  -- Use e32 slot decode (4 slots of 32 bits)
  let lne0 := Wire.mk "lne0"
  let lne1 := Wire.mk "lne1"
  let e32_slot := (List.range 4).map (fun i => Wire.mk s!"es{i}")
  let e32_slot_act := (List.range 4).map (fun i => Wire.mk s!"esa{i}")
  let load_slot_decode_gates : List Gate :=
    [Gate.mkNOT elem_idx_reg[0]! lne0,
     Gate.mkNOT elem_idx_reg[1]! lne1,
     Gate.mkAND lne0 lne1 e32_slot[0]!,
     Gate.mkAND elem_idx_reg[0]! lne1 e32_slot[1]!,
     Gate.mkAND lne0 elem_idx_reg[1]! e32_slot[2]!,
     Gate.mkAND elem_idx_reg[0]! elem_idx_reg[1]! e32_slot[3]!] ++
    (List.range 4).map (fun i =>
      Gate.mkAND load_resp_active e32_slot[i]! e32_slot_act[i]!)

  -- For each 32-bit chunk (0-3): if active, write from resp_data, else hold
  let load_data_next_gates : List Gate :=
    ((List.range 4).map (fun chunk =>
      (List.range 32).map (fun b =>
        Gate.mkMUX load_data_reg[chunk * 32 + b]! dmem_resp_data[b]!
          e32_slot_act[chunk]! load_data_next[chunk * 32 + b]!))).flatten

  -- store_buf_next: capture on idle_is_store (store data arrives with dispatch), else hold
  let store_buf_next_gates : List Gate :=
    (List.range 128).map (fun i =>
      Gate.mkMUX store_buf_reg[i]! rvv2lsu_vregfile_data[i]! idle_is_store store_buf_next[i]!)

  -- idx_buf_next: capture on idle_accept when idx_valid, else hold
  let idx_capture := Wire.mk "idx_cap"
  let idx_buf_next_gates : List Gate :=
    [Gate.mkAND idle_accept rvv2lsu_idx_valid idx_capture] ++
    (List.range 128).map (fun i =>
      Gate.mkMUX idx_buf_reg[i]! rvv2lsu_idx_data[i]! idx_capture idx_buf_next[i]!)

  -- mask_buf_next: capture on idle_accept, else hold
  let mask_buf_next_gates : List Gate :=
    (List.range 16).map (fun i =>
      Gate.mkMUX mask_buf_reg[i]! rvv2lsu_mask[i]! idle_accept mask_buf_next[i]!)

  -- vd_addr_next: capture on idle_accept, else hold
  let vd_addr_next_gates : List Gate :=
    (List.range 5).map (fun i =>
      Gate.mkMUX vd_addr_reg[i]! rvv2lsu_vd_addr[i]! idle_accept vd_addr_next[i]!)

  -- Control and EEW next
  let ctrl_next_gates : List Gate :=
    [Gate.mkMUX is_store_reg rvv2lsu_is_store idle_accept is_store_next,
     Gate.mkMUX has_idx_reg rvv2lsu_idx_valid idle_accept has_idx_next] ++
    (List.range 2).map (fun i =>
      Gate.mkMUX eew_reg[i]! eew[i]! idle_accept eew_next[i]!)

  -- ════════════════════════════════════════════
  -- DFF instances
  -- ════════════════════════════════════════════
  let mkDFFs (pfx : String) (d q : List Wire) : List CircuitInstance :=
    (List.range d.length).map (fun i => {
      moduleName := "DFlipFlop", instName := s!"{pfx}_{i}",
      portMap := [("d", d[i]!), ("q", q[i]!), ("clock", clock), ("reset", reset)] })

  let mkDFF1 (name : String) (d q : Wire) : CircuitInstance := {
    moduleName := "DFlipFlop", instName := name,
    portMap := [("d", d), ("q", q), ("clock", clock), ("reset", reset)] }

  let all_dffs : List CircuitInstance :=
    mkDFFs "u_st" state_next state_reg ++
    mkDFFs "u_ei" elem_idx_next elem_idx_reg ++
    mkDFFs "u_aa" addr_acc_next addr_acc_reg ++
    mkDFFs "u_ld" load_data_next load_data_reg ++
    mkDFFs "u_sb" store_buf_next store_buf_reg ++
    mkDFFs "u_ib" idx_buf_next idx_buf_reg ++
    mkDFFs "u_mb" mask_buf_next mask_buf_reg ++
    mkDFFs "u_vd" vd_addr_next vd_addr_reg ++
    [mkDFF1 "u_ist" is_store_next is_store_reg,
     mkDFF1 "u_hix" has_idx_next has_idx_reg] ++
    mkDFFs "u_ew" eew_next eew_reg
  -- Adder instances
  let stride_adder : CircuitInstance := {
    moduleName := "KoggeStoneAdder32", instName := "u_stride_adder",
    portMap :=
      (List.range 32).map (fun i => (s!"a[{i}]", addr_acc_reg[i]!)) ++
      (List.range 32).map (fun i => (s!"b[{i}]", stride_val[i]!)) ++
      [("cin", zero)] ++
      (List.range 32).map (fun i => (s!"sum[{i}]", stride_sum[i]!)) }

  let idx_adder : CircuitInstance := {
    moduleName := "KoggeStoneAdder32", instName := "u_idx_adder",
    portMap :=
      (List.range 32).map (fun i => (s!"a[{i}]", base_addr[i]!)) ++
      (List.range 32).map (fun i => (s!"b[{i}]", idx_element[i]!)) ++
      [("cin", zero)] ++
      (List.range 32).map (fun i => (s!"sum[{i}]", idx_sum[i]!)) }

  -- ════════════════════════════════════════════
  -- Circuit
  -- ════════════════════════════════════════════
  { name := "VecLsu"
    inputs := [clock, reset, zero, one] ++
              base_addr ++ stride ++ [has_stride] ++
              [rvv2lsu_valid, rvv2lsu_idx_valid] ++ rvv2lsu_idx_data ++
              [rvv2lsu_vregfile_valid] ++ rvv2lsu_vregfile_data ++
              [rvv2lsu_mask_valid] ++ rvv2lsu_mask ++
              rvv2lsu_vd_addr ++ [rvv2lsu_is_store] ++
              [lsu2rvv_ready] ++
              [dmem_req_ready, dmem_resp_valid] ++ dmem_resp_data ++
              eew
    outputs := [rvv2lsu_ready] ++
               [lsu2rvv_valid] ++ lsu2rvv_data ++ lsu2rvv_addr ++ [lsu2rvv_last] ++
               [dmem_req_valid, dmem_req_we] ++ dmem_req_addr ++ dmem_req_data ++ dmem_req_size
    gates :=
      state_decode_gates ++ eew_decode_gates ++ stride_val_gates ++
      transition_gates ++ mask_index_gates ++ mask_mux_gates ++
      inc_gates ++ max_detect_gates ++
      store_extract_gates ++ idx_extract_gates ++
      addr_mux_gates ++ dmem_out_gates ++ handshake_gates ++
      state_next_gates ++ elem_idx_next_gates ++ addr_acc_next_gates ++
      load_slot_decode_gates ++ load_data_next_gates ++
      store_buf_next_gates ++ idx_buf_next_gates ++
      mask_buf_next_gates ++ vd_addr_next_gates ++ ctrl_next_gates
    instances := [stride_adder, idx_adder] ++ all_dffs }

end Shoumei.RISCV
