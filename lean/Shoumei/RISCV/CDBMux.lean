import Shoumei.DSL

/-!
# CDB Priority Drain Mux (W=2 Dual CDB)

Dual-channel CDB priority mux for 2-wide superscalar pipeline.
- CDB 0: dmem (highest) > lsu > ib_0 (lowest)
- CDB 1: fp (highest) > muldiv > ib_1 (lowest)

Built as a standalone module with `keepHierarchy := true` so that Yosys
preserves the internal buffer tree topology.
-/

namespace Shoumei.RISCV

/-- Build the dual-CDB priority drain mux circuit.

  `enableF`: when false, is_fp outputs are tied low and fp_deq/dmem_is_fp are unused.
-/
def mkCDBMux (enableF : Bool) : Circuit :=
  let mk := Wire.mk
  let mkIdx (pfx : String) (n : Nat) := (List.range n).map (fun i => mk s!"{pfx}_{i}")

  -- Shared inputs
  let ib_valid_0  := mk "ib_valid_0";  let ib_deq_0  := mkIdx "ib_deq_0"  72
  let ib_valid_1  := mk "ib_valid_1";  let ib_deq_1  := mkIdx "ib_deq_1"  72
  let fp_valid    := mk "fp_valid";     let fp_deq    := mkIdx "fp_deq"     39
  let muldiv_valid := mk "muldiv_valid"; let muldiv_deq := mkIdx "muldiv_deq" 39
  let lsu_valid   := mk "lsu_valid";   let lsu_deq   := mkIdx "lsu_deq"    39
  let dmem_valid  := mk "dmem_valid";  let dmem_fmt  := mkIdx "dmem_fmt"   32
  let dmem_tag    := mkIdx "dmem_tag" 6; let dmem_is_fp := mk "dmem_is_fp"
  let zero        := mk "zero"

  -- CDB 0 outputs
  let pre_valid_0  := mk "pre_valid_0";  let pre_tag_0  := mkIdx "pre_tag_0"  6
  let pre_data_0   := mkIdx "pre_data_0" 32; let pre_is_fp_0 := mk "pre_is_fp_0"
  let redirect_0   := mkIdx "redirect_0" 32; let pre_mispred_0 := mk "pre_mispredicted_0"
  let drain_lsu    := mk "drain_lsu";   let drain_ib_0 := mk "drain_ib_0"

  -- CDB 1 outputs
  let pre_valid_1  := mk "pre_valid_1";  let pre_tag_1  := mkIdx "pre_tag_1"  6
  let pre_data_1   := mkIdx "pre_data_1" 32; let pre_is_fp_1 := mk "pre_is_fp_1"
  let redirect_1   := mkIdx "redirect_1" 32; let pre_mispred_1 := mk "pre_mispredicted_1"
  let drain_fp     := mk "drain_fp";  let drain_muldiv := mk "drain_muldiv"
  let drain_ib_1   := mk "drain_ib_1"

  -- CDB 0: dmem > lsu > ib_0
  let dmem_wins := mk "dmem_wins";  let not_dmem := mk "not_dmem"
  let lsu_wins  := mk "lsu_wins";   let not_lsu  := mk "not_lsu"
  let ib0_wins_tmp := mk "ib0_wins_tmp"; let ib0_wins := mk "ib0_wins"
  let arb0_gates := [
    Gate.mkBUF dmem_valid dmem_wins,   Gate.mkNOT dmem_valid not_dmem,
    Gate.mkAND lsu_valid not_dmem lsu_wins,  Gate.mkNOT lsu_wins not_lsu,
    Gate.mkAND ib_valid_0 not_dmem ib0_wins_tmp,
    Gate.mkAND ib0_wins_tmp not_lsu ib0_wins,
    Gate.mkBUF lsu_wins drain_lsu,  Gate.mkBUF ib0_wins drain_ib_0
  ]
  let valid0_gates := [
    Gate.mkOR dmem_wins lsu_wins (mk "v0_tmp"),
    Gate.mkOR (mk "v0_tmp") ib0_wins pre_valid_0
  ]
  let tag0_gates := (List.range 6).map (fun i =>
    let m1 := mk s!"t0_m1_{i}"
    [Gate.mkMUX ib_deq_0[i]! lsu_deq[i]! lsu_wins m1,
     Gate.mkMUX m1 dmem_tag[i]! dmem_wins pre_tag_0[i]!]) |>.flatten
  let data0_gates := (List.range 32).map (fun i =>
    let m1 := mk s!"d0_m1_{i}"
    [Gate.mkMUX ib_deq_0[6+i]! lsu_deq[6+i]! lsu_wins m1,
     Gate.mkMUX m1 dmem_fmt[i]! dmem_wins pre_data_0[i]!]) |>.flatten
  let is_fp0_gates :=
    if enableF then
      let m1 := mk "f0_m1"
      [Gate.mkMUX ib_deq_0[38]! lsu_deq[38]! lsu_wins m1,
       Gate.mkMUX m1 dmem_is_fp dmem_wins pre_is_fp_0]
    else [Gate.mkBUF zero pre_is_fp_0]
  let redir0_gates :=
    (List.range 32).map (fun i => Gate.mkAND ib_deq_0[39+i]! ib0_wins redirect_0[i]!) ++
    [Gate.mkAND ib_deq_0[71]! ib0_wins pre_mispred_0]

  -- CDB 1: fp > muldiv > ib_1
  let fp_wins    := mk "fp_wins";  let not_fp     := mk "not_fp"
  let muldiv_wins := mk "muldiv_wins"; let not_muldiv := mk "not_muldiv"
  let ib1_wins_tmp := mk "ib1_wins_tmp"; let ib1_wins := mk "ib1_wins"
  let arb1_gates := [
    Gate.mkBUF fp_valid fp_wins,      Gate.mkNOT fp_valid not_fp,
    Gate.mkAND muldiv_valid not_fp muldiv_wins, Gate.mkNOT muldiv_wins not_muldiv,
    Gate.mkAND ib_valid_1 not_fp ib1_wins_tmp,
    Gate.mkAND ib1_wins_tmp not_muldiv ib1_wins,
    Gate.mkBUF fp_wins drain_fp,  Gate.mkBUF muldiv_wins drain_muldiv,
    Gate.mkBUF ib1_wins drain_ib_1
  ]
  let valid1_gates := [
    Gate.mkOR fp_wins muldiv_wins (mk "v1_tmp"),
    Gate.mkOR (mk "v1_tmp") ib1_wins pre_valid_1
  ]
  let tag1_gates := (List.range 6).map (fun i =>
    let m1 := mk s!"t1_m1_{i}"
    [Gate.mkMUX ib_deq_1[i]! muldiv_deq[i]! muldiv_wins m1,
     Gate.mkMUX m1 fp_deq[i]! fp_wins pre_tag_1[i]!]) |>.flatten
  let data1_gates := (List.range 32).map (fun i =>
    let m1 := mk s!"d1_m1_{i}"
    [Gate.mkMUX ib_deq_1[6+i]! muldiv_deq[6+i]! muldiv_wins m1,
     Gate.mkMUX m1 fp_deq[6+i]! fp_wins pre_data_1[i]!]) |>.flatten
  let is_fp1_gates :=
    if enableF then
      let m1 := mk "f1_m1"
      [Gate.mkMUX ib_deq_1[38]! muldiv_deq[38]! muldiv_wins m1,
       Gate.mkMUX m1 fp_deq[38]! fp_wins pre_is_fp_1]
    else [Gate.mkBUF zero pre_is_fp_1]
  let redir1_gates :=
    (List.range 32).map (fun i => Gate.mkAND ib_deq_1[39+i]! ib1_wins redirect_1[i]!) ++
    [Gate.mkAND ib_deq_1[71]! ib1_wins pre_mispred_1]

  { name := if enableF then "CDBMux_F_W2" else "CDBMux_W2"
    inputs := [ib_valid_0, ib_valid_1, fp_valid, muldiv_valid, lsu_valid, dmem_valid] ++
              ib_deq_0 ++ ib_deq_1 ++ fp_deq ++ muldiv_deq ++ lsu_deq ++
              dmem_fmt ++ dmem_tag ++ [dmem_is_fp, zero]
    outputs := [pre_valid_0, pre_valid_1] ++ pre_tag_0 ++ pre_tag_1 ++
               pre_data_0 ++ pre_data_1 ++ [pre_is_fp_0, pre_is_fp_1] ++
               [drain_lsu, drain_muldiv, drain_fp, drain_ib_0, drain_ib_1] ++
               redirect_0 ++ redirect_1 ++ [pre_mispred_0, pre_mispred_1]
    gates := arb0_gates ++ valid0_gates ++ tag0_gates ++ data0_gates ++
             is_fp0_gates ++ redir0_gates ++
             arb1_gates ++ valid1_gates ++ tag1_gates ++ data1_gates ++
             is_fp1_gates ++ redir1_gates
    instances := [] }

/-- CDB Mux without F extension (dual CDB) -/
def cdbMuxW2 : Circuit := mkCDBMux false

/-- CDB Mux with F extension (dual CDB) -/
def cdbMuxFW2 : Circuit := mkCDBMux true

end Shoumei.RISCV
