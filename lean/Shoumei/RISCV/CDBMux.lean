import Shoumei.DSL

/-!
# CDB Priority Drain Mux

5-input priority mux for the Common Data Bus (CDB). Selects between
DMEM response (highest), LSU FIFO, MulDiv FIFO, FP FIFO, and INT/Branch
FIFO (lowest). Outputs tag, data, valid, is_fp, redirect info, and
per-FIFO drain signals.

Built as a standalone module with `keepHierarchy := true` so that Yosys
preserves the internal buffer tree topology.
-/

namespace Shoumei.RISCV

/-- Build the CDB priority drain mux circuit.

  Inputs (named with prefix to avoid collision):
  - ib_valid, fp_valid, muldiv_valid, lsu_valid, dmem_valid  (1-bit each)
  - ib_deq_0..ib_deq_71   (72 bits: [5:0]=tag, [37:6]=data, [38]=is_fp, [70:39]=redirect, [71]=mispred)
  - fp_deq_0..fp_deq_38   (39 bits)
  - muldiv_deq_0..muldiv_deq_38 (39 bits)
  - lsu_deq_0..lsu_deq_38  (39 bits)
  - dmem_fmt_0..dmem_fmt_31 (32 bits formatted load data)
  - dmem_tag_0..dmem_tag_5  (6 bits registered load tag)
  - dmem_is_fp              (1 bit)
  - csr_inject              (1 bit)
  - csr_tag_0..csr_tag_5   (6 bits)
  - csr_data_0..csr_data_31 (32 bits)

  Outputs:
  - pre_valid               (1 bit)
  - pre_tag_0..pre_tag_5   (6 bits)
  - pre_data_0..pre_data_31 (32 bits)
  - pre_is_fp               (1 bit)
  - drain_lsu, drain_muldiv, drain_fp, drain_ib  (1 bit each, FIFO deq_ready)
  - redirect_0..redirect_31 (32 bits)
  - pre_mispredicted        (1 bit)

  `enableF`: when false, is_fp output is tied low and fp_deq/dmem_is_fp are unused.
-/
def mkCDBMux (enableF : Bool) (width : Nat := 2) : Circuit :=
  let mk := Wire.mk
  let mkIdx (pfx : String) (n : Nat) := (List.range n).map (fun i => mk s!"{pfx}_{i}")
  if width == 1 then

  -- Inputs
  let ib_valid := mk "ib_valid"
  let fp_valid := mk "fp_valid"
  let muldiv_valid := mk "muldiv_valid"
  let lsu_valid := mk "lsu_valid"
  let dmem_valid := mk "dmem_valid"

  let ib_deq := mkIdx "ib_deq" 72
  let fp_deq := mkIdx "fp_deq" 39
  let muldiv_deq := mkIdx "muldiv_deq" 39
  let lsu_deq := mkIdx "lsu_deq" 39
  let dmem_fmt := mkIdx "dmem_fmt" 32
  let dmem_tag := mkIdx "dmem_tag" 6
  let dmem_is_fp := mk "dmem_is_fp"
  let csr_inject := mk "csr_inject"
  let csr_tag := mkIdx "csr_tag" 6
  let csr_data := mkIdx "csr_data" 32

  -- Outputs
  let pre_valid := mk "pre_valid"
  let pre_tag := mkIdx "pre_tag" 6
  let pre_data := mkIdx "pre_data" 32
  let pre_is_fp := mk "pre_is_fp"
  let drain_lsu := mk "drain_lsu"
  let drain_muldiv := mk "drain_muldiv"
  let drain_fp := mk "drain_fp"
  let drain_ib := mk "drain_ib"
  let redirect := mkIdx "redirect" 32
  let pre_mispred := mk "pre_mispredicted"

  let zero := mk "zero"

  -- Priority arbiter
  let dmem_wins := mk "dmem_wins"
  let not_dmem := mk "not_dmem"
  let lsu_wins := mk "lsu_wins"
  let not_lsu := mk "not_lsu"
  let muldiv_wins_tmp := mk "muldiv_wins_tmp"
  let muldiv_wins := mk "muldiv_wins"
  let not_muldiv := mk "not_muldiv"
  let fp_wins_tmp := mk "fp_wins_tmp"
  let fp_wins_tmp2 := mk "fp_wins_tmp2"
  let fp_wins := mk "fp_wins"
  let not_fp := mk "not_fp"
  let ib_wins_tmp := mk "ib_wins_tmp"
  let ib_wins_tmp2 := mk "ib_wins_tmp2"
  let ib_wins_tmp3 := mk "ib_wins_tmp3"
  let ib_wins := mk "ib_wins"

  let arb_gates := [
    Gate.mkBUF dmem_valid dmem_wins,
    Gate.mkNOT dmem_valid not_dmem,
    Gate.mkAND lsu_valid not_dmem lsu_wins,
    Gate.mkNOT lsu_wins not_lsu,
    Gate.mkAND muldiv_valid not_dmem muldiv_wins_tmp,
    Gate.mkAND muldiv_wins_tmp not_lsu muldiv_wins,
    Gate.mkNOT muldiv_wins not_muldiv,
    Gate.mkAND fp_valid not_dmem fp_wins_tmp,
    Gate.mkAND fp_wins_tmp not_lsu fp_wins_tmp2,
    Gate.mkAND fp_wins_tmp2 not_muldiv fp_wins,
    Gate.mkNOT fp_wins not_fp,
    Gate.mkAND ib_valid not_dmem ib_wins_tmp,
    Gate.mkAND ib_wins_tmp not_lsu ib_wins_tmp2,
    Gate.mkAND ib_wins_tmp2 not_muldiv ib_wins_tmp3,
    Gate.mkAND ib_wins_tmp3 not_fp ib_wins,
    -- Drain signals
    Gate.mkBUF lsu_wins drain_lsu,
    Gate.mkBUF muldiv_wins drain_muldiv,
    Gate.mkBUF fp_wins drain_fp,
    Gate.mkBUF ib_wins drain_ib
  ]

  -- Valid: any source won, OR'd with CSR inject
  let v_tmp := mk "v_tmp"
  let v_tmp2 := mk "v_tmp2"
  let v_tmp3 := mk "v_tmp3"
  let v_arb := mk "v_arb"
  let valid_gates := [
    Gate.mkOR dmem_wins lsu_wins v_tmp,
    Gate.mkOR v_tmp muldiv_wins v_tmp2,
    Gate.mkOR v_tmp2 fp_wins v_tmp3,
    Gate.mkOR v_tmp3 ib_wins v_arb,
    Gate.mkOR v_arb csr_inject pre_valid
  ]

  -- Tag MUX (6 bits): priority cascade + CSR override
  let tag_mux_gates := (List.range 6).map (fun i =>
    let m1 := mk s!"tag_m1_{i}"
    let m2 := mk s!"tag_m2_{i}"
    let m3 := mk s!"tag_m3_{i}"
    let arb := mk s!"tag_arb_{i}"
    [Gate.mkMUX ib_deq[i]! fp_deq[i]! fp_wins m1,
     Gate.mkMUX m1 muldiv_deq[i]! muldiv_wins m2,
     Gate.mkMUX m2 lsu_deq[i]! lsu_wins m3,
     Gate.mkMUX m3 dmem_tag[i]! dmem_wins arb,
     Gate.mkMUX arb csr_tag[i]! csr_inject pre_tag[i]!]) |>.flatten

  -- Data MUX (32 bits): buffered select signals to reduce fanout
  let fp_wins_d := mk "fp_wins_d"
  let muldiv_wins_d := mk "muldiv_wins_d"
  let lsu_wins_d := mk "lsu_wins_d"
  let dmem_wins_d := mk "dmem_wins_d"
  let csr_inject_d := mk "csr_inject_d"
  let data_sel_bufs := [
    Gate.mkBUF fp_wins fp_wins_d,
    Gate.mkBUF muldiv_wins muldiv_wins_d,
    Gate.mkBUF lsu_wins lsu_wins_d,
    Gate.mkBUF dmem_wins dmem_wins_d,
    Gate.mkBUF csr_inject csr_inject_d
  ]

  let data_mux_gates := (List.range 32).map (fun i =>
    let m1 := mk s!"data_m1_{i}"
    let m2 := mk s!"data_m2_{i}"
    let m3 := mk s!"data_m3_{i}"
    let arb := mk s!"data_arb_{i}"
    [Gate.mkMUX ib_deq[6+i]! fp_deq[6+i]! fp_wins_d m1,
     Gate.mkMUX m1 muldiv_deq[6+i]! muldiv_wins_d m2,
     Gate.mkMUX m2 lsu_deq[6+i]! lsu_wins_d m3,
     Gate.mkMUX m3 dmem_fmt[i]! dmem_wins_d arb,
     Gate.mkMUX arb csr_data[i]! csr_inject_d pre_data[i]!]) |>.flatten

  -- is_fp MUX (1 bit)
  let is_fp_gates :=
    if enableF then
      let fp_mux1 := mk "fp_mux1"
      let fp_mux2 := mk "fp_mux2"
      let fp_mux3 := mk "fp_mux3"
      let fp_from_fifo := mk "fp_from_fifo"
      [Gate.mkMUX ib_deq[38]! fp_deq[38]! fp_wins fp_mux1,
       Gate.mkMUX fp_mux1 muldiv_deq[38]! muldiv_wins fp_mux2,
       Gate.mkMUX fp_mux2 lsu_deq[38]! lsu_wins fp_mux3,
       Gate.mkMUX fp_mux3 dmem_is_fp dmem_wins fp_from_fifo,
       Gate.mkBUF fp_from_fifo pre_is_fp]
    else
      [Gate.mkBUF zero pre_is_fp]

  -- Redirect extract: AND ib_deq[39+i..70] with ib_wins
  let redirect_gates :=
    (List.range 32).map (fun i =>
      Gate.mkAND ib_deq[39+i]! ib_wins redirect[i]!) ++
    [Gate.mkAND ib_deq[71]! ib_wins pre_mispred]

  let allGates := arb_gates ++ valid_gates ++ tag_mux_gates ++
    data_sel_bufs ++ data_mux_gates ++ is_fp_gates ++ redirect_gates

  let inputs :=
    [ib_valid, fp_valid, muldiv_valid, lsu_valid, dmem_valid] ++
    ib_deq ++ fp_deq ++ muldiv_deq ++ lsu_deq ++
    dmem_fmt ++ dmem_tag ++ [dmem_is_fp] ++
    [csr_inject] ++ csr_tag ++ csr_data ++
    [zero]

  let outputs :=
    [pre_valid] ++ pre_tag ++ pre_data ++ [pre_is_fp] ++
    [drain_lsu, drain_muldiv, drain_fp, drain_ib] ++
    redirect ++ [pre_mispred]

  -- Explicit signal groups for input/output buses (auto-detect only covers internals)
  let portGroups : List SignalGroup := [
    { name := "ib_deq", width := 72, wires := ib_deq },
    { name := "fp_deq", width := 39, wires := fp_deq },
    { name := "muldiv_deq", width := 39, wires := muldiv_deq },
    { name := "lsu_deq", width := 39, wires := lsu_deq },
    { name := "dmem_fmt", width := 32, wires := dmem_fmt },
    { name := "dmem_tag", width := 6, wires := dmem_tag },
    { name := "csr_tag", width := 6, wires := csr_tag },
    { name := "csr_data", width := 32, wires := csr_data },
    { name := "pre_tag", width := 6, wires := pre_tag },
    { name := "pre_data", width := 32, wires := pre_data },
    { name := "redirect", width := 32, wires := redirect }
  ]

  { name := if enableF then "CDBMux_F" else "CDBMux"
    inputs := inputs
    outputs := outputs
    gates := allGates
    instances := []
    signalGroups := portGroups
    keepHierarchy := false }
  else
  -- === W=2: Dual-CDB priority drain mux (from CDBMux_W2.lean) ===
  -- CDB 0 priority: dmem > lsu > ib_0
  -- CDB 1 priority: fp > muldiv > ib_1
  let mk2 := Wire.mk
  let mkIdx2 (pfx : String) (n : Nat) := (List.range n).map (fun i => mk2 s!"{pfx}_{i}")

  let ib_valid_0  := mk2 "ib_valid_0";  let ib_deq_0  := mkIdx2 "ib_deq_0"  72
  let ib_valid_1  := mk2 "ib_valid_1";  let ib_deq_1  := mkIdx2 "ib_deq_1"  72
  let fp_valid    := mk2 "fp_valid";     let fp_deq    := mkIdx2 "fp_deq"     39
  let muldiv_valid := mk2 "muldiv_valid"; let muldiv_deq := mkIdx2 "muldiv_deq" 39
  let lsu_valid   := mk2 "lsu_valid";   let lsu_deq   := mkIdx2 "lsu_deq"    39
  let dmem_valid  := mk2 "dmem_valid";  let dmem_fmt  := mkIdx2 "dmem_fmt"   32
  let dmem_tag    := mkIdx2 "dmem_tag" 6; let dmem_is_fp := mk2 "dmem_is_fp"
  let zero        := mk2 "zero"

  let pre_valid_0  := mk2 "pre_valid_0";  let pre_tag_0  := mkIdx2 "pre_tag_0"  6
  let pre_data_0   := mkIdx2 "pre_data_0" 32; let pre_is_fp_0 := mk2 "pre_is_fp_0"
  let redirect_0   := mkIdx2 "redirect_0" 32; let pre_mispred_0 := mk2 "pre_mispredicted_0"
  let drain_lsu    := mk2 "drain_lsu";   let drain_ib_0 := mk2 "drain_ib_0"

  let pre_valid_1  := mk2 "pre_valid_1";  let pre_tag_1  := mkIdx2 "pre_tag_1"  6
  let pre_data_1   := mkIdx2 "pre_data_1" 32; let pre_is_fp_1 := mk2 "pre_is_fp_1"
  let redirect_1   := mkIdx2 "redirect_1" 32; let pre_mispred_1 := mk2 "pre_mispredicted_1"
  let drain_fp     := mk2 "drain_fp";  let drain_muldiv := mk2 "drain_muldiv"
  let drain_ib_1   := mk2 "drain_ib_1"

  -- CDB 0: dmem > lsu > ib_0
  let dmem_wins := mk2 "dmem_wins";  let not_dmem := mk2 "not_dmem"
  let lsu_wins  := mk2 "lsu_wins";   let not_lsu  := mk2 "not_lsu"
  let ib0_wins_tmp := mk2 "ib0_wins_tmp"; let ib0_wins := mk2 "ib0_wins"
  let arb0_gates := [
    Gate.mkBUF dmem_valid dmem_wins,   Gate.mkNOT dmem_valid not_dmem,
    Gate.mkAND lsu_valid not_dmem lsu_wins,  Gate.mkNOT lsu_wins not_lsu,
    Gate.mkAND ib_valid_0 not_dmem ib0_wins_tmp,
    Gate.mkAND ib0_wins_tmp not_lsu ib0_wins,
    Gate.mkBUF lsu_wins drain_lsu,  Gate.mkBUF ib0_wins drain_ib_0
  ]
  let valid0_gates := [
    Gate.mkOR dmem_wins lsu_wins (mk2 "v0_tmp"),
    Gate.mkOR (mk2 "v0_tmp") ib0_wins pre_valid_0
  ]
  let tag0_gates := (List.range 6).map (fun i =>
    let m1 := mk2 s!"t0_m1_{i}"
    [Gate.mkMUX ib_deq_0[i]! lsu_deq[i]! lsu_wins m1,
     Gate.mkMUX m1 dmem_tag[i]! dmem_wins pre_tag_0[i]!]) |>.flatten
  let data0_gates := (List.range 32).map (fun i =>
    let m1 := mk2 s!"d0_m1_{i}"
    [Gate.mkMUX ib_deq_0[6+i]! lsu_deq[6+i]! lsu_wins m1,
     Gate.mkMUX m1 dmem_fmt[i]! dmem_wins pre_data_0[i]!]) |>.flatten
  let is_fp0_gates :=
    if enableF then
      let m1 := mk2 "f0_m1"
      [Gate.mkMUX ib_deq_0[38]! lsu_deq[38]! lsu_wins m1,
       Gate.mkMUX m1 dmem_is_fp dmem_wins pre_is_fp_0]
    else [Gate.mkBUF zero pre_is_fp_0]
  let redir0_gates :=
    (List.range 32).map (fun i => Gate.mkAND ib_deq_0[39+i]! ib0_wins redirect_0[i]!) ++
    [Gate.mkAND ib_deq_0[71]! ib0_wins pre_mispred_0]

  -- CDB 1: fp > muldiv > ib_1
  let fp_wins    := mk2 "fp_wins";  let not_fp     := mk2 "not_fp"
  let muldiv_wins := mk2 "muldiv_wins"; let not_muldiv := mk2 "not_muldiv"
  let ib1_wins_tmp := mk2 "ib1_wins_tmp"; let ib1_wins := mk2 "ib1_wins"
  let arb1_gates := [
    Gate.mkBUF fp_valid fp_wins,      Gate.mkNOT fp_valid not_fp,
    Gate.mkAND muldiv_valid not_fp muldiv_wins, Gate.mkNOT muldiv_wins not_muldiv,
    Gate.mkAND ib_valid_1 not_fp ib1_wins_tmp,
    Gate.mkAND ib1_wins_tmp not_muldiv ib1_wins,
    Gate.mkBUF fp_wins drain_fp,  Gate.mkBUF muldiv_wins drain_muldiv,
    Gate.mkBUF ib1_wins drain_ib_1
  ]
  let valid1_gates := [
    Gate.mkOR fp_wins muldiv_wins (mk2 "v1_tmp"),
    Gate.mkOR (mk2 "v1_tmp") ib1_wins pre_valid_1
  ]
  let tag1_gates := (List.range 6).map (fun i =>
    let m1 := mk2 s!"t1_m1_{i}"
    [Gate.mkMUX ib_deq_1[i]! muldiv_deq[i]! muldiv_wins m1,
     Gate.mkMUX m1 fp_deq[i]! fp_wins pre_tag_1[i]!]) |>.flatten
  let data1_gates := (List.range 32).map (fun i =>
    let m1 := mk2 s!"d1_m1_{i}"
    [Gate.mkMUX ib_deq_1[6+i]! muldiv_deq[6+i]! muldiv_wins m1,
     Gate.mkMUX m1 fp_deq[6+i]! fp_wins pre_data_1[i]!]) |>.flatten
  let is_fp1_gates :=
    if enableF then
      let m1 := mk2 "f1_m1"
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

/-- CDB Mux without F extension (W=1) -/
def cdbMux : Circuit := mkCDBMux false 1

/-- CDB Mux with F extension (W=1) -/
def cdbMuxF : Circuit := mkCDBMux true 1

/-- CDB Mux without F extension (W=2, dual CDB) -/
def cdbMuxW2 : Circuit := mkCDBMux false 2

/-- CDB Mux with F extension (W=2, dual CDB) -/
def cdbMuxFW2 : Circuit := mkCDBMux true 2

end Shoumei.RISCV

