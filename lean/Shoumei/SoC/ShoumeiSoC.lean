/-
SoC/ShoumeiSoC.lean - Top-Level Shoumei System-on-Chip (SoC)

Integrates:
- Shoumei RV64 OoO Dual-Issue CPU Core
- Memory Hierarchy (L1I, L1D, L2 Caches)
- 2-stage Asynchronous-Assert Synchronous-Deassert (AASD) Reset Synchronizer
- TileLink TL-UH 1-to-8 Interconnect Crossbar
- ACLINT (MTIMER + MSWI + SSWI)
- AIA APLIC (Direct Delivery Mode)
- 8-N-1 UART (115,200 baud, TX/RX buffers)
- 8-bit GPIO (Direction, Output, Interrupt)
- On-Chip Bootloader ROM
- On-Chip Scratchpad SRAM
-/

import Shoumei.DSL
import Shoumei.RISCV.Config
import Shoumei.RISCV.Memory.Cache.CachedCPU
import Shoumei.Circuits.Sequential.ResetSync
import Shoumei.Interconnect.TileLink.TLXbar
import Shoumei.Peripherals.ACLINT
import Shoumei.Peripherals.APLIC
import Shoumei.Peripherals.UART
import Shoumei.Peripherals.GPIO
import Shoumei.Peripherals.BootROM
import Shoumei.Peripherals.SRAM

namespace Shoumei.SoC

open Shoumei
open Shoumei.RISCV
open Shoumei.RISCV.Memory.Cache
open Shoumei.Circuits.Sequential
open Shoumei.Interconnect.TileLink
open Shoumei.Peripherals

/-- Build top-level Shoumei SoC circuit. -/
def mkShoumeiSoC (config : CPUConfig) : Circuit :=
  let clock := Wire.mk "clock"
  let reset_n := Wire.mk "reset_n"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  -- Synchronized active-high reset
  let sync_reset := Wire.mk "sync_reset"
  let reset_async := Wire.mk "reset_async"
  let not_rst_n := Gate.mkNOT reset_n reset_async

  let rst_sync_inst : CircuitInstance := {
    moduleName := "ResetSync"
    instName := "u_rst_sync"
    portMap := [("clock", clock), ("reset", reset_async), ("one", one), ("sync_reset", sync_reset)]
  }

  -- Core Interrupt Wires
  let mtip_in := Wire.mk "soc_mtip"
  let msip_in := Wire.mk "soc_msip"
  let meip_in := Wire.mk "soc_meip"

  -- External UART Pins
  let uart_rx := Wire.mk "uart_rx"
  let uart_tx := Wire.mk "uart_tx"
  let uart_irq := Wire.mk "uart_irq"

  -- External GPIO Pins
  let gpio_i := (List.range 8).map fun i => Wire.mk s!"gpio_i_{i}"
  let gpio_o := (List.range 8).map fun i => Wire.mk s!"gpio_o_{i}"
  let gpio_oen := (List.range 8).map fun i => Wire.mk s!"gpio_oen_{i}"
  let gpio_irq := Wire.mk "gpio_irq"

  -- Main Memory Interface (External DRAM / backing store): one cache line per
  -- transaction, so the width follows the configured line size.
  let lineBits := config.cacheGeom.lineBytes * 8
  let mem_resp_valid := Wire.mk "mem_resp_valid"
  let mem_resp_data := (List.range lineBits).map fun i => Wire.mk s!"mem_resp_data_{i}"
  let mem_req_valid := Wire.mk "mem_req_valid"
  let mem_req_addr := (List.range 32).map fun i => Wire.mk s!"mem_req_addr_{i}"
  let mem_req_we := Wire.mk "mem_req_we"
  let mem_req_data := (List.range lineBits).map fun i => Wire.mk s!"mem_req_data_{i}"
  let rob_empty := Wire.mk "rob_empty"

  -- Internal CPU store snoop (used to feed TileLink master Channel A)
  let store_snoop_valid := Wire.mk "cpu_snoop_valid"
  let store_snoop_addr := (List.range 32).map fun i => Wire.mk s!"cpu_snoop_addr_{i}"
  let store_snoop_data := (List.range 64).map fun i => Wire.mk s!"cpu_snoop_data_{i}"

  -- CachedCPU Instance
  let cached_cpu_inst : CircuitInstance := {
    moduleName := s!"CPU_{config.isaString}_{config.cacheString}"
    instName := "u_cached_cpu"
    portMap :=
      [("clock", clock), ("reset", sync_reset), ("zero", zero), ("one", one),
       ("mem_resp_valid", mem_resp_valid),
       ("mtip_in", mtip_in),
       ("msip_in", msip_in),
       ("meip_in", meip_in)] ++
      (mem_resp_data.enum.map fun ⟨i, w⟩ => (s!"mem_resp_data_{i}", w)) ++
      [("mem_req_valid", mem_req_valid)] ++
      (mem_req_addr.enum.map fun ⟨i, w⟩ => (s!"mem_req_addr_{i}", w)) ++
      [("mem_req_we", mem_req_we)] ++
      (mem_req_data.enum.map fun ⟨i, w⟩ => (s!"mem_req_data_{i}", w)) ++
      [("rob_empty", rob_empty),
       ("store_snoop_valid", store_snoop_valid)] ++
      (store_snoop_addr.enum.map fun ⟨i, w⟩ => (s!"store_snoop_addr_{i}", w)) ++
      (store_snoop_data.enum.map fun ⟨i, w⟩ => (s!"store_snoop_data_{i}", w))
  }

  -- TileLink Interconnect Wires
  let m_a := makeChannelAWires "m"
  let m_d := makeChannelDWires "m"
  let s_a := (List.range 8).map fun i => makeChannelAWires s!"s{i}"
  let s_d := (List.range 8).map fun i => makeChannelDWires s!"s{i}"

  -- Connect CPU store snoop / MMIO access to TileLink Master Channel A
  let tl_master_gates : List Gate :=
    [Gate.mkBUF store_snoop_valid m_a.valid] ++
    (store_snoop_addr.enum.map fun ⟨i, w⟩ => Gate.mkBUF w m_a.address[i]!) ++
    (store_snoop_data.enum.map fun ⟨i, w⟩ => Gate.mkBUF w m_a.data[i]!) ++
    ((List.range 3).map fun i => Gate.mkBUF zero m_a.opcode[i]!) ++ -- PutFullData
    ((List.range 3).map fun i => Gate.mkBUF zero m_a.param[i]!) ++
    ((List.range 3).map fun i => Gate.mkBUF (if i == 1 then one else zero) m_a.size[i]!) ++ -- 4 bytes
    ((List.range 4).map fun i => Gate.mkBUF zero m_a.source[i]!) ++
    ((List.range 8).map fun i => Gate.mkBUF one m_a.mask[i]!) ++
    [Gate.mkBUF one m_d.ready]

  -- TLXbar8 Instance
  let xbar_inst : CircuitInstance := {
    moduleName := "TLXbar8"
    instName := "u_tl_xbar"
    portMap :=
      [("clock", clock), ("reset", sync_reset), ("zero", zero), ("one", one),
       ("m_a_valid", m_a.valid)] ++
      (m_a.opcode.enum.map fun ⟨i, w⟩ => (s!"m_a_opcode_{i}", w)) ++
      (m_a.param.enum.map fun ⟨i, w⟩ => (s!"m_a_param_{i}", w)) ++
      (m_a.size.enum.map fun ⟨i, w⟩ => (s!"m_a_size_{i}", w)) ++
      (m_a.source.enum.map fun ⟨i, w⟩ => (s!"m_a_source_{i}", w)) ++
      (m_a.address.enum.map fun ⟨i, w⟩ => (s!"m_a_address_{i}", w)) ++
      (m_a.mask.enum.map fun ⟨i, w⟩ => (s!"m_a_mask_{i}", w)) ++
      (m_a.data.enum.map fun ⟨i, w⟩ => (s!"m_a_data_{i}", w)) ++
      [("m_d_ready", m_d.ready), ("m_a_ready", m_a.ready), ("m_d_valid", m_d.valid)] ++
      (m_d.opcode.enum.map fun ⟨i, w⟩ => (s!"m_d_opcode_{i}", w)) ++
      (m_d.param.enum.map fun ⟨i, w⟩ => (s!"m_d_param_{i}", w)) ++
      (m_d.size.enum.map fun ⟨i, w⟩ => (s!"m_d_size_{i}", w)) ++
      (m_d.source.enum.map fun ⟨i, w⟩ => (s!"m_d_source_{i}", w)) ++
      (m_d.sink.enum.map fun ⟨i, w⟩ => (s!"m_d_sink_{i}", w)) ++
      (m_d.data.enum.map fun ⟨i, w⟩ => (s!"m_d_data_{i}", w)) ++
      [("m_d_denied", m_d.denied)] ++
      ((List.range 8).flatMap fun k =>
        [ (s!"s{k}_a_ready", s_a[k]!.ready),
          (s!"s{k}_d_valid", s_d[k]!.valid) ] ++
        (s_d[k]!.opcode.enum.map fun ⟨i, w⟩ => (s!"s{k}_d_opcode_{i}", w)) ++
        (s_d[k]!.data.enum.map fun ⟨i, w⟩ => (s!"s{k}_d_data_{i}", w)) ++
        [ (s!"s{k}_a_valid", s_a[k]!.valid) ] ++
        (s_a[k]!.opcode.enum.map fun ⟨i, w⟩ => (s!"s{k}_a_opcode_{i}", w)) ++
        (s_a[k]!.param.enum.map fun ⟨i, w⟩ => (s!"s{k}_a_param_{i}", w)) ++
        (s_a[k]!.size.enum.map fun ⟨i, w⟩ => (s!"s{k}_a_size_{i}", w)) ++
        (s_a[k]!.source.enum.map fun ⟨i, w⟩ => (s!"s{k}_a_source_{i}", w)) ++
        (s_a[k]!.address.enum.map fun ⟨i, w⟩ => (s!"s{k}_a_address_{i}", w)) ++
        (s_a[k]!.mask.enum.map fun ⟨i, w⟩ => (s!"s{k}_a_mask_{i}", w)) ++
        (s_a[k]!.data.enum.map fun ⟨i, w⟩ => (s!"s{k}_a_data_{i}", w)) ++
        [ (s!"s{k}_d_ready", s_d[k]!.ready) ])
  }

  -- Helper function to map slave TileLink port
  let tlPortMap (pfx : String) (a : ChannelAWires) (d : ChannelDWires) : List (String × Wire) :=
    [("clock", clock), ("reset", sync_reset), ("zero", zero), ("one", one),
     (s!"{pfx}_a_valid", a.valid)] ++
    (a.opcode.enum.map fun ⟨i, w⟩ => (s!"{pfx}_a_opcode_{i}", w)) ++
    (a.param.enum.map fun ⟨i, w⟩ => (s!"{pfx}_a_param_{i}", w)) ++
    (a.size.enum.map fun ⟨i, w⟩ => (s!"{pfx}_a_size_{i}", w)) ++
    (a.source.enum.map fun ⟨i, w⟩ => (s!"{pfx}_a_source_{i}", w)) ++
    (a.address.enum.map fun ⟨i, w⟩ => (s!"{pfx}_a_address_{i}", w)) ++
    (a.mask.enum.map fun ⟨i, w⟩ => (s!"{pfx}_a_mask_{i}", w)) ++
    (a.data.enum.map fun ⟨i, w⟩ => (s!"{pfx}_a_data_{i}", w)) ++
    [(s!"{pfx}_d_ready", d.ready),
     (s!"{pfx}_a_ready", a.ready),
     (s!"{pfx}_d_valid", d.valid)] ++
    (d.opcode.enum.map fun ⟨i, w⟩ => (s!"{pfx}_d_opcode_{i}", w)) ++
    (d.param.enum.map fun ⟨i, w⟩ => (s!"{pfx}_d_param_{i}", w)) ++
    (d.size.enum.map fun ⟨i, w⟩ => (s!"{pfx}_d_size_{i}", w)) ++
    (d.source.enum.map fun ⟨i, w⟩ => (s!"{pfx}_d_source_{i}", w)) ++
    (d.sink.enum.map fun ⟨i, w⟩ => (s!"{pfx}_d_sink_{i}", w)) ++
    (d.data.enum.map fun ⟨i, w⟩ => (s!"{pfx}_d_data_{i}", w)) ++
    [(s!"{pfx}_d_denied", d.denied)]

  -- S0: BootROM Instance
  let bootrom_inst : CircuitInstance := {
    moduleName := "BootROM"
    instName := "u_bootrom"
    portMap := tlPortMap "bootrom" s_a[0]! s_d[0]!
  }

  -- S1: ACLINT Instance
  let aclint_inst : CircuitInstance := {
    moduleName := "ACLINT"
    instName := "u_aclint"
    portMap := tlPortMap "aclint" s_a[1]! s_d[1]! ++
               [("mtip_out", mtip_in), ("msip_out", msip_in), ("ssip_out", Wire.mk "unused_ssip")]
  }

  -- Tie off unused slave channels S2 and S3 for now
  let s2_s3_tie_gates : List Gate := [
    Gate.mkBUF one s_a[2]!.ready, Gate.mkBUF zero s_d[2]!.valid,
    Gate.mkBUF one s_a[3]!.ready, Gate.mkBUF zero s_d[3]!.valid
  ] ++
  (s_d[2]!.opcode.map fun w => Gate.mkBUF zero w) ++
  (s_d[2]!.data.map fun w => Gate.mkBUF zero w) ++
  (s_d[3]!.opcode.map fun w => Gate.mkBUF zero w) ++
  (s_d[3]!.data.map fun w => Gate.mkBUF zero w)

  -- S4: APLIC Instance
  let aplic_inst : CircuitInstance := {
    moduleName := "APLIC"
    instName := "u_aplic"
    portMap := tlPortMap "aplic" s_a[4]! s_d[4]! ++
               [("irq_src_0", zero), ("irq_src_1", uart_irq), ("irq_src_2", gpio_irq)] ++
               ((List.range 13).map fun i => (s!"irq_src_{i+3}", zero)) ++
               [("meip_out", meip_in), ("seip_out", Wire.mk "unused_seip")]
  }

  -- S5: UART Instance
  let uart_inst : CircuitInstance := {
    moduleName := "UART"
    instName := "u_uart"
    portMap := tlPortMap "uart" s_a[5]! s_d[5]! ++
               [("uart_rx", uart_rx), ("uart_tx", uart_tx), ("uart_irq", uart_irq)]
  }

  -- S6: GPIO Instance
  let gpio_inst : CircuitInstance := {
    moduleName := "GPIO"
    instName := "u_gpio"
    portMap := tlPortMap "gpio" s_a[6]! s_d[6]! ++
               (gpio_i.enum.map fun ⟨i, w⟩ => (s!"gpio_i_{i}", w)) ++
               (gpio_o.enum.map fun ⟨i, w⟩ => (s!"gpio_o_{i}", w)) ++
               (gpio_oen.enum.map fun ⟨i, w⟩ => (s!"gpio_oen_{i}", w)) ++
               [("gpio_irq", gpio_irq)]
  }

  -- S7: SRAM Instance
  let sram_inst : CircuitInstance := {
    moduleName := "SRAM"
    instName := "u_sram"
    portMap := tlPortMap "sram" s_a[7]! s_d[7]!
  }

  let all_inputs :=
    [clock, reset_n, zero, one, uart_rx, mem_resp_valid] ++
    gpio_i ++ mem_resp_data

  let all_outputs :=
    [uart_tx, rob_empty, mem_req_valid, mem_req_we] ++
    mem_req_addr ++ mem_req_data ++ gpio_o ++ gpio_oen

  { name := "Shoumei_SoC"
    inputs := all_inputs
    outputs := all_outputs
    gates := [not_rst_n] ++ tl_master_gates ++ s2_s3_tie_gates
    instances := [rst_sync_inst, cached_cpu_inst, xbar_inst, bootrom_inst,
                  aclint_inst, aplic_inst, uart_inst, gpio_inst, sram_inst]
    keepHierarchy := true
  }

def shoumeiSoCCircuit : Circuit := mkShoumeiSoC defaultCPUConfig

end Shoumei.SoC
