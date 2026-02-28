/-
Codegen/Testbench.lean - Testbench Code Generation

Generates SystemVerilog and plain C++ simulation testbenches from a
TestbenchConfig. The config maps circuit ports to memory interfaces
(imem/dmem), control signals, and constants. Generators produce:

- SV testbench: module instantiation, memory model, HTIF, DPI-C loader
- C++ sim testbench: plain bool signals, manual eval loop

Both share the same ELF loader library (testbench/lib/elf_loader.h).
-/

import Shoumei.DSL
import Shoumei.Codegen.Common
import Shoumei.Codegen.SystemVerilog

namespace Shoumei.Codegen.Testbench

open Shoumei
open Shoumei.Codegen

/-- A memory port describes how a CPU connects to a memory interface. -/
structure MemoryPort where
  addrSignal : String
  dataInSignal : Option String := none
  dataOutSignal : Option String := none
  validSignal : Option String := none
  readySignal : Option String := none
  weSignal : Option String := none
  /-- Store size signal (2-bit): 00=byte, 01=half, 10=word. When set, byte-enable
      store logic is generated. The signal may be a bus or individual bits
      (detected automatically from the circuit outputs). -/
  sizeSignal : Option String := none
  respValidSignal : Option String := none
  respDataSignal : Option String := none
  deriving Repr

/-- A cache-line memory port for 256-bit (8-word) cache line transactions. -/
structure CacheLineMemPort where
  reqValidSignal : String     -- "mem_req_valid"
  reqAddrSignal : String      -- "mem_req_addr" (32-bit)
  reqWeSignal : String        -- "mem_req_we"
  reqDataSignal : String      -- "mem_req_data" (256-bit)
  respValidSignal : String    -- "mem_resp_valid"
  respDataSignal : String     -- "mem_resp_data" (256-bit)
  deriving Repr

/-- Configuration for testbench generation. -/
structure TestbenchConfig where
  circuit : Circuit
  imemPort : MemoryPort
  dmemPort : MemoryPort
  /-- Cache-line memory port. When set, generates 256-bit memory model instead of
      separate imem/dmem. -/
  cacheLineMemPort : Option CacheLineMemPort := none
  memSizeWords : Nat := 16384
  tohostAddr : Nat := 0x1000
  /-- MMIO putchar address. Writes to this address emit the low byte to $write. -/
  putcharAddr : Option Nat := none
  timeoutCycles : Nat := 100000
  constantPorts : List (String × Bool) := [("zero", false), ("one", true)]
  /-- Override the testbench module/file name (default: tb_<circuit.name>) -/
  tbName : Option String := none
  debugOutputs : List String := []
  /-- Spike ISA string for cosimulation (e.g. "rv32imf", "rv32im_zicsr_zifencei") -/
  spikeIsa : String := "rv32imf"
  /-- Enable CLINT timer peripheral (mtime/mtimecmp/mtip) in the testbench.
      Adds MMIO registers at clintBaseAddr and an mtip output. -/
  enableCLINT : Bool := false
  /-- CLINT base address (standard: 0x0200_0000). Registers:
      +0x4000: mtimecmp_lo, +0x4004: mtimecmp_hi,
      +0xBFF8: mtime_lo,    +0xBFFC: mtime_hi -/
  clintBaseAddr : Nat := 0x02000000
  deriving Repr

/-! ## Helpers -/

private def optOrDefault (o : Option String) (d : String) : String :=
  match o with | some s => s | none => d

private def natToHexDigits (n : Nat) : String :=
  if n == 0 then "0"
  else String.ofList (Nat.toDigits 16 n)

private def hexLit (_width : Nat) (value : Nat) : String :=
  "32'h" ++ natToHexDigits value

/-! ## SystemVerilog Testbench Generator -/

def toTestbenchSV (cfg : TestbenchConfig) : String :=
  let c := cfg.circuit
  let inputGroups := SystemVerilog.autoDetectSignalGroups c.inputs
  let outputGroups := SystemVerilog.autoDetectSignalGroups c.outputs

  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let clockName := if clockWires.isEmpty then "clock" else Wire.name (List.head! clockWires)
  let resetName := if resetWires.isEmpty then "reset" else Wire.name (List.head! resetWires)

  -- Build signal lists: (name, width) for inputs and outputs
  let inputBusWireNames := inputGroups.flatMap (fun sg => sg.wires.map Wire.name)
  let outputBusWireNames := outputGroups.flatMap (fun sg => sg.wires.map Wire.name)

  let inputSignals : List (String × Nat) :=
    let scalars := c.inputs.filter (fun w => !inputBusWireNames.contains w.name)
    scalars.map (fun w => (w.name, 1)) ++ inputGroups.map (fun sg => (sg.name, sg.width))

  let outputSignals : List (String × Nat) :=
    let scalars := c.outputs.filter (fun w => !outputBusWireNames.contains w.name)
    scalars.map (fun w => (w.name, 1)) ++ outputGroups.map (fun sg => (sg.name, sg.width))

  -- Filter: signals that are not clock/reset/constants
  let isSpecial (name : String) : Bool :=
    name == clockName || name == resetName ||
    cfg.constantPorts.any (fun (cn, _) => cn == name)

  -- Signal declarations
  let mkDecl (name : String) (width : Nat) : String :=
    if width > 1 then s!"  logic [{width-1}:0] {name};"
    else s!"  logic        {name};"

  -- Size signal handling (must be before signalDecls/portConns)
  let dmemSize := cfg.dmemPort.sizeSignal

  -- Detect output signal groups that need individual bit ports (not bus ports)
  -- in the generated SV. Uses the same logic as the SV codegen to determine
  -- which output groups are vectorized vs individual.
  let svCtx := SystemVerilog.mkContext c
  let bitwiseOutputGroups := outputGroups.filter (fun sg =>
    SystemVerilog.outputNeedsIndividualPorts svCtx.wireToGroup svCtx.wireToIndex c sg)
  let isBitwiseBus (name : String) : Bool :=
    bitwiseOutputGroups.any (fun sg => sg.name == name)

  let signalDecls := String.intercalate "\n" (
    (inputSignals.filter (fun (n, _) => !isSpecial n)).map (fun (n, w) => mkDecl n w) ++
    (outputSignals.filter (fun (n, _) => !isSpecial n && !isBitwiseBus n)).map (fun (n, w) => mkDecl n w)
  )

  -- Generate individual bit declarations + combined wire for bitwise output groups
  let bitwiseDeclStrs := bitwiseOutputGroups.map (fun sg =>
    let bitDecls := (List.range sg.width).map (fun i =>
      s!"  logic       {sg.name}_{i};")
    let bits := (List.range sg.width).reverse.map (fun i => s!"{sg.name}_{i}")
    let wireDecl := s!"  wire  [{sg.width - 1}:0] {sg.name} = " ++
      "{" ++ String.intercalate ", " bits ++ "};"
    String.intercalate "\n" bitDecls ++ "\n" ++ wireDecl ++ "\n")

  -- Port connections for CPU instance
  let portConns := String.intercalate ",\n" (
    [s!"      .{clockName}(clk)"] ++
    [s!"      .{resetName}({resetName})"] ++
    cfg.constantPorts.map (fun (name, value) =>
      s!"      .{name}(1'b{if value then "1" else "0"})") ++
    (inputSignals.filter (fun (n, _) => !isSpecial n)).map (fun (n, _) =>
      s!"      .{n}({n})") ++
    (outputSignals.filter (fun (n, _) => !isBitwiseBus n)).map (fun (n, _) =>
      s!"      .{n}({n})") ++
    -- Add individual bit connections for bitwise output groups
    bitwiseOutputGroups.flatMap (fun sg =>
      (List.range sg.width).map (fun i =>
        s!"      .{sg.name}_{i}({sg.name}_{i})"))
  )

  let pcSig := cfg.imemPort.addrSignal
  let imemDataIn := optOrDefault cfg.imemPort.dataInSignal "imem_resp_data"
  let dmemAddr := cfg.dmemPort.addrSignal
  let dmemValid := optOrDefault cfg.dmemPort.validSignal "dmem_req_valid"
  let dmemWe := optOrDefault cfg.dmemPort.weSignal "dmem_req_we"
  let dmemDataOut := optOrDefault cfg.dmemPort.dataOutSignal "dmem_req_data"
  let dmemReady := optOrDefault cfg.dmemPort.readySignal "dmem_req_ready"
  let dmemRespValid := optOrDefault cfg.dmemPort.respValidSignal "dmem_resp_valid"
  let dmemRespData := optOrDefault cfg.dmemPort.respDataSignal "dmem_resp_data"

  let memSizeStr := toString cfg.memSizeWords
  let timeoutStr := toString cfg.timeoutCycles
  let tohostHex := hexLit 32 cfg.tohostAddr
  let putcharParam := match cfg.putcharAddr with
    | some addr => s!",\n    parameter PUTCHAR_ADDR    = {hexLit 32 addr}"
    | none => ""

  let tbName := optOrDefault cfg.tbName s!"tb_{c.name}"

  -- Individual bit declarations for all bitwise output groups
  let bitwiseDeclStr := String.intercalate "" bitwiseDeclStrs

  -- Build the complete SV string
  "//==============================================================================\n" ++
  s!"// {tbName}.sv - Auto-generated testbench for {c.name}\n" ++
  "//\n" ++
  "// Generated by Shoumei RTL testbench code generator.\n" ++
  "// DO NOT EDIT - regenerate with: lake exe generate_all\n" ++
  "//==============================================================================\n\n" ++

  s!"module {tbName} #(\n" ++
  s!"    parameter MEM_SIZE_WORDS = {memSizeStr},\n" ++
  s!"    parameter TIMEOUT_CYCLES = {timeoutStr},\n" ++
  s!"    parameter TOHOST_ADDR    = {tohostHex}\n" ++
  putcharParam ++
  ") (\n" ++
  "    input logic clk,\n" ++
  "    input logic rst_n,\n" ++
  "    // Test status\n" ++
  "    output logic        o_test_done,\n" ++
  "    output logic        o_test_pass,\n" ++
  "    output logic [31:0] o_test_code,\n" ++
  "    // Debug outputs\n" ++
  "    output logic [31:0] o_fetch_pc,\n" ++
  "    output logic        o_rob_empty,\n" ++
  "    output logic        o_global_stall,\n" ++
  "    output logic [31:0] o_cycle_count,\n" ++
  "    // Memory request observation\n" ++
  "    output logic        o_dmem_req_valid,\n" ++
  "    output logic        o_dmem_req_we,\n" ++
  "    output logic [31:0] o_dmem_req_addr,\n" ++
  "    output logic [31:0] o_dmem_req_data,\n" ++
  "    // HTIF\n" ++
  "    output logic [31:0] o_tohost,\n" ++
  "    // RVVI-TRACE outputs (cosimulation)\n" ++
  "    output logic        o_rvvi_valid,\n" ++
  "    output logic        o_rvvi_trap,\n" ++
  "    output logic [31:0] o_rvvi_pc_rdata,\n" ++
  "    output logic [31:0] o_rvvi_insn,\n" ++
  "    output logic [4:0]  o_rvvi_rd,\n" ++
  "    output logic        o_rvvi_rd_valid,\n" ++
  "    output logic [31:0] o_rvvi_rd_data,\n" ++
  "    // RVVI-TRACE FP outputs (F extension cosimulation)\n" ++
  "    output logic [4:0]  o_rvvi_frd,\n" ++
  "    output logic        o_rvvi_frd_valid,\n" ++
  "    output logic [31:0] o_rvvi_frd_data,\n" ++
  "    // FP exception flags accumulator\n" ++
  "    output logic [4:0]  o_fflags_acc,\n" ++
  "    // Kanata pipeline trace outputs\n" ++
  "    output logic        o_trace_alloc_valid,\n" ++
  "    output logic [3:0]  o_trace_alloc_idx,\n" ++
  "    output logic [5:0]  o_trace_alloc_physrd,\n" ++
  "    output logic        o_trace_cdb_valid,\n" ++
  "    output logic [5:0]  o_trace_cdb_tag,\n" ++
  "    output logic        o_trace_flush,\n" ++
  "    output logic [3:0]  o_trace_head_idx,\n" ++
  "    // Kanata dispatch tracking\n" ++
  "    output logic        o_trace_dispatch_int,\n" ++
  "    output logic [5:0]  o_trace_dispatch_int_tag,\n" ++
  "    output logic        o_trace_dispatch_mem,\n" ++
  "    output logic [5:0]  o_trace_dispatch_mem_tag,\n" ++
  "    output logic        o_trace_dispatch_branch,\n" ++
  "    output logic [5:0]  o_trace_dispatch_branch_tag,\n" ++
  "    output logic        o_trace_dispatch_muldiv,\n" ++
  "    output logic [5:0]  o_trace_dispatch_muldiv_tag,\n" ++
  "    output logic        o_trace_dispatch_fp,\n" ++
  "    output logic [5:0]  o_trace_dispatch_fp_tag\n" ++
  ");\n\n" ++
  "  // =========================================================================\n" ++
  "  // CPU I/O signals\n" ++
  "  // =========================================================================\n" ++
  signalDecls ++ "\n" ++
  bitwiseDeclStr ++ "\n" ++
  s!"  logic        {resetName};\n" ++
  s!"  assign {resetName} = ~rst_n;\n\n" ++

  "  // =========================================================================\n" ++
  "  // CPU instance\n" ++
  "  // =========================================================================\n" ++
  s!"  {c.name} u_cpu (\n" ++
  portConns ++ "\n" ++
  "  );\n\n" ++

  "  // =========================================================================\n" ++
  "  // Memory: shared instruction + data, word-addressed\n" ++
  "  // =========================================================================\n" ++
  "  logic [31:0] mem [0:MEM_SIZE_WORDS-1];\n\n" ++
  "  // DPI-C: allow C++ to write memory words before simulation starts\n" ++
  "  export \"DPI-C\" function dpi_mem_write;\n" ++
  "  function void dpi_mem_write(input int unsigned word_addr, input int unsigned data);\n" ++
  "    mem[word_addr] = data;\n" ++
  "  endfunction\n\n" ++
  "  // DPI-C: allow C++ to override HTIF addresses from ELF symbols\n" ++
  "  logic [31:0] tohost_addr_r;\n" ++
  "  initial tohost_addr_r = TOHOST_ADDR;\n" ++
  "  export \"DPI-C\" function dpi_set_tohost_addr;\n" ++
  "  function void dpi_set_tohost_addr(input int unsigned addr);\n" ++
  "    tohost_addr_r = addr;\n" ++
  "  endfunction\n\n" ++
  (match cfg.putcharAddr with
   | some _ =>
     "  logic [31:0] putchar_addr_r;\n" ++
     "  initial putchar_addr_r = PUTCHAR_ADDR;\n" ++
     "  export \"DPI-C\" function dpi_set_putchar_addr;\n" ++
     "  function void dpi_set_putchar_addr(input int unsigned addr);\n" ++
     "    putchar_addr_r = addr;\n" ++
     "  endfunction\n\n"
   | none => "") ++
  "  localparam logic [31:0] MEM_BASE = 32'h00000000;\n\n" ++
  "  function automatic logic [31:0] addr_to_idx(input logic [31:0] addr);\n" ++
  "    return (addr - MEM_BASE) >> 2;\n" ++
  "  endfunction\n\n" ++

  "  // --- Instruction memory: combinational read ---\n" ++
  s!"  assign {imemDataIn} = mem[addr_to_idx({pcSig})];\n\n" ++

  "  // --- Data memory: 1-cycle latency ---\n" ++
  "  logic        dmem_pending;\n" ++
  "  logic [31:0] dmem_read_data;\n\n" ++
  s!"  assign {dmemReady} = 1'b1;  // Always ready\n\n" ++
  s!"  always_ff @(posedge clk or posedge {resetName}) begin\n" ++
  s!"    if ({resetName}) begin\n" ++
  s!"      {dmemRespValid} <= 1'b0;\n" ++
  "      dmem_read_data  <= 32'b0;\n" ++
  "      dmem_pending    <= 1'b0;\n" ++
  "    end else begin\n" ++
  "      dmem_pending    <= 1'b0;\n" ++
  s!"      {dmemRespValid} <= 1'b0;\n\n" ++
  s!"      if ({dmemValid}) begin\n" ++
  s!"        if ({dmemWe}) begin\n" ++
  (match dmemSize with
   | some sizeName =>
     s!"          // Store with byte-enable based on {sizeName} and addr[1:0]\n" ++
     s!"          // {sizeName}: 00=byte, 01=half, 10=word\n" ++
     s!"          case ({sizeName})\n" ++
     s!"            2'b00: begin // SB: store byte\n" ++
     s!"              case ({dmemAddr}[1:0])\n" ++
     s!"                2'b00: mem[addr_to_idx({dmemAddr})][7:0]   <= {dmemDataOut}[7:0];\n" ++
     s!"                2'b01: mem[addr_to_idx({dmemAddr})][15:8]  <= {dmemDataOut}[7:0];\n" ++
     s!"                2'b10: mem[addr_to_idx({dmemAddr})][23:16] <= {dmemDataOut}[7:0];\n" ++
     s!"                2'b11: mem[addr_to_idx({dmemAddr})][31:24] <= {dmemDataOut}[7:0];\n" ++
     s!"              endcase\n" ++
     s!"            end\n" ++
     s!"            2'b01: begin // SH: store halfword\n" ++
     s!"              case ({dmemAddr}[1])\n" ++
     s!"                1'b0: mem[addr_to_idx({dmemAddr})][15:0]  <= {dmemDataOut}[15:0];\n" ++
     s!"                1'b1: mem[addr_to_idx({dmemAddr})][31:16] <= {dmemDataOut}[15:0];\n" ++
     s!"              endcase\n" ++
     s!"            end\n" ++
     s!"            default: begin // SW: store word\n" ++
     s!"              mem[addr_to_idx({dmemAddr})] <= {dmemDataOut};\n" ++
     s!"            end\n" ++
     s!"          endcase\n"
   | none =>
     s!"          // Store\n" ++
     s!"          mem[addr_to_idx({dmemAddr})] <= {dmemDataOut};\n") ++
  "        end else begin\n" ++
  "          // Load: respond next cycle\n" ++
  s!"          dmem_read_data  <= mem[addr_to_idx({dmemAddr})];\n" ++
  "          dmem_pending    <= 1'b1;\n" ++
  "        end\n" ++
  "      end\n\n" ++
  "      if (dmem_pending) begin\n" ++
  s!"        {dmemRespValid} <= 1'b1;\n" ++
  "      end\n" ++
  "    end\n" ++
  "  end\n\n" ++
  s!"  assign {dmemRespData} = dmem_read_data;\n\n" ++

  "  // =========================================================================\n" ++
  "  // HTIF: tohost termination\n" ++
  "  // =========================================================================\n" ++
  "  // Speculative stores are blocked by SB commit gating, so the first tohost\n" ++
  "  // write is always the correct committed one.\n" ++
  "  logic        test_done;\n" ++
  "  logic        test_pass;\n" ++
  "  logic [31:0] test_code;\n\n" ++
  s!"  always_ff @(posedge clk or posedge {resetName}) begin\n" ++
  s!"    if ({resetName}) begin\n" ++
  "      test_done <= 1'b0;\n" ++
  "      test_pass <= 1'b0;\n" ++
  "      test_code <= 32'b0;\n" ++
  "    end else begin\n" ++
  s!"      if ({dmemValid} && {dmemWe} &&\n" ++
  s!"          {dmemAddr} == tohost_addr_r) begin\n" ++
  s!"        test_code <= {dmemDataOut};\n" ++
  s!"        test_pass <= ({dmemDataOut} == 32'h1);\n" ++
  "        test_done <= 1'b1;\n" ++
  "      end\n" ++
  "    end\n" ++
  "  end\n\n" ++

  -- MMIO putchar support
  (match cfg.putcharAddr with
   | some _ =>
     "  // =========================================================================\n" ++
     "  // MMIO putchar: writes to PUTCHAR_ADDR emit a character\n" ++
     "  // =========================================================================\n" ++
     s!"  always_ff @(posedge clk) begin\n" ++
     s!"    if (!{resetName} && {dmemValid} && {dmemWe} &&\n" ++
     s!"        {dmemAddr} == putchar_addr_r) begin\n" ++
     s!"      $write(\"%c\", {dmemDataOut}[7:0]);\n" ++
     "    end\n" ++
     "  end\n\n"
   | none => "") ++

  "  // =========================================================================\n" ++
  "  // Cycle counter\n" ++
  "  // =========================================================================\n" ++
  "  logic [31:0] cycle_count;\n\n" ++
  s!"  always_ff @(posedge clk or posedge {resetName}) begin\n" ++
  s!"    if ({resetName}) begin\n" ++
  "      cycle_count <= 32'b0;\n" ++
  "    end else begin\n" ++
  "      cycle_count <= cycle_count + 1;\n" ++
  "    end\n" ++
  "  end\n\n" ++

  "  // =========================================================================\n" ++
  "  // Debug trace (enable with +define+TRACE_PIPELINE)\n" ++
  "  // =========================================================================\n" ++
  "  `ifdef TRACE_PIPELINE\n" ++
  "  always_ff @(posedge clk) begin\n" ++
  s!"    if (!{resetName}) begin\n" ++
  "      $display(\"[%0d] PC=0x%08x stall=%b rob_empty=%b\",\n" ++
  s!"               cycle_count, {pcSig}, global_stall_out, rob_empty);\n" ++
  "    end\n" ++
  "  end\n" ++
  "  `endif\n\n" ++

  "  // =========================================================================\n" ++
  "  // Output assignments\n" ++
  "  // =========================================================================\n" ++
  "  assign o_test_done       = test_done;\n" ++
  "  assign o_test_pass       = test_pass;\n" ++
  "  assign o_test_code       = test_code;\n" ++
  s!"  assign o_fetch_pc       = {pcSig};\n" ++
  "  assign o_rob_empty       = rob_empty;\n" ++
  "  assign o_global_stall    = global_stall_out;\n" ++
  "  assign o_cycle_count     = cycle_count;\n" ++
  s!"  assign o_dmem_req_valid = {dmemValid};\n" ++
  s!"  assign o_dmem_req_we    = {dmemWe};\n" ++
  s!"  assign o_dmem_req_addr  = {dmemAddr};\n" ++
  s!"  assign o_dmem_req_data  = {dmemDataOut};\n" ++
  "  assign o_tohost          = test_code;\n" ++
  "  assign o_rvvi_valid      = rvvi_valid;\n" ++
  "  assign o_rvvi_trap       = rvvi_trap;\n" ++
  "  assign o_rvvi_pc_rdata   = rvvi_pc_rdata;\n" ++
  "  assign o_rvvi_insn       = rvvi_insn;\n" ++
  "  assign o_rvvi_rd         = rvvi_rd;\n" ++
  "  assign o_rvvi_rd_valid   = rvvi_rd_valid;\n" ++
  "  assign o_rvvi_rd_data    = rvvi_rd_data;\n" ++
  "  assign o_rvvi_frd        = rvvi_frd;\n" ++
  "  assign o_rvvi_frd_valid  = rvvi_frd_valid;\n" ++
  "  assign o_rvvi_frd_data   = rvvi_frd_data;\n" ++
  "  assign o_fflags_acc      = fflags_acc;\n" ++
  "  assign o_trace_alloc_valid = trace_alloc_valid;\n" ++
  "  assign o_trace_alloc_idx   = trace_alloc_idx;\n" ++
  "  assign o_trace_alloc_physrd = trace_alloc_physrd;\n" ++
  "  assign o_trace_cdb_valid   = trace_cdb_valid;\n" ++
  "  assign o_trace_cdb_tag     = trace_cdb_tag;\n" ++
  "  assign o_trace_flush       = trace_flush;\n" ++
  "  assign o_trace_head_idx    = trace_head_idx;\n" ++
  "  assign o_trace_dispatch_int        = trace_dispatch_int;\n" ++
  "  assign o_trace_dispatch_int_tag    = trace_dispatch_int_tag;\n" ++
  "  assign o_trace_dispatch_mem        = trace_dispatch_mem;\n" ++
  "  assign o_trace_dispatch_mem_tag    = trace_dispatch_mem_tag;\n" ++
  "  assign o_trace_dispatch_branch     = trace_dispatch_branch;\n" ++
  "  assign o_trace_dispatch_branch_tag = trace_dispatch_branch_tag;\n" ++
  "  assign o_trace_dispatch_muldiv        = trace_dispatch_muldiv;\n" ++
  "  assign o_trace_dispatch_muldiv_tag    = trace_dispatch_muldiv_tag;\n" ++
  "  assign o_trace_dispatch_fp         = trace_dispatch_fp;\n" ++
  "  assign o_trace_dispatch_fp_tag     = trace_dispatch_fp_tag;\n\n" ++
  "endmodule\n"

/-! ## Plain C++ Simulation Testbench Generator -/

/-- Generate bus pack/unpack helpers for plain C++ simulation.
    These operate on bool* arrays (declared later in main scope). -/
private def generateCppSimBusHelpers (c : Circuit) : String :=
  let groups := SystemVerilog.autoDetectSignalGroups (c.inputs ++ c.outputs)
  let lb := "{"
  let rb := "}"
  let helpers := groups.map fun sg =>
    let width := sg.width
    let isInput := sg.wires.any (fun w => c.inputs.any (fun iw => iw.name == w.name))
    let isOutput := sg.wires.any (fun w => c.outputs.any (fun ow => ow.name == w.name))

    -- For input buses: write to the connected bool (passed as pointer array)
    let setter := if isInput then
      let lines := (List.range width).map fun i =>
        s!"    *sigs[{i}] = (v >> {i}) & 1;"
      "void set_" ++ sg.name ++ "(bool** sigs, uint32_t v) " ++ lb ++ "\n" ++
        String.intercalate "\n" lines ++ "\n" ++ rb
    else ""

    -- For output buses: read from the connected bool
    let getter := if isOutput then
      let terms := (List.range width).map fun i =>
        if i == 0 then s!"(uint32_t)(*sigs[{i}])"
        else s!"((uint32_t)(*sigs[{i}]) << {i})"
      "uint32_t get_" ++ sg.name ++ "(bool** sigs) " ++ lb ++ "\n" ++
        "    return " ++ String.intercalate " | " terms ++ ";\n" ++ rb
    else ""

    let s1 := if setter.isEmpty then "" else setter ++ "\n\n"
    let s2 := if getter.isEmpty then "" else getter ++ "\n"
    s1 ++ s2
  String.intercalate "\n" (helpers.filter (· != ""))

/-! ## CPU Setup File Generator -/

/-- Generate the thin header for CPU setup. -/
private def toCpuSetupHeader (c : Circuit) : String :=
  let lb := "{"
  let rb := "}"
  "// Auto-generated thin header for CPU setup. DO NOT EDIT.\n" ++
  s!"#ifndef CPU_SETUP_{c.name.toUpper}_H\n" ++
  s!"#define CPU_SETUP_{c.name.toUpper}_H\n\n" ++
  "#include <cstdint>\n\n" ++
  s!"// Opaque handle to {c.name} instance + bound ports\n" ++
  s!"struct CpuCtx {lb}\n" ++
  "    void* cpu;\n" ++
  s!"{rb};\n\n" ++
  "// Create, bind ports (ports array order matches circuit definition), and return context\n" ++
  s!"CpuCtx* cpu_create(const char* name, bool* reset_sig,\n" ++
  "                    bool* ports[], int num_ports);\n" ++
  "void cpu_delete(CpuCtx* ctx);\n" ++
  "// Manual evaluation\n" ++
  "void cpu_eval_comb_all(CpuCtx* ctx);\n" ++
  "void cpu_eval_seq_sample_all(CpuCtx* ctx);\n" ++
  "void cpu_eval_seq_all(CpuCtx* ctx);\n\n" ++
  s!"#endif // CPU_SETUP_{c.name.toUpper}_H\n"

/-- Generate the heavy setup .cpp file (includes the full module header). -/
private def toCpuSetupCpp (cfg : TestbenchConfig) : String :=
  let c := cfg.circuit
  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let _clockName := if clockWires.isEmpty then "clock" else Wire.name (List.head! clockWires)
  let resetName := if resetWires.isEmpty then "reset" else Wire.name (List.head! resetWires)
  let lb := "{"
  let rb := "}"

  -- Build port list (excluding reset only; clock is included as a dummy bool*)
  let allPorts := c.inputs ++ c.outputs
  let portList := allPorts.filter fun w =>
    w.name != resetName
  let portBindings := String.intercalate "\n" (
    portList.enum.map fun ⟨idx, w⟩ =>
      s!"    cpu->{w.name} = ports[{idx}];"
  )

  s!"// Auto-generated CPU setup (heavy -- includes full module headers). DO NOT EDIT.\n" ++
  s!"#include \"cpu_setup_{c.name}.h\"\n" ++
  s!"#include \"{c.name}.h\"\n\n" ++
  s!"CpuCtx* cpu_create(const char* name, bool* reset_sig,\n" ++
  s!"                    bool* ports[], int num_ports) {lb}\n" ++
  s!"    (void)name; (void)num_ports;  // used for assert in debug builds\n" ++
  s!"    auto* cpu = new {c.name}();\n" ++
  s!"    cpu->{resetName} = reset_sig;\n" ++
  portBindings ++ "\n" ++
  s!"    cpu->bind_ports();\n" ++
  s!"    auto* ctx = new CpuCtx{lb}cpu{rb};\n" ++
  "    return ctx;\n" ++
  s!"{rb}\n\n" ++
  s!"void cpu_delete(CpuCtx* ctx) {lb}\n" ++
  s!"    delete static_cast<{c.name}*>(ctx->cpu);\n" ++
  "    delete ctx;\n" ++
  s!"{rb}\n\n" ++
  s!"void cpu_eval_comb_all(CpuCtx* ctx) {lb}\n" ++
  s!"    static_cast<{c.name}*>(ctx->cpu)->eval_comb_all();\n" ++
  s!"{rb}\n\n" ++
  s!"void cpu_eval_seq_sample_all(CpuCtx* ctx) {lb}\n" ++
  s!"    static_cast<{c.name}*>(ctx->cpu)->eval_seq_sample_all();\n" ++
  s!"{rb}\n\n" ++
  s!"void cpu_eval_seq_all(CpuCtx* ctx) {lb}\n" ++
  s!"    static_cast<{c.name}*>(ctx->cpu)->eval_seq_all();\n" ++
  s!"{rb}\n"

/-- Generate a plain C++ simulation testbench. -/
def toTestbenchCppSim (cfg : TestbenchConfig) : String :=
  let c := cfg.circuit
  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let _clockName := if clockWires.isEmpty then "clock" else Wire.name (List.head! clockWires)
  let resetName := if resetWires.isEmpty then "reset" else Wire.name (List.head! resetWires)

  let busHelpers := generateCppSimBusHelpers c

  let inputGroups := SystemVerilog.autoDetectSignalGroups c.inputs
  let outputGroups := SystemVerilog.autoDetectSignalGroups c.outputs
  let groups := SystemVerilog.autoDetectSignalGroups (c.inputs ++ c.outputs)

  let busWireNames : List String :=
    inputGroups.flatMap (fun sg => sg.wires.map Wire.name) ++
    outputGroups.flatMap (fun sg => sg.wires.map Wire.name)
  let scalarInputs := c.inputs.filter fun w =>
    !busWireNames.contains w.name &&
    w.name != resetName &&
    !cfg.constantPorts.any (fun (cn, _) => cn == w.name)
  let scalarOutputs := c.outputs.filter fun w =>
    !busWireNames.contains w.name

  let pcSig := cfg.imemPort.addrSignal
  let imemDataIn := optOrDefault cfg.imemPort.dataInSignal "imem_resp_data"
  let dmemAddr := cfg.dmemPort.addrSignal
  let dmemValid := optOrDefault cfg.dmemPort.validSignal "dmem_req_valid"
  let dmemWe := optOrDefault cfg.dmemPort.weSignal "dmem_req_we"
  let dmemDataOut := optOrDefault cfg.dmemPort.dataOutSignal "dmem_req_data"
  let dmemReady := optOrDefault cfg.dmemPort.readySignal "dmem_req_ready"
  let dmemRespValid := optOrDefault cfg.dmemPort.respValidSignal "dmem_resp_valid"
  let dmemRespData := optOrDefault cfg.dmemPort.respDataSignal "dmem_resp_data"
  let dmemSize := cfg.dmemPort.sizeSignal

  let signalDecls := String.intercalate "\n" (
    scalarInputs.map (fun w => s!"    bool {w.name}_sig = false;") ++
    scalarOutputs.map (fun w => s!"    bool {w.name}_sig = false;") ++
    cfg.constantPorts.map (fun (name, _) => s!"    bool {name}_sig = false;") ++
    groups.flatMap (fun sg =>
      (List.range sg.width).map fun i => s!"    bool {sg.name}_{i}_sig = false;")
  )

  let lb := "{"
  let rb := "}"
  let signalArrayDecls := String.intercalate "\n" (
    groups.map fun sg =>
      let ptrs := String.intercalate ", " (
        (List.range sg.width).map fun i => s!"&{sg.name}_{i}_sig")
      s!"    bool* {sg.name}_sigs[] = {lb}{ptrs}{rb};"
  )

  -- Build the port pointer array in the same order as toCpuSetupCpp
  let allPorts := c.inputs ++ c.outputs
  let portList := allPorts.filter fun w =>
    w.name != resetName
  let portPtrArray := String.intercalate ", " (
    portList.map fun w => s!"&{w.name}_sig"
  )

  let constBindings := String.intercalate "\n" (
    cfg.constantPorts.map fun (name, value) =>
      s!"    {name}_sig = {if value then "true" else "false"};"
  )

  "//==============================================================================\n" ++
  s!"// sim_main_{c.name}.cpp - Auto-generated plain C++ simulation testbench\n" ++
  "// DO NOT EDIT - regenerate with: lake exe generate_all\n" ++
  "//==============================================================================\n\n" ++
  "#include <cstdint>\n" ++
  "#include <cstdlib>\n" ++
  "#include <cstring>\n" ++
  "#include <cstdio>\n" ++
  s!"#include \"cpu_setup_{c.name}.h\"\n" ++
  "#include \"elf_loader.h\"\n\n" ++
  s!"static const uint32_t MEM_SIZE_WORDS = {cfg.memSizeWords};\n" ++
  s!"static const uint32_t TOHOST_ADDR = 0x{natToHexDigits cfg.tohostAddr};\n" ++
  (match cfg.putcharAddr with
   | some addr => s!"static const uint32_t PUTCHAR_ADDR = 0x{natToHexDigits addr};\n"
   | none => "") ++
  s!"static const uint32_t TIMEOUT_CYCLES = {cfg.timeoutCycles};\n\n" ++

  "// Memory model\n" ++
  s!"static uint32_t mem[{cfg.memSizeWords}];\n\n" ++
  s!"static void mem_write_cb(uint32_t addr, uint32_t data) {lb}\n" ++
  s!"    uint32_t widx = addr / 4;\n" ++
  s!"    if (widx < MEM_SIZE_WORDS) mem[widx] = data;\n" ++
  s!"{rb}\n\n" ++

  "// Bus pack/unpack helpers\n" ++
  busHelpers ++ "\n\n" ++

  "//------------------------------------------------------------------------------\n" ++
  "// Imem: combinational instruction memory (plain function)\n" ++
  "//------------------------------------------------------------------------------\n" ++
  s!"static void imem_update(bool** pc_sigs, bool** data_sigs) {lb}\n" ++
  s!"    uint32_t pc_val = 0;\n" ++
  s!"    for (int i = 0; i < 32; i++) pc_val |= (*pc_sigs[i] ? 1u : 0u) << i;\n" ++
  s!"    uint32_t widx = pc_val >> 2;\n" ++
  s!"    uint32_t dval = (widx < MEM_SIZE_WORDS) ? mem[widx] : 0;\n" ++
  s!"    for (int i = 0; i < 32; i++) *data_sigs[i] = (dval >> i) & 1;\n" ++
  s!"{rb}\n\n" ++

  "//------------------------------------------------------------------------------\n" ++
  "// Dmem: data memory with 1-cycle read latency, byte/halfword/word stores\n" ++
  "//------------------------------------------------------------------------------\n" ++
  s!"struct DmemState {lb}\n" ++
  s!"    bool pending = false;\n" ++
  s!"    uint32_t read_data = 0;\n" ++
  s!"    bool test_done = false;\n" ++
  s!"    uint32_t test_data = 0;\n" ++
  s!"{rb};\n\n" ++
  s!"static void dmem_tick(DmemState& ds,\n" ++
  s!"    bool snap_req_valid, bool snap_req_we,\n" ++
  s!"    uint32_t snap_addr, uint32_t snap_data, uint32_t snap_size,\n" ++
  s!"    bool& req_ready_sig, bool& resp_valid_sig,\n" ++
  s!"    bool** resp_data_sigs) {lb}\n" ++
  s!"    req_ready_sig = true;\n\n" ++
  s!"    // Respond to pending load from previous cycle\n" ++
  s!"    if (ds.pending) {lb}\n" ++
  s!"        resp_valid_sig = true;\n" ++
  s!"        for (int i = 0; i < 32; i++) *resp_data_sigs[i] = (ds.read_data >> i) & 1;\n" ++
  s!"        ds.pending = false;\n" ++
  s!"    {rb} else {lb}\n" ++
  s!"        resp_valid_sig = false;\n" ++
  s!"        // Keep resp_data at last read value (matches SV: assign dmem_resp_data = dmem_read_data)\n" ++
  s!"        for (int i = 0; i < 32; i++) *resp_data_sigs[i] = (ds.read_data >> i) & 1;\n" ++
  s!"    {rb}\n\n" ++
  s!"    // Handle new request\n" ++
  s!"    if (snap_req_valid) {lb}\n" ++
  s!"        uint32_t addr = snap_addr;\n" ++
  s!"        if (snap_req_we) {lb}\n" ++
  s!"            uint32_t data = snap_data;\n" ++
  s!"            if (addr == TOHOST_ADDR) {lb}\n" ++
  s!"                ds.test_done = true;\n" ++
  s!"                ds.test_data = data;\n" ++
  (match cfg.putcharAddr with
   | some _ =>
     s!"            {rb} else if (addr == PUTCHAR_ADDR) {lb}\n" ++
     s!"                putchar(data & 0xFF);\n"
   | none => "") ++
  s!"            {rb} else {lb}\n" ++
  s!"                uint32_t widx = addr >> 2;\n" ++
  s!"                if (widx < MEM_SIZE_WORDS) {lb}\n" ++
  s!"                    // Byte-enable store based on size: 00=byte, 01=half, 10=word\n" ++
  s!"                    uint32_t size = snap_size;\n" ++
  s!"                    uint32_t cur = mem[widx];\n" ++
  s!"                    uint32_t byte_off = addr & 3;\n" ++
  s!"                    if (size == 0) {lb} // SB\n" ++
  s!"                        uint32_t shift = byte_off * 8;\n" ++
  s!"                        cur = (cur & ~(0xFFu << shift)) | ((data & 0xFF) << shift);\n" ++
  s!"                    {rb} else if (size == 1) {lb} // SH\n" ++
  s!"                        uint32_t shift = (byte_off & 2) * 8;\n" ++
  s!"                        cur = (cur & ~(0xFFFFu << shift)) | ((data & 0xFFFF) << shift);\n" ++
  s!"                    {rb} else {lb} // SW\n" ++
  s!"                        cur = data;\n" ++
  s!"                    {rb}\n" ++
  s!"                    mem[widx] = cur;\n" ++
  s!"                {rb}\n" ++
  s!"            {rb}\n" ++
  s!"        {rb} else {lb}\n" ++
  s!"            uint32_t ridx = addr >> 2;\n" ++
  s!"            ds.read_data = (ridx < MEM_SIZE_WORDS) ? mem[ridx] : 0;\n" ++
  s!"            ds.pending = true;\n" ++
  s!"        {rb}\n" ++
  s!"    {rb}\n" ++
  s!"{rb}\n\n" ++

  s!"int main(int argc, char* argv[]) {lb}\n" ++
  "    const char* elf_path = nullptr;\n" ++
  s!"    uint32_t timeout = TIMEOUT_CYCLES;\n" ++
  s!"    for (int i = 1; i < argc; i++) {lb}\n" ++
  "        if (strncmp(argv[i], \"+elf=\", 5) == 0) elf_path = argv[i] + 5;\n" ++
  "        if (strncmp(argv[i], \"+timeout=\", 9) == 0) timeout = atoi(argv[i] + 9);\n" ++
  s!"    {rb}\n\n" ++
  s!"    if (!elf_path) {lb}\n" ++
  "        fprintf(stderr, \"ERROR: No ELF file. Use +elf=path\\n\");\n" ++
  "        return 1;\n" ++
  s!"    {rb}\n\n" ++
  "    memset(mem, 0, sizeof(mem));\n" ++
  "    if (load_elf(elf_path, mem_write_cb) < 0) return 1;\n\n" ++

  "    // Create signals (all plain bool)\n" ++
  s!"    bool {resetName}_sig = false;\n" ++
  signalDecls ++ "\n\n" ++

  "    // Signal arrays for bus helpers\n" ++
  signalArrayDecls ++ "\n\n" ++

  "    // Port pointer array (order matches cpu_setup port binding)\n" ++
  s!"    bool* cpu_ports[] = {lb}{portPtrArray}{rb};\n\n" ++

  "    // Create and bind CPU via setup module\n" ++
  s!"    CpuCtx* ctx = cpu_create(\"u_cpu\", &{resetName}_sig,\n" ++
  s!"        cpu_ports, {portList.length});\n\n" ++

  "    // Constants\n" ++
  constBindings ++ "\n\n" ++

  "    // Memory model state\n" ++
  "    DmemState dmem_state;\n\n" ++

  "    // ========================================================================\n" ++
  "    // Manual simulation loop\n" ++
  "    // ========================================================================\n" ++
  "    printf(\"Simulation started (timeout=%u)\\n\", timeout);\n\n" ++

  "    // Helper lambda: settle combinational logic\n" ++
  s!"    auto settle = [&]() {lb}\n" ++
  s!"        for (int i = 0; i < 10; i++) {lb}\n" ++
  s!"            imem_update({pcSig}_sigs, {imemDataIn}_sigs);\n" ++
  s!"            cpu_eval_comb_all(ctx);\n" ++
  s!"        {rb}\n" ++
  s!"    {rb};\n\n" ++

  "    // Reset phase: hold reset high for 5 cycles\n" ++
  s!"    {resetName}_sig = true;\n" ++
  s!"    {dmemReady}_sig = true;\n" ++
  s!"    for (uint32_t cyc = 0; cyc < 5; cyc++) {lb}\n" ++
  "        cpu_eval_seq_sample_all(ctx);\n" ++
  "        cpu_eval_seq_all(ctx);\n" ++
  "        settle();\n" ++
  s!"    {rb}\n" ++
  s!"    {resetName}_sig = false;\n" ++
  "    settle();  // settle after de-asserting reset\n\n" ++

  "    // Main simulation loop\n" ++
  s!"    for (uint32_t cyc = 0; cyc < timeout; cyc++) {lb}\n" ++
  "        // 1. Snapshot dmem inputs (both always_ff blocks must see same pre-edge state)\n" ++
  s!"        bool snap_req_valid = {dmemValid}_sig;\n" ++
  s!"        bool snap_req_we = {dmemWe}_sig;\n" ++
  s!"        uint32_t snap_addr = 0;\n" ++
  s!"        for (int i = 0; i < 32; i++) snap_addr |= (*{dmemAddr}_sigs[i] ? 1u : 0u) << i;\n" ++
  s!"        uint32_t snap_data = 0;\n" ++
  s!"        for (int i = 0; i < 32; i++) snap_data |= (*{dmemDataOut}_sigs[i] ? 1u : 0u) << i;\n" ++
  s!"        uint32_t snap_size = 2;\n" ++
  (match dmemSize with
   | some sizeName => s!"        snap_size = (*{sizeName}_sigs[0] ? 1u : 0u) | (*{sizeName}_sigs[1] ? 2u : 0u);\n"
   | none => "") ++
  "\n" ++
  "        // 2. Two-phase DFF evaluation: sample all d inputs, then update all q outputs\n" ++
  "        cpu_eval_seq_sample_all(ctx);\n" ++
  "        cpu_eval_seq_all(ctx);\n\n" ++
  "        // 3. Process dmem with snapshotted inputs (registered response like SV always_ff)\n" ++
  s!"        dmem_tick(dmem_state,\n" ++
  s!"            snap_req_valid, snap_req_we, snap_addr, snap_data, snap_size,\n" ++
  s!"            {dmemReady}_sig, {dmemRespValid}_sig,\n" ++
  s!"            {dmemRespData}_sigs);\n\n" ++
  "        // 4. Settle combinational logic (imem + CPU comb)\n" ++
  "        settle();\n\n" ++
  "        // 5. Check for test completion\n" ++
  s!"        if (dmem_state.test_done) break;\n" ++
  s!"    {rb}\n\n" ++

  s!"    printf(\"\\nTEST %s\\n\", dmem_state.test_data == 1 ? \"PASS\" : \"FAIL\");\n" ++
  s!"    printf(\"tohost: 0x%08x\\n\", dmem_state.test_data);\n" ++
  "    cpu_delete(ctx);\n" ++
  s!"    return dmem_state.test_done ? 0 : 1;\n" ++
  s!"{rb}\n"

/-! ## Cache-Line Memory SV Testbench Generator -/

/-- Generate SV testbench for a cached CPU with 256-bit cache-line memory interface. -/
def toTestbenchSVCached (cfg : TestbenchConfig) : String :=
  let c := cfg.circuit
  let inputGroups := SystemVerilog.autoDetectSignalGroups c.inputs
  let outputGroups := SystemVerilog.autoDetectSignalGroups c.outputs

  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let _clockName := if clockWires.isEmpty then "clock" else Wire.name (List.head! clockWires)
  let resetName := if resetWires.isEmpty then "reset" else Wire.name (List.head! resetWires)

  let inputBusWireNames := inputGroups.flatMap (fun sg => sg.wires.map Wire.name)
  let outputBusWireNames := outputGroups.flatMap (fun sg => sg.wires.map Wire.name)

  let inputSignals : List (String × Nat) :=
    let scalars := c.inputs.filter (fun w => !inputBusWireNames.contains w.name)
    scalars.map (fun w => (w.name, 1)) ++ inputGroups.map (fun sg => (sg.name, sg.width))

  let outputSignals : List (String × Nat) :=
    let scalars := c.outputs.filter (fun w => !outputBusWireNames.contains w.name)
    scalars.map (fun w => (w.name, 1)) ++ outputGroups.map (fun sg => (sg.name, sg.width))

  let isSpecial (name : String) : Bool :=
    name == _clockName || name == resetName ||
    cfg.constantPorts.any (fun (cn, _) => cn == name)

  let mkDecl (name : String) (width : Nat) : String :=
    if width > 1 then s!"  logic [{width-1}:0] {name};"
    else s!"  logic        {name};"

  let signalDecls := String.intercalate "\n" (
    (inputSignals.filter (fun (n, _) => !isSpecial n)).map (fun (n, w) => mkDecl n w) ++
    (outputSignals.filter (fun (n, _) => !isSpecial n)).map (fun (n, w) => mkDecl n w)
  )

  let portConns := String.intercalate ",\n" (
    [s!"      .{_clockName}(clk)"] ++
    [s!"      .{resetName}({resetName})"] ++
    cfg.constantPorts.map (fun (name, value) =>
      s!"      .{name}(1'b{if value then "1" else "0"})") ++
    (inputSignals.filter (fun (n, _) => !isSpecial n)).map (fun (n, _) =>
      s!"      .{n}({n})") ++
    outputSignals.map (fun (n, _) =>
      s!"      .{n}({n})")
  )

  let clmp := cfg.cacheLineMemPort.getD {
    reqValidSignal := "mem_req_valid"
    reqAddrSignal := "mem_req_addr"
    reqWeSignal := "mem_req_we"
    reqDataSignal := "mem_req_data"
    respValidSignal := "mem_resp_valid"
    respDataSignal := "mem_resp_data"
  }

  let memSizeStr := toString cfg.memSizeWords
  let timeoutStr := toString cfg.timeoutCycles
  let tohostHex := hexLit 32 cfg.tohostAddr
  let putcharParam := match cfg.putcharAddr with
    | some addr => s!",\n    parameter PUTCHAR_ADDR    = {hexLit 32 addr}"
    | none => ""

  let tbName := optOrDefault cfg.tbName s!"tb_{c.name}"

  "//==============================================================================\n" ++
  s!"// {tbName}.sv - Auto-generated testbench for {c.name} (cache-line memory)\n" ++
  "//\n" ++
  "// Generated by Shoumei RTL testbench code generator.\n" ++
  "// DO NOT EDIT - regenerate with: lake exe generate_all\n" ++
  "//==============================================================================\n\n" ++

  s!"module {tbName} #(\n" ++
  s!"    parameter MEM_SIZE_WORDS = {memSizeStr},\n" ++
  s!"    parameter TIMEOUT_CYCLES = {timeoutStr},\n" ++
  s!"    parameter TOHOST_ADDR    = {tohostHex}\n" ++
  putcharParam ++
  ") (\n" ++
  "    input logic clk,\n" ++
  "    input logic rst_n,\n" ++
  "    // Test status\n" ++
  "    output logic        o_test_done,\n" ++
  "    output logic        o_test_pass,\n" ++
  "    output logic [31:0] o_test_code,\n" ++
  "    // Debug outputs\n" ++
  "    output logic [31:0] o_cycle_count,\n" ++
  "    output logic        o_rob_empty,\n" ++
  "    // Memory request observation\n" ++
  "    output logic        o_mem_req_valid,\n" ++
  "    output logic        o_mem_req_we,\n" ++
  "    output logic [31:0] o_mem_req_addr,\n" ++
  "    // HTIF\n" ++
  "    output logic [31:0] o_tohost,\n" ++
  "    // RVVI-TRACE outputs (dual-retire W=2 cosimulation)\n" ++
  "    output logic        o_rvvi_valid_0,\n" ++
  "    output logic        o_rvvi_valid_1,\n" ++
  "    output logic        o_rvvi_trap_0,\n" ++
  "    output logic        o_rvvi_trap_1,\n" ++
  "    output logic [31:0] o_rvvi_pc_rdata_0,\n" ++
  "    output logic [31:0] o_rvvi_pc_rdata_1,\n" ++
  "    output logic [31:0] o_rvvi_insn_0,\n" ++
  "    output logic [31:0] o_rvvi_insn_1,\n" ++
  "    output logic [4:0]  o_rvvi_rd_0,\n" ++
  "    output logic [4:0]  o_rvvi_rd_1,\n" ++
  "    output logic        o_rvvi_rd_valid_0,\n" ++
  "    output logic        o_rvvi_rd_valid_1,\n" ++
  "    output logic [31:0] o_rvvi_rd_data_0,\n" ++
  "    output logic [31:0] o_rvvi_rd_data_1\n" ++
  ");\n\n" ++

  "  // =========================================================================\n" ++
  "  // DUT I/O signals\n" ++
  "  // =========================================================================\n" ++
  signalDecls ++ "\n" ++
  s!"  logic        {resetName};\n" ++
  s!"  assign {resetName} = ~rst_n;\n\n" ++

  "  // =========================================================================\n" ++
  "  // DUT instance\n" ++
  "  // =========================================================================\n" ++
  s!"  {c.name} u_cpu (\n" ++
  portConns ++ "\n" ++
  "  );\n\n" ++

  "  // =========================================================================\n" ++
  "  // Memory: 256-bit cache-line interface, 1-cycle latency\n" ++
  "  // =========================================================================\n" ++
  "  logic [31:0] mem [0:MEM_SIZE_WORDS-1];\n\n" ++
  "  // DPI-C: allow C++ to write memory words before simulation starts\n" ++
  "  export \"DPI-C\" function dpi_mem_write;\n" ++
  "  function void dpi_mem_write(input int unsigned word_addr, input int unsigned data);\n" ++
  "    mem[word_addr] = data;\n" ++
  "  endfunction\n\n" ++
  "  // DPI-C: override HTIF address from ELF symbol\n" ++
  "  logic [31:0] tohost_addr_r;\n" ++
  "  initial tohost_addr_r = TOHOST_ADDR;\n" ++
  "  export \"DPI-C\" function dpi_set_tohost_addr;\n" ++
  "  function void dpi_set_tohost_addr(input int unsigned addr);\n" ++
  "    tohost_addr_r = addr;\n" ++
  "  endfunction\n\n" ++
  (match cfg.putcharAddr with
   | some _ =>
     "  logic [31:0] putchar_addr_r;\n" ++
     "  initial putchar_addr_r = PUTCHAR_ADDR;\n" ++
     "  export \"DPI-C\" function dpi_set_putchar_addr;\n" ++
     "  function void dpi_set_putchar_addr(input int unsigned addr);\n" ++
     "    putchar_addr_r = addr;\n" ++
     "  endfunction\n\n"
   | none => "") ++
  "  localparam logic [31:0] MEM_BASE = 32'h00000000;\n\n" ++
  "  function automatic logic [31:0] addr_to_idx(input logic [31:0] addr);\n" ++
  "    return (addr - MEM_BASE) >> 2;\n" ++
  "  endfunction\n\n" ++

  "  // --- Cache-line memory: 1-cycle read latency, combinational write ---\n" ++
  "  logic        mem_pending;\n" ++
  "  logic [255:0] mem_read_line;\n\n" ++
  s!"  always_ff @(posedge clk or posedge {resetName}) begin\n" ++
  s!"    if ({resetName}) begin\n" ++
  s!"      {clmp.respValidSignal} <= 1'b0;\n" ++
  "      mem_read_line  <= 256'b0;\n" ++
  "      mem_pending    <= 1'b0;\n" ++
  "    end else begin\n" ++
  "      mem_pending    <= 1'b0;\n" ++
  s!"      {clmp.respValidSignal} <= 1'b0;\n\n" ++
  s!"      if ({clmp.reqValidSignal}) begin\n" ++
  s!"        if ({clmp.reqWeSignal}) begin\n" ++
  "          // Write 8-word cache line (line-aligned address)\n" ++
  s!"          for (int w = 0; w < 8; w++) begin\n" ++
  s!"            mem[addr_to_idx({clmp.reqAddrSignal}) + w] <= {clmp.reqDataSignal}[w*32 +: 32];\n" ++
  "          end\n" ++
  "        end else begin\n" ++
  (if cfg.enableCLINT then
    let clintBaseHex := natToHexDigits cfg.clintBaseAddr
    s!"          if ({clmp.reqAddrSignal} >= 32'h{clintBaseHex} && {clmp.reqAddrSignal} < 32'h{clintBaseHex} + 32'h10000) begin\n" ++
    "            // CLINT MMIO read: return register values\n" ++
    "            for (int w = 0; w < 8; w++) begin\n" ++
    s!"              mem_read_line[w*32 +: 32] <= clint_read_word({clmp.reqAddrSignal} + w*4);\n" ++
    "            end\n" ++
    "            mem_pending <= 1'b1;\n" ++
    "          end else begin\n" ++
    "            // Normal memory read\n" ++
    "            for (int w = 0; w < 8; w++) begin\n" ++
    s!"              mem_read_line[w*32 +: 32] <= mem[addr_to_idx({clmp.reqAddrSignal}) + w];\n" ++
    "            end\n" ++
    "            mem_pending <= 1'b1;\n" ++
    "          end\n"
   else
    "          // Read 8-word cache line (line-aligned address)\n" ++
    "          for (int w = 0; w < 8; w++) begin\n" ++
    s!"            mem_read_line[w*32 +: 32] <= mem[addr_to_idx({clmp.reqAddrSignal}) + w];\n" ++
    "          end\n" ++
    "          mem_pending <= 1'b1;\n") ++
  "        end\n" ++
  "      end\n\n" ++
  "      if (mem_pending) begin\n" ++
  s!"        {clmp.respValidSignal} <= 1'b1;\n" ++
  "      end\n" ++
  "    end\n" ++
  "  end\n\n" ++
  s!"  assign {clmp.respDataSignal} = mem_read_line;\n\n" ++

  "  // =========================================================================\n" ++
  "  // HTIF: tohost termination (detected from CPU store snoop)\n" ++
  "  // =========================================================================\n" ++
  "  logic        test_done;\n" ++
  "  logic        test_pass;\n" ++
  "  logic [31:0] test_code;\n\n" ++
  "  // Monitor CPU store interface directly (bypasses cache hierarchy)\n" ++
  "  wire        tohost_store = store_snoop_valid && (store_snoop_addr == tohost_addr_r);\n\n" ++
  s!"  always_ff @(posedge clk or posedge {resetName}) begin\n" ++
  s!"    if ({resetName}) begin\n" ++
  "      test_done <= 1'b0;\n" ++
  "      test_pass <= 1'b0;\n" ++
  "      test_code <= 32'b0;\n" ++
  "    end else begin\n" ++
  "      if (tohost_store) begin\n" ++
  "        test_code <= store_snoop_data;\n" ++
  "        test_pass <= (store_snoop_data == 32'h1);\n" ++
  "        test_done <= 1'b1;\n" ++
  "      end\n" ++
  "    end\n" ++
  "  end\n\n" ++

  -- MMIO putchar: also monitor cache-line writes for putchar address
  (match cfg.putcharAddr with
   | some _ =>
     "  // =========================================================================\n" ++
     "  // MMIO putchar: monitor CPU store snoop for putchar address\n" ++
     "  // =========================================================================\n" ++
     "  wire putchar_store = store_snoop_valid && (store_snoop_addr == putchar_addr_r);\n" ++
     "  // Deduplicate: store_snoop may fire multiple cycles for one store (stall replays)\n" ++
     "  logic putchar_prev;\n\n" ++
     s!"  always_ff @(posedge clk) begin\n" ++
     s!"    if ({resetName}) begin\n" ++
     "      putchar_prev <= 1'b0;\n" ++
     "    end else begin\n" ++
     "      if (putchar_store && !putchar_prev)\n" ++
     "        $write(\"%c\", store_snoop_data[7:0]);\n" ++
     "      putchar_prev <= putchar_store;\n" ++
     "    end\n" ++
     "  end\n\n"
   | none => "") ++

  "  // =========================================================================\n" ++
  "  // Cycle counter\n" ++
  "  // =========================================================================\n" ++
  "  logic [31:0] cycle_count;\n\n" ++
  s!"  always_ff @(posedge clk or posedge {resetName}) begin\n" ++
  s!"    if ({resetName}) begin\n" ++
  "      cycle_count <= 32'b0;\n" ++
  "    end else begin\n" ++
  "      cycle_count <= cycle_count + 1;\n" ++
  "    end\n" ++
  "  end\n\n" ++

  (if cfg.enableCLINT then
    let clintBase := cfg.clintBaseAddr
    let clintBaseHex := natToHexDigits clintBase
    "  // =========================================================================\n" ++
    "  // CLINT Timer Peripheral (mtime + mtimecmp + mtip)\n" ++
    "  // Standard RISC-V CLINT at CLINT_BASE:\n" ++
    "  //   +0x4000: mtimecmp_lo  +0x4004: mtimecmp_hi\n" ++
    "  //   +0xBFF8: mtime_lo     +0xBFFC: mtime_hi\n" ++
    "  // =========================================================================\n" ++
    s!"  localparam logic [31:0] CLINT_BASE = 32'h{clintBaseHex};\n" ++
    "  logic [63:0] mtime;\n" ++
    "  logic [63:0] mtimecmp;\n" ++
    "  logic        mtip;\n\n" ++
    "  assign mtip = (mtime >= mtimecmp);\n" ++
    "  assign mtip_in = mtip;\n\n" ++
    s!"  always_ff @(posedge clk or posedge {resetName}) begin\n" ++
    s!"    if ({resetName}) begin\n" ++
    "      mtime    <= 64'b0;\n" ++
    "      mtimecmp <= 64'hFFFFFFFF_FFFFFFFF;\n" ++
    "    end else begin\n" ++
    "      mtime <= mtime + 64'd1;\n" ++
    "      // Store-snoop writes to CLINT registers\n" ++
    "      if (store_snoop_valid) begin\n" ++
    "        case (store_snoop_addr)\n" ++
    "          CLINT_BASE + 32'h4000: mtimecmp[31:0]  <= store_snoop_data;\n" ++
    "          CLINT_BASE + 32'h4004: mtimecmp[63:32] <= store_snoop_data;\n" ++
    "          // mtime writes (optional, some impls allow SW reset)\n" ++
    "          CLINT_BASE + 32'hBFF8: mtime[31:0]     <= store_snoop_data;\n" ++
    "          CLINT_BASE + 32'hBFFC: mtime[63:32]    <= store_snoop_data;\n" ++
    "          default: ;\n" ++
    "        endcase\n" ++
    "      end\n" ++
    "    end\n" ++
    "  end\n\n" ++
    "  // CLINT cache-line read: return register values when address is in CLINT range\n" ++
    "  function automatic logic [31:0] clint_read_word(input logic [31:0] addr);\n" ++
    "    case (addr)\n" ++
    "      CLINT_BASE + 32'h4000: return mtimecmp[31:0];\n" ++
    "      CLINT_BASE + 32'h4004: return mtimecmp[63:32];\n" ++
    "      CLINT_BASE + 32'hBFF8: return mtime[31:0];\n" ++
    "      CLINT_BASE + 32'hBFFC: return mtime[63:32];\n" ++
    "      default:               return 32'b0;\n" ++
    "    endcase\n" ++
    "  endfunction\n\n"
   else
    "  assign mtip_in = 1'b0;  // No CLINT, tie interrupt low\n\n") ++

  "  // =========================================================================\n" ++
  "  // Output assignments\n" ++
  "  // =========================================================================\n" ++
  "  assign o_test_done       = test_done;\n" ++
  "  assign o_test_pass       = test_pass;\n" ++
  "  assign o_test_code       = test_code;\n" ++
  "  assign o_cycle_count     = cycle_count;\n" ++
  "  assign o_rob_empty       = rob_empty;\n" ++
  s!"  assign o_mem_req_valid  = {clmp.reqValidSignal};\n" ++
  s!"  assign o_mem_req_we     = {clmp.reqWeSignal};\n" ++
  s!"  assign o_mem_req_addr   = {clmp.reqAddrSignal};\n" ++
  "  assign o_tohost          = test_code;\n" ++
  "  assign o_rvvi_valid_0    = rvvi_validS0;\n" ++
  "  assign o_rvvi_valid_1    = rvvi_validS1;\n" ++
  "  assign o_rvvi_trap_0     = rvvi_trapS0;\n" ++
  "  assign o_rvvi_trap_1     = rvvi_trapS1;\n" ++
  "  assign o_rvvi_pc_rdata_0 = rvvi_pc_0;\n" ++
  "  assign o_rvvi_pc_rdata_1 = rvvi_pc_1;\n" ++
  "  assign o_rvvi_insn_0     = rvvi_insn_0;\n" ++
  "  assign o_rvvi_insn_1     = rvvi_insn_1;\n" ++
  "  assign o_rvvi_rd_0       = rvvi_rd_0;\n" ++
  "  assign o_rvvi_rd_1       = rvvi_rd_1;\n" ++
  "  assign o_rvvi_rd_valid_0 = rvvi_rd_validS0;\n" ++
  "  assign o_rvvi_rd_valid_1 = rvvi_rd_validS1;\n" ++
  "  assign o_rvvi_rd_data_0  = rvvi_rdd_0;\n" ++
  "  assign o_rvvi_rd_data_1  = rvvi_rdd_1;\n\n" ++
  "endmodule\n"

/-! ## Verilator sim_main.cpp Generator -/

/-- Generate sim_main.cpp for Verilator simulation, templated on testbench config. -/
def toSimMainCpp (cfg : TestbenchConfig) : String :=
  let tbName := optOrDefault cfg.tbName s!"tb_{cfg.circuit.name}"
  let vType := s!"V{tbName}"
  let isCached := cfg.cacheLineMemPort.isSome
  let lb := "{"
  let rb := "}"

  "//==============================================================================\n" ++
  s!"// sim_main_{tbName}.cpp - Auto-generated Verilator testbench driver\n" ++
  "// DO NOT EDIT - regenerate with: lake exe generate_all\n" ++
  "//==============================================================================\n\n" ++
  "#include <cstdio>\n" ++
  "#include <cstdlib>\n" ++
  "#include <cstring>\n" ++
  "#include <memory>\n" ++
  "#include <elf.h>\n\n" ++
  "static struct _StdoutUnbuffer " ++ lb ++ "\n" ++
  "    _StdoutUnbuffer() " ++ lb ++ " setvbuf(stdout, nullptr, _IONBF, 0); " ++ rb ++ "\n" ++
  rb ++ " _stdout_unbuffer;\n\n" ++
  s!"#include \"{vType}.h\"\n" ++
  "#include \"verilated.h\"\n" ++
  "#include \"svdpi.h\"\n\n" ++
  "#if VM_TRACE\n" ++
  "#include \"verilated_fst_c.h\"\n" ++
  "#endif\n\n" ++
  "extern \"C\" void dpi_mem_write(unsigned int word_addr, unsigned int data);\n" ++
  "extern \"C\" void dpi_set_tohost_addr(unsigned int addr);\n" ++
  (if cfg.putcharAddr.isSome then
    "extern \"C\" void dpi_set_putchar_addr(unsigned int addr);\n"
   else "") ++
  "\nstatic const uint32_t DEFAULT_TIMEOUT = " ++ toString cfg.timeoutCycles ++ ";\n\n" ++

  "static const char* get_plusarg(int argc, char** argv, const char* name) " ++ lb ++ "\n" ++
  "    size_t len = strlen(name);\n" ++
  "    for (int i = 1; i < argc; i++)\n" ++
  "        if (strncmp(argv[i], name, len) == 0 && argv[i][len] == '=')\n" ++
  "            return argv[i] + len + 1;\n" ++
  "    return nullptr;\n" ++
  rb ++ "\n\n" ++
  "static bool has_plusarg(int argc, char** argv, const char* name) " ++ lb ++ "\n" ++
  "    for (int i = 1; i < argc; i++)\n" ++
  "        if (strcmp(argv[i], name) == 0) return true;\n" ++
  "    return false;\n" ++
  rb ++ "\n\n" ++

  -- ELF symbol lookup
  "static int64_t elf_lookup_symbol(const char* path, const char* sym_name) " ++ lb ++ "\n" ++
  "    FILE* f = fopen(path, \"rb\");\n" ++
  "    if (!f) return -1;\n" ++
  "    Elf32_Ehdr ehdr;\n" ++
  "    if (fread(&ehdr, sizeof(ehdr), 1, f) != 1) " ++ lb ++ " fclose(f); return -1; " ++ rb ++ "\n" ++
  "    for (int i = 0; i < ehdr.e_shnum; i++) " ++ lb ++ "\n" ++
  "        Elf32_Shdr shdr;\n" ++
  "        fseek(f, ehdr.e_shoff + i * ehdr.e_shentsize, SEEK_SET);\n" ++
  "        if (fread(&shdr, sizeof(shdr), 1, f) != 1) continue;\n" ++
  "        if (shdr.sh_type != SHT_SYMTAB) continue;\n" ++
  "        Elf32_Shdr strhdr;\n" ++
  "        fseek(f, ehdr.e_shoff + shdr.sh_link * ehdr.e_shentsize, SEEK_SET);\n" ++
  "        if (fread(&strhdr, sizeof(strhdr), 1, f) != 1) continue;\n" ++
  "        auto* strtab = new char[strhdr.sh_size];\n" ++
  "        fseek(f, strhdr.sh_offset, SEEK_SET);\n" ++
  "        if (fread(strtab, 1, strhdr.sh_size, f) != strhdr.sh_size) " ++ lb ++ " delete[] strtab; continue; " ++ rb ++ "\n" ++
  "        int nsyms = shdr.sh_size / shdr.sh_entsize;\n" ++
  "        for (int j = 0; j < nsyms; j++) " ++ lb ++ "\n" ++
  "            Elf32_Sym sym;\n" ++
  "            fseek(f, shdr.sh_offset + j * shdr.sh_entsize, SEEK_SET);\n" ++
  "            if (fread(&sym, sizeof(sym), 1, f) != 1) continue;\n" ++
  "            if (sym.st_name < strhdr.sh_size && strcmp(strtab + sym.st_name, sym_name) == 0) " ++ lb ++ "\n" ++
  "                delete[] strtab; fclose(f); return (int64_t)sym.st_value;\n" ++
  "            " ++ rb ++ "\n" ++
  "        " ++ rb ++ "\n" ++
  "        delete[] strtab;\n" ++
  "    " ++ rb ++ "\n" ++
  "    fclose(f);\n" ++
  "    return -1;\n" ++
  rb ++ "\n\n" ++

  -- ELF loader
  "static int load_elf(const char* path) " ++ lb ++ "\n" ++
  "    FILE* f = fopen(path, \"rb\");\n" ++
  "    if (!f) " ++ lb ++ " fprintf(stderr, \"ERROR: Cannot open ELF: %s\\n\", path); return -1; " ++ rb ++ "\n" ++
  "    Elf32_Ehdr ehdr;\n" ++
  "    if (fread(&ehdr, sizeof(ehdr), 1, f) != 1) " ++ lb ++ " fclose(f); return -1; " ++ rb ++ "\n" ++
  "    if (memcmp(ehdr.e_ident, ELFMAG, SELFMAG) != 0 || ehdr.e_ident[EI_CLASS] != ELFCLASS32) " ++ lb ++ "\n" ++
  "        fprintf(stderr, \"ERROR: Not a valid 32-bit ELF\\n\"); fclose(f); return -1;\n" ++
  "    " ++ rb ++ "\n" ++
  "    uint32_t total = 0;\n" ++
  "    for (int i = 0; i < ehdr.e_phnum; i++) " ++ lb ++ "\n" ++
  "        Elf32_Phdr phdr;\n" ++
  "        fseek(f, ehdr.e_phoff + i * ehdr.e_phentsize, SEEK_SET);\n" ++
  "        if (fread(&phdr, sizeof(phdr), 1, f) != 1) continue;\n" ++
  "        if (phdr.p_type != PT_LOAD || phdr.p_memsz == 0) continue;\n" ++
  "        for (uint32_t off = 0; off < phdr.p_memsz; off += 4)\n" ++
  "            dpi_mem_write((phdr.p_paddr + off) / 4, 0);\n" ++
  "        if (phdr.p_filesz > 0) " ++ lb ++ "\n" ++
  "            fseek(f, phdr.p_offset, SEEK_SET);\n" ++
  "            uint32_t words = (phdr.p_filesz + 3) / 4;\n" ++
  "            for (uint32_t w = 0; w < words; w++) " ++ lb ++ "\n" ++
  "                uint32_t word = 0;\n" ++
  "                uint32_t rem = phdr.p_filesz - w * 4;\n" ++
  "                (void)fread(&word, 1, rem < 4 ? rem : 4, f);\n" ++
  "                dpi_mem_write((phdr.p_paddr / 4) + w, word);\n" ++
  "            " ++ rb ++ "\n" ++
  "        " ++ rb ++ "\n" ++
  "        printf(\"  PT_LOAD: paddr=0x%08x filesz=%u memsz=%u\\n\", phdr.p_paddr, phdr.p_filesz, phdr.p_memsz);\n" ++
  "        total += phdr.p_memsz;\n" ++
  "    " ++ rb ++ "\n" ++
  "    fclose(f);\n" ++
  "    printf(\"Loaded ELF %s (%u bytes)\\n\", path, total);\n" ++
  "    return (int)total;\n" ++
  rb ++ "\n\n" ++

  s!"int main(int argc, char** argv) {lb}\n" ++
  "    Verilated::commandArgs(argc, argv);\n" ++
  s!"    auto dut = std::make_unique<{vType}>();\n\n" ++
  "    const char* elf_path = get_plusarg(argc, argv, \"+elf\");\n" ++
  "    const char* timeout_str = get_plusarg(argc, argv, \"+timeout\");\n" ++
  "    bool do_trace = has_plusarg(argc, argv, \"+trace\");\n" ++
  "    bool verbose = has_plusarg(argc, argv, \"+verbose\");\n" ++
  "    uint32_t timeout = timeout_str ? atoi(timeout_str) : DEFAULT_TIMEOUT;\n\n" ++
  "#if VM_TRACE\n" ++
  "    VerilatedFstC* trace = nullptr;\n" ++
  "    if (do_trace) " ++ lb ++ "\n" ++
  "        Verilated::traceEverOn(true);\n" ++
  "        trace = new VerilatedFstC;\n" ++
  "        dut->trace(trace, 99);\n" ++
  s!"        trace->open(\"{tbName}.fst\");\n" ++
  "    " ++ rb ++ "\n" ++
  "#else\n" ++
  "    (void)do_trace;\n" ++
  "#endif\n\n" ++
  "    if (!elf_path) " ++ lb ++ "\n" ++
  "        fprintf(stderr, \"ERROR: No ELF file. Use +elf=path\\n\");\n" ++
  "        return 1;\n" ++
  "    " ++ rb ++ "\n\n" ++
  s!"    svSetScope(svGetScopeFromName(\"TOP.{tbName}\"));\n" ++
  "    if (load_elf(elf_path) < 0) return 1;\n\n" ++
  "    // Reset (must happen before DPI overrides — initial blocks run during eval)\n" ++
  "    dut->rst_n = 0; dut->clk = 0;\n" ++
  "    for (int i = 0; i < 10; i++) " ++ lb ++ "\n" ++
  "        dut->clk = !dut->clk; dut->eval();\n" ++
  "#if VM_TRACE\n" ++
  "        if (trace) trace->dump(i);\n" ++
  "#endif\n" ++
  "    " ++ rb ++ "\n" ++
  "    dut->rst_n = 1;\n\n" ++
  "    // Override HTIF addresses from ELF symbols (after reset so initial blocks don't overwrite)\n" ++
  "    int64_t tohost_sym = elf_lookup_symbol(elf_path, \"tohost\");\n" ++
  "    if (tohost_sym >= 0) " ++ lb ++ "\n" ++
  "        printf(\"ELF symbol: tohost = 0x%08x\\n\", (uint32_t)tohost_sym);\n" ++
  "        dpi_set_tohost_addr((uint32_t)tohost_sym);\n" ++
  "    " ++ rb ++ "\n" ++
  (if cfg.putcharAddr.isSome then
    "    int64_t putchar_sym = elf_lookup_symbol(elf_path, \"putchar_addr\");\n" ++
    "    if (putchar_sym >= 0) " ++ lb ++ "\n" ++
    "        printf(\"ELF symbol: putchar_addr = 0x%08x\\n\", (uint32_t)putchar_sym);\n" ++
    "        dpi_set_putchar_addr((uint32_t)putchar_sym);\n" ++
    "    " ++ rb ++ "\n"
   else "") ++
  "\n" ++
  "#if VM_TRACE\n" ++
  "    uint64_t sim_time = 10;\n" ++
  "#endif\n" ++
  "    uint32_t cycle = 0, retired = 0;\n" ++
  "    bool done = false;\n\n" ++
  "    printf(\"Simulation started (timeout=%u cycles)\\n\", timeout);\n" ++
  "    printf(\"─────────────────────────────────────────────\\n\");\n\n" ++
  "    while (!done && cycle < timeout && !Verilated::gotFinish()) " ++ lb ++ "\n" ++
  "        dut->clk = 1; dut->eval();\n" ++
  "#if VM_TRACE\n" ++
  "        if (trace) trace->dump(sim_time++);\n" ++
  "#endif\n\n" ++
  "        // Dual-retire RVVI (W=2)\n" ++
  "        if (dut->o_rvvi_valid_0) " ++ lb ++ "\n" ++
  "            retired++;\n" ++
  "            if (verbose)\n" ++
  "                printf(\"  RET0[%u] PC=0x%08x insn=0x%08x rd=x%u(%d) data=0x%08x\\n\",\n" ++
  "                    retired, dut->o_rvvi_pc_rdata_0, dut->o_rvvi_insn_0,\n" ++
  "                    dut->o_rvvi_rd_0, (int)dut->o_rvvi_rd_valid_0, dut->o_rvvi_rd_data_0);\n" ++
  "        " ++ rb ++ "\n" ++
  "        if (dut->o_rvvi_valid_1) " ++ lb ++ "\n" ++
  "            retired++;\n" ++
  "            if (verbose)\n" ++
  "                printf(\"  RET1[%u] PC=0x%08x insn=0x%08x rd=x%u(%d) data=0x%08x\\n\",\n" ++
  "                    retired, dut->o_rvvi_pc_rdata_1, dut->o_rvvi_insn_1,\n" ++
  "                    dut->o_rvvi_rd_1, (int)dut->o_rvvi_rd_valid_1, dut->o_rvvi_rd_data_1);\n" ++
  "        " ++ rb ++ "\n\n" ++
  (if !isCached then
    "        if (verbose && dut->o_dmem_req_valid)\n" ++
    "            printf(\"  %s cy%u addr=0x%08x data=0x%08x\\n\",\n" ++
    "                dut->o_dmem_req_we ? \"STORE\" : \"LOAD \",\n" ++
    "                cycle, dut->o_dmem_req_addr, dut->o_dmem_req_data);\n\n"
   else
    "        if (verbose && dut->o_mem_req_valid)\n" ++
    "            printf(\"  %s cy%u addr=0x%08x\\n\",\n" ++
    "                dut->o_mem_req_we ? \"WB   \" : \"FETCH\", cycle, dut->o_mem_req_addr);\n\n") ++
  "        if (dut->o_test_done) " ++ lb ++ "\n" ++
  "            done = true;\n" ++
  "            printf(\"\\n══════ TEST %s ══════\\n\", dut->o_test_pass ? \"PASS\" : \"FAIL\");\n" ++
  "            if (!dut->o_test_pass) printf(\"  test_num:  %u\\n\", dut->o_test_code >> 1);\n" ++
  "            printf(\"  Cycle:     %u\\n\", cycle);\n" ++
  "            printf(\"  Retired:   %u\\n\", retired);\n" ++
  "            printf(\"  IPC:       %.3f\\n\", cycle > 0 ? (double)retired / cycle : 0.0);\n" ++
  "            printf(\"  tohost:    0x%08x\\n\", dut->o_test_code);\n" ++
  "        " ++ rb ++ "\n\n" ++
  "        dut->clk = 0; dut->eval();\n" ++
  "#if VM_TRACE\n" ++
  "        if (trace) trace->dump(sim_time++);\n" ++
  "#endif\n" ++
  "        cycle++;\n" ++
  "        if (cycle % 10000 == 0)\n" ++
  "            printf(\"  [%u cycles]\\n\", cycle);\n" ++
  "    " ++ rb ++ "\n\n" ++
  "    if (!done) " ++ lb ++ "\n" ++
  "        printf(\"\\n══════ TIMEOUT ══════\\n\");\n" ++
  "        printf(\"  Cycle: %u  rob_empty: %d\\n\", cycle, dut->o_rob_empty);\n" ++
  "    " ++ rb ++ "\n" ++
  "    printf(\"─────────────────────────────────────────────\\n\");\n" ++
  "    printf(\"Total cycles: %u\\n\", cycle);\n" ++
  "    printf(\"Total retired: %u\\n\", retired);\n" ++
  "    printf(\"IPC: %.3f\\n\", cycle > 0 ? (double)retired / cycle : 0.0);\n\n" ++
  "#if VM_TRACE\n" ++
  "    if (trace) " ++ lb ++ " trace->close(); delete trace; " ++ rb ++ "\n" ++
  "#endif\n" ++
  "    dut->final();\n" ++
  "    return done && dut->o_test_pass ? 0 : 1;\n" ++
  rb ++ "\n"

/-! ## LeanSim Generator (replaces hand-written cppsim_oracle) -/

/-- Generate lean_sim header for a given testbench config. -/
def toLeanSimH (cfg : TestbenchConfig) : String :=
  let c := cfg.circuit
  let isCached := cfg.cacheLineMemPort.isSome
  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let resetName := if resetWires.isEmpty then "reset" else Wire.name (List.head! resetWires)
  let lb := "{"
  let rb := "}"

  -- Build signal member declarations from circuit ports
  let groups := SystemVerilog.autoDetectSignalGroups (c.inputs ++ c.outputs)
  let busWireNames : List String :=
    groups.flatMap (fun sg => sg.wires.map Wire.name)

  -- All ports minus reset
  let allPorts := c.inputs ++ c.outputs
  let portList := allPorts.filter fun w => w.name != resetName

  -- Scalar signals (not in any bus, not clock/constant)
  let isSpecial (name : String) : Bool :=
    (clockWires.any fun cw => cw.name == name) ||
    name == resetName ||
    cfg.constantPorts.any (fun (cn, _) => cn == name)

  let scalarPorts := portList.filter fun w =>
    !busWireNames.contains w.name && !isSpecial w.name
  let scalarDecls := String.intercalate "\n" (
    scalarPorts.map fun w => s!"    bool {w.name}_ = false;")

  -- Bus signal declarations
  let busDecls := String.intercalate "\n" (
    groups.map fun sg => s!"    bool {sg.name}_[{sg.width}] = {lb}{rb};")

  -- Bus pointer array declarations (for read_bus/write_bus)
  let busPtrDecls := String.intercalate "\n" (
    groups.map fun sg => s!"    bool* {sg.name}_sigs_[{sg.width}];")

  "// Auto-generated Lean gate-level simulation. DO NOT EDIT.\n" ++
  s!"// Generated from circuit: {c.name}\n" ++
  s!"#pragma once\n\n" ++
  "#include <cstdint>\n" ++
  "#include <string>\n\n" ++
  s!"#include \"cpu_setup_{c.name}.h\"\n" ++
  "#include \"elf_loader.h\"\n\n" ++
  s!"struct LeanSimStepResult {lb}\n" ++
  "    uint32_t pc;\n" ++
  "    uint32_t insn;\n" ++
  "    uint32_t rd;\n" ++
  "    uint32_t rd_data;\n" ++
  "    bool     rd_valid;\n" ++
  "    uint32_t frd;\n" ++
  "    uint32_t frd_data;\n" ++
  "    bool     frd_valid;\n" ++
  "    uint32_t fflags;\n" ++
  "    bool     done;\n" ++
  "    uint32_t tohost;\n" ++
  s!"{rb};\n\n" ++
  s!"class LeanSim {lb}\n" ++
  "public:\n" ++
  "    explicit LeanSim(const std::string& elf_path);\n" ++
  "    ~LeanSim();\n" ++
  "    LeanSimStepResult step();\n\n" ++
  "private:\n" ++
  "    static constexpr uint32_t MEM_SIZE_WORDS = " ++ toString cfg.memSizeWords ++ ";\n" ++
  "    uint32_t mem_[MEM_SIZE_WORDS] = " ++ lb ++ rb ++ ";\n" ++
  "    CpuCtx* ctx_ = nullptr;\n\n" ++
  "    // Special signals\n" ++
  "    bool clock_sig_ = false;\n" ++
  "    bool reset_sig_ = false;\n" ++
  (String.intercalate "\n" (
    cfg.constantPorts.map fun (name, val) =>
      s!"    bool {name}_sig_ = {if val then "true" else "false"};")) ++ "\n\n" ++
  "    // Scalar signals\n" ++
  scalarDecls ++ "\n\n" ++
  "    // Bus signals\n" ++
  busDecls ++ "\n\n" ++
  "    // Bus pointer arrays\n" ++
  busPtrDecls ++ "\n\n" ++
  (if !isCached then
    "    // Dmem state\n" ++
    "    bool dmem_pending_ = false;\n" ++
    "    uint32_t dmem_read_data_ = 0;\n"
   else
    "    // Cache-line memory state\n" ++
    "    bool mem_pending_ = false;\n" ++
    "    uint32_t mem_read_line_[8] = " ++ lb ++ rb ++ ";\n") ++
  "    bool test_done_ = false;\n" ++
  "    uint32_t test_data_ = 0;\n" ++
  "    uint32_t cycle_ = 0;\n" ++
  "    static constexpr uint32_t MAX_CYCLES = 200000;\n\n" ++
  "    uint32_t read_bus(bool** sigs, int bits);\n" ++
  "    void write_bus(bool** sigs, uint32_t val, int bits);\n" ++
  (if !isCached then
    "    void imem_update();\n" ++
    "    void dmem_tick(bool req_valid, bool req_we, uint32_t addr, uint32_t data, uint32_t size);\n"
   else
    "    void mem_tick(bool req_valid, bool req_we, uint32_t addr, uint32_t* data_line);\n") ++
  "    void settle();\n" ++
  s!"{rb};\n"

/-- Generate lean_sim cpp for a given testbench config. -/
def toLeanSimCpp (cfg : TestbenchConfig) : String :=
  let c := cfg.circuit
  let isCached := cfg.cacheLineMemPort.isSome
  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let resetName := if resetWires.isEmpty then "reset" else Wire.name (List.head! resetWires)
  let lb := "{"
  let rb := "}"

  -- Build port list (same as toCpuSetupCpp: exclude reset only)
  let allPorts := c.inputs ++ c.outputs
  let portList := allPorts.filter fun w =>
    w.name != resetName

  -- Detect signal groups to distinguish bus wires from scalar wires
  let groups := SystemVerilog.autoDetectSignalGroups (c.inputs ++ c.outputs)
  let busWireMap : List (String × String × Nat) :=
    groups.flatMap fun sg =>
      sg.wires.enum.map fun ⟨i, w⟩ => (w.name, sg.name, i)

  -- Generate the port pointer array entries with correct signal variable names
  let portPtrEntries := String.intercalate ",\n" (
    portList.map fun w =>
      let wireName := w.name
      -- Clock -> &clock_sig_
      if (clockWires.any fun cw => cw.name == wireName) then
        "        &clock_sig_"
      -- Constants -> &{name}_sig_
      else if cfg.constantPorts.any (fun (cn, _) => cn == wireName) then
        s!"        &{wireName}_sig_"
      -- Bus signals: look up in signal groups
      else match busWireMap.find? (fun (wn, _, _) => wn == wireName) with
        | some (_, baseName, idx) => s!"        &{baseName}_[{idx}]"
        | none => s!"        &{wireName}_"
  )

  s!"// Auto-generated Lean gate-level simulation. DO NOT EDIT.\n" ++
  s!"// Generated from circuit: {c.name}\n" ++
  s!"#include \"lean_sim_{c.name}.h\"\n" ++
  s!"#include \"cpu_setup_{c.name}.h\"\n" ++
  "#include \"elf_loader.h\"\n" ++
  "#include <cstring>\n" ++
  "#include <cstdio>\n\n" ++

  "// ============================================================================\n" ++
  "// Bus helpers\n" ++
  "// ============================================================================\n\n" ++
  s!"uint32_t LeanSim::read_bus(bool** sigs, int bits) {lb}\n" ++
  "    uint32_t v = 0;\n" ++
  "    for (int i = 0; i < bits; i++)\n" ++
  "        v |= (*sigs[i] ? 1u : 0u) << i;\n" ++
  "    return v;\n" ++
  s!"{rb}\n\n" ++
  s!"void LeanSim::write_bus(bool** sigs, uint32_t val, int bits) {lb}\n" ++
  "    for (int i = 0; i < bits; i++)\n" ++
  "        *sigs[i] = (val >> i) & 1;\n" ++
  s!"{rb}\n\n" ++

  "// ============================================================================\n" ++
  "// Memory models\n" ++
  "// ============================================================================\n\n" ++

  (if !isCached then
    -- Non-cached: imem + dmem
    "static constexpr uint32_t TOHOST_ADDR = 0x" ++ natToHexDigits cfg.tohostAddr ++ ";\n" ++
    (match cfg.putcharAddr with
     | some addr => "static constexpr uint32_t PUTCHAR_ADDR = 0x" ++ natToHexDigits addr ++ ";\n"
     | none => "") ++
    "\n" ++
    s!"void LeanSim::imem_update() {lb}\n" ++
    "    uint32_t pc = read_bus(fetch_pc_sigs_, 32);\n" ++
    "    uint32_t widx = pc / 4;\n" ++
    "    uint32_t word = (widx < MEM_SIZE_WORDS) ? mem_[widx] : 0;\n" ++
    "    write_bus(imem_resp_data_sigs_, word, 32);\n" ++
    s!"{rb}\n\n" ++
    s!"void LeanSim::dmem_tick(bool req_valid, bool req_we,\n" ++
    s!"                          uint32_t addr, uint32_t data, uint32_t size) {lb}\n" ++
    "    dmem_req_ready_ = true;\n\n" ++
    "    if (dmem_pending_) " ++ lb ++ "\n" ++
    "        dmem_resp_valid_ = true;\n" ++
    "        write_bus(dmem_resp_data_sigs_, dmem_read_data_, 32);\n" ++
    "        dmem_pending_ = false;\n" ++
    "    " ++ rb ++ " else " ++ lb ++ "\n" ++
    "        dmem_resp_valid_ = false;\n" ++
    "        write_bus(dmem_resp_data_sigs_, dmem_read_data_, 32);\n" ++
    "    " ++ rb ++ "\n\n" ++
    "    if (req_valid) " ++ lb ++ "\n" ++
    "        if (req_we) " ++ lb ++ "\n" ++
    "            if (addr == TOHOST_ADDR) " ++ lb ++ "\n" ++
    "                test_done_ = true;\n" ++
    "                test_data_ = data;\n" ++
    (match cfg.putcharAddr with
     | some _ =>
       "            " ++ rb ++ " else if (addr == PUTCHAR_ADDR) " ++ lb ++ "\n" ++
       "                putchar(data & 0xFF);\n"
     | none => "") ++
    "            " ++ rb ++ " else " ++ lb ++ "\n" ++
    "                uint32_t widx = addr / 4;\n" ++
    "                if (widx < MEM_SIZE_WORDS) " ++ lb ++ "\n" ++
    "                    uint32_t cur = mem_[widx];\n" ++
    "                    uint32_t byte_off = addr & 3;\n" ++
    "                    if (size == 0) " ++ lb ++ " // SB\n" ++
    "                        uint32_t shift = byte_off * 8;\n" ++
    "                        cur = (cur & ~(0xFFu << shift)) | ((data & 0xFF) << shift);\n" ++
    "                    " ++ rb ++ " else if (size == 1) " ++ lb ++ " // SH\n" ++
    "                        uint32_t shift = (byte_off & 2) * 8;\n" ++
    "                        cur = (cur & ~(0xFFFFu << shift)) | ((data & 0xFFFF) << shift);\n" ++
    "                    " ++ rb ++ " else " ++ lb ++ " // SW\n" ++
    "                        cur = data;\n" ++
    "                    " ++ rb ++ "\n" ++
    "                    mem_[widx] = cur;\n" ++
    "                " ++ rb ++ "\n" ++
    "            " ++ rb ++ "\n" ++
    "        " ++ rb ++ " else " ++ lb ++ "\n" ++
    "            uint32_t ridx = addr / 4;\n" ++
    "            dmem_read_data_ = (ridx < MEM_SIZE_WORDS) ? mem_[ridx] : 0;\n" ++
    "            dmem_pending_ = true;\n" ++
    "        " ++ rb ++ "\n" ++
    "    " ++ rb ++ "\n" ++
    s!"{rb}\n\n" ++
    s!"void LeanSim::settle() {lb}\n" ++
    "    for (int i = 0; i < 10; i++) " ++ lb ++ "\n" ++
    "        imem_update();\n" ++
    "        cpu_eval_comb_all(ctx_);\n" ++
    "    " ++ rb ++ "\n" ++
    s!"{rb}\n\n"
   else
    -- Cached: cache-line memory
    "static constexpr uint32_t TOHOST_ADDR = 0x" ++ natToHexDigits cfg.tohostAddr ++ ";\n" ++
    (match cfg.putcharAddr with
     | some addr => "static constexpr uint32_t PUTCHAR_ADDR = 0x" ++ natToHexDigits addr ++ ";\n"
     | none => "") ++
    "\n" ++
    s!"void LeanSim::mem_tick(bool req_valid, bool req_we,\n" ++
    s!"                        uint32_t addr, uint32_t* data_line) {lb}\n" ++
    "    if (mem_pending_) " ++ lb ++ "\n" ++
    "        mem_resp_valid_ = true;\n" ++
    "        for (int w = 0; w < 8; w++)\n" ++
    "            write_bus(&mem_resp_data_sigs_[w * 32], mem_read_line_[w], 32);\n" ++
    "        mem_pending_ = false;\n" ++
    "    " ++ rb ++ " else " ++ lb ++ "\n" ++
    "        mem_resp_valid_ = false;\n" ++
    "    " ++ rb ++ "\n\n" ++
    "    if (req_valid) " ++ lb ++ "\n" ++
    "        if (req_we) " ++ lb ++ "\n" ++
    "            // Write 8-word cache line\n" ++
    "            uint32_t widx = addr / 4;\n" ++
    "            for (int w = 0; w < 8; w++) " ++ lb ++ "\n" ++
    "                if (widx + w < MEM_SIZE_WORDS)\n" ++
    "                    mem_[widx + w] = data_line[w];\n" ++
    "            " ++ rb ++ "\n" ++
    "        " ++ rb ++ " else " ++ lb ++ "\n" ++
    "            // Read 8-word cache line\n" ++
    "            uint32_t widx = addr / 4;\n" ++
    "            for (int w = 0; w < 8; w++)\n" ++
    "                mem_read_line_[w] = (widx + w < MEM_SIZE_WORDS) ? mem_[widx + w] : 0;\n" ++
    "            mem_pending_ = true;\n" ++
    "        " ++ rb ++ "\n" ++
    "    " ++ rb ++ "\n" ++
    s!"{rb}\n\n" ++
    s!"void LeanSim::settle() {lb}\n" ++
    "    for (int i = 0; i < 10; i++)\n" ++
    "        cpu_eval_comb_all(ctx_);\n" ++
    s!"{rb}\n\n") ++

  "// ============================================================================\n" ++
  "// Constructor\n" ++
  "// ============================================================================\n\n" ++
  s!"LeanSim::LeanSim(const std::string& elf_path) {lb}\n" ++
  "    // Initialize signal pointer arrays\n" ++
  (String.intercalate "\n" (
    groups.map fun sg =>
      s!"    for (int i = 0; i < {sg.width}; i++) {sg.name}_sigs_[i] = &{sg.name}_[i];")) ++ "\n" ++
  "\n" ++
  "    // Build the port pointer array matching the cpu_setup port order\n" ++
  s!"    bool* cpu_ports[] = {lb}\n" ++
  portPtrEntries ++ "\n" ++
  s!"    {rb};\n\n" ++
  s!"    ctx_ = cpu_create(\"lean_sim\", &reset_sig_, cpu_ports, {portList.length});\n\n" ++
  "    // Load ELF into memory\n" ++
  "    load_elf(elf_path.c_str(), [this](uint32_t addr, uint32_t data) " ++ lb ++ "\n" ++
  "        uint32_t widx = addr / 4;\n" ++
  "        if (widx < MEM_SIZE_WORDS) mem_[widx] = data;\n" ++
  "    " ++ rb ++ ");\n\n" ++
  "    // Reset phase\n" ++
  "    reset_sig_ = true;\n" ++
  (if !isCached then "    dmem_req_ready_ = true;\n" else "") ++
  "    for (int i = 0; i < 5; i++) " ++ lb ++ "\n" ++
  "        cpu_eval_seq_sample_all(ctx_);\n" ++
  "        cpu_eval_seq_all(ctx_);\n" ++
  "        settle();\n" ++
  "    " ++ rb ++ "\n" ++
  "    reset_sig_ = false;\n" ++
  "    settle();\n" ++
  s!"{rb}\n\n" ++

  s!"LeanSim::~LeanSim() {lb}\n" ++
  "    if (ctx_) cpu_delete(ctx_);\n" ++
  s!"{rb}\n\n" ++

  "// ============================================================================\n" ++
  "// Step: run cycles until next RVVI retirement\n" ++
  "// ============================================================================\n\n" ++
  s!"LeanSimStepResult LeanSim::step() {lb}\n" ++
  "    while (cycle_ < MAX_CYCLES) " ++ lb ++ "\n" ++
  (if !isCached then
    "        bool snap_req_valid = dmem_req_valid_;\n" ++
    "        bool snap_req_we = dmem_req_we_;\n" ++
    "        uint32_t snap_addr = read_bus(dmem_req_addr_sigs_, 32);\n" ++
    "        uint32_t snap_data = read_bus(dmem_req_data_sigs_, 32);\n" ++
    "        uint32_t snap_size = read_bus(dmem_req_size_sigs_, 2);\n"
   else
    "        bool snap_req_valid = mem_req_valid_;\n" ++
    "        bool snap_req_we = mem_req_we_;\n" ++
    "        uint32_t snap_addr = read_bus(mem_req_addr_sigs_, 32);\n" ++
    "        uint32_t snap_data_line[8];\n" ++
    "        for (int w = 0; w < 8; w++)\n" ++
    "            snap_data_line[w] = read_bus(&mem_req_data_sigs_[w * 32], 32);\n") ++
  "\n" ++
  "        cpu_eval_seq_sample_all(ctx_);\n" ++
  "        cpu_eval_seq_all(ctx_);\n\n" ++
  (if !isCached then
    "        dmem_tick(snap_req_valid, snap_req_we, snap_addr, snap_data, snap_size);\n"
   else
    "        mem_tick(snap_req_valid, snap_req_we, snap_addr, snap_data_line);\n") ++
  "        settle();\n" ++
  "        cycle_++;\n\n" ++
  (if isCached then
    "        // Check store snoop for tohost\n" ++
    "        if (store_snoop_valid_) " ++ lb ++ "\n" ++
    "            uint32_t snoop_addr = read_bus(store_snoop_addr_sigs_, 32);\n" ++
    "            uint32_t snoop_data = read_bus(store_snoop_data_sigs_, 32);\n" ++
    "            if (snoop_addr == TOHOST_ADDR) " ++ lb ++ "\n" ++
    "                test_done_ = true;\n" ++
    "                test_data_ = snoop_data;\n" ++
    "            " ++ rb ++ "\n" ++
    (match cfg.putcharAddr with
     | some _ =>
       "            if (snoop_addr == PUTCHAR_ADDR)\n" ++
       "                putchar(snoop_data & 0xFF);\n"
     | none => "") ++
    "        " ++ rb ++ "\n\n"
   else "") ++
  "        if (rvvi_valid_) " ++ lb ++ "\n" ++
  "            LeanSimStepResult r = " ++ lb ++ rb ++ ";\n" ++
  "            r.pc       = read_bus(rvvi_pc_rdata_sigs_, 32);\n" ++
  "            r.insn     = read_bus(rvvi_insn_sigs_, 32);\n" ++
  "            r.rd       = read_bus(rvvi_rd_sigs_, 5);\n" ++
  "            r.rd_valid = rvvi_rd_valid_;\n" ++
  "            r.rd_data  = read_bus(rvvi_rd_data_sigs_, 32);\n" ++
  "            r.frd      = read_bus(rvvi_frd_sigs_, 5);\n" ++
  "            r.frd_valid = rvvi_frd_valid_;\n" ++
  "            r.frd_data = read_bus(rvvi_frd_data_sigs_, 32);\n" ++
  "            r.fflags   = read_bus(fflags_acc_sigs_, 5);\n" ++
  "            r.done     = test_done_;\n" ++
  "            r.tohost   = test_data_;\n" ++
  "            return r;\n" ++
  "        " ++ rb ++ "\n\n" ++
  "        if (test_done_) " ++ lb ++ "\n" ++
  "            LeanSimStepResult r = " ++ lb ++ rb ++ ";\n" ++
  "            r.done = true;\n" ++
  "            r.tohost = test_data_;\n" ++
  "            return r;\n" ++
  "        " ++ rb ++ "\n" ++
  "    " ++ rb ++ "\n\n" ++
  "    LeanSimStepResult r = " ++ lb ++ rb ++ ";\n" ++
  "    r.done = true;\n" ++
  "    r.tohost = 0;\n" ++
  "    return r;\n" ++
  s!"{rb}\n"

/-! ## Verilator cosim_main.cpp Generator -/

/-- Generate cosim_main.cpp for Verilator cosimulation, templated on testbench config. -/
def toCosimMainCpp (cfg : TestbenchConfig) : String :=
  let tbName := optOrDefault cfg.tbName s!"tb_{cfg.circuit.name}"
  let vType := s!"V{tbName}"
  let lb := "{"
  let rb := "}"

  "//==============================================================================\n" ++
  s!"// cosim_main_{tbName}.cpp - Auto-generated lock-step cosimulation driver\n" ++
  "// DO NOT EDIT - regenerate with: lake exe generate_all\n" ++
  "//==============================================================================\n\n" ++
  "#include <cstdio>\n" ++
  "#include <cstdlib>\n" ++
  "#include <cstring>\n" ++
  "#include <memory>\n" ++
  "#include <vector>\n" ++
  "#include <elf.h>\n\n" ++
  s!"#include \"{vType}.h\"\n" ++
  "#include \"verilated.h\"\n" ++
  "#include \"svdpi.h\"\n\n" ++
  "#include \"lib/spike_oracle.h\"\n" ++
  (if cfg.cacheLineMemPort.isNone then
    s!"#include \"lean_sim_{cfg.circuit.name}.h\"\n\n"
  else
    "\n") ++
  "extern \"C\" void dpi_mem_write(unsigned int word_addr, unsigned int data);\n" ++
  "extern \"C\" void dpi_set_tohost_addr(unsigned int addr);\n\n" ++

  "static const uint32_t DEFAULT_TIMEOUT = " ++ toString cfg.timeoutCycles ++ ";\n\n" ++

  "static const char* get_plusarg(int argc, char** argv, const char* name) " ++ lb ++ "\n" ++
  "    size_t len = strlen(name);\n" ++
  "    for (int i = 1; i < argc; i++)\n" ++
  "        if (strncmp(argv[i], name, len) == 0 && argv[i][len] == '=')\n" ++
  "            return argv[i] + len + 1;\n" ++
  "    return nullptr;\n" ++
  rb ++ "\n\n" ++

  "static int load_elf(const char* path) " ++ lb ++ "\n" ++
  "    FILE* f = fopen(path, \"rb\");\n" ++
  "    if (!f) " ++ lb ++ " fprintf(stderr, \"ERROR: Cannot open ELF: %s\\n\", path); return -1; " ++ rb ++ "\n" ++
  "    Elf32_Ehdr ehdr;\n" ++
  "    if (fread(&ehdr, sizeof(ehdr), 1, f) != 1) " ++ lb ++ " fclose(f); return -1; " ++ rb ++ "\n" ++
  "    if (memcmp(ehdr.e_ident, ELFMAG, SELFMAG) != 0 || ehdr.e_ident[EI_CLASS] != ELFCLASS32) " ++ lb ++ "\n" ++
  "        fclose(f); return -1;\n" ++
  "    " ++ rb ++ "\n" ++
  "    for (int i = 0; i < ehdr.e_phnum; i++) " ++ lb ++ "\n" ++
  "        Elf32_Phdr phdr;\n" ++
  "        fseek(f, ehdr.e_phoff + i * ehdr.e_phentsize, SEEK_SET);\n" ++
  "        if (fread(&phdr, sizeof(phdr), 1, f) != 1) continue;\n" ++
  "        if (phdr.p_type != PT_LOAD || phdr.p_filesz == 0) continue;\n" ++
  "        std::vector<uint8_t> seg(phdr.p_memsz, 0);\n" ++
  "        fseek(f, phdr.p_offset, SEEK_SET);\n" ++
  "        (void)fread(seg.data(), 1, phdr.p_filesz, f);\n" ++
  "        for (uint32_t off = 0; off < phdr.p_memsz; off += 4) " ++ lb ++ "\n" ++
  "            uint32_t word = 0;\n" ++
  "            memcpy(&word, &seg[off], std::min<uint32_t>(4, phdr.p_memsz - off));\n" ++
  "            dpi_mem_write((phdr.p_paddr + off) >> 2, word);\n" ++
  "        " ++ rb ++ "\n" ++
  "    " ++ rb ++ "\n" ++
  "    fclose(f);\n" ++
  "    return 0;\n" ++
  rb ++ "\n\n" ++

  "static bool is_unsyncable_csr_read(uint32_t insn) " ++ lb ++ "\n" ++
  "    uint32_t opcode = insn & 0x7f;\n" ++
  "    if (opcode != 0x73) return false;\n" ++
  "    uint32_t funct3 = (insn >> 12) & 0x7;\n" ++
  "    if (funct3 == 0) return false;\n" ++
  "    uint32_t csr_addr = (insn >> 20) & 0xfff;\n" ++
  "    return csr_addr == 0xB00 || csr_addr == 0xB02 || csr_addr == 0xB80 || csr_addr == 0xB82 ||\n" ++
  "           csr_addr == 0xC00 || csr_addr == 0xC02 || csr_addr == 0xC80 || csr_addr == 0xC82;\n" ++
  rb ++ "\n\n" ++

  "static uint32_t find_tohost_addr(const char* path) " ++ lb ++ "\n" ++
  "    FILE* f = fopen(path, \"rb\");\n" ++
  "    if (!f) return 0x1000;\n" ++
  "    Elf32_Ehdr ehdr;\n" ++
  "    if (fread(&ehdr, sizeof(ehdr), 1, f) != 1) " ++ lb ++ " fclose(f); return 0x1000; " ++ rb ++ "\n" ++
  "    for (int i = 0; i < ehdr.e_shnum; i++) " ++ lb ++ "\n" ++
  "        Elf32_Shdr shdr;\n" ++
  "        fseek(f, ehdr.e_shoff + i * ehdr.e_shentsize, SEEK_SET);\n" ++
  "        if (fread(&shdr, sizeof(shdr), 1, f) != 1) continue;\n" ++
  "        if (shdr.sh_type != SHT_SYMTAB) continue;\n" ++
  "        Elf32_Shdr strhdr;\n" ++
  "        fseek(f, ehdr.e_shoff + shdr.sh_link * ehdr.e_shentsize, SEEK_SET);\n" ++
  "        if (fread(&strhdr, sizeof(strhdr), 1, f) != 1) continue;\n" ++
  "        std::vector<char> strtab(strhdr.sh_size);\n" ++
  "        fseek(f, strhdr.sh_offset, SEEK_SET);\n" ++
  "        (void)fread(strtab.data(), 1, strhdr.sh_size, f);\n" ++
  "        int nsyms = shdr.sh_size / shdr.sh_entsize;\n" ++
  "        for (int j = 0; j < nsyms; j++) " ++ lb ++ "\n" ++
  "            Elf32_Sym sym;\n" ++
  "            fseek(f, shdr.sh_offset + j * shdr.sh_entsize, SEEK_SET);\n" ++
  "            if (fread(&sym, sizeof(sym), 1, f) != 1) continue;\n" ++
  "            if (sym.st_name < strhdr.sh_size && strcmp(&strtab[sym.st_name], \"tohost\") == 0) " ++ lb ++ "\n" ++
  "                fclose(f); return sym.st_value;\n" ++
  "            " ++ rb ++ "\n" ++
  "        " ++ rb ++ "\n" ++
  "    " ++ rb ++ "\n" ++
  "    fclose(f);\n" ++
  "    return 0x1000;\n" ++
  rb ++ "\n\n" ++

  "struct RVVIState " ++ lb ++ "\n" ++
  "    bool valid, trap, rd_valid, frd_valid;\n" ++
  "    uint32_t pc, insn, rd, rd_data, frd, frd_data, fflags;\n" ++
  rb ++ ";\n\n" ++

  s!"static void read_rvvi_dual(const {vType}* dut, RVVIState out[2]) {lb}\n" ++
  "    out[0] = " ++ lb ++ rb ++ ";\n" ++
  "    out[0].valid     = dut->o_rvvi_valid_0;\n" ++
  "    out[0].trap      = dut->o_rvvi_trap_0;\n" ++
  "    out[0].pc        = dut->o_rvvi_pc_rdata_0;\n" ++
  "    out[0].insn      = dut->o_rvvi_insn_0;\n" ++
  "    out[0].rd        = dut->o_rvvi_rd_0;\n" ++
  "    out[0].rd_valid  = dut->o_rvvi_rd_valid_0;\n" ++
  "    out[0].rd_data   = dut->o_rvvi_rd_data_0;\n" ++
  "    out[0].frd_valid = false;\n" ++
  "    out[1] = " ++ lb ++ rb ++ ";\n" ++
  "    out[1].valid     = dut->o_rvvi_valid_1;\n" ++
  "    out[1].trap      = dut->o_rvvi_trap_1;\n" ++
  "    out[1].pc        = dut->o_rvvi_pc_rdata_1;\n" ++
  "    out[1].insn      = dut->o_rvvi_insn_1;\n" ++
  "    out[1].rd        = dut->o_rvvi_rd_1;\n" ++
  "    out[1].rd_valid  = dut->o_rvvi_rd_valid_1;\n" ++
  "    out[1].rd_data   = dut->o_rvvi_rd_data_1;\n" ++
  "    out[1].frd_valid = false;\n" ++
  rb ++ "\n\n" ++

  s!"int main(int argc, char** argv) {lb}\n" ++
  "    Verilated::commandArgs(argc, argv);\n" ++
  "    const char* elf_path = get_plusarg(argc, argv, \"+elf\");\n" ++
  "    if (!elf_path) " ++ lb ++ "\n" ++
  "        fprintf(stderr, \"Usage: %s +elf=<path.elf> [+timeout=N]\\n\", argv[0]);\n" ++
  "        return 1;\n" ++
  "    " ++ rb ++ "\n" ++
  "    uint32_t timeout = DEFAULT_TIMEOUT;\n" ++
  "    const char* to = get_plusarg(argc, argv, \"+timeout\");\n" ++
  "    if (to) timeout = (uint32_t)atol(to);\n\n" ++
  s!"    auto dut = std::make_unique<{vType}>();\n" ++
  "    dut->eval();\n" ++
  s!"    svSetScope(svGetScopeFromName(\"TOP.{tbName}\"));\n" ++
  "    if (load_elf(elf_path) != 0) return 1;\n\n" ++
  "    uint32_t tohost_addr = find_tohost_addr(elf_path);\n" ++
  "    dpi_set_tohost_addr(tohost_addr);\n\n" ++
  s!"    auto spike = std::make_unique<SpikeOracle>(elf_path, \"{cfg.spikeIsa}\");\n" ++
  (if cfg.cacheLineMemPort.isNone then
    "    auto lean_sim = std::make_unique<LeanSim>(elf_path);\n\n"
  else "\n") ++
  "    dut->clk = 0; dut->rst_n = 0;\n" ++
  "    for (int i = 0; i < 10; i++) " ++ lb ++ " dut->clk = !dut->clk; dut->eval(); " ++ rb ++ "\n" ++
  "    dut->rst_n = 1;\n\n" ++
  "    uint64_t cycle = 0, retired = 0, mismatches = 0;\n" ++
  "    bool done = false;\n\n" ++
  "    while (!done && cycle < timeout) " ++ lb ++ "\n" ++
  "        dut->clk = 1; dut->eval();\n" ++
  "        RVVIState rvvi[2];\n" ++
  "        read_rvvi_dual(dut.get(), rvvi);\n\n" ++
  "        for (int slot = 0; slot < 2; slot++) " ++ lb ++ "\n" ++
  "            if (!rvvi[slot].valid) continue;\n" ++
  "            SpikeStepResult spike_r = spike->step();\n" ++
  "            int skip = 0;\n" ++
  "            while (spike_r.pc != rvvi[slot].pc && skip < 32) " ++ lb ++ "\n" ++
  "                if (is_unsyncable_csr_read(spike_r.insn) && spike_r.rd != 0) " ++ lb ++ "\n" ++
  "                    uint32_t csr = (spike_r.insn >> 20) & 0xfff;\n" ++
  "                    if (csr == 0xB02 || csr == 0xC02)\n" ++
  "                        spike->set_xreg(spike_r.rd, spike_r.rd_value - 1);\n" ++
  "                " ++ rb ++ "\n" ++
  "                spike_r = spike->step(); skip++;\n" ++
  "            " ++ rb ++ "\n\n" ++
  "            bool skip_rd_cmp = false;\n" ++
  "            if (is_unsyncable_csr_read(rvvi[slot].insn)) " ++ lb ++ "\n" ++
  "                if (rvvi[slot].rd_valid && spike_r.rd != 0)\n" ++
  "                    spike->set_xreg(spike_r.rd, rvvi[slot].rd_data);\n" ++
  "                skip_rd_cmp = true;\n" ++
  "            " ++ rb ++ "\n\n" ++
  "            if (rvvi[slot].pc != spike_r.pc) " ++ lb ++ "\n" ++
  "                fprintf(stderr, \"MISMATCH ret#%lu cy%lu slot%d: PC RTL=0x%08x Spike=0x%08x (skip %d)\\n\",\n" ++
  "                    retired, cycle, slot, rvvi[slot].pc, spike_r.pc, skip);\n" ++
  "                mismatches++;\n" ++
  "            " ++ rb ++ "\n" ++
  "            if (rvvi[slot].insn != spike_r.insn) " ++ lb ++ "\n" ++
  "                fprintf(stderr, \"MISMATCH ret#%lu cy%lu slot%d: insn RTL=0x%08x Spike=0x%08x\\n\",\n" ++
  "                    retired, cycle, slot, rvvi[slot].insn, spike_r.insn);\n" ++
  "                mismatches++;\n" ++
  "            " ++ rb ++ "\n" ++
  "            if (rvvi[slot].rd_valid && spike_r.rd != 0 && !skip_rd_cmp) " ++ lb ++ "\n" ++
  "                if (rvvi[slot].rd_data != spike_r.rd_value) " ++ lb ++ "\n" ++
  "                    fprintf(stderr, \"MISMATCH ret#%lu cy%lu slot%d: x%u RTL=0x%08x Spike=0x%08x\\n\",\n" ++
  "                        retired, cycle, slot, spike_r.rd, rvvi[slot].rd_data, spike_r.rd_value);\n" ++
  "                    mismatches++;\n" ++
  "                " ++ rb ++ "\n" ++
  "            " ++ rb ++ "\n\n" ++
  "            retired++;\n" ++
  "            if (mismatches > 10) " ++ lb ++ " fprintf(stderr, \"Too many mismatches\\n\"); done = true; break; " ++ rb ++ "\n" ++
  "        " ++ rb ++ "\n\n" ++
  "        if (dut->o_test_done) done = true;\n" ++
  "        dut->clk = 0; dut->eval();\n" ++
  "        cycle++;\n" ++
  "    " ++ rb ++ "\n\n" ++
  "    printf(\"Cosimulation complete:\\n\");\n" ++
  "    printf(\"  Cycles:      %lu\\n\", cycle);\n" ++
  "    printf(\"  Retired:     %lu\\n\", retired);\n" ++
  "    printf(\"  IPC:         %.3f\\n\", cycle > 0 ? (double)retired / cycle : 0.0);\n" ++
  "    printf(\"  Mismatches:  %lu\\n\", mismatches);\n" ++
  "    printf(\"  tohost:      0x%08x\\n\", dut->o_tohost);\n\n" ++
  "    if (mismatches == 0 && dut->o_tohost == 1)\n" ++
  "        printf(\"COSIM PASS\\n\");\n" ++
  "    else\n" ++
  "        printf(\"COSIM FAIL\\n\");\n\n" ++
  "    return (mismatches == 0 && dut->o_tohost == 1) ? 0 : 1;\n" ++
  rb ++ "\n"

/-! ## File Writers -/

def testbenchOutputDir : String := "testbench/generated"

def writeTestbenchSV (cfg : TestbenchConfig) : IO Unit := do
  IO.FS.createDirAll testbenchOutputDir
  let sv := if cfg.cacheLineMemPort.isSome then toTestbenchSVCached cfg else toTestbenchSV cfg
  let tbName := optOrDefault cfg.tbName s!"tb_{cfg.circuit.name}"
  let path := s!"{testbenchOutputDir}/{tbName}.sv"
  IO.FS.writeFile path sv
  IO.println s!"  ✓ {tbName}.sv (testbench)"

def writeTestbenchCppSim (cfg : TestbenchConfig) : IO Unit := do
  IO.FS.createDirAll testbenchOutputDir
  let c := cfg.circuit
  -- Write thin setup header
  let setupH := toCpuSetupHeader c
  IO.FS.writeFile s!"{testbenchOutputDir}/cpu_setup_{c.name}.h" setupH
  -- Write heavy setup cpp (includes full module header)
  let setupCpp := toCpuSetupCpp cfg
  IO.FS.writeFile s!"{testbenchOutputDir}/cpu_setup_{c.name}.cpp" setupCpp
  -- Write thin sim_main (no module header includes)
  let sc := toTestbenchCppSim cfg
  IO.FS.writeFile s!"{testbenchOutputDir}/sim_main_{c.name}.cpp" sc
  IO.println s!"  ✓ sim_main_{c.name}.cpp + cpu_setup_{c.name}.cpp (testbench, split)"

def writeSimMainCpp (cfg : TestbenchConfig) : IO Unit := do
  IO.FS.createDirAll testbenchOutputDir
  let tbName := optOrDefault cfg.tbName s!"tb_{cfg.circuit.name}"
  let cpp := toSimMainCpp cfg
  IO.FS.writeFile s!"{testbenchOutputDir}/sim_main_{tbName}.cpp" cpp
  IO.println s!"  ✓ sim_main_{tbName}.cpp (Verilator sim driver)"

def writeCosimMainCpp (cfg : TestbenchConfig) : IO Unit := do
  IO.FS.createDirAll testbenchOutputDir
  let tbName := optOrDefault cfg.tbName s!"tb_{cfg.circuit.name}"
  let cpp := toCosimMainCpp cfg
  IO.FS.writeFile s!"{testbenchOutputDir}/cosim_main_{tbName}.cpp" cpp
  IO.println s!"  ✓ cosim_main_{tbName}.cpp (Verilator cosim driver)"

def writeLeanSim (cfg : TestbenchConfig) : IO Unit := do
  IO.FS.createDirAll testbenchOutputDir
  let c := cfg.circuit
  let h := toLeanSimH cfg
  IO.FS.writeFile s!"{testbenchOutputDir}/lean_sim_{c.name}.h" h
  let cpp := toLeanSimCpp cfg
  IO.FS.writeFile s!"{testbenchOutputDir}/lean_sim_{c.name}.cpp" cpp
  IO.println s!"  ✓ lean_sim_{c.name}.h + lean_sim_{c.name}.cpp (Lean gate-level sim)"

def writeTestbenches (cfg : TestbenchConfig) : IO Unit := do
  Testbench.writeTestbenchSV cfg
  -- CppSim and LeanSim generators don't support cache-line memory interface yet
  if cfg.cacheLineMemPort.isNone then
    Testbench.writeTestbenchCppSim cfg
    Testbench.writeLeanSim cfg
  Testbench.writeSimMainCpp cfg
  Testbench.writeCosimMainCpp cfg

end Shoumei.Codegen.Testbench
