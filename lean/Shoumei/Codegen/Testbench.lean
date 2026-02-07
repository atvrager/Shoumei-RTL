/-
Codegen/Testbench.lean - Testbench Code Generation

Generates SystemVerilog and SystemC testbenches from a TestbenchConfig.
The config maps circuit ports to memory interfaces (imem/dmem), control
signals, and constants. Generators produce:

- SV testbench: module instantiation, memory model, HTIF, DPI-C loader
- SystemC testbench: sc_main with bus pack/unpack helpers, memory model

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
  respValidSignal : Option String := none
  respDataSignal : Option String := none
  deriving Repr

/-- Configuration for testbench generation. -/
structure TestbenchConfig where
  circuit : Circuit
  imemPort : MemoryPort
  dmemPort : MemoryPort
  memSizeWords : Nat := 16384
  tohostAddr : Nat := 0x1000
  timeoutCycles : Nat := 100000
  constantPorts : List (String × Bool) := [("zero", false), ("one", true)]
  /-- Override the testbench module/file name (default: tb_<circuit.name>) -/
  tbName : Option String := none
  debugOutputs : List String := []
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

  let signalDecls := String.intercalate "\n" (
    (inputSignals.filter (fun (n, _) => !isSpecial n)).map (fun (n, w) => mkDecl n w) ++
    (outputSignals.filter (fun (n, _) => !isSpecial n)).map (fun (n, w) => mkDecl n w)
  )

  -- Port connections for CPU instance
  let portConns := String.intercalate ",\n" (
    [s!"      .{clockName}(clk)"] ++
    [s!"      .{resetName}({resetName})"] ++
    cfg.constantPorts.map (fun (name, value) =>
      s!"      .{name}(1'b{if value then "1" else "0"})") ++
    (inputSignals.filter (fun (n, _) => !isSpecial n)).map (fun (n, _) =>
      s!"      .{n}({n})") ++
    outputSignals.map (fun (n, _) => s!"      .{n}({n})")
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

  let tbName := optOrDefault cfg.tbName s!"tb_{c.name}"

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
  "    output logic [31:0] o_dmem_req_data\n" ++
  ");\n\n" ++

  "  // =========================================================================\n" ++
  "  // CPU I/O signals\n" ++
  "  // =========================================================================\n" ++
  signalDecls ++ "\n\n" ++
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
  "          // Store\n" ++
  s!"          mem[addr_to_idx({dmemAddr})] <= {dmemDataOut};\n" ++
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
  s!"          {dmemAddr} == TOHOST_ADDR) begin\n" ++
  "        test_done <= 1'b1;\n" ++
  s!"        test_code <= {dmemDataOut};\n" ++
  s!"        test_pass <= ({dmemDataOut} == 32'h1);\n" ++
  "      end\n" ++
  "    end\n" ++
  "  end\n\n" ++

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
  s!"  assign o_dmem_req_data  = {dmemDataOut};\n\n" ++
  "endmodule\n"

/-! ## SystemC Testbench Generator -/

/-- Generate bus pack/unpack helpers for SystemC.
    These operate on sc_signal arrays (declared later in sc_main scope),
    not on module ports, because sc_in ports are read-only. -/
private def generateSystemCBusHelpers (c : Circuit) : String :=
  let groups := SystemVerilog.autoDetectSignalGroups (c.inputs ++ c.outputs)
  let lb := "{"
  let rb := "}"
  let helpers := groups.map fun sg =>
    let width := sg.width
    let isInput := sg.wires.any (fun w => c.inputs.any (fun iw => iw.name == w.name))
    let isOutput := sg.wires.any (fun w => c.outputs.any (fun ow => ow.name == w.name))

    -- For input buses: write to the connected sc_signal (passed as array)
    let setter := if isInput then
      let lines := (List.range width).map fun i =>
        s!"    sigs[{i}]->write((v >> {i}) & 1);"
      "void set_" ++ sg.name ++ "(sc_signal<bool>* sigs[], uint32_t v) " ++ lb ++ "\n" ++
        String.intercalate "\n" lines ++ "\n" ++ rb
    else ""

    -- For output buses: read from the connected sc_signal
    let getter := if isOutput then
      let terms := (List.range width).map fun i =>
        if i == 0 then s!"(uint32_t)sigs[{i}]->read()"
        else s!"((uint32_t)sigs[{i}]->read() << {i})"
      "uint32_t get_" ++ sg.name ++ "(sc_signal<bool>* sigs[]) " ++ lb ++ "\n" ++
        "    return " ++ String.intercalate " | " terms ++ ";\n" ++ rb
    else ""

    let s1 := if setter.isEmpty then "" else setter ++ "\n\n"
    let s2 := if getter.isEmpty then "" else getter ++ "\n"
    s1 ++ s2
  String.intercalate "\n" (helpers.filter (· != ""))

/-- Generate a SystemC testbench (sc_main). -/
def toTestbenchSystemC (cfg : TestbenchConfig) : String :=
  let c := cfg.circuit
  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let clockName := if clockWires.isEmpty then "clock" else Wire.name (List.head! clockWires)
  let resetName := if resetWires.isEmpty then "reset" else Wire.name (List.head! resetWires)

  let busHelpers := generateSystemCBusHelpers c

  let inputGroups := SystemVerilog.autoDetectSignalGroups c.inputs
  let outputGroups := SystemVerilog.autoDetectSignalGroups c.outputs
  let groups := SystemVerilog.autoDetectSignalGroups (c.inputs ++ c.outputs)

  let busWireNames : List String :=
    inputGroups.flatMap (fun sg => sg.wires.map Wire.name) ++
    outputGroups.flatMap (fun sg => sg.wires.map Wire.name)
  let scalarInputs := c.inputs.filter fun w =>
    !busWireNames.contains w.name &&
    w.name != clockName && w.name != resetName &&
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

  let signalDecls := String.intercalate "\n" (
    scalarInputs.map (fun w => s!"    sc_signal<bool> {w.name}_sig;") ++
    scalarOutputs.map (fun w => s!"    sc_signal<bool> {w.name}_sig;") ++
    -- Constant port signals
    cfg.constantPorts.map (fun (name, _) => s!"    sc_signal<bool> {name}_sig;") ++
    -- Bus signal declarations
    groups.flatMap (fun sg =>
      (List.range sg.width).map fun i => s!"    sc_signal<bool> {sg.name}_{i}_sig;")
  )

  -- Signal array declarations for bus helpers
  let lb := "{"
  let rb := "}"
  let signalArrayDecls := String.intercalate "\n" (
    groups.map fun sg =>
      let ptrs := String.intercalate ", " (
        (List.range sg.width).map fun i => s!"&{sg.name}_{i}_sig")
      s!"    sc_signal<bool>* {sg.name}_sigs[] = {lb}{ptrs}{rb};"
  )

  let portBindings := String.intercalate "\n" (
    scalarInputs.map (fun w => s!"    u_cpu->{w.name}({w.name}_sig);") ++
    scalarOutputs.map (fun w => s!"    u_cpu->{w.name}({w.name}_sig);") ++
    -- Constant port bindings
    cfg.constantPorts.map (fun (name, _) => s!"    u_cpu->{name}({name}_sig);") ++
    groups.flatMap (fun sg =>
      (List.range sg.width).map fun i => s!"    u_cpu->{sg.name}_{i}({sg.name}_{i}_sig);")
  )

  let constBindings := String.intercalate "\n" (
    cfg.constantPorts.map fun (name, value) =>
      s!"    {name}_sig.write({if value then "true" else "false"});"
  )

  let lb := "{"
  let rb := "}"

  "//==============================================================================\n" ++
  s!"// sc_main_{c.name}.cpp - Auto-generated SystemC testbench\n" ++
  "// DO NOT EDIT - regenerate with: lake exe generate_all\n" ++
  "//==============================================================================\n\n" ++
  "#include <systemc.h>\n" ++
  "#include <cstdio>\n" ++
  "#include <cstdlib>\n" ++
  "#include <cstring>\n" ++
  s!"#include \"{c.name}.h\"\n" ++
  "#include \"elf_loader.h\"\n\n" ++
  s!"static const uint32_t MEM_SIZE_WORDS = {cfg.memSizeWords};\n" ++
  s!"static const uint32_t TOHOST_ADDR = 0x{natToHexDigits cfg.tohostAddr};\n" ++
  s!"static const uint32_t TIMEOUT_CYCLES = {cfg.timeoutCycles};\n\n" ++

  "// Bus pack/unpack helpers\n" ++
  busHelpers ++ "\n\n" ++

  "// Memory model\n" ++
  s!"static uint32_t mem[{cfg.memSizeWords}];\n\n" ++
  s!"static void mem_write_cb(uint32_t addr, uint32_t data) {lb}\n" ++
  s!"    uint32_t widx = addr / 4;\n" ++
  s!"    if (widx < MEM_SIZE_WORDS) mem[widx] = data;\n" ++
  s!"{rb}\n\n" ++
  s!"static uint32_t mem_read(uint32_t byte_addr) {lb}\n" ++
  s!"    uint32_t widx = byte_addr >> 2;\n" ++
  s!"    if (widx < MEM_SIZE_WORDS) return mem[widx];\n" ++
  s!"    return 0;\n" ++
  s!"{rb}\n\n" ++

  s!"int sc_main(int argc, char* argv[]) {lb}\n" ++
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

  "    // Create signals\n" ++
  "    sc_clock clk(\"clk\", 10, SC_NS);\n" ++
  s!"    sc_signal<bool> {resetName}_sig;\n" ++
  signalDecls ++ "\n\n" ++

  "    // Signal arrays for bus helpers\n" ++
  signalArrayDecls ++ "\n\n" ++

  "    // Instantiate CPU (heap-allocated to avoid stack overflow)\n" ++
  s!"    auto* u_cpu = new {c.name}(\"u_cpu\");\n" ++
  s!"    u_cpu->{clockName}(clk);\n" ++
  s!"    u_cpu->{resetName}({resetName}_sig);\n" ++
  portBindings ++ "\n\n" ++

  "    // Constants\n" ++
  constBindings ++ "\n\n" ++

  "    // Reset\n" ++
  s!"    {resetName}_sig.write(true);\n" ++
  "    sc_start(50, SC_NS);\n" ++
  s!"    {resetName}_sig.write(false);\n\n" ++

  "    // Simulation loop\n" ++
  "    bool done = false;\n" ++
  "    uint32_t cycle = 0;\n" ++
  "    printf(\"Simulation started (timeout=%u)\\n\", timeout);\n\n" ++

  s!"    while (!done && cycle < timeout) {lb}\n" ++
  s!"        uint32_t pc = get_{pcSig}({pcSig}_sigs);\n" ++
  s!"        set_{imemDataIn}({imemDataIn}_sigs, mem_read(pc));\n" ++
  s!"        {dmemReady}_sig.write(true);\n\n" ++
  "        sc_start(10, SC_NS);\n" ++
  "        cycle++;\n\n" ++
  s!"        if ({dmemValid}_sig.read()) {lb}\n" ++
  s!"            uint32_t addr = get_{dmemAddr}({dmemAddr}_sigs);\n" ++
  s!"            uint32_t data = get_{dmemDataOut}({dmemDataOut}_sigs);\n" ++
  s!"            if ({dmemWe}_sig.read()) {lb}\n" ++
  s!"                if (addr == TOHOST_ADDR) {lb}\n" ++
  "                    done = true;\n" ++
  "                    printf(\"\\nTEST %s\\n\", data == 1 ? \"PASS\" : \"FAIL\");\n" ++
  "                    printf(\"  Cycle: %u\\ntohost: 0x%08x\\n\", cycle, data);\n" ++
  s!"                {rb} else {lb}\n" ++
  s!"                    uint32_t widx = addr >> 2;\n" ++
  s!"                    if (widx < MEM_SIZE_WORDS) mem[widx] = data;\n" ++
  s!"                {rb}\n" ++
  s!"            {rb} else {lb}\n" ++
  s!"                {dmemRespValid}_sig.write(true);\n" ++
  s!"                set_{dmemRespData}({dmemRespData}_sigs, mem_read(addr));\n" ++
  s!"            {rb}\n" ++
  s!"        {rb} else {lb}\n" ++
  s!"            {dmemRespValid}_sig.write(false);\n" ++
  s!"        {rb}\n\n" ++
  "        if (cycle % 10000 == 0)\n" ++
  s!"            printf(\"  [%u cycles] PC=0x%08x\\n\", cycle, get_{pcSig}({pcSig}_sigs));\n" ++
  s!"    {rb}\n\n" ++
  s!"    if (!done) {lb}\n" ++
  s!"        printf(\"TIMEOUT at cycle %u PC=0x%08x\\n\", cycle, get_{pcSig}({pcSig}_sigs));\n" ++
  s!"    {rb}\n" ++
  "    printf(\"Total cycles: %u\\n\", cycle);\n" ++
  "    delete u_cpu;\n" ++
  "    return done ? 0 : 1;\n" ++
  s!"{rb}\n"

/-! ## File Writers -/

def testbenchOutputDir : String := "testbench/generated"

def writeTestbenchSV (cfg : TestbenchConfig) : IO Unit := do
  IO.FS.createDirAll testbenchOutputDir
  let sv := toTestbenchSV cfg
  let tbName := optOrDefault cfg.tbName s!"tb_{cfg.circuit.name}"
  let path := s!"{testbenchOutputDir}/{tbName}.sv"
  IO.FS.writeFile path sv
  IO.println s!"  ✓ {tbName}.sv (testbench)"

def writeTestbenchSystemC (cfg : TestbenchConfig) : IO Unit := do
  IO.FS.createDirAll testbenchOutputDir
  let sc := toTestbenchSystemC cfg
  let path := s!"{testbenchOutputDir}/sc_main_{cfg.circuit.name}.cpp"
  IO.FS.writeFile path sc
  IO.println s!"  ✓ sc_main_{cfg.circuit.name}.cpp (testbench)"

def writeTestbenches (cfg : TestbenchConfig) : IO Unit := do
  Testbench.writeTestbenchSV cfg
  Testbench.writeTestbenchSystemC cfg

end Shoumei.Codegen.Testbench
