# Build, Codegen, and CI Optimization Analysis

This document outlines the compute-time bottlenecks, workflow redundancies, and performance optimization opportunities across Shoumei RTL's build system, code generation pipeline, formal verification (LEC), and CI workflows.

---

## 1. Executive Summary

Current end-to-end continuous integration runs require **15–20 minutes** on standard 2-vCPU runners, and local developer builds consume significant wall-clock time due to serialized execution and redundant artifact generation.

Key findings:
1. **Redundant Work & Duplication**:
   - The CI `codegen` job restores a cached Lean build and immediately wipes it (`lake clean`), forcing a full 3–4 minute Lean recompilation from scratch.
   - Code generation targets in the `Makefile` and CI repeat generation passes already completed by `GenerateAll.lean`.
   - Formal Logical Equivalence Checking (LEC) re-parses all 140+ design files for each individual module check, resulting in over **28,000 redundant file parses** per run.
2. **Compute Underutilization**:
   - CI runner concurrency defaults in `run-lec.sh` calculate `PARALLEL_JOBS = nproc - 1`, resolving to 1 on 2-vCPU VMs and disabling the parallel dependency scheduler.
   - Testbench simulation and cosimulation suites execute 101 tests in a single-threaded serial bash loop, ignoring multi-core host capabilities.
   - Chisel SystemVerilog generation processes 141 modules serially on a single thread, elaborating each module twice.

Applying the targeted optimizations detailed below can reduce CI cycle time from **~18 minutes to ~5 minutes** and significantly speed up local development cycles.

---

## 2. Redundant Work & Duplication Analysis

### 2.1 The Lean "Build, Wipe, Rebuild" Loop in CI

* **Location**: [`.github/workflows/ci.yml`](../.github/workflows/ci.yml#L208-L248)
* **Mechanism**:
  1. The `lean-build` job executes `lake build` and saves `.lake` to the GitHub Actions cache, keyed by:
     ```yaml
     key: ${{ runner.os }}-lean-${{ hashFiles('lean-toolchain', 'lakefile.lean', 'lake-manifest.json', 'lean/**/*.lean', 'GenerateAll.lean') }}
     ```
  2. The downstream `codegen` job restores this exact `.lake` cache.
  3. Immediately following cache restoration, line 244 runs:
     ```yaml
     - name: Clean stale build artifacts
       run: lake clean
     ```
  4. Line 247 runs `make codegen`, which invokes `lake build`, forcing Lean to rebuild all libraries, proofs, and executables from source on a 2-vCPU runner.
* **Why this is unnecessary**:
  The cache key incorporates a cryptographic hash of all Lean sources, the toolchain, and package manifests, with no fallback restore keys. When a cache hit occurs, the `.olean` and executable artifacts are guaranteed to match the commit.
* **Impact**: Wastes **3 to 4 minutes** of runner compute per CI run.
* **Remedy**: Remove `lake clean` from the `codegen` job.

---

### 2.2 Redundant Codegen Passes in `Makefile` and CI

* **Location**: [`Makefile`](../Makefile#L106-L117) and [`.github/workflows/ci.yml`](../.github/workflows/ci.yml#L246-L256)
* **Mechanism**:
  `GenerateAll.lean` serves as the centralized generator for all RTL circuits. It already contains:
  ```lean
  -- RISC-V decoders
  let _ ← generateRISCVDecoders
  ...
  -- Physical synthesis filelists
  writePhysicalFilelist ...
  ```
  However, the `Makefile` `codegen` target executes redundant phases:
  ```makefile
  codegen: lean opcodes
      lake exe generate_all               # Phase 1: Generates circuits, decoders, & filelists
      lake exe generate_riscv_decoder     # Phase 2: Redundantly regenerates decoders
      lake exe export_verification_certs > verification/compositional-certs.txt
      @$(MAKE) --no-print-directory filelists # Phase 4: Redundantly rewrites filelists
  ```
  Furthermore, `ci.yml` runs `make filelists` an additional time after `make codegen`.
* **Impact**: Unnecessary process invocations, file I/O, and build log noise.
* **Remedy**: Streamline `make codegen` to invoke `lake exe generate_all` and certificate export only; remove extra filelist generation steps.

---

### 2.3 Yosys LEC AST Re-parsing Overhead (400× Per-Module Speedup)

* **Location**: [`verification/run-lec.sh`](../verification/run-lec.sh#L435-L448)
* **Mechanism**:
  When invoking Yosys with the built-in parser (the default in CI where `yosys-slang` is not installed), `run-lec.sh` defines module reading as:
  ```bash
  generate_read_commands_for_module() {
      local module_name="$1"
      local dir="$2"

      if [ "$READ_CMD" = "read_slang" ]; then
          local files
          files=$(collect_transitive_deps "$dir" "$module_name")
          echo "$READ_CMD $files"
      else
          # Built-in parser can handle wildcards
          echo "$READ_CMD $dir/*.sv"
      fi
  }
  ```
  For every single module verification, Yosys executes:
  ```yosys
  read_verilog -sv output/sv-from-lean/*.sv   # Reads all 140+ Lean files
  ...
  read_verilog -sv tmp/.../chisel_clean/*.sv # Reads all 140+ Chisel files
  ```
  Over ~100 verified modules, Yosys re-reads and re-parses identical Verilog text **more than 28,000 times**.
* **Measured Benchmark**:
  - Reading `*.sv` (all 140 files) for one module: **5.68s**
  - Reading only the target module and direct dependencies: **0.014s** (**400× faster**)
* **Impact**: Re-parsing consumes **~8 to 9 minutes** of CPU time in CI and during local full LEC runs.
* **Remedy**: Apply `collect_transitive_deps` (which is already implemented for the slang path) to the `read_verilog -sv` path as well.

---

## 3. Concurrency & Compute Bottlenecks

### 3.1 Serialization on 2-vCPU CI Runners

* **Location**: [`verification/run-lec.sh`](../verification/run-lec.sh#L20-L21)
* **Mechanism**:
  ```bash
  PARALLEL_JOBS=$(( $(nproc) - 1 ))
  [ "$PARALLEL_JOBS" -lt 1 ] && PARALLEL_JOBS=1
  ```
  On GitHub-hosted `ubuntu-latest` runners with 2 vCPUs, `2 - 1 = 1`.
  Because `PARALLEL_JOBS <= 1`, the script branches at line 669:
  ```bash
  if [ "$PARALLEL_JOBS" -le 1 ]; then
      # Serial mode (original behavior)
      while IFS= read -r LEAN_FILE; do
          verify_module "$LEAN_FILE"
      ...
  ```
  This completely disables the multi-level parallel dependency runner, executing all checks sequentially on a single core and leaving 50% of the available runner compute idle.
* **Remedy**: Default `PARALLEL_JOBS` to `$(nproc)` in automated CI environments or pass `-j $(nproc)` explicitly in `ci.yml`.

---

### 3.2 Serial Testbench Execution in `testbench/Makefile`

* **Location**: [`testbench/Makefile`](../testbench/Makefile#L299-L318, #L344-L362)
* **Mechanism**:
  `make run-all-tests` and `make run-cosim` iterate over all 101 tests (custom unit tests + RISC-V architectural tests) in a serial bash loop:
  ```bash
  for elf in $(CUSTOM_TEST_GLOBS) $(RISCV_TEST_GLOBS); do
      result=$$($(SIM_BIN) +elf=$$elf +timeout=$$tout 2>&1);
      ...
  done
  ```
* **Impact**:
  On developer workstations with 16 to 64 cores, testing is limited to 1 core, taking ~30–40 seconds. In CI, it takes ~3–4 minutes per simulation job.
* **Remedy**:
  Execute tests in parallel using a worker pool (e.g., `xargs -P $(nproc)` or a Python test runner with `concurrent.futures`). On high-core workstations, 101 tests finish in **1 to 2 seconds**.

---

### 3.3 Chisel Generation Single-Threading & Dual Elaboration

* **Location**: [`chisel/src/main/scala/Main.scala`](../chisel/src/main/scala/Main.scala#L96-L115, #L170-L176)
* **Mechanism**:
  1. `Main.scala` processes modules sequentially:
     ```scala
     for ((moduleName, fqClassName) <- modules) {
       compileModule(moduleName, fqClassName)
     }
     ```
  2. For each module, it elaborates the circuit twice:
     - First elaboration: `ChiselStage.emitSystemVerilogFile(generatorFn(), ...)`
     - Second elaboration: `ChiselStage.emitCHIRRTL(generatorFn())`
  3. `firtool` is spawned sequentially 141 times.
* **Remedy**:
  - Dispatch module compilation across available CPU cores using Scala/Java parallel collections or a `ForkJoinPool`.
  - Gate CHIRRTL emission behind an explicit CLI flag or configuration (only needed when targeting the Arcilator flow).

---

### 3.4 Spike Binary Footprint & Cache Transfer Overhead

* **Location**: [`scripts/build-spike.sh`](../scripts/build-spike.sh) and [`.github/workflows/ci.yml`](../.github/workflows/ci.yml#L423-L436)
* **Mechanism**:
  Spike builds unstripped dynamic libraries with debug symbols:
  - `libriscv.so`: ~193 MB
  - `libcustomext.so`: ~187 MB
  The resulting `~/.local/spike` directory exceeds **380 MB**, which must be compressed, uploaded, downloaded, and decompressed across workflow jobs.
* **Remedy**:
  Run `strip` on the compiled libraries in `scripts/build-spike.sh`, reducing the total footprint to **~15 MB** (>95% size and transfer reduction).

---

### 3.5 LEC Result Caching in CI

* **Location**: [`verification/run-lec.sh`](../verification/run-lec.sh#L292-L309)
* **Mechanism**:
  `run-lec.sh` supports fine-grained caching via `.lec-cache/<module>.ok` stamps, checking timestamps against source files and certificates. However, `.github/workflows/ci.yml` does not cache or restore `.lec-cache`.
* **Remedy**:
  Add `actions/cache` for `.lec-cache` keyed by the hash of `output/sv-from-lean` and `output/sv-from-chisel`. On pull requests with localized RTL changes, unchanged modules are verified instantaneously.

---

## 4. Optimization Matrix & Estimated Savings

| Optimization | Affected Stages | Estimated CI Savings | Estimated Local Savings | Complexity / Risk |
| :--- | :--- | :--- | :--- | :--- |
| **Yosys LEC Targeted Reads** | CI `lec`, local `make lec` | ~6–8 minutes | ~4–6 minutes | Low (isolated script edit) |
| **Remove `lake clean` in CI** | CI `codegen` | ~3–4 minutes | N/A | Trivial / Zero risk |
| **Enable 2-core LEC in CI** | CI `lec` | ~2–3 minutes | N/A | Trivial / Zero risk |
| **Parallelize Testbench Execution**| CI `verilator-sim`, `cosim` | ~2 minutes | ~30s → ~2s | Low |
| **Strip Spike Binaries** | CI `cosim` (cache transfer) | ~30–45s | ~365 MB disk | Trivial / Zero risk |
| **Deduplicate Codegen Passes** | `make codegen`, CI `codegen` | ~20–30s | ~15–20s | Trivial / Zero risk |
| **Parallelize Chisel Generation**| `make chisel`, CI `codegen` | ~1–2 minutes | ~1–2 minutes | Medium |
| **Cache `.lec-cache` in CI** | CI `lec` on PR updates | Up to ~7 minutes | N/A | Low |

---

## 5. Next Steps

1. **Step 1 (Immediate CI Wins)**:
   - Update [`verification/run-lec.sh`](../verification/run-lec.sh) to use `collect_transitive_deps` for built-in Yosys parser.
   - Remove `lake clean` from `.github/workflows/ci.yml`.
   - Set `PARALLEL_JOBS=$(nproc)` in CI.
2. **Step 2 (Local & Testbench Performance)**:
   - Add parallel test execution to `testbench/Makefile`.
   - Strip Spike binaries in `scripts/build-spike.sh`.
   - Clean up redundant targets in `Makefile`.
3. **Step 3 (Compiler Optimizations)**:
   - Parallelize `Main.scala` Chisel elaboration and firtool invocation.
