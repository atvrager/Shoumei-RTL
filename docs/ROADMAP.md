# Roadmap

What's planned but not yet built.

## Near-Term

### Phase 9: Compliance Testing
- Run RISC-V architectural compliance test suite (riscv-arch-test)
- Identify and fix any ISA conformance gaps
- Target: full RV32IM compliance certification

### Microarchitecture-Targeted Test Generation
- Generate test ELFs from Lean behavioral models targeting specific pipeline states
- 20 hazard patterns cataloged (see `docs/hazard-patterns.md`):
  - Data hazards: RAW forwarding, WAW renaming, CDB dual wakeup, x0 sink
  - Structural hazards: RS/ROB/free-list exhaustion
  - Control hazards: branch misprediction, JAL/JALR
  - Memory hazards: store-to-load forwarding, store buffer full, width matrix
  - Execution: divider occupancy, multiplier pipeline fill, M-extension corners
  - Combined: multi-hazard combos, pipeline drain
- ~240 targeted ELFs estimated

### Deferred Behavioral Proofs
- 9 RS4 generic axioms (issue preserves existing entries, CDB broadcast correctness, etc.)
- 7 LSU/memory system axioms (store buffer FIFO ordering, forwarding correctness)
- Estimated effort: ~20 hours of manual Lean tactics

## Medium-Term

### Codegen V2: Structured Signals
- Vec-based bundled I/O for all large modules (currently >500-port modules use flat vectors)
- SystemVerilog `struct packed` types for semantic port grouping
- Chisel `Bundle` types with bulk connect
- RAM as DSL primitive (async/sync read modes)
- Two-pair LEC: netlist-to-hierarchical + hierarchical-to-Chisel

### Wire Naming Cleanup
- Bracket notation in DSL: `mkWire "foo[3]"` instead of `foo3`
- Hierarchical naming: `entry[0].valid` instead of `e00`
- Priority encoder primitive (`mkPriorityEncoder n`)
- Partial port mapping for `CircuitInstance` (unused outputs left dangling)

### Compiler Integration (LLVM)
- **Tier 1** (hours): `shoumei-clang` wrapper with microarchitecture-tuned flags (unroll limits from ROB/RS sizes)
- **Tier 2** (days): `llvm-mca` scheduling model for pipeline profiling
- **Tier 3** (weeks): Full TableGen scheduling model in LLVM RISC-V backend

## Long-Term

### Performance
- Instruction cache (reduce fetch bubbles)
- Branch prediction (static, then dynamic BTB/BHT)
- Superscalar dispatch (2-wide issue)
- Speculative execution (beyond branch prediction)

### Architecture Extensions
- Privileged ISA (M/S/U modes, CSRs, interrupts, page tables)
- Compressed instructions (RV32IMC)
- Atomic extensions (RV32IMA)

### Scale
- Multicore (cache coherence, interconnect)
- FPGA prototyping (target board TBD)
