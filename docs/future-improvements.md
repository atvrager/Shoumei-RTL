# Future Improvements for Shoumei RTL

## Standardize Vec-Based Bundled IO for All Large Modules

**Problem:** Current modules have inconsistent I/O organization. Some use individual named ports, others use bundled `Vec` types. This leads to:
- Verbose port mapping code (one line per bit)
- JVM class size limits when generating Chisel (methods too large)
- Difficult-to-read SystemVerilog with thousands of individual wires
- No semantic structure to port groups

**Proper Solution:** Consistently use Vec-based bundled I/O with semantic grouping

### Design Principles

1. **Use Vec for all multi-bit signals**
   ```lean
   -- Instead of: rd_tag1_0, rd_tag1_1, ..., rd_tag1_5
   -- Use: rd_tag1[6] mapped to io.rd_tag1(idx)
   ```

2. **Group related signals into bundles**
   ```scala
   // Chisel: Use Bundle types for related signals
   class ReadPort extends Bundle {
     val tag = Input(UInt(6.W))
     val data = Output(UInt(32.W))
   }

   val io = IO(new Bundle {
     val read1 = new ReadPort
     val read2 = new ReadPort
     val write = Flipped(new WritePort)
   })
   ```

3. **Enable batch assignment in codegen**
   ```scala
   // Instead of 32 individual assignments:
   io.rd_data1(0) := mux_out(0)
   io.rd_data1(1) := mux_out(1)
   // ...

   // Use bulk connect:
   io.rd_data1 := mux_out
   ```

4. **SystemVerilog struct support**
   ```systemverilog
   typedef struct packed {
     logic [5:0] tag;
     logic [31:0] data;
   } read_port_t;

   module PhysRegFile (
     input read_port_t rd_req1,
     output read_port_t rd_resp1,
     ...
   );
   ```

### Benefits

- **Reduced code size:** Batch assignments reduce generated code from thousands to tens of lines
- **JVM compliance:** Smaller methods stay well below 64KB limit
- **Better readability:** Semantic grouping makes generated code human-comprehensible
- **Type safety:** Bundle types catch port width mismatches at compile time
- **Easier verification:** Structured ports simplify LEC and simulation
- **Physical design:** Struct-based SV enables better synthesis constraints

### Migration Path

1. Add `Bundle` helper types to Lean DSL (e.g., `SignalVec`, `ReadPort`, `WritePort`)
2. Update large modules (PhysRegFile, PipelinedMultiplier, RAT, FreeList) to use bundles
3. Enhance Chisel codegen to emit `io.bundle := other.bundle` bulk connects
4. Add SystemVerilog struct codegen option (controlled by flag)
5. Re-verify all modules with LEC

### Affected Modules

Priority order for migration:
1. PhysRegFile_64x32 (4160 gates, 192 ports) - register file with 2 read + 1 write port
2. PipelinedMultiplier (2365 gates, 148 ports) - 3-stage multiply with metadata passthrough
3. RAT_32x6 (416 gates, bundled but could use better grouping)
4. FreeList_64 (32 gates, 156 ports)
5. ReservationStation4 (433 gates, 211 ports) - already bundled, but could use semantic groups
6. MulDivRS4 (similar to RS4)

**Estimated effort:** 2-3 weeks for DSL + codegen changes, 1 week per module migration

**Priority:** Medium-High (blocks scaling to larger designs, but current workarounds exist)
