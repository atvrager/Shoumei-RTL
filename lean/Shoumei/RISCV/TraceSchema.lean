/-!
# Trace schema (single source of truth)

The Kanata pipeline trace vocabulary that the C++ tracer
(`testbench/lib/kanata_tracer.h`) emits and the TypeScript viewer
(`viewer/src/viewer.ts`) renders. `generate_all` emits both
`testbench/generated/trace_schema.gen.h` and `viewer/src/schema.gen.ts` from
this definition, so a Lean-side stage change breaks a compile on both sides
instead of silently mis-rendering a trace.
-/
namespace Shoumei.TraceSchema

/-- (code, human name) per pipeline stage, in tracer emission order. -/
def traceStages : List (String × String) :=
  [
    ("F", "Fetch"),
    ("D", "Decode"),
    ("Rn", "Rename"),
    ("Is", "Issue"),
    ("Xec", "Execute"),
    ("Cm", "Complete"),
    ("Rt", "Retire")
  ]

/-- Instruction-per-cycle width of the superscalar core (display constant). -/
def traceWidth : Nat := 2

/-- The `"` character (Lean strings cannot contain escaped quotes). -/
private def QUOTE : String := String.singleton '"'

/-- C header consumed by KanataTracer (testbench/lib/kanata_tracer.cpp). -/
def renderCHeader : String :=
  let rows := traceStages.map fun (code, name) =>
    "    {" ++ QUOTE ++ code ++ QUOTE ++ ", " ++ QUOTE ++ name ++ QUOTE ++ "},"
  "/** Auto-generated from lean/Shoumei/RISCV/TraceSchema.lean — do not edit. */\n" ++
  "#pragma once\n" ++
  s!"#define TRACE_STAGE_COUNT {traceStages.length}\n" ++
  "typedef struct { const char* code; const char* name; } TraceStageInfo;\n" ++
  "static const TraceStageInfo TRACE_STAGES[TRACE_STAGE_COUNT] = {\n" ++
  String.intercalate "\n" rows ++
  "\n};\n"

/-- TS schema consumed by the pipeline viewer (viewer/src/viewer.ts). -/
def renderTsSchema : String :=
  let rows := traceStages.map fun (code, name) =>
    "  { code: " ++ QUOTE ++ code ++ QUOTE ++ ", name: " ++ QUOTE ++ name ++ QUOTE ++ " },"
  "// Auto-generated from lean/Shoumei/RISCV/TraceSchema.lean — do not edit.\n" ++
  "export const TRACE_STAGES = [\n" ++
  String.intercalate "\n" rows ++
  "\n] as const;\n\n" ++
  "export type StageCode = typeof TRACE_STAGES[number][\"code\"];\n\n" ++
  s!"export const TRACE_WIDTH = {traceWidth} as const;\n"

end Shoumei.TraceSchema