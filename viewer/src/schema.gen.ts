// Auto-generated from lean/Shoumei/RISCV/TraceSchema.lean — do not edit.
export const TRACE_STAGES = [
  { code: "F", name: "Fetch" },
  { code: "D", name: "Decode" },
  { code: "Rn", name: "Rename" },
  { code: "Is", name: "Issue" },
  { code: "Xec", name: "Execute" },
  { code: "Cm", name: "Complete" },
  { code: "Rt", name: "Retire" },
] as const;

export type StageCode = typeof TRACE_STAGES[number]["code"];

export const TRACE_WIDTH = 2 as const;
