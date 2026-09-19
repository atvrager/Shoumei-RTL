// viewer.ts - Kanata pipeline trace viewer (canvas, virtualized).
//
// Renders the same legacy kanata-format traces Konata shows, in the browser:
// rows are instructions, the x-axis is cycles, colored bars are stage
// segments. Stage codes/colors come from the Lean-generated schema
// (schema.gen.ts), so a stage added in Lean/Shoumei/RISCV/TraceSchema.lean
// fails this compile until a color/label case lands here.

import "./schema.gen.js";
import { TRACE_STAGES, type StageCode } from "./schema.gen.js";

// ------------------------------------------------------------------ schema

// One color per Lean-defined stage. `Record<StageCode, ...>` is exhaustive:
// a new stage code in schema.gen.ts is a type error until it appears here.
const STAGE_COLORS: Record<StageCode, string> = {
  F: "#fbbf24",    // Fetch
  D: "#f59e0b",    // Decode
  Rn: "#34d399",   // Rename
  Is: "#60a5fa",   // Issue (waiting in RS)
  Xec: "#a78bfa",  // Execute
  Cm: "#f472b6",   // Complete (commit queue)
  Rt: "#4ade80",   // Retire
};

const STAGE_NAMES: Record<StageCode, string> = Object.fromEntries(
  TRACE_STAGES.map((s) => [s.code, s.name])
) as Record<StageCode, string>;

// --------------------------------------------------------------------- data

type Seg = { stage: StageCode; start: number; end: number };

type Insn = {
  id: number;
  label: string;
  order: number;
  segments: Seg[];
  flushed: boolean;
  startCycle: number;
  endCycle: number;
};

function parseTrace(text: string): Map<number, Insn> {
  const insns = new Map<number, Insn>();
  let cycle = 0;

  const open = (ins: Insn, stage: StageCode) => {
    if (ins.segments.length === 0) {
      ins.startCycle = cycle;
    }
    ins.segments.push({ stage, start: cycle, end: cycle });
  };

  for (const raw of text.split("\n")) {
    const line = raw.trimEnd();
    if (line.length === 0) {
      continue;
    }
    const f = line.split("\t");
    switch (f[0]) {
      case "C":
        cycle += Number(f[1]);
        break;
      case "I": {
        const id = Number(f[1]);
        let ins = insns.get(id);
        if (!ins) {
          ins = { id, label: `insn #${id}`, order: insns.size, segments: [], flushed: false, startCycle: cycle, endCycle: cycle };
          insns.set(id, ins);
        }
        open(ins, "F");
        break;
      }
      case "L": {
        const ins = insns.get(Number(f[1]));
        if (ins) {
          ins.label = f.slice(2).join("\t"); // label text after `id seq`
        }
        break;
      }
      case "S": {
        const ins = insns.get(Number(f[1]));
        if (ins) {
          open(ins, f[3] as StageCode);
        }
        break;
      }
      case "E": {
        const ins = insns.get(Number(f[1]));
        if (ins && ins.segments.length > 0) {
          const seg = ins.segments[ins.segments.length - 1];
          seg.end = cycle;
          ins.endCycle = cycle;
        }
        break;
      }
      case "R": {
        const ins = insns.get(Number(f[1]));
        if (ins) {
          ins.flushed = f[3] === "1";
          ins.endCycle = cycle;
        }
        break;
      }
      default:
        break; // header (`Kanata 0004`) and comments pass through
    }
  }
  return insns;
}

// --------------------------------------------------------------- rendering

const ROW_H = 18;
const GUTTER = 280;
const AXIS_H = 30;
const PX_PER_CYCLE = 6;

const DIM_ALPHA = 0.12; // filter non-matching rows

type View = { scale: number; ox: number; oy: number };

class Viewer {
  private canvas: HTMLCanvasElement;
  private ctx: CanvasRenderingContext2D;
  private insns: Map<number, Insn> = new Map();
  private view: View = { scale: 1, ox: GUTTER, oy: AXIS_H };
  private filter = "";
  private selected: Insn | null = null;
  private hover: Insn | null = null;
  private dragging = false;
  private lastPtr = { x: 0, y: 0 };
  private dirty = true;

  constructor(
    canvas: HTMLCanvasElement,
    private tooltip: HTMLElement,
    private details: HTMLElement,
    private status: HTMLElement
  ) {
    this.canvas = canvas;
    const ctx = canvas.getContext("2d");
    if (!ctx) {
      throw new Error("no 2d context");
    }
    this.ctx = ctx;
    this.bindEvents();
    this.fit();
  }

  load(text: string, name: string): void {
    this.insns = parseTrace(text);
    this.selected = null;
    this.filter = "";
    const input = document.getElementById("filter") as HTMLInputElement;
    if (input) {
      input.value = "";
    }
    const maxCycle = Math.max(1, ...[...this.insns.values()].map((i) => i.endCycle));
    this.status.textContent =
      `${name} — ${this.insns.size.toLocaleString()} instructions, ` +
      `${maxCycle.toLocaleString()} cycles, ` +
      `${this.insns.size ? Math.round((this.insns.size / maxCycle) * 100) / 100 : 0} IPC`;
    this.fit();
  }

  fit(): void {
    const maxCycle = Math.max(1, ...[...this.insns.values()].map((i) => i.endCycle));
    // Leave a little padding; never zoom in past 4 px/cycle
    this.view.scale = Math.min(4, Math.max(0.1, (this.canvas.clientWidth - GUTTER - 40) / (maxCycle * PX_PER_CYCLE)));
    this.view.ox = GUTTER;
    this.view.oy = AXIS_H;
    this.dirty = true;
  }

  resize(): void {
    const dpr = Math.min(window.devicePixelRatio || 1, 2);
    this.canvas.width = this.canvas.clientWidth * dpr;
    this.canvas.height = this.canvas.clientHeight * dpr;
    this.ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    this.dirty = true;
  }

  private insnAt(screenY: number): Insn | null {
    const order = Math.floor((screenY - this.view.oy - AXIS_H) / ROW_H);
    for (const ins of this.insns.values()) {
      if (ins.order === order) {
        return ins;
      }
    }
    return null;
  }

  private bindEvents(): void {
    const c = this.canvas;

    c.addEventListener("wheel", (ev) => {
      ev.preventDefault();
      const factor = Math.pow(1.0015, -ev.deltaY);
      const worldX = (ev.offsetX - this.view.ox) / this.view.scale;
      const worldY = ev.offsetY - this.view.oy;
      this.view.scale = Math.min(60, Math.max(0.02, this.view.scale * factor));
      this.view.ox = ev.offsetX - worldX * this.view.scale;
      this.view.oy = ev.offsetY - worldY;
      this.dirty = true;
    });

    c.addEventListener("pointerdown", (ev) => {
      this.dragging = true;
      this.lastPtr = { x: ev.offsetX, y: ev.offsetY };
      c.setPointerCapture(ev.pointerId);
    });

    c.addEventListener("pointermove", (ev) => {
      if (this.dragging) {
        this.view.ox += ev.offsetX - this.lastPtr.x;
        this.view.oy += ev.offsetY - this.lastPtr.y;
        this.lastPtr = { x: ev.offsetX, y: ev.offsetY };
        this.dirty = true;
      } else {
        this.hover = this.insnAt(ev.offsetY);
        this.tooltip.style.display = this.hover ? "block" : "none";
        if (this.hover) {
          const stage = this.hover.segments[this.hover.segments.length - 1];
          const label = this.hover.label.replace(/&/g, "&amp;").replace(/</g, "&lt;");
          const stageName = stage ? STAGE_NAMES[stage.stage] : "?";
          const dur = stage ? stage.end - stage.start : 0;
          this.tooltip.innerHTML =
            `<b>#${this.hover.id}</b> ${label}<br>` +
            `${stageName} (${stage.stage}) at cycle ${stage ? stage.start : 0}, ` +
            `${dur} cycles${this.hover.flushed ? " · <span style='color:#f87171'>flushed</span>" : ""}`;
          this.tooltip.style.left = Math.min(ev.offsetX + 16, c.clientWidth - 320) + "px";
          this.tooltip.style.top = Math.max(ev.offsetY + 12, 8) + "px";
        }
      }
    });

    const stop = (ev: PointerEvent) => {
      if (this.dragging) {
        const moved = Math.abs(ev.offsetX - this.lastPtr.x) + Math.abs(ev.offsetY - this.lastPtr.y);
        if (moved < 4) {
          this.selected = this.insnAt(ev.offsetY);
          this.renderDetails();
        }
      }
      this.dragging = false;
    };
    c.addEventListener("pointerup", stop);
    c.addEventListener("pointerleave", () => {
      this.dragging = false;
      this.hover = null;
      this.tooltip.style.display = "none";
    });

    document.getElementById("filter")?.addEventListener("input", (ev) => {
      this.filter = (ev.target as HTMLInputElement).value.toLowerCase();
      this.dirty = true;
    });
    document.getElementById("zoom-in")?.addEventListener("click", () => {
      this.view.scale = Math.min(60, this.view.scale * 1.4);
      this.dirty = true;
    });
    document.getElementById("zoom-out")?.addEventListener("click", () => {
      this.view.scale = Math.max(0.02, this.view.scale / 1.4);
      this.dirty = true;
    });
    document.getElementById("reset")?.addEventListener("click", () => this.fit());
  }

  private renderDetails(): void {
    const el = this.details;
    if (!this.selected) {
      el.style.display = "none";
      return;
    }
    const ins = this.selected;
    const rows = ins.segments
      .map((s) => {
        const dur = s.end - s.start;
        const span = dur > 0 ? `${dur} cy` : "";
        return `<div><span style="display:inline-block;width:10px;height:10px;background:${STAGE_COLORS[s.stage]};border-radius:2px"></span> ` +
          `${STAGE_NAMES[s.stage]} <i>${s.stage}</i> · cycle ${s.start}–${s.end} ${span}</div>`;
      })
      .join("");
    el.style.display = "block";
    el.innerHTML =
      `<b>#${ins.id}</b> ${ins.label.replace(/&/g, "&amp;").replace(/</g, "&lt;")}` +
      (ins.flushed ? " <span style='color:#f87171'>(flushed)</span>" : "") +
      `<br><div style="margin-top:4px">${rows}</div>`;
  }

  render(): void {
    if (!this.dirty) {
      return;
    }
    this.dirty = false;
    const ctx = this.ctx;
    const w = this.canvas.clientWidth;
    const h = this.canvas.clientHeight;
    ctx.clearRect(0, 0, w, h);

    // Cycle axis
    const maxCycle = Math.max(1, ...[...this.insns.values()].map((i) => i.endCycle));
    const pxPerCycle = PX_PER_CYCLE * this.view.scale;
    const stepPow = Math.pow(10, Math.floor(Math.log10(80 / pxPerCycle)));
    let step = stepPow;
    for (const m of [1, 2, 5, 10]) {
      if (m * stepPow >= 80 / pxPerCycle) {
        step = m * stepPow;
        break;
      }
    }
    ctx.fillStyle = "#c8cdd3";
    ctx.font = "11px system-ui";
    ctx.textAlign = "left";
    for (let cy = 0; cy <= maxCycle; cy += step) {
      const x = this.view.ox + cy * pxPerCycle;
      if (x < GUTTER || x > w) {
        continue;
      }
      ctx.fillRect(x, AXIS_H - 6, 1, 6);
      ctx.fillText(String(cy), x + 3, AXIS_H - 9);
    }
    ctx.fillStyle = "#2a3038";
    ctx.fillRect(0, AXIS_H - 1, w, 1);

    // Instruction rows (virtualized: only the visible slice is drawn)
    const top = this.view.oy - ROW_H;
    const bottom = this.view.oy + h;
    const order0 = Math.max(0, Math.floor(top / ROW_H));
    const order1 = Math.ceil(bottom / ROW_H);

    const insns = [...this.insns.values()];
    // orders are dense (0..n-1); sort once for binary-free lookup via bisect-ish
    insns.sort((a, b) => a.order - b.order);
    const startIdx = Math.max(0, order0);
    const endIdx = Math.min(insns.length, order1 + 1);

    for (let i = startIdx; i < endIdx; i++) {
      const ins = insns[i];
      const y = AXIS_H + ins.order * ROW_H + this.view.oy;
      ctx.globalAlpha = !this.filter || ins.label.toLowerCase().includes(this.filter) ? 1 : DIM_ALPHA;
      if (y + ROW_H < AXIS_H || y > h) {
        continue;
      }
      // Label in the fixed gutter
      ctx.fillStyle = "#9aa4b0";
      ctx.font = "11px ui-monospace, monospace";
      ctx.textAlign = "left";
      ctx.fillText(ins.label.slice(0, 38), 8, y + ROW_H / 2 + 4);

      // Stage segments
      for (const seg of ins.segments) {
        const x0 = this.view.ox + seg.start * pxPerCycle;
        const x1 = this.view.ox + seg.end * pxPerCycle;
        const xa = Math.max(x0, GUTTER);
        const xb = Math.min(x1, w);
        if (xb <= xa || xb <= GUTTER) {
          continue;
        }
        ctx.fillStyle = STAGE_COLORS[seg.stage];
        ctx.fillRect(xa, y + 2, Math.max(1, xb - xa), ROW_H - 5);
      }
      if (ins.flushed) {
        ctx.fillStyle = "rgba(248,113,113,0.45)";
        const x0 = this.view.ox + ins.startCycle * pxPerCycle;
        ctx.fillRect(Math.max(x0, GUTTER), y + 2, Math.max(1, (this.view.ox + ins.endCycle * pxPerCycle) - Math.max(x0, GUTTER)), ROW_H - 5);
      }
      ctx.globalAlpha = 1;
      if (ins === this.selected) {
        ctx.strokeStyle = "#e2e8f0";
        ctx.lineWidth = 1.6;
        ctx.strokeRect(GUTTER, y + 1, w - GUTTER - 1, ROW_H - 2);
      }
    }

    // Gutter separator
    ctx.fillStyle = "#232a32";
    ctx.fillRect(GUTTER - 1, 0, 1, h);
    const _ = void maxCycle;
  }

  loop(): void {
    this.render();
    requestAnimationFrame(() => this.loop());
  }
}

// ------------------------------------------------------------------- boot

function init(): void {
  const canvas = document.getElementById("canvas") as HTMLCanvasElement | null;
  if (!canvas) {
    return;
  }
  const tooltip = document.getElementById("tooltip") as HTMLElement;
  const details = document.getElementById("details") as HTMLElement;
  const status = document.getElementById("status") as HTMLElement;
  const viewer = new Viewer(canvas, tooltip, details, status);

  const resize = () => viewer.resize();
  new ResizeObserver(resize).observe(canvas.parentElement ?? canvas);
  addEventListener("resize", resize);

  const fileInput = document.getElementById("file") as HTMLInputElement;
  fileInput.addEventListener("change", () => {
    const f = fileInput.files?.[0];
    if (!f) {
      return;
    }
    f.text().then((t) => viewer.load(t, f.name));
  });

  const params = new URLSearchParams(location.search);
  const traceUrl = params.get("trace");
  const loadRemote = (url: string) => {
    fetch(url)
      .then((r) => {
        if (!r.ok) {
          throw new Error(`${url}: HTTP ${r.status}`);
        }
        return r.text();
      })
      .then((t) => viewer.load(t, url.split("/").pop() ?? url))
      .catch((err) => {
        status.textContent = `failed to load ${url}: ${err.message}`;
      });
  };
  if (traceUrl) {
    loadRemote(traceUrl);
  } else {
    status.textContent = "drop a trace: ?trace=path/to/x.txt, or open a file";
  }

  viewer.resize();
  viewer.loop();
}

if (document.readyState === "loading") {
  document.addEventListener("DOMContentLoaded", init);
} else {
  init();
}