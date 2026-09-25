/-
Codegen/SoCDiagram.lean - Native Lean interactive SoC architecture diagram

Emits an interactive HTML/SVG visualization of the complete Shoumei SoC:
- Outer silicon die pad ring with pinout (clock, reset_n, UART, GPIO, DRAM bus)
- 2-Stage AASD Reset Synchronizer
- Out-of-Order CPU Core Complex
- Coherent Multi-Level Cache Hierarchy (L1I, L1D, L2) derived from CPUConfig
- TileLink TL-UH 1-to-8 Crossbar Interconnect
- Peripherals: BootROM, ACLINT, APLIC, UART, GPIO, SRAM
- Interactive sidebar inspector with register maps, gate/area stats, and Lean certificates
-/

import Shoumei.DSL
import Shoumei.RISCV.Config

namespace Shoumei.Codegen.SoCDiagram

open Shoumei
open Shoumei.RISCV

/-- Format capacity in bytes to human-readable string (e.g. 512 B, 8 KB, 16 KB, 1 MB). -/
def formatBytes (bytes : Nat) : String :=
  if bytes % (1024 * 1024) == 0 then s!"{bytes / (1024 * 1024)} MB"
  else if bytes % 1024 == 0 then s!"{bytes / 1024} KB"
  else s!"{bytes} B"

/-- Format cache way count for diagram labels (e.g. "Direct-Mapped", "2-Way Set-Assoc"). -/
def formatWays (ways : Nat) : String :=
  if ways == 1 then "Direct-Mapped"
  else s!"{ways}-Way Set-Assoc"

/-- Format cache way count for narrative descriptions (e.g. "direct-mapped", "2-way set-associative"). -/
def formatWaysDesc (ways : Nat) : String :=
  if ways == 1 then "direct-mapped"
  else s!"{ways}-way set-associative"

/-- Default output destination for the interactive diagram. -/
def defaultOutPath : System.FilePath := "output/architecture-visuals/soc-diagram.html"

/-- Render the complete HTML/SVG interactive SoC visualizer. -/
def renderHtml (config : CPUConfig) : String :=
  let g := config.cacheGeom
  let l1iBytes := g.levelBytes g.l1iSets g.l1iWays
  let l1dBytes := g.levelBytes g.l1dSets g.l1dWays
  let l2Bytes := g.levelBytes g.l2Sets g.l2Ways
  let lineBytes := g.lineBytes
  let lineBits := lineBytes * 8

  let l1iLabel := s!"{formatBytes l1iBytes} {formatWays g.l1iWays}"
  let l1dLabel := s!"{formatBytes l1dBytes} {formatWays g.l1dWays}"
  let l2Label := s!"{formatBytes l2Bytes} {formatWays g.l2Ways} • Tree-PLRU"
  let cacheLineSub := s!"{lineBytes}B Cache Lines • Write-Back • Tree-PLRU"

  let cacheDesc := s!"High-performance cache hierarchy comprising an {formatBytes l1iBytes} {formatWaysDesc g.l1iWays} L1I instruction cache, {formatBytes l1dBytes} {formatWaysDesc g.l1dWays} write-back L1D data cache, and a {formatBytes l2Bytes} {formatWaysDesc g.l2Ways} unified L2 cache with {lineBytes}B lines. Features Tree-PLRU replacement, single-cycle hit latency, and connects to external DRAM via a {lineBits}-bit line-refill bus."

  let headStyles := r##"<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Shoumei SoC &mdash; Interactive System-on-Chip Visualizer</title>
<style>
  :root {
    --bg: #0b0e14;
    --card-bg: #141a23;
    --card-border: #232c3b;
    --accent-cpu: #ff4d6d;
    --accent-cache: #ff85a1;
    --accent-bus: #4cc9f0;
    --accent-periph: #06d6a0;
    --accent-mem: #ffd166;
    --accent-irq: #b5179e;
    --text: #e0e6ed;
    --text-muted: #8892b0;
  }
  * { box-sizing: border-box; margin: 0; padding: 0; }
  body {
    font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, "Helvetica Neue", Arial, sans-serif;
    background: var(--bg);
    color: var(--text);
    display: flex;
    flex-direction: column;
    height: 100vh;
    overflow: hidden;
  }
  header {
    background: #111620;
    border-bottom: 1px solid var(--card-border);
    padding: 12px 24px;
    display: flex;
    justify-content: space-between;
    align-items: center;
    flex-shrink: 0;
  }
  header h1 {
    font-size: 18px;
    font-weight: 700;
    letter-spacing: 0.5px;
    display: flex;
    align-items: center;
    gap: 8px;
  }
  header h1 span.badge {
    background: #1e293b;
    color: var(--accent-bus);
    font-size: 11px;
    font-weight: 600;
    padding: 3px 8px;
    border-radius: 4px;
    border: 1px solid #334155;
  }
  .controls {
    display: flex;
    gap: 8px;
  }
  .btn {
    background: var(--card-bg);
    color: var(--text);
    border: 1px solid var(--card-border);
    padding: 6px 14px;
    border-radius: 6px;
    font-size: 13px;
    cursor: pointer;
    transition: all 0.15s ease;
  }
  .btn:hover {
    background: #1d2634;
    border-color: #3b495e;
  }
  .btn.active {
    background: #1e293b;
    border-color: var(--accent-bus);
    color: var(--accent-bus);
  }
  .workspace {
    display: flex;
    flex: 1;
    height: calc(100vh - 58px);
    position: relative;
  }
  .canvas-container {
    flex: 1;
    overflow: auto;
    display: flex;
    justify-content: center;
    align-items: center;
    padding: 24px;
    background: radial-gradient(circle at center, #111722 0%, #080a0f 100%);
  }
  svg.soc-svg {
    max-width: 100%;
    max-height: 100%;
    filter: drop-shadow(0 12px 32px rgba(0,0,0,0.6));
    user-select: none;
  }
  .block {
    cursor: pointer;
    transition: transform 0.15s ease, filter 0.15s ease;
  }
  .block:hover {
    filter: brightness(1.18);
  }
  .block.selected rect {
    stroke-width: 3px !important;
    stroke: #ffffff !important;
    filter: drop-shadow(0 0 10px rgba(255,255,255,0.4));
  }
  .inspector {
    width: 380px;
    background: var(--card-bg);
    border-left: 1px solid var(--card-border);
    display: flex;
    flex-direction: column;
    flex-shrink: 0;
    overflow-y: auto;
    padding: 20px;
  }
  .inspector h2 {
    font-size: 18px;
    margin-bottom: 4px;
    color: #fff;
  }
  .inspector .sub {
    font-size: 12px;
    color: var(--text-muted);
    margin-bottom: 16px;
    text-transform: uppercase;
    letter-spacing: 0.8px;
  }
  .metric-pill-grid {
    display: grid;
    grid-template-columns: 1fr 1fr;
    gap: 8px;
    margin-bottom: 20px;
  }
  .metric-pill {
    background: #0d1219;
    border: 1px solid #1f2735;
    border-radius: 6px;
    padding: 10px;
  }
  .metric-pill .label {
    font-size: 11px;
    color: var(--text-muted);
    margin-bottom: 2px;
  }
  .metric-pill .value {
    font-size: 15px;
    font-weight: 700;
    color: #fff;
    font-family: monospace;
  }
  .section-title {
    font-size: 13px;
    font-weight: 600;
    color: var(--text-muted);
    text-transform: uppercase;
    letter-spacing: 0.6px;
    margin: 16px 0 8px 0;
    border-bottom: 1px solid #1e2532;
    padding-bottom: 4px;
  }
  .desc-box {
    font-size: 13px;
    line-height: 1.5;
    color: #c0cad6;
    margin-bottom: 16px;
  }
  .port-list {
    list-style: none;
    font-family: monospace;
    font-size: 12px;
  }
  .port-list li {
    padding: 4px 6px;
    border-radius: 4px;
    margin-bottom: 3px;
    display: flex;
    justify-content: space-between;
    background: #0e141c;
  }
  .port-in { color: #4cc9f0; }
  .port-out { color: #f72585; }
  .port-dir {
    font-size: 10px;
    padding: 2px 4px;
    border-radius: 3px;
    background: #1b2330;
  }
</style>
</head>
<body>

<header>
"##

  let headerBar :=
    s!"  <h1>証明 Shoumei SoC <span class=\"badge\">{config.isaString} • TileLink TL-UH • {config.dispatchWidth}-Way OoO</span></h1>\n" ++
    r##"  <div class="controls">
    <button class="btn active" id="btn-all" onclick="filterView('all')">Full Chip</button>
    <button class="btn" id="btn-bus" onclick="filterView('bus')">TileLink Interconnect</button>
    <button class="btn" id="btn-irq" onclick="filterView('irq')">Interrupt Matrix</button>
    <a class="btn" href="index.html">&larr; Architecture Hub</a>
  </div>
</header>

<div class="workspace">
  <div class="canvas-container">
    <svg class="soc-svg" viewBox="0 0 1060 840" width="1020" height="800">
      <defs>
        <linearGradient id="cpuGrad" x1="0%" y1="0%" x2="100%" y2="100%">
          <stop offset="0%" stop-color="#2a1220" />
          <stop offset="100%" stop-color="#190d16" />
        </linearGradient>
        <linearGradient id="cacheGrad" x1="0%" y1="0%" x2="100%" y2="100%">
          <stop offset="0%" stop-color="#24132b" />
          <stop offset="100%" stop-color="#140a1c" />
        </linearGradient>
        <linearGradient id="busGrad" x1="0%" y1="0%" x2="100%" y2="100%">
          <stop offset="0%" stop-color="#0e2338" />
          <stop offset="100%" stop-color="#081422" />
        </linearGradient>
        <linearGradient id="periphGrad" x1="0%" y1="0%" x2="100%" y2="100%">
          <stop offset="0%" stop-color="#0d2822" />
          <stop offset="100%" stop-color="#081714" />
        </linearGradient>
        <linearGradient id="sramGrad" x1="0%" y1="0%" x2="100%" y2="100%">
          <stop offset="0%" stop-color="#2d2410" />
          <stop offset="100%" stop-color="#1a1508" />
        </linearGradient>
        <marker id="arrow-bus" markerWidth="6" markerHeight="6" refX="5" refY="3" orient="auto">
          <path d="M0,0 L6,3 L0,6 Z" fill="#4cc9f0" />
        </marker>
        <marker id="arrow-irq" markerWidth="6" markerHeight="6" refX="5" refY="3" orient="auto">
          <path d="M0,0 L6,3 L0,6 Z" fill="#b5179e" />
        </marker>
      </defs>

      <!-- Outer Silicon Die / Pad Ring -->
      <rect x="20" y="20" width="1020" height="800" rx="16" fill="#0d1117" stroke="#30363d" stroke-width="2" />
      <text x="40" y="46" fill="#8b949e" font-family="monospace" font-size="12" font-weight="600">SHMIC_ASIC_DIE_TOP // 8.46 mm&sup2; (GF180) &bull; 0.033 mm&sup2; (ASAP7)</text>

      <!-- NORTH PADS -->
      <g id="north-pads">
        <rect x="80" y="6" width="70" height="20" rx="4" fill="#1f242c" stroke="#4cc9f0" stroke-width="1.5" />
        <text x="115" y="20" fill="#4cc9f0" font-family="monospace" font-size="11" text-anchor="middle">clock</text>
        <line x1="115" y1="26" x2="115" y2="70" stroke="#4cc9f0" stroke-width="2" stroke-dasharray="3 3" />

        <rect x="180" y="6" width="80" height="20" rx="4" fill="#1f242c" stroke="#4cc9f0" stroke-width="1.5" />
        <text x="220" y="20" fill="#4cc9f0" font-family="monospace" font-size="11" text-anchor="middle">reset_n</text>
        <line x1="220" y1="26" x2="220" y2="70" stroke="#4cc9f0" stroke-width="2" stroke-dasharray="3 3" />

        <rect x="720" y="6" width="80" height="20" rx="4" fill="#1f242c" stroke="#06d6a0" stroke-width="1.5" />
        <text x="760" y="20" fill="#06d6a0" font-family="monospace" font-size="11" text-anchor="middle">uart_rx</text>

        <rect x="830" y="6" width="80" height="20" rx="4" fill="#1f242c" stroke="#06d6a0" stroke-width="1.5" />
        <text x="870" y="20" fill="#06d6a0" font-family="monospace" font-size="11" text-anchor="middle">uart_tx</text>

        <rect x="930" y="6" width="90" height="20" rx="4" fill="#1f242c" stroke="#e0e6ed" stroke-width="1.5" />
        <text x="975" y="20" fill="#e0e6ed" font-family="monospace" font-size="11" text-anchor="middle">rob_empty</text>
      </g>

      <!-- 1. ResetSync -->
      <g class="block" id="blk-resetsync" onclick="selectBlock('resetsync')">
        <rect x="60" y="70" width="220" height="50" rx="8" fill="#1e2330" stroke="#3b4b66" stroke-width="1.5" />
        <text x="170" y="94" fill="#fff" font-size="13" font-weight="700" text-anchor="middle">ResetSync</text>
        <text x="170" y="110" fill="#8892b0" font-size="10" text-anchor="middle">2-Stage AASD Synchronizer</text>
      </g>
"##

  let cpuAndCaches :=
    s!"      <!-- 2. CPU Core Complex (CPU_W{config.dispatchWidth}) -->\n" ++
    r##"      <g class="block" id="blk-cpu" onclick="selectBlock('cpu')">
        <rect x="60" y="150" width="560" height="340" rx="12" fill="url(#cpuGrad)" stroke="#ff4d6d" stroke-width="2" />
"## ++
    s!"        <text x=\"80\" y=\"180\" fill=\"#ff4d6d\" font-size=\"16\" font-weight=\"800\">CPU_W{config.dispatchWidth} Core ({config.isaString} OoO)</text>\n" ++
    s!"        <text x=\"80\" y=\"198\" fill=\"#a0aec0\" font-size=\"11\">{config.dispatchWidth}-Way Dispatch • {config.commitWidth}-Way Commit • 64 Physical Registers</text>\n" ++
    r##"
        <!-- Sub-units in CPU -->
        <rect x="80" y="220" width="155" height="60" rx="6" fill="#3b1525" stroke="#ff758f" stroke-width="1" />
        <text x="157" y="246" fill="#fff" font-size="12" font-weight="600" text-anchor="middle">Fetch &amp; Rename</text>
        <text x="157" y="264" fill="#ffb3c6" font-size="10" text-anchor="middle">64-Tag RAT + FreeList</text>

        <rect x="250" y="220" width="180" height="60" rx="6" fill="#3b1525" stroke="#ff758f" stroke-width="1" />
        <text x="340" y="246" fill="#fff" font-size="12" font-weight="600" text-anchor="middle">Execution Units</text>
        <text x="340" y="264" fill="#ffb3c6" font-size="10" text-anchor="middle">Dual ALU • MulDiv • FPU(D)</text>

        <rect x="445" y="220" width="155" height="60" rx="6" fill="#3b1525" stroke="#ff758f" stroke-width="1" />
        <text x="522" y="246" fill="#fff" font-size="12" font-weight="600" text-anchor="middle">ROB &amp; Retirement</text>
        <text x="522" y="264" fill="#ffb3c6" font-size="10" text-anchor="middle">16-Entry Dual-Retire</text>

        <rect x="80" y="300" width="235" height="60" rx="6" fill="#3b1525" stroke="#ff758f" stroke-width="1" />
        <text x="197" y="326" fill="#fff" font-size="12" font-weight="600" text-anchor="middle">LSU &amp; Store Buffer</text>
        <text x="197" y="344" fill="#ffb3c6" font-size="10" text-anchor="middle">8-Entry SB • 1-Cycle Snoop</text>

        <rect x="330" y="300" width="270" height="60" rx="6" fill="#3b1525" stroke="#ff758f" stroke-width="1" />
        <text x="465" y="326" fill="#fff" font-size="12" font-weight="600" text-anchor="middle">CSR &amp; Trap Sequencer</text>
        <text x="465" y="344" fill="#ffb3c6" font-size="10" text-anchor="middle">Microcoded Trap Entry &amp; MRET</text>

        <!-- PRF file indicator -->
        <rect x="80" y="380" width="520" height="40" rx="6" fill="#240c18" stroke="#ff758f" stroke-width="1" stroke-dasharray="4 2" />
        <text x="340" y="405" fill="#ffccd5" font-size="11" text-anchor="middle">Unified PhysRegFile (64&times;64-bit Int + 64&times;64-bit FP)</text>
      </g>

      <!-- 3. Memory Hierarchy (Caches) -->
      <g class="block" id="blk-caches" onclick="selectBlock('caches')">
        <rect x="650" y="150" width="350" height="180" rx="12" fill="url(#cacheGrad)" stroke="#ff85a1" stroke-width="1.5" />
        <text x="670" y="180" fill="#ff85a1" font-size="15" font-weight="700">MemoryHierarchy</text>
"## ++
    s!"        <text x=\"670\" y=\"196\" fill=\"#a0aec0\" font-size=\"11\">{cacheLineSub}</text>\n\n" ++
    r##"        <rect x="670" y="215" width="145" height="45" rx="6" fill="#3d1e44" stroke="#f72585" stroke-width="1" />
        <text x="742" y="236" fill="#fff" font-size="11" font-weight="600" text-anchor="middle">L1I Cache</text>
"## ++
    s!"        <text x=\"742\" y=\"250\" fill=\"#ffb3c6\" font-size=\"9\" text-anchor=\"middle\">{l1iLabel}</text>\n\n" ++
    r##"        <rect x="835" y="215" width="145" height="45" rx="6" fill="#3d1e44" stroke="#f72585" stroke-width="1" />
        <text x="907" y="236" fill="#fff" font-size="11" font-weight="600" text-anchor="middle">L1D Cache</text>
"## ++
    s!"        <text x=\"907\" y=\"250\" fill=\"#ffb3c6\" font-size=\"9\" text-anchor=\"middle\">{l1dLabel}</text>\n\n" ++
    r##"        <rect x="670" y="270" width="310" height="45" rx="6" fill="#3d1e44" stroke="#f72585" stroke-width="1" />
        <text x="825" y="291" fill="#fff" font-size="11" font-weight="600" text-anchor="middle">L2 Unified Cache</text>
"## ++
    s!"        <text x=\"825\" y=\"305\" fill=\"#ffb3c6\" font-size=\"9\" text-anchor=\"middle\">{l2Label}</text>\n" ++
    r##"      </g>

      <!-- Interconnect Bus (TileLink TL-UH Crossbar) -->
      <g class="block" id="blk-xbar" onclick="selectBlock('xbar')">
        <rect x="60" y="520" width="940" height="70" rx="10" fill="url(#busGrad)" stroke="#4cc9f0" stroke-width="2" />
        <text x="530" y="550" fill="#4cc9f0" font-size="16" font-weight="800" text-anchor="middle">TileLink TL-UH 1-to-8 Crossbar (TLXbar8)</text>
        <text x="530" y="570" fill="#a0c4ff" font-size="11" text-anchor="middle">Channel A (Request/Data) &bull; Channel D (Response/Ack) &bull; Zero Combinational Loops</text>
      </g>

      <!-- Bus lines connecting CPU/Snoop to Crossbar -->
      <g id="flow-snoop">
        <line x1="200" y1="490" x2="200" y2="520" stroke="#4cc9f0" stroke-width="3" marker-end="url(#arrow-bus)" />
        <text x="210" y="510" fill="#4cc9f0" font-family="monospace" font-size="10">store_snoop (MMIO)</text>
      </g>

      <!-- 4. Peripherals Row -->
      <!-- P0: BootROM -->
      <g class="block" id="blk-bootrom" onclick="selectBlock('bootrom')">
        <rect x="60" y="630" width="130" height="85" rx="8" fill="url(#periphGrad)" stroke="#06d6a0" stroke-width="1.5" />
        <text x="125" y="655" fill="#06d6a0" font-size="13" font-weight="700" text-anchor="middle">BootROM</text>
        <text x="125" y="673" fill="#8892b0" font-size="10" text-anchor="middle">Port 0 &bull; 512 B</text>
        <text x="125" y="695" fill="#fff" font-family="monospace" font-size="9" text-anchor="middle">0x0001_0000</text>
        <line x1="125" y1="590" x2="125" y2="630" stroke="#4cc9f0" stroke-width="2" marker-end="url(#arrow-bus)" />
      </g>

      <!-- P1: ACLINT -->
      <g class="block" id="blk-aclint" onclick="selectBlock('aclint')">
        <rect x="210" y="630" width="150" height="85" rx="8" fill="url(#periphGrad)" stroke="#06d6a0" stroke-width="1.5" />
        <text x="285" y="655" fill="#06d6a0" font-size="13" font-weight="700" text-anchor="middle">ACLINT</text>
        <text x="285" y="673" fill="#8892b0" font-size="10" text-anchor="middle">Port 1 &bull; MTIMER/MSWI</text>
        <text x="285" y="695" fill="#fff" font-family="monospace" font-size="9" text-anchor="middle">0x0200_0000</text>
        <line x1="285" y1="590" x2="285" y2="630" stroke="#4cc9f0" stroke-width="2" marker-end="url(#arrow-bus)" />
      </g>

      <!-- P4: APLIC -->
      <g class="block" id="blk-aplic" onclick="selectBlock('aplic')">
        <rect x="380" y="630" width="150" height="85" rx="8" fill="url(#periphGrad)" stroke="#06d6a0" stroke-width="1.5" />
        <text x="455" y="655" fill="#06d6a0" font-size="13" font-weight="700" text-anchor="middle">APLIC</text>
        <text x="455" y="673" fill="#8892b0" font-size="10" text-anchor="middle">Port 4 &bull; AIA Direct</text>
        <text x="455" y="695" fill="#fff" font-family="monospace" font-size="9" text-anchor="middle">0x0C00_0000</text>
        <line x1="455" y1="590" x2="455" y2="630" stroke="#4cc9f0" stroke-width="2" marker-end="url(#arrow-bus)" />
      </g>

      <!-- P5: UART -->
      <g class="block" id="blk-uart" onclick="selectBlock('uart')">
        <rect x="550" y="630" width="140" height="85" rx="8" fill="url(#periphGrad)" stroke="#06d6a0" stroke-width="1.5" />
        <text x="620" y="655" fill="#06d6a0" font-size="13" font-weight="700" text-anchor="middle">UART (8-N-1)</text>
        <text x="620" y="673" fill="#8892b0" font-size="10" text-anchor="middle">Port 5 &bull; 115.2k Baud</text>
        <text x="620" y="695" fill="#fff" font-family="monospace" font-size="9" text-anchor="middle">0x1000_0000</text>
        <line x1="620" y1="590" x2="620" y2="630" stroke="#4cc9f0" stroke-width="2" marker-end="url(#arrow-bus)" />
      </g>

      <!-- P6: GPIO -->
      <g class="block" id="blk-gpio" onclick="selectBlock('gpio')">
        <rect x="710" y="630" width="130" height="85" rx="8" fill="url(#periphGrad)" stroke="#06d6a0" stroke-width="1.5" />
        <text x="775" y="655" fill="#06d6a0" font-size="13" font-weight="700" text-anchor="middle">GPIO (8-Bit)</text>
        <text x="775" y="673" fill="#8892b0" font-size="10" text-anchor="middle">Port 6 &bull; Bi-Dir</text>
        <text x="775" y="695" fill="#fff" font-family="monospace" font-size="9" text-anchor="middle">0x1001_0000</text>
        <line x1="775" y1="590" x2="775" y2="630" stroke="#4cc9f0" stroke-width="2" marker-end="url(#arrow-bus)" />
      </g>

      <!-- P7: SRAM -->
      <g class="block" id="blk-sram" onclick="selectBlock('sram')">
        <rect x="860" y="630" width="140" height="85" rx="8" fill="url(#sramGrad)" stroke="#ffd166" stroke-width="1.5" />
        <text x="930" y="655" fill="#ffd166" font-size="13" font-weight="700" text-anchor="middle">Scratchpad SRAM</text>
        <text x="930" y="673" fill="#8892b0" font-size="10" text-anchor="middle">Port 7 &bull; 4 KB</text>
        <text x="930" y="695" fill="#fff" font-family="monospace" font-size="9" text-anchor="middle">0x8000_0000</text>
        <line x1="930" y1="590" x2="930" y2="630" stroke="#4cc9f0" stroke-width="2" marker-end="url(#arrow-bus)" />
      </g>

      <!-- Interrupt routing paths (dashed magenta) -->
      <g id="flow-irqs">
        <!-- ACLINT to CPU -->
        <path d="M 285,630 L 285,500" stroke="#b5179e" stroke-width="2" stroke-dasharray="4 3" marker-end="url(#arrow-irq)" />
        <text x="240" y="510" fill="#b5179e" font-family="monospace" font-size="9">mtip/msip</text>

        <!-- UART to APLIC -->
        <path d="M 620,630 L 620,610 L 490,610 L 490,630" fill="none" stroke="#b5179e" stroke-width="2" stroke-dasharray="4 3" marker-end="url(#arrow-irq)" />
        <text x="540" y="605" fill="#b5179e" font-family="monospace" font-size="9">uart_irq</text>

        <!-- GPIO to APLIC -->
        <path d="M 775,630 L 775,600 L 510,600 L 510,630" fill="none" stroke="#b5179e" stroke-width="2" stroke-dasharray="4 3" marker-end="url(#arrow-irq)" />
        <text x="680" y="596" fill="#b5179e" font-family="monospace" font-size="9">gpio_irq</text>

        <!-- APLIC to CPU -->
        <path d="M 455,630 L 455,500" stroke="#b5179e" stroke-width="2" stroke-dasharray="4 3" marker-end="url(#arrow-irq)" />
        <text x="462" y="510" fill="#b5179e" font-family="monospace" font-size="9">meip_in</text>
      </g>

      <!-- SOUTH PADS -->
      <g id="south-pads">
        <rect x="680" y="800" width="190" height="25" rx="4" fill="#1f242c" stroke="#06d6a0" stroke-width="1.5" />
        <text x="775" y="817" fill="#06d6a0" font-family="monospace" font-size="11" text-anchor="middle">gpio_i/o/oen[7:0]</text>
        <line x1="775" y1="715" x2="775" y2="800" stroke="#06d6a0" stroke-width="2" />

        <rect x="250" y="800" width="320" height="25" rx="4" fill="#1f242c" stroke="#ffd166" stroke-width="1.5" />
        <text x="410" y="817" fill="#ffd166" font-family="monospace" font-size="11" text-anchor="middle">mem_req_* &amp; mem_resp_* (L2 Refill/DRAM)</text>
        <path d="M 825,330 L 825,480 L 410,480 L 410,800" fill="none" stroke="#ffd166" stroke-width="2.5" stroke-dasharray="5 3" marker-end="url(#arrow-bus)" />
      </g>
    </svg>
  </div>

  <!-- Inspector Sidebar -->
  <div class="inspector" id="inspector">
    <h2 id="ins-name">Shoumei_SoC</h2>
    <div class="sub" id="ins-type">Complete System-on-Chip Top</div>
    <div class="metric-pill-grid">
      <div class="metric-pill">
        <div class="label">GF180 Cell Area</div>
        <div class="value" id="ins-gf180">8.46 mm&sup2;</div>
      </div>
      <div class="metric-pill">
        <div class="label">ASAP7 Cell Area</div>
        <div class="value" id="ins-asap7">32,785 &micro;m&sup2;</div>
      </div>
      <div class="metric-pill">
        <div class="label">Sequential FFs</div>
        <div class="value" id="ins-ffs">29,588</div>
      </div>
      <div class="metric-pill">
        <div class="label">Clock Freq</div>
        <div class="value" id="ins-clock">64M / 1.0G</div>
      </div>
    </div>

    <div class="section-title">Block Description</div>
    <div class="desc-box" id="ins-desc">
      Select any block or pad in the SoC diagram to inspect its interface, TileLink port assignment, register mappings, and verification proofs.
    </div>

    <div class="section-title">Key Ports &amp; Interfaces</div>
    <ul class="port-list" id="ins-ports">
      <li><span class="port-in">clock</span> <span class="port-dir">INPUT (1b)</span></li>
      <li><span class="port-in">reset_n</span> <span class="port-dir">INPUT (1b)</span></li>
      <li><span class="port-in">uart_rx</span> <span class="port-dir">INPUT (1b)</span></li>
      <li><span class="port-out">uart_tx</span> <span class="port-dir">OUTPUT (1b)</span></li>
      <li><span class="port-in">gpio_i[7:0]</span> <span class="port-dir">INPUT (8b)</span></li>
      <li><span class="port-out">gpio_o[7:0]</span> <span class="port-dir">OUTPUT (8b)</span></li>
      <li><span class="port-out">mem_req_valid</span> <span class="port-dir">OUTPUT (1b)</span></li>
      <li><span class="port-in">mem_resp_valid</span> <span class="port-dir">INPUT (1b)</span></li>
    </ul>

    <div class="section-title">Formal Verification &amp; Provenance</div>
    <div class="desc-box" id="ins-proof">
      <b>Lean 4 DSL:</b> <code>lean/Shoumei/SoC/ShoumeiSoC.lean</code><br>
      <b>Proofs:</b> <code>ShoumeiSoCProofs.lean</code> (5 structural theorems, 100% discharge)<br>
      <b>Certificate:</b> <code>shoumeiSoC_cert</code> (9 compositional dependencies verified)
    </div>
  </div>
</div>

<script>
const BLOCKS = {
  cpu: {
    name: "CPU_W2 Core",
    type: "2-Way Superscalar OoO Compute Core",
    gf180: "8.32 mm²",
    asap7: "32,240 µm²",
    ffs: "29,180",
    clock: "64 MHz / 1.0 GHz",
"##

  let cpuDesc :=
    s!"    desc: \"Out-of-Order execution engine implementing {config.isaString}. Features 64-entry physical register files (Int & FP), 16-entry dual-retire ROB, speculative store buffer with 1-cycle dequeue-fire snoop, branch predictor, microcoded trap sequencer, and pipelined double-precision FPU.\",\n" ++
    r##"    ports: [
      { name: "clock", dir: "INPUT", cls: "port-in" },
      { name: "sync_reset", dir: "INPUT", cls: "port-in" },
      { name: "mtip_in / msip_in", dir: "INPUT", cls: "port-in" },
      { name: "meip_in (APLIC)", dir: "INPUT", cls: "port-in" },
      { name: "store_snoop_valid", dir: "OUTPUT", cls: "port-out" },
      { name: "store_snoop_addr[31:0]", dir: "OUTPUT", cls: "port-out" },
      { name: "store_snoop_data[63:0]", dir: "OUTPUT", cls: "port-out" },
      { name: "rob_empty", dir: "OUTPUT", cls: "port-out" }
    ],
    proof: "<b>File:</b> <code>lean/Shoumei/RISCV/CPU.lean</code><br><b>Verification:</b> RAT & FreeList invariants proven, ROB FIFO order preserved, 0 axioms, 100% discharged."
  },
  caches: {
    name: "MemoryHierarchy",
    type: "Multi-Level Cache Subsystem",
    gf180: "0.12 mm²",
    asap7: "473 µm²",
    ffs: "280",
    clock: "64 MHz / 1.0 GHz",
"##

  let cachesSection :=
    s!"    desc: \"{cacheDesc}\",\n" ++
    r##"    ports: [
      { name: "ifetch_addr[31:0]", dir: "INPUT", cls: "port-in" },
      { name: "ifetch_data[31:0]", dir: "OUTPUT", cls: "port-out" },
      { name: "dmem_req_*", dir: "INPUT", cls: "port-in" },
      { name: "dmem_resp_*", dir: "OUTPUT", cls: "port-out" },
"## ++
    s!"      \{ name: \"mem_req_* ({lineBits}b line)\", dir: \"OUTPUT\", cls: \"port-out\" },\n" ++
    s!"      \{ name: \"mem_resp_* ({lineBits}b line)\", dir: \"INPUT\", cls: \"port-in\" }\n" ++
    r##"    ],
    proof: "<b>File:</b> <code>lean/Shoumei/RISCV/Memory/Cache/MemoryHierarchy.lean</code><br><b>Theorems:</b> <code>fence_i_invalidates_l1i</code>, <code>fence_i_clears_l1d_dirty</code>, <code>memoryHierarchy_cert</code> (100% discharged)."
  },
  xbar: {
    name: "TLXbar8",
    type: "TileLink TL-UH 1-to-8 Crossbar Interconnect",
    gf180: "8,920 µm²",
    asap7: "34.5 µm²",
    ffs: "0 (Pure Comb)",
    clock: "Unclocked",
    desc: "Full crossbar interconnect routing CPU MMIO requests from Master Channel A to 8 slave devices based on memory map decoding. Implements TileLink TL-UH protocol with zero combinational loops and standard handshake routing.",
    ports: [
      { name: "m_a_* (Master Ch A)", dir: "INPUT", cls: "port-in" },
      { name: "m_d_* (Master Ch D)", dir: "OUTPUT", cls: "port-out" },
      { name: "s0..s7_a_* (Slave A)", dir: "OUTPUT", cls: "port-out" },
      { name: "s0..s7_d_* (Slave D)", dir: "INPUT", cls: "port-in" }
    ],
    proof: "<b>File:</b> <code>lean/Shoumei/Interconnect/TileLink/TLXbar.lean</code><br><b>Theorems:</b> <code>tlXbar8_routes_port0</code>, <code>tlXbar8_routes_port5_uart</code>, <code>tlXbar8_instances</code> (native_decide)."
  },
  uart: {
    name: "UART (8-N-1)",
    type: "TileLink Serial Communication Peripheral",
    gf180: "3,850 µm²",
    asap7: "16.2 µm²",
    ffs: "38",
    clock: "115,200 Baud",
    desc: "Full-duplex 8-N-1 UART with 16x oversampled receiver, shift-register transmitter, and programmable baud clock divisor. MMIO registers: 0x00 DATA (TX/RX buffer), 0x04 STATUS (busy/ready), 0x08 CTRL (IRQ en), 0x0C DIV (divisor).",
    ports: [
      { name: "uart_rx", dir: "INPUT", cls: "port-in" },
      { name: "uart_tx", dir: "OUTPUT", cls: "port-out" },
      { name: "uart_irq", dir: "OUTPUT", cls: "port-out" },
      { name: "tl_a / tl_d", dir: "SLAVE", cls: "port-in" }
    ],
    proof: "<b>File:</b> <code>lean/Shoumei/Peripherals/UART.lean</code><br><b>Theorems:</b> <code>uart_framing</code>, <code>uart_baud_div</code>, <code>uart_ports</code>."
  },
  aclint: {
    name: "ACLINT",
    type: "Advanced Core Local Interruptor",
    gf180: "4,120 µm²",
    asap7: "17.4 µm²",
    ffs: "66",
    clock: "Core Clock",
    desc: "RISC-V spec compliant interruptor block hosting 64-bit real-time counter (mtime), 64-bit timer comparator (mtimecmp), and inter-processor software interrupt register (msip). Generates mtip and msip directly to the core.",
    ports: [
      { name: "soc_mtip", dir: "OUTPUT", cls: "port-out" },
      { name: "soc_msip", dir: "OUTPUT", cls: "port-out" },
      { name: "tl_a / tl_d", dir: "SLAVE", cls: "port-in" }
    ],
    proof: "<b>File:</b> <code>lean/Shoumei/Peripherals/ACLINT.lean</code><br><b>Theorems:</b> <code>aclint_mtime_inc</code>, <code>aclint_cmp_fire</code>."
  },
  aplic: {
    name: "APLIC",
    type: "AIA Platform-Level Interrupt Controller",
    gf180: "1,850 µm²",
    asap7: "7.8 µm²",
    ffs: "8",
    clock: "Core Clock",
    desc: "RISC-V Advanced Interrupt Architecture (AIA) compliant controller in Direct Delivery mode. Arbitrates priority between peripheral interrupts (UART IRQ 1, GPIO IRQ 2) and asserts soc_meip to the CPU.",
    ports: [
      { name: "uart_irq (Src 1)", dir: "INPUT", cls: "port-in" },
      { name: "gpio_irq (Src 2)", dir: "INPUT", cls: "port-in" },
      { name: "soc_meip", dir: "OUTPUT", cls: "port-out" }
    ],
    proof: "<b>File:</b> <code>lean/Shoumei/Peripherals/APLIC.lean</code><br><b>Theorems:</b> <code>aplic_priority_arb</code>, <code>aplic_ports</code>."
  },
  gpio: {
    name: "GPIO (8-Bit)",
    type: "General Purpose Digital Input/Output",
    gf180: "1,620 µm²",
    asap7: "6.9 µm²",
    ffs: "16",
    clock: "Core Clock",
    desc: "8-bit bidirectional digital I/O port with programmable direction register, output data latch, and input edge interrupt generation.",
    ports: [
      { name: "gpio_i[7:0]", dir: "INPUT", cls: "port-in" },
      { name: "gpio_o[7:0]", dir: "OUTPUT", cls: "port-out" },
      { name: "gpio_oen[7:0]", dir: "OUTPUT", cls: "port-out" },
      { name: "gpio_irq", dir: "OUTPUT", cls: "port-out" }
    ],
    proof: "<b>File:</b> <code>lean/Shoumei/Peripherals/GPIO.lean</code><br><b>Theorems:</b> <code>gpio_oen_mask</code>, <code>gpio_irq_edge</code>."
  },
  bootrom: {
    name: "BootROM",
    type: "On-Chip Power-on Bootloader ROM",
    gf180: "950 µm²",
    asap7: "4.1 µm²",
    ffs: "0 (Pure ROM)",
    clock: "Asynchronous Read",
    desc: "512-byte on-chip ROM located at 0x0001_0000. Houses initial power-on reset code, hardware self-test routines, and jump vector to main memory.",
    ports: [
      { name: "tl_a[31:0]", dir: "INPUT", cls: "port-in" },
      { name: "tl_d[63:0]", dir: "OUTPUT", cls: "port-out" }
    ],
    proof: "<b>File:</b> <code>lean/Shoumei/Peripherals/BootROM.lean</code><br><b>Theorems:</b> <code>bootrom_vector_read</code>."
  },
  sram: {
    name: "Scratchpad SRAM",
    type: "4 KB On-Chip Zero-Wait Memory",
    gf180: "3,200 µm²",
    asap7: "13.6 µm²",
    ffs: "0 (SRAM Macro)",
    clock: "Synchronous",
    desc: "4 Kilobyte on-chip scratchpad memory mapped at 0x8000_0000. Provides deterministic zero-wait-state storage for critical real-time interrupt handlers.",
    ports: [
      { name: "tl_a[31:0]", dir: "INPUT", cls: "port-in" },
      { name: "tl_d[63:0]", dir: "OUTPUT", cls: "port-out" }
    ],
    proof: "<b>File:</b> <code>lean/Shoumei/Peripherals/SRAM.lean</code><br><b>Theorems:</b> <code>sram_read_write_coherence</code>."
  },
  resetsync: {
    name: "ResetSync",
    type: "2-Stage AASD Reset Synchronizer",
    gf180: "140 µm²",
    asap7: "0.6 µm²",
    ffs: "2",
    clock: "Core Clock",
    desc: "Asynchronous-Assert Synchronous-Deassert (AASD) synchronizer. Prevents reset recovery/removal timing violations across the clock domain upon releasing reset_n.",
    ports: [
      { name: "clock", dir: "INPUT", cls: "port-in" },
      { name: "reset_n", dir: "INPUT", cls: "port-in" },
      { name: "sync_reset", dir: "OUTPUT", cls: "port-out" }
    ],
    proof: "<b>File:</b> <code>lean/Shoumei/Circuits/Sequential/ResetSync.lean</code><br><b>Theorems:</b> <code>resetSync_ff_count</code>, <code>resetSync_aasd_property</code>."
  }
};

let currentSelected = null;

function selectBlock(id) {
  const data = BLOCKS[id];
  if (!data) return;

  document.querySelectorAll('.block').forEach(b => b.classList.remove('selected'));
  const el = document.getElementById('blk-' + id);
  if (el) el.classList.add('selected');

  document.getElementById('ins-name').innerText = data.name;
  document.getElementById('ins-type').innerText = data.type;
  document.getElementById('ins-gf180').innerText = data.gf180;
  document.getElementById('ins-asap7').innerText = data.asap7;
  document.getElementById('ins-ffs').innerText = data.ffs;
  document.getElementById('ins-clock').innerText = data.clock;
  document.getElementById('ins-desc').innerHTML = data.desc;
  document.getElementById('ins-proof').innerHTML = data.proof;

  const portList = document.getElementById('ins-ports');
  portList.innerHTML = data.ports.map(p =>
    `<li><span class="${p.cls}">${p.name}</span> <span class="port-dir">${p.dir}</span></li>`
  ).join('');
}

function filterView(mode) {
  document.querySelectorAll('.controls button').forEach(b => b.classList.remove('active'));
  document.getElementById('btn-' + mode).classList.add('active');

  const busLines = document.querySelectorAll('#flow-snoop, [id^="blk-bootrom"] line, [id^="blk-aclint"] line, [id^="blk-aplic"] line, [id^="blk-uart"] line, [id^="blk-gpio"] line, [id^="blk-sram"] line');
  const irqLines = document.querySelectorAll('#flow-irqs');

  if (mode === 'all') {
    busLines.forEach(l => l.style.opacity = '1');
    irqLines.forEach(l => l.style.opacity = '1');
  } else if (mode === 'bus') {
    busLines.forEach(l => l.style.opacity = '1');
    irqLines.forEach(l => l.style.opacity = '0.1');
  } else if (mode === 'irq') {
    busLines.forEach(l => l.style.opacity = '0.1');
    irqLines.forEach(l => l.style.opacity = '1');
  }
}
</script>
</body>
</html>
"##

  headStyles ++ headerBar ++ cpuAndCaches ++ cpuDesc ++ cachesSection

/-- Generate the interactive SoC diagram HTML file. -/
def generate (config : CPUConfig := defaultCPUConfig)
    (outPath : System.FilePath := defaultOutPath) : IO Unit := do
  if let some parentDir := outPath.parent then
    IO.FS.createDirAll parentDir
  IO.FS.writeFile outPath (renderHtml config)
  IO.println s!"✓ Generated interactive SoC visualization: {outPath}"

end Shoumei.Codegen.SoCDiagram
