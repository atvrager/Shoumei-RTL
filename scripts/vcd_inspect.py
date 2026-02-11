#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# ///
"""VCD signal inspector for Shoumei RTL debugging.

Usage examples:
  # List all signals matching a pattern
  ./scripts/vcd_inspect.py shoumei_cpu.vcd --list "muldiv*"

  # Dump signals over a cycle range (clock period auto-detected or specified)
  ./scripts/vcd_inspect.py shoumei_cpu.vcd --cycles 60-100 --signals "rvvi_valid,rvvi_pc_rdata,rvvi_rd_data"

  # Dump signals by scope
  ./scripts/vcd_inspect.py shoumei_cpu.vcd --cycles 90-110 --scope "u_exec_muldiv" --signals "op,valid_in,valid_out,busy,result"

  # Show only cycles where a signal is high
  ./scripts/vcd_inspect.py shoumei_cpu.vcd --cycles 0-200 --signals "rvvi_valid,rvvi_pc_rdata" --when rvvi_valid=1
"""

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class VCDSignal:
    id: str
    name: str
    width: int
    scope: str  # full hierarchical scope

    @property
    def full_name(self) -> str:
        return f"{self.scope}.{self.name}" if self.scope else self.name


@dataclass
class VCDFile:
    signals: dict[str, VCDSignal] = field(default_factory=dict)  # id -> signal
    by_name: dict[str, list[VCDSignal]] = field(default_factory=dict)  # name -> [signals]
    # time -> list of (signal_id, value_str)
    changes: dict[int, list[tuple[str, str]]] = field(default_factory=dict)
    max_time: int = 0


def parse_vcd_header(path: Path) -> VCDFile:
    """Parse VCD header to extract signal definitions."""
    vcd = VCDFile()
    scope_stack: list[str] = []

    with open(path) as f:
        for line in f:
            line = line.strip()
            if line.startswith("$scope"):
                parts = line.split()
                if len(parts) >= 3:
                    scope_stack.append(parts[2])
            elif line.startswith("$upscope"):
                if scope_stack:
                    scope_stack.pop()
            elif line.startswith("$var"):
                parts = line.split()
                if len(parts) >= 5:
                    width = int(parts[2])
                    sig_id = parts[3]
                    name = parts[4]
                    scope = ".".join(scope_stack)
                    sig = VCDSignal(id=sig_id, name=name, width=width, scope=scope)
                    vcd.signals[sig_id] = sig
                    vcd.by_name.setdefault(name, []).append(sig)
            elif line.startswith("$enddefinitions"):
                break
            elif line.startswith("#"):
                break  # some VCDs skip $enddefinitions
    return vcd


def parse_vcd_values(path: Path, vcd: VCDFile, time_min: int, time_max: int,
                     signal_ids: set[str] | None = None) -> None:
    """Parse VCD value changes in the given time range for the given signals."""
    current_time = -1
    in_header = True

    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue

            if in_header:
                if line.startswith("$enddefinitions") or (line.startswith("#") and not line.startswith("$")):
                    in_header = False
                    if not line.startswith("#"):
                        continue
                else:
                    continue

            if line.startswith("#"):
                current_time = int(line[1:])
                vcd.max_time = max(vcd.max_time, current_time)
                if current_time > time_max:
                    break
                continue

            if current_time < time_min or current_time > time_max:
                continue

            # Parse value change
            if line.startswith("b") or line.startswith("B"):
                parts = line.split()
                if len(parts) >= 2:
                    val = parts[0][1:]  # strip 'b'
                    sig_id = parts[1]
                    if signal_ids is None or sig_id in signal_ids:
                        vcd.changes.setdefault(current_time, []).append((sig_id, val))
            elif line[0] in "01xXzZ":
                val = line[0]
                sig_id = line[1:]
                if signal_ids is None or sig_id in signal_ids:
                    vcd.changes.setdefault(current_time, []).append((sig_id, val))


def resolve_signals(vcd: VCDFile, names: list[str], scope_filter: str | None) -> list[VCDSignal]:
    """Resolve signal names to VCDSignal objects, with optional scope filter."""
    result = []
    for name in names:
        candidates = vcd.by_name.get(name, [])
        if scope_filter:
            candidates = [s for s in candidates if scope_filter in s.scope]
        if not candidates:
            # Try substring match
            candidates = [s for sigs in vcd.by_name.values() for s in sigs
                          if name in s.name and (not scope_filter or scope_filter in s.scope)]
        if candidates:
            result.append(candidates[0])
        else:
            print(f"WARNING: signal '{name}' not found", file=sys.stderr)
    return result


def bin_to_hex(binstr: str, width: int) -> str:
    """Convert binary string to hex, handling x/z."""
    if 'x' in binstr.lower() or 'z' in binstr.lower():
        return binstr
    val = int(binstr, 2)
    hex_width = (width + 3) // 4
    return f"0x{val:0{hex_width}x}"


def format_value(binstr: str, width: int) -> str:
    """Format a signal value for display."""
    if width == 1:
        return binstr
    return bin_to_hex(binstr, width)


def list_signals(vcd: VCDFile, pattern: str | None, scope_filter: str | None) -> None:
    """List signals matching a pattern."""
    import fnmatch
    for sig_id, sig in sorted(vcd.signals.items(), key=lambda x: x[1].full_name):
        if scope_filter and scope_filter not in sig.scope:
            continue
        if pattern and not fnmatch.fnmatch(sig.name, pattern) and not fnmatch.fnmatch(sig.full_name, pattern):
            continue
        print(f"  [{sig.width:3d}] {sig.full_name}  (id={sig.id})")


def dump_signals(vcd: VCDFile, vcd_path: Path, signals: list[VCDSignal], cycle_start: int,
                 cycle_end: int, clock_period: int, when_filter: tuple[str, str] | None) -> None:
    """Dump signal values at each cycle's negedge."""
    sig_ids = {s.id for s in signals}
    state: dict[str, str] = {}
    time_max = cycle_end * clock_period + clock_period
    all_changes: dict[int, list[tuple[str, str]]] = {}

    current_time = -1
    in_header = True
    with open(vcd_path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            if in_header:
                if line.startswith("$enddefinitions") or (line.startswith("#") and '$' not in line):
                    in_header = False
                    if not line.startswith("#"):
                        continue
                else:
                    continue
            if line.startswith("#"):
                current_time = int(line[1:])
                if current_time > time_max:
                    break
                continue
            if line.startswith("b") or line.startswith("B"):
                parts = line.split()
                if len(parts) >= 2:
                    sig_id = parts[1]
                    if sig_id in sig_ids:
                        state[sig_id] = parts[0][1:]
                        all_changes.setdefault(current_time, []).append((sig_id, parts[0][1:]))
            elif line[0] in "01xXzZ":
                sig_id = line[1:]
                if sig_id in sig_ids:
                    state[sig_id] = line[0]
                    all_changes.setdefault(current_time, []).append((sig_id, line[0]))

    # Now sample at negedge of each cycle
    # Re-read with state tracking
    state = {}
    sorted_times = sorted(all_changes.keys())
    time_idx = 0

    # Header
    col_names = [s.name for s in signals]
    col_widths = [max(len(n), 10) for n in col_names]
    header = f"{'cy':>4} | " + " | ".join(n.rjust(w) for n, w in zip(col_names, col_widths))
    print(header)
    print("-" * len(header))

    for cycle in range(cycle_start, cycle_end + 1):
        sample_time = cycle * clock_period + (clock_period // 2)  # negedge

        # Advance state to sample_time
        while time_idx < len(sorted_times) and sorted_times[time_idx] <= sample_time:
            t = sorted_times[time_idx]
            for sig_id, val in all_changes[t]:
                state[sig_id] = val
            time_idx += 1

        # Format values
        vals = []
        for sig in signals:
            raw = state.get(sig.id, "x")
            vals.append(format_value(raw, sig.width))

        # Apply when filter
        if when_filter:
            filter_name, filter_val = when_filter
            filter_sig = next((s for s in signals if s.name == filter_name), None)
            if filter_sig:
                cur = state.get(filter_sig.id, "x")
                if cur != filter_val:
                    continue

        row = f"{cycle:>4} | " + " | ".join(v.rjust(w) for v, w in zip(vals, col_widths))
        print(row)


def main():
    parser = argparse.ArgumentParser(description="VCD signal inspector for Shoumei RTL")
    parser.add_argument("vcd", help="Path to VCD file")
    parser.add_argument("--list", metavar="PATTERN", nargs="?", const="*",
                        help="List signals (optionally matching glob pattern)")
    parser.add_argument("--scope", help="Filter to signals in this scope")
    parser.add_argument("--signals", help="Comma-separated signal names to dump")
    parser.add_argument("--cycles", help="Cycle range, e.g. 60-100")
    parser.add_argument("--clock-period", type=int, default=2,
                        help="Clock period in time units (default: 2)")
    parser.add_argument("--when", help="Only show cycles where SIGNAL=VALUE, e.g. rvvi_valid=1")

    args = parser.parse_args()
    vcd_path = Path(args.vcd)

    if not vcd_path.exists():
        print(f"Error: {vcd_path} not found", file=sys.stderr)
        sys.exit(1)

    vcd = parse_vcd_header(vcd_path)

    if args.list is not None:
        list_signals(vcd, args.list, args.scope)
        return

    if args.signals and args.cycles:
        sig_names = [s.strip() for s in args.signals.split(",")]
        signals = resolve_signals(vcd, sig_names, args.scope)
        if not signals:
            print("No signals resolved", file=sys.stderr)
            sys.exit(1)

        m = re.match(r"(\d+)-(\d+)", args.cycles)
        if not m:
            print("Invalid cycle range, use e.g. 60-100", file=sys.stderr)
            sys.exit(1)
        cy_start, cy_end = int(m.group(1)), int(m.group(2))

        when_filter = None
        if args.when:
            parts = args.when.split("=", 1)
            if len(parts) == 2:
                when_filter = (parts[0], parts[1])

        dump_signals(vcd, vcd_path, signals, cy_start, cy_end, args.clock_period, when_filter)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
