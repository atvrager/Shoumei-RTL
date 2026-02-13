#!/usr/bin/env bash
# setup-env.sh — Bootstrap the Shoumei RTL dev environment for Claude Code web sessions.
#
# Installs missing tools and starts the Java proxy bridge if an
# authenticated egress proxy is detected (common in sandboxed envs).
#
# Usage:  source scripts/setup-env.sh   (or run as: bash scripts/setup-env.sh)
# Idempotent — safe to run multiple times.
set -euo pipefail

# Only run in remote (web) sessions — skip on local CLI
if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
    exit 0
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

# ── Colour helpers ──────────────────────────────────────────────────
_green()  { printf '\033[92m✓ %s\033[0m\n' "$*"; }
_yellow() { printf '\033[93m⚠ %s\033[0m\n' "$*"; }
_red()    { printf '\033[91m✗ %s\033[0m\n' "$*"; }
_blue()   { printf '\033[94m==> %s\033[0m\n' "$*"; }

# ── PATH ────────────────────────────────────────────────────────────
export PATH="$HOME/.elan/bin:$HOME/.local/share/coursier/bin:$HOME/.local/riscv32-elf/bin:$HOME/.local/bin:/usr/local/sbt/bin:$PATH"

# ── 1. elan + Lean 4 ───────────────────────────────────────────────
if ! command -v lake &>/dev/null; then
    _blue "Installing elan + Lean 4"
    curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
        | sh -s -- -y --default-toolchain "$(cat "$PROJECT_DIR/lean-toolchain")"
    export PATH="$HOME/.elan/bin:$PATH"
fi
_green "lake $(lake --version 2>&1 | head -1)"

# ── 2. sbt (direct tarball, no coursier needed) ────────────────────
if ! command -v sbt &>/dev/null; then
    _blue "Installing sbt"
    SBT_VER="1.10.11"
    curl -fSL "https://github.com/sbt/sbt/releases/download/v${SBT_VER}/sbt-${SBT_VER}.tgz" \
        -o /tmp/sbt.tgz
    tar xzf /tmp/sbt.tgz -C /usr/local 2>/dev/null || tar xzf /tmp/sbt.tgz -C "$HOME/.local"
    rm -f /tmp/sbt.tgz
    # Symlink into a PATH dir
    if [ -d /usr/local/sbt/bin ]; then
        ln -sf /usr/local/sbt/bin/sbt /usr/local/bin/sbt 2>/dev/null || true
    fi
    export PATH="/usr/local/sbt/bin:$HOME/.local/sbt/bin:$PATH"
fi
_green "sbt installed"

# ── 3. System packages (yosys, verilator, shellcheck, systemc) ─────
_install_apt() {
    local missing=()
    for pkg in "$@"; do
        dpkg -s "$pkg" &>/dev/null || missing+=("$pkg")
    done
    if [ ${#missing[@]} -gt 0 ]; then
        _blue "Installing ${missing[*]}"
        apt-get update -qq 2>/dev/null || true
        apt-get install -y -o APT::Get::AllowUnauthenticated=true "${missing[@]}" 2>/dev/null || \
            _yellow "apt install failed for ${missing[*]} — may need manual install"
    fi
}

# Only try apt if we're root (CI / devcontainer)
if [ "$(id -u)" = "0" ]; then
    _install_apt yosys verilator shellcheck libsystemc-dev
fi

# ── 4. RISC-V GCC ──────────────────────────────────────────────────
if ! command -v riscv32-unknown-elf-gcc &>/dev/null && \
   [ ! -x "$HOME/.local/riscv32-elf/bin/riscv32-unknown-elf-gcc" ]; then
    _blue "Installing RISC-V GCC"
    bash "$PROJECT_DIR/scripts/setup-riscv-toolchain.sh"
fi
_green "RISC-V GCC ready"

# ── 5. GitHub CLI ──────────────────────────────────────────────────
if ! command -v gh &>/dev/null; then
    _blue "Installing GitHub CLI"
    GH_VER="2.67.0"
    curl -fsSL "https://github.com/cli/cli/releases/download/v${GH_VER}/gh_${GH_VER}_linux_amd64.tar.gz" \
        -o /tmp/gh.tar.gz
    cd /tmp && tar xzf gh.tar.gz && cp "gh_${GH_VER}_linux_amd64/bin/gh" /usr/local/bin/gh 2>/dev/null \
        || cp "gh_${GH_VER}_linux_amd64/bin/gh" "$HOME/.local/bin/gh"
    chmod +x /usr/local/bin/gh 2>/dev/null || chmod +x "$HOME/.local/bin/gh"
    rm -rf /tmp/gh* && cd "$PROJECT_DIR"
fi
_green "gh $(gh --version 2>&1 | head -1)"

# ── 6. Git submodules ──────────────────────────────────────────────
if [ ! -f "$PROJECT_DIR/third_party/riscv-opcodes/instr_dict.json" ]; then
    _blue "Initialising git submodules"
    git -C "$PROJECT_DIR" submodule update --init third_party/riscv-opcodes 2>/dev/null || true
fi

# ── 7. Java proxy bridge (for sbt in sandbox environments) ─────────
_start_proxy_bridge() {
    # Only needed when an authenticated proxy is present and Java can't use it
    local proxy_url="${https_proxy:-${HTTPS_PROXY:-}}"
    [ -z "$proxy_url" ] && return 0

    # Check if proxy has user:pass@host format
    if ! echo "$proxy_url" | grep -q '@'; then
        return 0  # No auth needed
    fi

    local BRIDGE_PORT="${BRIDGE_PORT:-18080}"

    # Already running?
    if curl -s -o /dev/null -x "http://127.0.0.1:$BRIDGE_PORT" --max-time 2 https://repo1.maven.org/ 2>/dev/null; then
        _green "Java proxy bridge already running on :$BRIDGE_PORT"
    else
        _blue "Starting Java proxy bridge on :$BRIDGE_PORT"
        python3 "$PROJECT_DIR/scripts/java-proxy-bridge.py" &
        BRIDGE_PID=$!
        sleep 1
        if kill -0 "$BRIDGE_PID" 2>/dev/null; then
            _green "Java proxy bridge started (PID $BRIDGE_PID)"
        else
            _yellow "Java proxy bridge failed to start — sbt may not work"
            return 0
        fi
    fi

    # Configure Java to use the local bridge
    export JAVA_OPTS="-Dhttp.proxyHost=127.0.0.1 -Dhttp.proxyPort=$BRIDGE_PORT -Dhttps.proxyHost=127.0.0.1 -Dhttps.proxyPort=$BRIDGE_PORT"
    export SBT_OPTS="$JAVA_OPTS"
    _green "JAVA_OPTS configured for proxy bridge"
}

_start_proxy_bridge

# ── 8. Build Lean (if not already built) ───────────────────────────
if [ ! -f "$PROJECT_DIR/.lake/build/bin/generate_all" ]; then
    _blue "Running lake build"
    cd "$PROJECT_DIR" && lake build 2>&1
fi
_green "Lean build ready"

# ── 9. Persist env vars for Claude Code session ────────────────────
if [ -n "${CLAUDE_ENV_FILE:-}" ]; then
    _blue "Persisting environment to CLAUDE_ENV_FILE"
    {
        echo "export PATH=\"$HOME/.elan/bin:$HOME/.local/share/coursier/bin:$HOME/.local/riscv32-elf/bin:$HOME/.local/bin:/usr/local/sbt/bin:\$PATH\""
        if [ -n "${JAVA_OPTS:-}" ]; then
            echo "export JAVA_OPTS=\"$JAVA_OPTS\""
            echo "export SBT_OPTS=\"$JAVA_OPTS\""
        fi
    } >> "$CLAUDE_ENV_FILE"
    _green "Environment persisted for session"
fi

# ── Summary ─────────────────────────────────────────────────────────
echo ""
_green "Environment ready!  Key commands:"
echo "  lake build                      # Build Lean proofs"
echo "  lake exe generate_all           # Generate SV + Chisel + SystemC"
echo "  cd chisel && sbt run && cd ..   # Compile Chisel → SV"
echo "  ./verification/run-lec.sh       # LEC verification"
echo "  make all                        # Full pipeline"
