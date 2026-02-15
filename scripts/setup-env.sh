#!/usr/bin/env bash
# setup-env.sh — Bootstrap the Shoumei RTL dev environment for Claude Code web sessions.
#
# The SessionStart hook calls this script.  It must return FAST so the
# session is responsive immediately.  Heavy work (installs, lake build)
# runs in a background re-invocation of this script; progress is logged
# to /tmp/shoumei-setup.log and a sentinel /tmp/shoumei-setup-done is
# created on completion.
#
# Idempotent — safe to run multiple times.
set -euo pipefail

# Only run in remote (web) sessions — skip on local CLI
if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
    exit 0
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

SETUP_LOG="/tmp/shoumei-setup.log"
SETUP_DONE="/tmp/shoumei-setup-done"

# ── Colour helpers (only used in foreground) ─────────────────────────
_green()  { printf '\033[92m✓ %s\033[0m\n' "$*"; }
_yellow() { printf '\033[93m⚠ %s\033[0m\n' "$*"; }

# ══════════════════════════════════════════════════════════════════════
#  BACKGROUND MODE — called with --background by the foreground phase
# ══════════════════════════════════════════════════════════════════════
if [ "${1:-}" = "--background" ]; then
    exec > "$SETUP_LOG" 2>&1
    echo "=== Shoumei background setup started at $(date) ==="

    export PATH="$HOME/.elan/bin:$HOME/.local/share/coursier/bin:$HOME/.local/riscv32-elf/bin:$HOME/.local/bin:/usr/local/sbt/bin:$PATH"

    # ── 1. elan + Lean 4 ─────────────────────────────────────────────
    if ! command -v lake &>/dev/null; then
        echo "==> Installing elan + Lean 4"
        curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
            | sh -s -- -y --default-toolchain "$(cat "$PROJECT_DIR/lean-toolchain")"
        export PATH="$HOME/.elan/bin:$PATH"
    fi
    echo "✓ lake ready"

    # ── 2. sbt ───────────────────────────────────────────────────────
    if ! command -v sbt &>/dev/null; then
        echo "==> Installing sbt"
        SBT_VER="1.10.11"
        curl -fSL "https://github.com/sbt/sbt/releases/download/v${SBT_VER}/sbt-${SBT_VER}.tgz" \
            -o /tmp/sbt.tgz
        tar xzf /tmp/sbt.tgz -C /usr/local 2>/dev/null || tar xzf /tmp/sbt.tgz -C "$HOME/.local"
        rm -f /tmp/sbt.tgz
        if [ -d /usr/local/sbt/bin ]; then
            ln -sf /usr/local/sbt/bin/sbt /usr/local/bin/sbt 2>/dev/null || true
        fi
        export PATH="/usr/local/sbt/bin:$HOME/.local/sbt/bin:$PATH"
    fi
    echo "✓ sbt ready"

    # ── 3. System packages ───────────────────────────────────────────
    if [ "$(id -u)" = "0" ]; then
        missing=()
        for pkg in yosys verilator shellcheck; do
            dpkg -s "$pkg" &>/dev/null || missing+=("$pkg")
        done
        if [ ${#missing[@]} -gt 0 ]; then
            echo "==> Installing ${missing[*]}"
            apt-get update -qq 2>/dev/null || true
            apt-get install -y -o APT::Get::AllowUnauthenticated=true "${missing[@]}" 2>/dev/null || \
                echo "⚠ apt install failed for ${missing[*]}"
        fi
    fi
    echo "✓ system packages ready"

    # ── 4. RISC-V GCC ───────────────────────────────────────────────
    if ! command -v riscv32-unknown-elf-gcc &>/dev/null && \
       [ ! -x "$HOME/.local/riscv32-elf/bin/riscv32-unknown-elf-gcc" ]; then
        echo "==> Installing RISC-V GCC"
        bash "$PROJECT_DIR/scripts/setup-riscv-toolchain.sh"
    fi
    echo "✓ RISC-V GCC ready"

    # ── 5. GitHub CLI ────────────────────────────────────────────────
    if ! command -v gh &>/dev/null; then
        echo "==> Installing GitHub CLI"
        GH_VER="2.67.0"
        curl -fsSL "https://github.com/cli/cli/releases/download/v${GH_VER}/gh_${GH_VER}_linux_amd64.tar.gz" \
            -o /tmp/gh.tar.gz
        tar xzf /tmp/gh.tar.gz -C /tmp
        if ! cp "/tmp/gh_${GH_VER}_linux_amd64/bin/gh" /usr/local/bin/gh 2>/dev/null; then
            cp "/tmp/gh_${GH_VER}_linux_amd64/bin/gh" "$HOME/.local/bin/gh"
            chmod +x "$HOME/.local/bin/gh"
        else
            chmod +x /usr/local/bin/gh
        fi
        rm -rf /tmp/gh*
    fi
    echo "✓ gh ready"

    # ── 6. Git submodules ────────────────────────────────────────────
    echo "==> Initialising git submodules"
    git -C "$PROJECT_DIR" submodule update --init \
        third_party/riscv-opcodes \
        third_party/riscv-tests \
        2>/dev/null || true

    if [ ! -f "$PROJECT_DIR/third_party/riscv-opcodes/instr_dict.json" ]; then
        echo "==> Generating RISC-V opcodes"
        make -C "$PROJECT_DIR" opcodes 2>&1 || echo "⚠ opcodes generation failed"
    fi
    echo "✓ submodules ready"

    # ── 7. Java proxy bridge ─────────────────────────────────────────
    proxy_url="${https_proxy:-${HTTPS_PROXY:-}}"
    if [ -n "$proxy_url" ] && echo "$proxy_url" | grep -q '@'; then
        BRIDGE_PORT="${BRIDGE_PORT:-18080}"
        if ! curl -s -o /dev/null -x "http://127.0.0.1:$BRIDGE_PORT" --max-time 2 https://repo1.maven.org/ 2>/dev/null; then
            echo "==> Starting Java proxy bridge on :$BRIDGE_PORT"
            python3 "$PROJECT_DIR/scripts/java-proxy-bridge.py" &
            sleep 1
        fi
        # Persist proxy env
        if [ -n "${CLAUDE_ENV_FILE:-}" ]; then
            {
                echo "export JAVA_OPTS=\"-Dhttp.proxyHost=127.0.0.1 -Dhttp.proxyPort=$BRIDGE_PORT -Dhttps.proxyHost=127.0.0.1 -Dhttps.proxyPort=$BRIDGE_PORT\""
                echo "export SBT_OPTS=\"\$JAVA_OPTS\""
            } >> "$CLAUDE_ENV_FILE"
        fi
        echo "✓ proxy bridge ready"
    fi

    # ── 8. Build Lean ────────────────────────────────────────────────
    if [ ! -f "$PROJECT_DIR/.lake/build/bin/generate_all" ]; then
        echo "==> Running lake build (this takes a while...)"
        cd "$PROJECT_DIR" && lake build 2>&1
    fi
    echo "✓ Lean build ready"

    # ── Done ─────────────────────────────────────────────────────────
    echo ""
    echo "=== Shoumei background setup completed at $(date) ==="
    touch "$SETUP_DONE"
    exit 0
fi

# ══════════════════════════════════════════════════════════════════════
#  FOREGROUND MODE — runs as SessionStart hook (must return fast)
# ══════════════════════════════════════════════════════════════════════

# Set up PATH immediately so tools already installed are available
export PATH="$HOME/.elan/bin:$HOME/.local/share/coursier/bin:$HOME/.local/riscv32-elf/bin:$HOME/.local/bin:/usr/local/sbt/bin:$PATH"

# Persist env vars so every Bash tool call in the session inherits them
if [ -n "${CLAUDE_ENV_FILE:-}" ]; then
    {
        echo "export PATH=\"$HOME/.elan/bin:$HOME/.local/share/coursier/bin:$HOME/.local/riscv32-elf/bin:$HOME/.local/bin:/usr/local/sbt/bin:\$PATH\""
    } >> "$CLAUDE_ENV_FILE"
fi

# If setup already completed, nothing to do
if [ -f "$SETUP_DONE" ]; then
    _green "Environment already set up"
    exit 0
fi

# If background setup is already running, don't launch another
if [ -f "$SETUP_LOG" ] && pgrep -f "setup-env.sh --background" &>/dev/null; then
    _yellow "Background setup already in progress (see $SETUP_LOG)"
    exit 0
fi

# Launch background setup and return immediately
nohup bash "$SCRIPT_DIR/setup-env.sh" --background </dev/null &>/dev/null &
disown

_green "Session ready — background setup running (tail -f $SETUP_LOG)"
