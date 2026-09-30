# Shoumei-RTL Development Container
# Mirrors CI (ubuntu-latest) with all toolchains pre-installed.
#
# Build:  docker build -t shoumei-dev .devcontainer/
# Run:    docker run --rm -v $(pwd):/workspace -w /workspace shoumei-dev bazel test //:presubmit

FROM ubuntu:24.04

# ── Version pins (update these when bumping toolchains) ──────────────
ARG LEAN_VERSION=v4.34.1

# ── System packages ─────────────────────────────────────────────────
# Matches what CI installs across its jobs: build tools, linters,
# simulation/verification tools, and the gh CLI for PR workflows.
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
        # Core build tools
        curl ca-certificates git git-lfs openssh-client make cmake pkg-config \
        gcc g++ python3 python3-pip xz-utils gzip unzip zlib1g-dev \
        # Linters (lint CI job)
        shellcheck cppcheck ripgrep \
        # HDL tools (verilator-sim, smoke-test CI jobs)
        yosys verilator zlib1g-dev liblz4-dev \
        device-tree-compiler \
        # GitHub CLI for PR workflows
        gpg \
    && rm -rf /var/lib/apt/lists/*

# Install gh CLI via official apt repo
RUN curl -fsSL https://cli.github.com/packages/githubcli-archive-keyring.gpg \
        | gpg --dearmor -o /usr/share/keyrings/githubcli-archive-keyring.gpg \
    && echo "deb [arch=$(dpkg --print-architecture) signed-by=/usr/share/keyrings/githubcli-archive-keyring.gpg] https://cli.github.com/packages stable main" \
        > /etc/apt/sources.list.d/github-cli.list \
    && apt-get update && apt-get install -y --no-install-recommends gh \
    && rm -rf /var/lib/apt/lists/*

# ── Non-root user ───────────────────────────────────────────────────
RUN userdel -r ubuntu 2>/dev/null || true \
    && useradd -m -s /bin/bash -u 1000 dev
USER dev
WORKDIR /home/dev

# ── elan + Lean 4 ──────────────────────────────────────────────────
# Same install command as CI's lean-build job.
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
        | sh -s -- -y --default-toolchain leanprover/lean4:${LEAN_VERSION}

# ── pyslang (SystemVerilog IEEE 1800-2017 lint) ──────────────────
RUN pip install --break-system-packages pyslang

# ── uv (Python package manager) ────────────────────────────────────
RUN curl -LsSf https://astral.sh/uv/install.sh | sh

# ── PATH ────────────────────────────────────────────────────────────
# The RISC-V compiler comes from the Bazel toolchain, so it is not here.
ENV PATH="/home/dev/.elan/bin:/home/dev/.local/spike/bin:/home/dev/.local/bin:${PATH}"

# ── Spike RISC-V ISA simulator (cosimulation oracle) ─────────────
# LAST because it COPYs from build context (submodule), busting cache
# when the submodule commit changes. Everything above is stable.
COPY --chown=dev:dev third_party/riscv-isa-sim /home/dev/spike-src
RUN cd /home/dev/spike-src \
    && mkdir -p build && cd build \
    && ../configure --prefix=/home/dev/.local/spike --enable-commitlog \
    && make -j"$(nproc)" \
    && make install \
    && cd /home/dev && rm -rf spike-src

WORKDIR /workspace
