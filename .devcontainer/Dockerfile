# Shoumei-RTL Development Container
# Mirrors CI (ubuntu-latest) with all toolchains pre-installed.
#
# Build:  docker build -t shoumei-dev .devcontainer/
# Run:    docker run --rm -v $(pwd):/workspace -w /workspace shoumei-dev make all

FROM ubuntu:24.04

# ── Version pins (update these when bumping toolchains) ──────────────
ARG LEAN_VERSION=v4.27.0
ARG RISCV_TAG=2026.01.23
ARG CHISEL_VERSION=7.7.0
ARG SCALA_VERSION=2.13.18
ARG JAVA_VERSION=11

# ── System packages ─────────────────────────────────────────────────
# Matches what CI installs across its jobs: build tools, linters,
# simulation/verification tools, and the gh CLI for PR workflows.
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
        # Core build tools
        curl ca-certificates git git-lfs openssh-client make cmake pkg-config \
        gcc g++ python3 python3-pip xz-utils gzip unzip \
        # Linters (lint CI job)
        shellcheck cppcheck \
        # HDL tools (lec, verilator-sim, smoke-test CI jobs)
        yosys verilator \
        # SystemC (systemc CI job)
        libsystemc-dev device-tree-compiler \
        # JDK for Scala/Chisel (scala-build CI job)
        openjdk-${JAVA_VERSION}-jdk-headless \
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

# ── Coursier + sbt ──────────────────────────────────────────────────
# Same install command as CI's scala-build job.
RUN mkdir -p /home/dev/.local/bin \
    && curl -fL "https://github.com/coursier/launchers/raw/master/cs-x86_64-pc-linux.gz" \
        | gzip -d > /home/dev/.local/bin/cs \
    && chmod +x /home/dev/.local/bin/cs \
    && /home/dev/.local/bin/cs setup --yes --jvm ${JAVA_VERSION}

# ── RISC-V GCC cross-compiler ──────────────────────────────────────
# Same archive as CI's systemc/verilator-sim jobs + setup-riscv-toolchain.sh
RUN mkdir -p /home/dev/.local/riscv32-elf \
    && curl -fSL "https://github.com/riscv-collab/riscv-gnu-toolchain/releases/download/${RISCV_TAG}/riscv32-elf-ubuntu-22.04-gcc.tar.xz" \
        | tar xJ -C /home/dev/.local/riscv32-elf --strip-components=1

# ── pyslang (SystemVerilog IEEE 1800-2017 lint) ──────────────────
RUN pip install --break-system-packages pyslang

# ── uv (Python package manager) ────────────────────────────────────
RUN curl -LsSf https://astral.sh/uv/install.sh | sh

# ── Claude Code (native installer) ───────────────────────────────
RUN curl -fsSL https://claude.ai/install.sh | bash

# ── PATH ────────────────────────────────────────────────────────────
# Matches the Makefile's PATH and bootstrap.py's layout.
ENV PATH="/home/dev/.elan/bin:/home/dev/.local/share/coursier/bin:/home/dev/.local/riscv32-elf/bin:/home/dev/.local/spike/bin:/home/dev/.local/bin:${PATH}"

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
