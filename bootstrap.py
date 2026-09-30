#!/usr/bin/env python3
"""
bootstrap.py - Development Environment Setup Script

Sets up the complete Shoumei RTL development environment:
- Verifies Python 3.11+
- Installs uv (fast Python package manager)
- Installs elan (LEAN toolchain manager)
- Installs LEAN 4 v4.34.1 (via lean-toolchain file)
- Verifies Bazel / Bazelisk installation
- Installs Yosys (SystemVerilog validation)
- Installs Verilator (RTL simulation)
- Installs RISC-V GCC cross-compiler (test ELF compilation)
- Verifies installation with `bazel build //lean:shoumei`

Requirements: Python 3.11+
Usage: python3 bootstrap.py [--check-only]
"""

import sys
import os
import subprocess
import shutil
import argparse
from pathlib import Path

# ANSI color codes for pretty output
class Color:
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    RED = '\033[91m'
    BLUE = '\033[94m'
    RESET = '\033[0m'
    BOLD = '\033[1m'

def print_step(msg):
    """Print a step header"""
    print(f"\n{Color.BLUE}{Color.BOLD}==> {msg}{Color.RESET}")

def print_success(msg):
    """Print a success message"""
    print(f"{Color.GREEN}✓ {msg}{Color.RESET}")

def print_warning(msg):
    """Print a warning message"""
    print(f"{Color.YELLOW}⚠ {msg}{Color.RESET}")

def print_error(msg):
    """Print an error message"""
    print(f"{Color.RED}✗ {msg}{Color.RESET}")

def run_command(cmd, check=True, capture=False):
    """Run a shell command"""
    try:
        if capture:
            result = subprocess.run(
                cmd,
                shell=True,
                check=check,
                capture_output=True,
                text=True
            )
            return result.stdout.strip()
        else:
            subprocess.run(cmd, shell=True, check=check)
            return None
    except subprocess.CalledProcessError as e:
        if check:
            print_error(f"Command failed: {cmd}")
            if capture and e.stderr:
                print(e.stderr)
            raise
        return None

def command_exists(cmd):
    """Check if a command exists in PATH"""
    return shutil.which(cmd) is not None

def check_python_version():
    """Verify Python 3.11+"""
    print_step("Checking Python version")
    version = sys.version_info
    if version.major < 3 or (version.major == 3 and version.minor < 11):
        print_error(f"Python 3.11+ required, found {version.major}.{version.minor}")
        sys.exit(1)
    print_success(f"Python {version.major}.{version.minor}.{version.micro}")

def install_uv():
    """Install uv if not present"""
    print_step("Checking uv installation")

    if command_exists("uv"):
        version = run_command("uv --version", capture=True)
        print_success(f"uv already installed: {version}")
        return

    print_warning("uv not found, installing...")

    install_cmd = "curl -LsSf https://astral.sh/uv/install.sh | sh"
    print(f"Running: {install_cmd}")
    run_command(install_cmd)

    print_success("uv installed")
    print_warning("You may need to restart your shell or run: source ~/.bashrc (or ~/.zshrc)")

def install_elan():
    """Install elan (LEAN toolchain manager) if not present"""
    print_step("Checking elan installation")

    if command_exists("elan"):
        version = run_command("elan --version", capture=True)
        print_success(f"elan already installed: {version}")
        return

    print_warning("elan not found, installing...")

    install_cmd = "curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y"
    print(f"Running: {install_cmd}")
    run_command(install_cmd)

    # Add elan to PATH for this session
    home = Path.home()
    elan_bin = home / ".elan" / "bin"
    os.environ["PATH"] = f"{elan_bin}:{os.environ['PATH']}"

    print_success("elan installed")

def setup_lean():
    """Set up LEAN via elan using lean-toolchain"""
    print_step("Setting up LEAN 4")

    toolchain_file = Path("lean-toolchain")
    if not toolchain_file.exists():
        print_error("lean-toolchain file not found!")
        sys.exit(1)

    with open(toolchain_file) as f:
        toolchain = f.read().strip()
    print(f"Target toolchain: {toolchain}")

    if command_exists("lean"):
        version = run_command("lean --version", capture=True)
        print_success(f"LEAN ready: {version}")
    elif command_exists("elan"):
        run_command(f"elan default {toolchain}", check=False)
        home = Path.home()
        elan_bin = home / ".elan" / "bin"
        os.environ["PATH"] = f"{elan_bin}:{os.environ['PATH']}"
        if command_exists("lean"):
            print_success("LEAN installed successfully")
        else:
            print_error("LEAN installation failed")
            sys.exit(1)
    else:
        print_error("elan not found; install elan first")
        sys.exit(1)

def install_bazel():
    """Verify Bazel / Bazelisk installation"""
    print_step("Checking Bazel installation")

    if command_exists("bazel"):
        version = run_command("bazel --version", capture=True)
        print_success(f"Bazel ready: {version}")
        return
    if command_exists("bazelisk"):
        version = run_command("bazelisk --version", capture=True)
        print_success(f"Bazelisk ready: {version}")
        return

    print_warning("Bazel/Bazelisk not found.")
    print("Install Bazelisk via:")
    print("  npm:            npm install -g @bazel/bazelisk")
    print("  macOS:          brew install bazelisk")
    print("  Ubuntu/Debian:  sudo apt-get install bazel")
    print("  Arch Linux:     sudo pacman -S bazel")
    print("  GitHub release: https://github.com/bazelbuild/bazelisk/releases")

def install_yosys():
    """Install Yosys (used for SystemVerilog validation)"""
    print_step("Checking Yosys installation")

    if command_exists("yosys"):
        version = run_command("yosys --version", capture=True)
        print_success(f"Yosys already installed: {version}")
        return

    print_warning("Yosys not found.")
    print("Install via your system package manager:")
    print("  Ubuntu/Debian:  sudo apt-get install yosys")
    print("  Arch Linux:     sudo pacman -S yosys")
    print("  macOS:          brew install yosys")

def install_verilator():
    """Install Verilator (used for RTL simulation)"""
    print_step("Checking Verilator installation")

    if command_exists("verilator"):
        version = run_command("verilator --version", capture=True)
        print_success(f"Verilator already installed: {version}")
        return

    print_warning("Verilator not found.")
    print("Install via your system package manager:")
    print("  Ubuntu/Debian:  sudo apt-get install verilator")
    print("  Arch Linux:     sudo pacman -S verilator")
    print("  macOS:          brew install verilator")

def install_riscv_gcc():
    """Install RISC-V GCC cross-compiler"""
    print_step("Checking RISC-V GCC cross-compiler")

    home = Path.home()
    riscv_dir = home / ".local" / "riscv32-elf"
    riscv_gcc = riscv_dir / "bin" / "riscv32-unknown-elf-gcc"

    if riscv_gcc.exists() or command_exists("riscv32-unknown-elf-gcc") or command_exists("riscv64-unknown-elf-gcc") or command_exists("riscv64-elf-gcc"):
        print_success("RISC-V GCC already installed")
        return

    print_warning("RISC-V GCC not found, installing...")

    setup_script = Path("scripts/setup-riscv-toolchain.sh")
    if setup_script.exists():
        run_command(f"bash {setup_script}")
        os.environ["PATH"] = f"{riscv_dir / 'bin'}:{os.environ['PATH']}"
        print_success(f"RISC-V GCC installed to {riscv_dir}")
    else:
        print_error("scripts/setup-riscv-toolchain.sh not found")
        print("Download manually from: https://github.com/riscv-collab/riscv-gnu-toolchain/releases")

def verify_build():
    """Verify the installation by running bazel build //lean:shoumei"""
    print_step("Verifying installation with 'bazel build //lean:shoumei'")

    try:
        run_command("bazel build //lean:shoumei")
        print_success("Build successful! Environment is ready.")
    except subprocess.CalledProcessError:
        print_error("Build failed - see errors above")
        print("This is expected if there are compilation errors in LEAN code")
        print("The toolchain is installed correctly.")

def check_all_tools():
    """Check-only mode: verify all tools are present and print a summary."""
    print(f"{Color.BOLD}Shoumei RTL - Tool Check{Color.RESET}")
    print("=" * 50)

    tools = [
        ("python3",                  "Python 3.11+"),
        ("bazel",                    "Bazel / Bazelisk"),
        ("lean",                     "Lean 4"),
        ("yosys",                    "Yosys (SystemVerilog validation)"),
        ("verilator",                "Verilator (RTL sim)"),
        ("riscv-gcc",                "RISC-V GCC"),
        ("uv",                       "uv (Python)"),
        ("gh",                       "GitHub CLI"),
    ]

    home = Path.home()
    riscv_gcc_32 = home / ".local" / "riscv32-elf" / "bin" / "riscv32-unknown-elf-gcc"
    riscv_gcc_64 = home / ".local" / "riscv64-elf" / "bin" / "riscv64-unknown-elf-gcc"

    missing = []
    for cmd, label in tools:
        found = False
        if cmd == "bazel":
            found = command_exists("bazel") or command_exists("bazelisk")
        elif cmd == "riscv-gcc":
            found = (
                command_exists("riscv32-unknown-elf-gcc")
                or command_exists("riscv64-unknown-elf-gcc")
                or command_exists("riscv64-elf-gcc")
                or riscv_gcc_32.exists()
                or riscv_gcc_64.exists()
            )
        else:
            found = command_exists(cmd)

        if found:
            print_success(label)
        else:
            print_error(f"{label} — NOT FOUND")
            missing.append(cmd)

    print()
    if missing:
        print_error(f"{len(missing)} tool(s) missing: {', '.join(missing)}")
        print("Run: python3 bootstrap.py  (without --check-only) to install")
        return False
    else:
        print_success("All tools present")
        return True

def main():
    """Main bootstrap process"""
    parser = argparse.ArgumentParser(description="Shoumei RTL development environment setup")
    parser.add_argument("--check-only", action="store_true",
                        help="Only verify tools are present; do not install anything")
    args = parser.parse_args()

    if args.check_only:
        ok = check_all_tools()
        sys.exit(0 if ok else 1)

    print(f"{Color.BOLD}Shoumei RTL - Development Environment Bootstrap{Color.RESET}")
    print("=" * 50)

    # Step 1: Check Python version
    check_python_version()

    # Step 2: Install uv
    install_uv()

    # Step 3: Install elan
    install_elan()

    # Step 4: Set up LEAN
    setup_lean()

    # Step 5: Check Bazel
    install_bazel()

    # Step 6: HDL / simulation tools
    install_yosys()
    install_verilator()

    # Step 7: RISC-V cross-compiler
    install_riscv_gcc()

    # Step 8: Verify with Bazel build
    verify_build()

    # Final message
    print(f"\n{Color.GREEN}{Color.BOLD}Bootstrap complete!{Color.RESET}")
    print("\nNext steps:")
    print("  1. Restart your shell or source your shell rc to update PATH:")
    print("     source ~/.bashrc  # or ~/.zshrc")
    print("  2. Verify installation:")
    print("     python3 bootstrap.py --check-only")
    print("  3. Build the RTL:")
    print("     bazel build //:rtl")
    print("  4. Run presubmit tests:")
    print("     bazel test //:presubmit")
    print("  5. See README.md for detailed Bazel workflow")

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print(f"\n{Color.YELLOW}Bootstrap interrupted{Color.RESET}")
        sys.exit(1)
    except Exception as e:
        print_error(f"Unexpected error: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
