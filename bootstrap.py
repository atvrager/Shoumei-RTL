#!/usr/bin/env python3
"""
bootstrap.py - Development Environment Setup Script

Sets up the complete Shoumei RTL development environment:
- Verifies Python 3.11+
- Installs uv (fast Python package manager)
- Installs elan (LEAN toolchain manager)
- Installs LEAN 4 v4.27.0 (via lean-toolchain file)
- Installs Coursier + sbt (for Chisel 7.7.0 / Scala 2.13.18)
- Installs Yosys (LEC verification)
- Installs Verilator (RTL simulation)
- Installs RISC-V GCC cross-compiler (test ELF compilation)
- Verifies installation with `lake build`

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

    # Install uv using the official installer
    install_cmd = "curl -LsSf https://astral.sh/uv/install.sh | sh"
    print(f"Running: {install_cmd}")
    run_command(install_cmd)

    # Source the shell rc to get uv in PATH
    # Note: User may need to restart shell or source manually
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

    # Install elan using the official installer
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

    # Check if lean-toolchain exists
    toolchain_file = Path("lean-toolchain")
    if not toolchain_file.exists():
        print_error("lean-toolchain file not found!")
        sys.exit(1)

    # Read the toolchain version
    with open(toolchain_file) as f:
        toolchain = f.read().strip()
    print(f"Target toolchain: {toolchain}")

    # elan will automatically install the right version when we run lake
    # But we can trigger it explicitly
    if command_exists("lake"):
        version = run_command("lake --version", capture=True)
        print_success(f"LEAN/Lake ready: {version}")
    else:
        print_warning("Running lake to trigger LEAN installation...")
        # This will fail but trigger elan to install LEAN
        run_command("lake --version || true", check=False)

        # Update PATH
        home = Path.home()
        elan_bin = home / ".elan" / "bin"
        os.environ["PATH"] = f"{elan_bin}:{os.environ['PATH']}"

        if command_exists("lake"):
            print_success("LEAN installed successfully")
        else:
            print_error("LEAN installation failed")
            sys.exit(1)

def install_coursier():
    """Install Coursier (Scala dependency manager) if not present"""
    print_step("Installing Coursier (Scala toolchain manager)")

    if command_exists("cs"):
        print_success("Coursier already installed")
        return

    print("Installing Coursier...")

    # Detect platform
    import platform
    system = platform.system().lower()
    machine = platform.machine().lower()

    # Determine the correct launcher
    if system == "linux":
        if "x86_64" in machine or "amd64" in machine:
            launcher_url = "https://github.com/coursier/launchers/raw/master/cs-x86_64-pc-linux.gz"
        elif "aarch64" in machine or "arm64" in machine:
            launcher_url = "https://github.com/coursier/launchers/raw/master/cs-aarch64-pc-linux.gz"
        else:
            print_error(f"Unsupported architecture: {machine}")
            sys.exit(1)
    elif system == "darwin":
        if "x86_64" in machine:
            launcher_url = "https://github.com/coursier/launchers/raw/master/cs-x86_64-apple-darwin.gz"
        elif "arm64" in machine:
            launcher_url = "https://github.com/coursier/launchers/raw/master/cs-aarch64-apple-darwin.gz"
        else:
            launcher_url = "https://github.com/coursier/launchers/raw/master/cs-x86_64-apple-darwin.gz"
    else:
        print_error(f"Unsupported OS: {system}")
        sys.exit(1)

    # Download and install Coursier
    home = Path.home()
    local_bin = home / ".local" / "bin"
    local_bin.mkdir(parents=True, exist_ok=True)
    cs_path = local_bin / "cs"

    try:
        print(f"Downloading from {launcher_url}")
        run_command(f'curl -fL "{launcher_url}" | gzip -d > {cs_path}')
        run_command(f"chmod +x {cs_path}")

        # Update PATH
        os.environ["PATH"] = f"{local_bin}:{os.environ['PATH']}"

        if command_exists("cs"):
            print_success("Coursier installed successfully")
        else:
            print_error("Coursier installation failed")
            sys.exit(1)
    except Exception as e:
        print_error(f"Failed to install Coursier: {e}")
        sys.exit(1)

def install_sbt():
    """Install sbt via Coursier (no system packages required)"""
    print_step("Installing sbt via Coursier")

    # First ensure Coursier is installed
    if not command_exists("cs"):
        install_coursier()

    if command_exists("sbt"):
        version = run_command("sbt --version 2>&1 | grep 'sbt version' | head -1 || sbt --version", capture=True)
        print_success(f"sbt already installed: {version.strip()}")
        return

    print("Installing sbt and Scala toolchain via Coursier...")

    try:
        # Use Coursier to install sbt, scala, and scalac
        # --yes flag auto-accepts all prompts
        run_command("cs setup --yes --jvm 11")

        # Update PATH to include Coursier bin directory
        home = Path.home()
        cs_bin = home / ".local" / "share" / "coursier" / "bin"
        os.environ["PATH"] = f"{cs_bin}:{os.environ['PATH']}"

        # Also update for Linux systems
        if cs_bin.exists():
            os.environ["PATH"] = f"{cs_bin}:{os.environ['PATH']}"

        if command_exists("sbt"):
            version = run_command("sbt --version 2>&1 | grep 'sbt version' | head -1", capture=True)
            print_success(f"sbt installed successfully: {version.strip()}")
        else:
            print_warning("sbt installation completed but not found in PATH")
            print(f"You may need to add {cs_bin} to your PATH")
            print("Add this to your ~/.bashrc or ~/.zshrc:")
            print(f'  export PATH="{cs_bin}:$PATH"')
    except Exception as e:
        print_error(f"Failed to install sbt: {e}")
        print("You can install sbt manually from: https://www.scala-sbt.org/download.html")

def install_yosys():
    """Install Yosys (used for LEC verification)"""
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

    if riscv_gcc.exists() or command_exists("riscv32-unknown-elf-gcc"):
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

def start_java_proxy_bridge():
    """Start the Java proxy bridge if an authenticated proxy is detected.

    Java's built-in HTTP client can't handle proxy auth via env vars.
    The bridge listens on localhost:18080 (no auth) and forwards to the
    upstream proxy with credentials, letting sbt/Coursier work normally.
    """
    print_step("Checking Java proxy bridge")

    proxy_url = os.environ.get("https_proxy") or os.environ.get("HTTPS_PROXY", "")
    if not proxy_url or "@" not in proxy_url:
        print_success("No authenticated proxy detected — bridge not needed")
        return

    bridge_port = int(os.environ.get("BRIDGE_PORT", "18080"))
    bridge_script = Path("scripts/java-proxy-bridge.py")

    if not bridge_script.exists():
        print_warning("scripts/java-proxy-bridge.py not found — skipping")
        return

    # Check if already running
    try:
        result = run_command(
            f'curl -s -o /dev/null -x "http://127.0.0.1:{bridge_port}" --max-time 2 https://repo1.maven.org/',
            check=True, capture=True
        )
        print_success(f"Java proxy bridge already running on :{bridge_port}")
    except (subprocess.CalledProcessError, Exception):
        print_warning("Starting Java proxy bridge...")
        proc = subprocess.Popen(
            [sys.executable, str(bridge_script)],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        import time
        time.sleep(1)
        if proc.poll() is None:
            print_success(f"Java proxy bridge started (PID {proc.pid}) on :{bridge_port}")
        else:
            print_warning("Java proxy bridge failed to start — sbt may not work through proxy")
            return

    # Set Java proxy env vars
    java_opts = (
        f"-Dhttp.proxyHost=127.0.0.1 -Dhttp.proxyPort={bridge_port} "
        f"-Dhttps.proxyHost=127.0.0.1 -Dhttps.proxyPort={bridge_port}"
    )
    os.environ["JAVA_OPTS"] = java_opts
    os.environ["SBT_OPTS"] = java_opts
    print_success("JAVA_OPTS/SBT_OPTS configured for proxy bridge")


def verify_build():
    """Verify the installation by running lake build"""
    print_step("Verifying installation with 'lake build'")

    try:
        run_command("lake build")
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
        ("lake",                     "Lean 4 / Lake"),
        ("sbt",                      "sbt (Scala build tool)"),
        ("yosys",                    "Yosys (LEC)"),
        ("verilator",                "Verilator (RTL sim)"),
        ("riscv32-unknown-elf-gcc",  "RISC-V GCC"),
        ("cmake",                    "CMake"),
        ("uv",                       "uv (Python)"),
        ("gh",                       "GitHub CLI"),
    ]

    # Also check RISC-V GCC in the standard install location
    home = Path.home()
    riscv_gcc = home / ".local" / "riscv32-elf" / "bin" / "riscv32-unknown-elf-gcc"

    missing = []
    for cmd, label in tools:
        found = command_exists(cmd)
        # Special case: riscv gcc might be in ~/.local/riscv32-elf/bin
        if cmd == "riscv32-unknown-elf-gcc" and not found and riscv_gcc.exists():
            found = True
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
    parser.add_argument("--start-proxy-bridge", action="store_true",
                        help="Start the Java proxy bridge for sandbox environments")
    args = parser.parse_args()

    if args.check_only:
        ok = check_all_tools()
        sys.exit(0 if ok else 1)

    if args.start_proxy_bridge:
        start_java_proxy_bridge()
        sys.exit(0)

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

    # Step 5: Install Coursier and sbt
    install_coursier()
    install_sbt()

    # Step 6: HDL / simulation tools
    install_yosys()
    install_verilator()
    # Step 7: RISC-V cross-compiler
    install_riscv_gcc()

    # Step 8: Java proxy bridge (for sandbox environments)
    start_java_proxy_bridge()

    # Step 9: Verify with lake build
    verify_build()

    # Final message
    print(f"\n{Color.GREEN}{Color.BOLD}Bootstrap complete!{Color.RESET}")
    print("\nNext steps:")
    print("  1. Restart your shell or source your shell rc to update PATH:")
    print("     source ~/.bashrc  # or ~/.zshrc")
    print("  2. Verify installation:")
    print("     python3 bootstrap.py --check-only")
    print("  3. Build the project:")
    print("     make all")
    print("  4. See README.md for detailed workflow")

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
