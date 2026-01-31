#!/usr/bin/env python3
"""
bootstrap.py - Development Environment Setup Script

Sets up the complete Proven RTL development environment:
- Verifies Python 3.11+
- Installs uv (fast Python package manager)
- Installs elan (LEAN toolchain manager)
- Installs LEAN 4 (via lean-toolchain file)
- Optionally installs sbt (for Chisel)
- Verifies installation with `lake build`

Requirements: Python 3.11+
Usage: python3 bootstrap.py
"""

import sys
import os
import subprocess
import shutil
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

def check_python_version():
    """Verify Python 3.11+"""
    print_step("Checking Python version")
    version = sys.version_info
    if version.major < 3 or (version.major == 3 and version.minor < 11):
        print_error(f"Python 3.11+ required, found {version.major}.{version.minor}")
        sys.exit(1)
    print_success(f"Python {version.major}.{version.minor}.{version.micro}")

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

def check_sbt():
    """Check if sbt is installed (optional for Chisel)"""
    print_step("Checking sbt installation (optional)")

    if command_exists("sbt"):
        version = run_command("sbt --version 2>&1 | grep 'sbt version' || sbt --version", capture=True)
        print_success(f"sbt installed: {version}")
    else:
        print_warning("sbt not found - required for Chisel compilation")
        print("Install manually:")
        print("  https://www.scala-sbt.org/download.html")
        print("  or use your package manager (e.g., pacman -S sbt on Arch)")

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

def main():
    """Main bootstrap process"""
    print(f"{Color.BOLD}Proven RTL - Development Environment Bootstrap{Color.RESET}")
    print("=" * 50)

    # Step 1: Check Python version
    check_python_version()

    # Step 2: Install uv
    install_uv()

    # Step 3: Install elan
    install_elan()

    # Step 4: Set up LEAN
    setup_lean()

    # Step 5: Check sbt (optional)
    check_sbt()

    # Step 6: Verify with lake build
    verify_build()

    # Final message
    print(f"\n{Color.GREEN}{Color.BOLD}Bootstrap complete!{Color.RESET}")
    print("\nNext steps:")
    print("  1. If you installed new tools, restart your shell or source your shell rc:")
    print("     source ~/.bashrc  # or ~/.zshrc")
    print("  2. Run 'lake build' to compile LEAN code")
    print("  3. Install sbt if you plan to use Chisel")
    print("  4. See README.md for build workflow")

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
