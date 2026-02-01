#!/bin/bash
# Run OpenROAD Flow Scripts for Shoumei RTL
# Based on docs/physical-design.md
#
# Usage:
#   ./physical/run-openroad.sh
#
# Prerequisites:
#   - Docker running and accessible
#   - ORFS submodule initialized: git submodule update --init --recursive
#   - Verilog generated: lake exe generate_riscv_decoder (for RV32IDecoder)
#
# Results will be in: third_party/orfs/flow/results/asap7/RV32IDecoder/base/
#   - 6_final.gds (GDSII layout)
#   - 6_final.odb (OpenDB database)
#   - 6_final.v (gate-level netlist)
#   - 6_final.def (DEF file)

set -e

# Colors
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m'

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

cd "$PROJECT_ROOT"

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  証明 Shoumei RTL - OpenROAD Flow"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# Check prerequisites
echo "==> Checking prerequisites..."

# Check Docker
if ! command -v docker > /dev/null 2>&1; then
    echo -e "${RED}✗ Docker not found${NC}"
    echo "Install Docker: https://docs.docker.com/get-docker/"
    exit 1
fi

if ! docker info > /dev/null 2>&1; then
    echo -e "${RED}✗ Docker daemon not running or permission denied${NC}"
    echo "Ensure Docker is running and you have permissions (add user to docker group)"
    exit 1
fi

echo -e "${GREEN}✓ Docker available${NC}"

# Check ORFS submodule
if [ ! -f "third_party/orfs/flow/Makefile" ]; then
    echo -e "${RED}✗ ORFS submodule not initialized${NC}"
    echo "Run: git submodule update --init --recursive"
    exit 1
fi

echo -e "${GREEN}✓ ORFS submodule initialized${NC}"

# Check generated Verilog (read from config.mk)
DESIGN_NAME=$(grep "^export DESIGN_NAME" physical/config.mk | cut -d= -f2 | tr -d ' ')
VERILOG_FILE=$(grep "^export VERILOG_FILES" physical/config.mk | cut -d= -f2 | tr -d ' ' | sed "s|\$(PROJECT_ROOT)|$PROJECT_ROOT|")

if [ -z "$DESIGN_NAME" ]; then
    echo -e "${RED}✗ DESIGN_NAME not found in physical/config.mk${NC}"
    exit 1
fi

if [ ! -f "$VERILOG_FILE" ]; then
    echo -e "${RED}✗ Verilog file not found: $VERILOG_FILE${NC}"
    echo "Run: make chisel (or lake exe generate_riscv_decoder for RV32IDecoder)"
    exit 1
fi

echo -e "${GREEN}✓ Verilog file exists: $VERILOG_FILE${NC}"
echo ""

# Display configuration
echo "==> Configuration:"
echo "  Design:    $DESIGN_NAME"
echo "  Platform:  $(grep "^export PLATFORM" physical/config.mk | cut -d= -f2 | tr -d ' ')"
echo "  Verilog:   $VERILOG_FILE"
echo "  Clock:     $(grep "^export CLK_PERIOD_NS" physical/config.mk | cut -d= -f2 | tr -d ' ') ns"
echo ""

# Ask for confirmation
read -p "Run OpenROAD flow? [y/N] " -n 1 -r
echo
if [[ ! $REPLY =~ ^[Yy]$ ]]; then
    echo "Aborted."
    exit 0
fi

# Run OpenROAD flow
echo ""
echo "==> Running OpenROAD flow (this will take several minutes)..."
echo ""

docker run --rm \
  -u "$(id -u):$(id -g)" \
  -v "$PROJECT_ROOT/third_party/orfs/flow:/OpenROAD-flow-scripts/flow" \
  -v "$PROJECT_ROOT:/project" \
  -w /OpenROAD-flow-scripts/flow \
  openroad/flow-ubuntu22.04-builder:3d5d5a \
  bash -c 'source ../env.sh && make DESIGN_CONFIG=/project/physical/config.mk PROJECT_ROOT=/project ABC_CLOCK_PERIOD_IN_PS=1000'

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo -e "${GREEN}✓ OpenROAD flow complete${NC}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# Display results location
PLATFORM=$(grep "^export PLATFORM" physical/config.mk | cut -d= -f2 | tr -d ' ')
RESULTS_DIR="third_party/orfs/flow/results/$PLATFORM/$DESIGN_NAME/base"
REPORTS_DIR="third_party/orfs/flow/reports/$PLATFORM/$DESIGN_NAME/base"

echo "Results:"
echo "  Directory: $RESULTS_DIR"
echo ""
echo "Key files:"
if [ -f "$RESULTS_DIR/6_final.gds" ]; then
    echo -e "  ${GREEN}✓${NC} GDSII Layout:      $RESULTS_DIR/6_final.gds"
else
    echo -e "  ${YELLOW}?${NC} GDSII Layout:      $RESULTS_DIR/6_final.gds"
fi

if [ -f "$RESULTS_DIR/6_final.odb" ]; then
    echo -e "  ${GREEN}✓${NC} OpenDB Database:   $RESULTS_DIR/6_final.odb"
else
    echo -e "  ${YELLOW}?${NC} OpenDB Database:   $RESULTS_DIR/6_final.odb"
fi

if [ -f "$RESULTS_DIR/6_final.v" ]; then
    echo -e "  ${GREEN}✓${NC} Gate-Level Netlist: $RESULTS_DIR/6_final.v"
else
    echo -e "  ${YELLOW}?${NC} Gate-Level Netlist: $RESULTS_DIR/6_final.v"
fi

if [ -f "$RESULTS_DIR/6_final.def" ]; then
    echo -e "  ${GREEN}✓${NC} DEF File:          $RESULTS_DIR/6_final.def"
else
    echo -e "  ${YELLOW}?${NC} DEF File:          $RESULTS_DIR/6_final.def"
fi

echo ""
echo "Reports:"
if [ -d "$REPORTS_DIR" ]; then
    echo -e "  ${GREEN}✓${NC} Reports directory: $REPORTS_DIR"
else
    echo -e "  ${YELLOW}?${NC} Reports directory: $REPORTS_DIR"
fi

echo ""
echo "View GDSII layout:"
echo "  klayout $RESULTS_DIR/6_final.gds"
echo ""
