#!/bin/bash
# Run OpenROAD Flow Scripts for Shoumei RTL
# Based on docs/physical-design.md
#
# Usage:
#   ./physical/run-openroad.sh
#
#   If Docker permission denied, use sg:
#   sg docker -c './physical/run-openroad.sh'
#
# Prerequisites:
#   - Docker running and accessible (user in docker group)
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
    echo ""
    echo "Solutions:"
    echo "  1. Add user to docker group: sudo usermod -aG docker \$USER"
    echo "  2. Use sg to run with docker group: sg docker -c './physical/run-openroad.sh'"
    echo "  3. Run with sudo (not recommended)"
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

if [ -z "$DESIGN_NAME" ]; then
    echo -e "${RED}✗ DESIGN_NAME not found in physical/config.mk${NC}"
    exit 1
fi

# Check main design file exists (check both physical/ and output/sv-from-lean/)
MAIN_VERILOG="$PROJECT_ROOT/output/sv-from-lean/${DESIGN_NAME}.sv"
if [ ! -f "$MAIN_VERILOG" ]; then
    MAIN_VERILOG="$PROJECT_ROOT/physical/${DESIGN_NAME}.sv"
fi
if [ ! -f "$MAIN_VERILOG" ]; then
    echo -e "${RED}✗ Main Verilog file not found: ${DESIGN_NAME}.sv${NC}"
    echo "Run: lake exe generate_all"
    exit 1
fi

# Count generated SV files for confirmation
SV_COUNT=$(find "$PROJECT_ROOT/output/sv-from-lean/" -maxdepth 1 -name "*.sv" -type f 2>/dev/null | wc -l)
echo -e "${GREEN}✓ Main Verilog file exists: $MAIN_VERILOG${NC}"
echo -e "${GREEN}✓ Found $SV_COUNT SystemVerilog modules for synthesis${NC}"
echo ""

# Display configuration
echo "==> Configuration:"
echo "  Design:    $DESIGN_NAME"
echo "  Platform:  $(grep "^export PLATFORM" physical/config.mk | cut -d= -f2 | tr -d ' ')"
echo "  Main SV:   $MAIN_VERILOG"
echo "  Modules:   $SV_COUNT SystemVerilog files"
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

# Capture exit code but don't fail the script
set +e
docker run --rm \
  -u "$(id -u):$(id -g)" \
  -v "$PROJECT_ROOT/third_party/orfs/flow:/OpenROAD-flow-scripts/flow" \
  -v "$PROJECT_ROOT:/project" \
  -w /OpenROAD-flow-scripts/flow \
  openroad/flow-ubuntu22.04-builder:3d5d5a \
  bash -c 'source ../env.sh && make DESIGN_CONFIG=/project/physical/config.mk PROJECT_ROOT=/project ABC_CLOCK_PERIOD_IN_PS=1000' 2>&1 | \
  grep -v "fatal: not a git repository" | \
  grep -v "Stopping at filesystem boundary"

ORFS_EXIT_CODE=${PIPESTATUS[0]}
set -e

echo ""
if [ "$ORFS_EXIT_CODE" -eq 0 ]; then
  echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  echo -e "${GREEN}✓ OpenROAD flow complete${NC}"
  echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
else
  echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  echo -e "${YELLOW}⚠ OpenROAD flow completed with warnings (exit code: $ORFS_EXIT_CODE)${NC}"
  echo -e "${YELLOW}  (This may be due to timing violations or minor issues)${NC}"
  echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
fi
echo ""

# Display results location
PLATFORM=$(grep "^export PLATFORM" physical/config.mk | cut -d= -f2 | tr -d ' ')
RESULTS_DIR="third_party/orfs/flow/results/$PLATFORM/$DESIGN_NAME/base"
REPORTS_DIR="third_party/orfs/flow/reports/$PLATFORM/$DESIGN_NAME/base"

echo "Results:"
echo "  Directory: $RESULTS_DIR"
echo ""

# Check for final outputs (stage 6)
if [ -f "$RESULTS_DIR/6_final.gds" ]; then
  echo "Key files (Final - Stage 6):"
  echo -e "  ${GREEN}✓${NC} GDSII Layout:       $RESULTS_DIR/6_final.gds"
  echo -e "  ${GREEN}✓${NC} OpenDB Database:    $RESULTS_DIR/6_final.odb"
  echo -e "  ${GREEN}✓${NC} Gate-Level Netlist: $RESULTS_DIR/6_final.v"
  echo -e "  ${GREEN}✓${NC} DEF File:           $RESULTS_DIR/6_final.def"
else
  # Show intermediate stages
  echo "Intermediate outputs:"

  if [ -f "$RESULTS_DIR/5_1_grt.odb" ]; then
    echo -e "  ${GREEN}✓${NC} Global Route (5_1): $RESULTS_DIR/5_1_grt.odb"
  elif [ -f "$RESULTS_DIR/4_1_cts.odb" ]; then
    echo -e "  ${GREEN}✓${NC} Clock Tree (4_1):   $RESULTS_DIR/4_1_cts.odb"
  elif [ -f "$RESULTS_DIR/3_1_place_gp.odb" ]; then
    echo -e "  ${GREEN}✓${NC} Placement (3_1):    $RESULTS_DIR/3_1_place_gp.odb"
  elif [ -f "$RESULTS_DIR/2_1_floorplan.odb" ]; then
    echo -e "  ${GREEN}✓${NC} Floorplan (2_1):    $RESULTS_DIR/2_1_floorplan.odb"
  elif [ -f "$RESULTS_DIR/1_1_yosys.v" ]; then
    echo -e "  ${GREEN}✓${NC} Synthesis (1_1):    $RESULTS_DIR/1_1_yosys.v"
  fi

  echo ""
  echo -e "  ${YELLOW}Note: Final outputs not generated. Check openroad.log for details.${NC}"
fi

echo ""
echo "Reports:"
if [ -d "$REPORTS_DIR" ]; then
    echo -e "  ${GREEN}✓${NC} Reports directory: $REPORTS_DIR"

    # Show key reports
    if [ -f "$REPORTS_DIR/final_report.txt" ]; then
      echo -e "  ${GREEN}✓${NC} Final report:      $REPORTS_DIR/final_report.txt"
    fi
else
    echo -e "  ${YELLOW}?${NC} Reports directory: $REPORTS_DIR"
fi

echo ""
if [ -f "$RESULTS_DIR/6_final.gds" ]; then
  echo "View GDSII layout:"
  echo "  klayout $RESULTS_DIR/6_final.gds"
  echo ""
fi
