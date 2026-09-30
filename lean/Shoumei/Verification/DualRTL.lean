/-
Verification/DualRTL.lean - Dual-RTL SEC Specification Registry and Manifest

Tracks independent SystemVerilog reference models for emitted circuits and
monitors formal equivalence coverage (via the Yosys SMT2 -> pure Lean bv_decide bridge).
-/

import Shoumei.DSL

namespace Shoumei.Verification.DualRTL

open Shoumei

/-- Status of a circuit's Dual-RTL SystemVerilog specification and formal equivalence. -/
inductive SpecStatus where
  | missing      : SpecStatus
  /-- A spec file is present, but no equivalence evidence has been recorded. -/
  | specExists   : SpecStatus
  /-- Equivalence established by `bv_decide` over the SMT2 models (a proof). -/
  | secVerified  : SpecStatus
  /-- Equivalence established by randomised differential co-simulation against the
      emitted netlist (`//verification:spec_equiv_all`).  Not a proof: it samples the input and
      state space, so it is a weaker, independent witness. -/
  | coSimVerified : SpecStatus
  deriving Repr, DecidableEq, Inhabited

def SpecStatus.asString : SpecStatus → String
  | .missing => "MISSING"
  | .specExists => "SPEC_EXISTS"
  | .secVerified => "VERIFIED"
  | .coSimVerified => "CO-SIM"

/-- An entry registering an independent SystemVerilog specification for a circuit. -/
structure DualRTLSpec where
  circuitName  : String
  specFile     : String
  topModule    : String
  hasProof     : Bool := false
  /-- Covered by `//verification:spec_equiv_all` (randomised differential co-simulation). -/
  coSimulated  : Bool := false
  proofRef     : String := ""
  deriving Repr, Inhabited

/-- Registered independent SystemVerilog specifications. -/
def allSpecs : List DualRTLSpec := [
  {
    circuitName := "Queue1_8"
    specFile := "verification/specs/Queue1_spec.sv"
    topModule := "Queue1_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeQueue1_8.queue1_8_sec"
  },
  {
    circuitName := "EqualityComparator6"
    specFile := "verification/specs/EqualityComparator_spec.sv"
    topModule := "EqualityComparator_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeEqualityComparator6.equalityComparator6_sec"
  },
  {
    circuitName := "Register1"
    specFile := "verification/specs/Register_spec.sv"
    topModule := "Register_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegister1.register1_sec"
  },
  {
    circuitName := "Register2"
    specFile := "verification/specs/Register_spec.sv"
    topModule := "Register_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegister2.register2_sec"
  },
  {
    circuitName := "Register3"
    specFile := "verification/specs/Register_spec.sv"
    topModule := "Register_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegister3.register3_sec"
  },
  {
    circuitName := "Register4"
    specFile := "verification/specs/Register_spec.sv"
    topModule := "Register_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegister4.register4_sec"
  },
  {
    circuitName := "Register6"
    specFile := "verification/specs/Register_spec.sv"
    topModule := "Register_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegister6.register6_sec"
  },
  {
    circuitName := "Register8"
    specFile := "verification/specs/Register_spec.sv"
    topModule := "Register_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegister8.register8_sec"
  },
  {
    circuitName := "Register12"
    specFile := "verification/specs/Register_spec.sv"
    topModule := "Register_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegister12.register12_sec"
  },
  {
    circuitName := "Register16"
    specFile := "verification/specs/Register_spec.sv"
    topModule := "Register_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegister16.register16_sec"
  },
  {
    circuitName := "Register20"
    specFile := "verification/specs/Register_spec.sv"
    topModule := "Register_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegister20.register20_sec"
  },
  {
    circuitName := "Register24"
    specFile := "verification/specs/Register_spec.sv"
    topModule := "Register_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegister24.register24_sec"
  },
  {
    circuitName := "Register32"
    specFile := "verification/specs/Register_spec.sv"
    topModule := "Register_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegister32.register32_sec"
  },
  {
    circuitName := "Register64"
    specFile := "verification/specs/Register_spec.sv"
    topModule := "Register_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegister64.register64_sec"
  },
  {
    circuitName := "Register96"
    specFile := "verification/specs/Register_spec.sv"
    topModule := "Register_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegister96.register96_sec"
  },
  {
    circuitName := "Register98"
    specFile := "verification/specs/Register_spec.sv"
    topModule := "Register_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegister98.register98_sec"
  },
  {
    circuitName := "Register130"
    specFile := "verification/specs/Register_spec.sv"
    topModule := "Register_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegister130.register130_sec"
  },
  {
    circuitName := "Register157"
    specFile := "verification/specs/Register_spec.sv"
    topModule := "Register_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegister157.register157_sec"
  },
  {
    circuitName := "Register158"
    specFile := "verification/specs/Register_spec.sv"
    topModule := "Register_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegister158.register158_sec"
  },
  {
    circuitName := "Register159"
    specFile := "verification/specs/Register_spec.sv"
    topModule := "Register_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegister159.register159_sec"
  },
  {
    circuitName := "Register160"
    specFile := "verification/specs/Register_spec.sv"
    topModule := "Register_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegister160.register160_sec"
  },
  {
    circuitName := "Register160Flat"
    specFile := "verification/specs/Register_spec.sv"
    topModule := "Register_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegister160Flat.register160flat_sec"
  },
  {
    circuitName := "DFlipFlop"
    specFile := "verification/specs/Register_spec.sv"
    topModule := "Register_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeDFlipFlop.dflipflop_sec"
  },
  {
    circuitName := "Decoder2"
    specFile := "verification/specs/Decoder_spec.sv"
    topModule := "Decoder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeDecoder2.decoder2_sec"
  },
  {
    circuitName := "Decoder3"
    specFile := "verification/specs/Decoder_spec.sv"
    topModule := "Decoder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeDecoder3.decoder3_sec"
  },
  {
    circuitName := "Decoder4"
    specFile := "verification/specs/Decoder_spec.sv"
    topModule := "Decoder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeDecoder4.decoder4_sec"
  },
  {
    circuitName := "Decoder5"
    specFile := "verification/specs/Decoder_spec.sv"
    topModule := "Decoder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeDecoder5.decoder5_sec"
  },
  {
    circuitName := "Decoder6"
    specFile := "verification/specs/Decoder_spec.sv"
    topModule := "Decoder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeDecoder6.decoder6_sec"
  },
  {
    circuitName := "RegisterEn1"
    specFile := "verification/specs/RegisterEn_spec.sv"
    topModule := "RegisterEn_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegisterEn1.registeren1_sec"
  },
  {
    circuitName := "RegisterEn2"
    specFile := "verification/specs/RegisterEn_spec.sv"
    topModule := "RegisterEn_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegisterEn2.registeren2_sec"
  },
  {
    circuitName := "RegisterEn4"
    specFile := "verification/specs/RegisterEn_spec.sv"
    topModule := "RegisterEn_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegisterEn4.registeren4_sec"
  },
  {
    circuitName := "RegisterEn8"
    specFile := "verification/specs/RegisterEn_spec.sv"
    topModule := "RegisterEn_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegisterEn8.registeren8_sec"
  },
  {
    circuitName := "RegisterEn16"
    specFile := "verification/specs/RegisterEn_spec.sv"
    topModule := "RegisterEn_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegisterEn16.registeren16_sec"
  },
  {
    circuitName := "RegisterEn32"
    specFile := "verification/specs/RegisterEn_spec.sv"
    topModule := "RegisterEn_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegisterEn32.registeren32_sec"
  },
  {
    circuitName := "RegisterEn64"
    specFile := "verification/specs/RegisterEn_spec.sv"
    topModule := "RegisterEn_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRegisterEn64.registeren64_sec"
  },
  {
    circuitName := "EqualityComparator20"
    specFile := "verification/specs/EqualityComparator_spec.sv"
    topModule := "EqualityComparator_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeEqualityComparator20.equalitycomparator20_sec"
  },
  {
    circuitName := "EqualityComparator32"
    specFile := "verification/specs/EqualityComparator_spec.sv"
    topModule := "EqualityComparator_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeEqualityComparator32.equalitycomparator32_sec"
  },
  {
    circuitName := "EqualityComparator64"
    specFile := "verification/specs/EqualityComparator_spec.sv"
    topModule := "EqualityComparator_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeEqualityComparator64.equalitycomparator64_sec"
  },
  {
    circuitName := "Mux4x1"
    specFile := "verification/specs/Mux4_spec.sv"
    topModule := "Mux4_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeMux4x1.mux4x1_sec"
  },
  {
    circuitName := "Mux4x32"
    specFile := "verification/specs/Mux4_spec.sv"
    topModule := "Mux4_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeMux4x32.mux4x32_sec"
  },
  {
    circuitName := "Mux4x64"
    specFile := "verification/specs/Mux4_spec.sv"
    topModule := "Mux4_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeMux4x64.mux4x64_sec"
  },
  {
    circuitName := "Mux8x2"
    specFile := "verification/specs/Mux8_spec.sv"
    topModule := "Mux8_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeMux8x2.mux8x2_sec"
  },
  {
    circuitName := "Mux8x32"
    specFile := "verification/specs/Mux8_spec.sv"
    topModule := "Mux8_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeMux8x32.mux8x32_sec"
  },
  {
    circuitName := "Mux8x64"
    specFile := "verification/specs/Mux8_spec.sv"
    topModule := "Mux8_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeMux8x64.mux8x64_sec"
  },
  {
    circuitName := "Mux16x5"
    specFile := "verification/specs/Mux16_spec.sv"
    topModule := "Mux16_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeMux16x5.mux16x5_sec"
  },
  {
    circuitName := "Mux16x6"
    specFile := "verification/specs/Mux16_spec.sv"
    topModule := "Mux16_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeMux16x6.mux16x6_sec"
  },
  {
    circuitName := "Mux16x32"
    specFile := "verification/specs/Mux16_spec.sv"
    topModule := "Mux16_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeMux16x32.mux16x32_sec"
  },
  {
    circuitName := "Mux32x6"
    specFile := "verification/specs/Mux32_spec.sv"
    topModule := "Mux32_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeMux32x6.mux32x6_sec"
  },
  {
    circuitName := "Mux64x20"
    specFile := "verification/specs/Mux64_spec.sv"
    topModule := "Mux64_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeMux64x20.mux64x20_sec"
  },
  {
    circuitName := "Mux64x32"
    specFile := "verification/specs/Mux64_spec.sv"
    topModule := "Mux64_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeMux64x32.mux64x32_sec"
  },
  {
    circuitName := "Mux64x64"
    specFile := "verification/specs/Mux64_spec.sv"
    topModule := "Mux64_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeMux64x64.mux64x64_sec"
  },
  {
    circuitName := "LogicUnit4"
    specFile := "verification/specs/LogicUnit_spec.sv"
    topModule := "LogicUnit_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeLogicUnit4.logicunit4_sec"
  },
  {
    circuitName := "LogicUnit32"
    specFile := "verification/specs/LogicUnit_spec.sv"
    topModule := "LogicUnit_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeLogicUnit32.logicunit32_sec"
  },
  {
    circuitName := "LogicUnit64"
    specFile := "verification/specs/LogicUnit_spec.sv"
    topModule := "LogicUnit_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeLogicUnit64.logicunit64_sec"
  },
  {
    circuitName := "Shifter32"
    specFile := "verification/specs/Shifter_spec.sv"
    topModule := "Shifter_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeShifter32.shifter32_sec"
  },
  {
    circuitName := "Shifter64"
    specFile := "verification/specs/Shifter_spec.sv"
    topModule := "Shifter_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeShifter64.shifter64_sec"
  },
  {
    circuitName := "PCIncrementer4"
    specFile := "verification/specs/PCIncrementer_spec.sv"
    topModule := "PCIncrementer_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgePCIncrementer4.pcincrementer4_sec"
  },
  {
    circuitName := "PCIncrementer8"
    specFile := "verification/specs/PCIncrementer_spec.sv"
    topModule := "PCIncrementer_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgePCIncrementer8.pcincrementer8_sec"
  },
  {
    circuitName := "Comparator4"
    specFile := "verification/specs/Comparator_spec.sv"
    topModule := "Comparator_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeComparator4.comparator4_sec"
  },
  {
    circuitName := "Comparator6"
    specFile := "verification/specs/Comparator_spec.sv"
    topModule := "Comparator_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeComparator6.comparator6_sec"
  },
  {
    circuitName := "Comparator32"
    specFile := "verification/specs/Comparator_spec.sv"
    topModule := "Comparator_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeComparator32.comparator32_sec"
  },
  {
    circuitName := "Comparator64"
    specFile := "verification/specs/Comparator_spec.sv"
    topModule := "Comparator_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeComparator64.comparator64_sec"
  },
  {
    circuitName := "BrentKungAdder32"
    specFile := "verification/specs/Adder_spec.sv"
    topModule := "Adder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeBrentKungAdder32.brentkungadder32_sec"
  },
  {
    circuitName := "BrentKungAdder32NoCin"
    specFile := "verification/specs/AdderNoCin_spec.sv"
    topModule := "AdderNoCin_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeBrentKungAdder32NoCin.brentkungadder32nocin_sec"
  },
  {
    circuitName := "BrentKungAdder32WithCin1"
    specFile := "verification/specs/AdderWithCin1_spec.sv"
    topModule := "AdderWithCin1_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeBrentKungAdder32WithCin1.brentkungadder32withcin1_sec"
  },
  {
    circuitName := "CarrySelectAdder32"
    specFile := "verification/specs/Adder_spec.sv"
    topModule := "Adder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeCarrySelectAdder32.carryselectadder32_sec"
  },
  {
    circuitName := "CarrySelectAdder32NoCin"
    specFile := "verification/specs/AdderNoCin_spec.sv"
    topModule := "AdderNoCin_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeCarrySelectAdder32NoCin.carryselectadder32nocin_sec"
  },
  {
    circuitName := "CarrySelectAdder32WithCin1"
    specFile := "verification/specs/AdderWithCin1_spec.sv"
    topModule := "AdderWithCin1_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeCarrySelectAdder32WithCin1.carryselectadder32withcin1_sec"
  },
  {
    circuitName := "HanCarlsonAdder32"
    specFile := "verification/specs/Adder_spec.sv"
    topModule := "Adder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeHanCarlsonAdder32.hancarlsonadder32_sec"
  },
  {
    circuitName := "HanCarlsonAdder32NoCin"
    specFile := "verification/specs/AdderNoCin_spec.sv"
    topModule := "AdderNoCin_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeHanCarlsonAdder32NoCin.hancarlsonadder32nocin_sec"
  },
  {
    circuitName := "HanCarlsonAdder32WithCin1"
    specFile := "verification/specs/AdderWithCin1_spec.sv"
    topModule := "AdderWithCin1_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeHanCarlsonAdder32WithCin1.hancarlsonadder32withcin1_sec"
  },
  {
    circuitName := "KoggeStoneAdder32"
    specFile := "verification/specs/Adder_spec.sv"
    topModule := "Adder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeKoggeStoneAdder32.koggestoneadder32_sec"
  },
  {
    circuitName := "KoggeStoneAdder32NoCin"
    specFile := "verification/specs/AdderNoCin_spec.sv"
    topModule := "AdderNoCin_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeKoggeStoneAdder32NoCin.koggestoneadder32nocin_sec"
  },
  {
    circuitName := "KoggeStoneAdder32WithCin1"
    specFile := "verification/specs/AdderWithCin1_spec.sv"
    topModule := "AdderWithCin1_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeKoggeStoneAdder32WithCin1.koggestoneadder32withcin1_sec"
  },
  {
    circuitName := "RippleCarryAdder32"
    specFile := "verification/specs/Adder_spec.sv"
    topModule := "Adder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRippleCarryAdder32.ripplecarryadder32_sec"
  },
  {
    circuitName := "RippleCarryAdder32NoCin"
    specFile := "verification/specs/AdderNoCin_spec.sv"
    topModule := "AdderNoCin_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRippleCarryAdder32NoCin.ripplecarryadder32nocin_sec"
  },
  {
    circuitName := "RippleCarryAdder32WithCin1"
    specFile := "verification/specs/AdderWithCin1_spec.sv"
    topModule := "AdderWithCin1_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRippleCarryAdder32WithCin1.ripplecarryadder32withcin1_sec"
  },
  {
    circuitName := "FullAdder"
    specFile := "verification/specs/FullAdder_spec.sv"
    topModule := "FullAdder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeFullAdder.fulladder_sec"
  },
  {
    circuitName := "RippleCarryAdder4"
    specFile := "verification/specs/RippleCarryAdder4_spec.sv"
    topModule := "RippleCarryAdder4_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRippleCarryAdder4.ripplecarryadder4_sec"
  },
  {
    circuitName := "MulFinalAdder64"
    specFile := "verification/specs/MulFinalAdder64_spec.sv"
    topModule := "MulFinalAdder64_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeMulFinalAdder64.mulfinaladder64_sec"
  },
  {
    circuitName := "BranchTargetAdder32"
    specFile := "verification/specs/BranchTargetAdder32_spec.sv"
    topModule := "BranchTargetAdder32_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeBranchTargetAdder32.branchtargetadder32_sec"
  },
  {
    circuitName := "SklanskyAdder32"
    specFile := "verification/specs/Adder_spec.sv"
    topModule := "Adder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeSklanskyAdder32.sklanskyadder32_sec"
  },
  {
    circuitName := "SklanskyAdder32NoCin"
    specFile := "verification/specs/AdderNoCin_spec.sv"
    topModule := "AdderNoCin_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeSklanskyAdder32NoCin.sklanskyadder32nocin_sec"
  },
  {
    circuitName := "SklanskyAdder32WithCin1"
    specFile := "verification/specs/AdderWithCin1_spec.sv"
    topModule := "AdderWithCin1_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeSklanskyAdder32WithCin1.sklanskyadder32withcin1_sec"
  },
  {
    circuitName := "BrentKungAdder64"
    specFile := "verification/specs/Adder_spec.sv"
    topModule := "Adder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeBrentKungAdder64.brentkungadder64_sec"
  },
  {
    circuitName := "BrentKungAdder64NoCin"
    specFile := "verification/specs/AdderNoCin_spec.sv"
    topModule := "AdderNoCin_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeBrentKungAdder64NoCin.brentkungadder64nocin_sec"
  },
  {
    circuitName := "BrentKungAdder64WithCin1"
    specFile := "verification/specs/AdderWithCin1_spec.sv"
    topModule := "AdderWithCin1_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeBrentKungAdder64WithCin1.brentkungadder64withcin1_sec"
  },
  {
    circuitName := "CarrySelectAdder64"
    specFile := "verification/specs/Adder_spec.sv"
    topModule := "Adder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeCarrySelectAdder64.carryselectadder64_sec"
  },
  {
    circuitName := "CarrySelectAdder64NoCin"
    specFile := "verification/specs/AdderNoCin_spec.sv"
    topModule := "AdderNoCin_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeCarrySelectAdder64NoCin.carryselectadder64nocin_sec"
  },
  {
    circuitName := "CarrySelectAdder64WithCin1"
    specFile := "verification/specs/AdderWithCin1_spec.sv"
    topModule := "AdderWithCin1_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeCarrySelectAdder64WithCin1.carryselectadder64withcin1_sec"
  },
  {
    circuitName := "HanCarlsonAdder64"
    specFile := "verification/specs/Adder_spec.sv"
    topModule := "Adder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeHanCarlsonAdder64.hancarlsonadder64_sec"
  },
  {
    circuitName := "HanCarlsonAdder64NoCin"
    specFile := "verification/specs/AdderNoCin_spec.sv"
    topModule := "AdderNoCin_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeHanCarlsonAdder64NoCin.hancarlsonadder64nocin_sec"
  },
  {
    circuitName := "HanCarlsonAdder64WithCin1"
    specFile := "verification/specs/AdderWithCin1_spec.sv"
    topModule := "AdderWithCin1_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeHanCarlsonAdder64WithCin1.hancarlsonadder64withcin1_sec"
  },
  {
    circuitName := "KoggeStoneAdder64"
    specFile := "verification/specs/Adder_spec.sv"
    topModule := "Adder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeKoggeStoneAdder64.koggestoneadder64_sec"
  },
  {
    circuitName := "KoggeStoneAdder64NoCin"
    specFile := "verification/specs/AdderNoCin_spec.sv"
    topModule := "AdderNoCin_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeKoggeStoneAdder64NoCin.koggestoneadder64nocin_sec"
  },
  {
    circuitName := "KoggeStoneAdder64WithCin1"
    specFile := "verification/specs/AdderWithCin1_spec.sv"
    topModule := "AdderWithCin1_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeKoggeStoneAdder64WithCin1.koggestoneadder64withcin1_sec"
  },
  {
    circuitName := "RippleCarryAdder64"
    specFile := "verification/specs/Adder_spec.sv"
    topModule := "Adder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRippleCarryAdder64.ripplecarryadder64_sec"
  },
  {
    circuitName := "RippleCarryAdder64NoCin"
    specFile := "verification/specs/AdderNoCin_spec.sv"
    topModule := "AdderNoCin_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRippleCarryAdder64NoCin.ripplecarryadder64nocin_sec"
  },
  {
    circuitName := "RippleCarryAdder64WithCin1"
    specFile := "verification/specs/AdderWithCin1_spec.sv"
    topModule := "AdderWithCin1_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRippleCarryAdder64WithCin1.ripplecarryadder64withcin1_sec"
  },
  {
    circuitName := "SklanskyAdder64"
    specFile := "verification/specs/Adder_spec.sv"
    topModule := "Adder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeSklanskyAdder64.sklanskyadder64_sec"
  },
  {
    circuitName := "SklanskyAdder64NoCin"
    specFile := "verification/specs/AdderNoCin_spec.sv"
    topModule := "AdderNoCin_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeSklanskyAdder64NoCin.sklanskyadder64nocin_sec"
  },
  {
    circuitName := "SklanskyAdder64WithCin1"
    specFile := "verification/specs/AdderWithCin1_spec.sv"
    topModule := "AdderWithCin1_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeSklanskyAdder64WithCin1.sklanskyadder64withcin1_sec"
  },
  {
    circuitName := "CarrySelectAdder106"
    specFile := "verification/specs/Adder_spec.sv"
    topModule := "Adder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeCarrySelectAdder106.carryselectadder106_sec"
  },
  {
    circuitName := "CarrySelectAdder106NoCin"
    specFile := "verification/specs/AdderNoCin_spec.sv"
    topModule := "AdderNoCin_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeCarrySelectAdder106NoCin.carryselectadder106nocin_sec"
  },
  {
    circuitName := "HanCarlsonAdder106"
    specFile := "verification/specs/Adder_spec.sv"
    topModule := "Adder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeHanCarlsonAdder106.hancarlsonadder106_sec"
  },
  {
    circuitName := "HanCarlsonAdder106NoCin"
    specFile := "verification/specs/AdderNoCin_spec.sv"
    topModule := "AdderNoCin_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeHanCarlsonAdder106NoCin.hancarlsonadder106nocin_sec"
  },
  {
    circuitName := "KoggeStoneAdder106"
    specFile := "verification/specs/Adder_spec.sv"
    topModule := "Adder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeKoggeStoneAdder106.koggestoneadder106_sec"
  },
  {
    circuitName := "KoggeStoneAdder106NoCin"
    specFile := "verification/specs/AdderNoCin_spec.sv"
    topModule := "AdderNoCin_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeKoggeStoneAdder106NoCin.koggestoneadder106nocin_sec"
  },
  {
    circuitName := "RippleCarryAdder106"
    specFile := "verification/specs/Adder_spec.sv"
    topModule := "Adder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRippleCarryAdder106.ripplecarryadder106_sec"
  },
  {
    circuitName := "RippleCarryAdder106NoCin"
    specFile := "verification/specs/AdderNoCin_spec.sv"
    topModule := "AdderNoCin_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRippleCarryAdder106NoCin.ripplecarryadder106nocin_sec"
  },
  {
    circuitName := "SklanskyAdder106"
    specFile := "verification/specs/Adder_spec.sv"
    topModule := "Adder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeSklanskyAdder106.sklanskyadder106_sec"
  },
  {
    circuitName := "SklanskyAdder106NoCin"
    specFile := "verification/specs/AdderNoCin_spec.sv"
    topModule := "AdderNoCin_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeSklanskyAdder106NoCin.sklanskyadder106nocin_sec"
  },
  {
    circuitName := "Subtractor32"
    specFile := "verification/specs/Subtractor_spec.sv"
    topModule := "Subtractor_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeSubtractor32.subtractor32_sec"
  },
  {
    circuitName := "Subtractor64"
    specFile := "verification/specs/Subtractor_spec.sv"
    topModule := "Subtractor_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeSubtractor64.subtractor64_sec"
  },
  {
    circuitName := "CSACompressor48"
    specFile := "verification/specs/CSACompressor_spec.sv"
    topModule := "CSACompressor_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeCSACompressor48.csacompressor48_sec"
  },
  {
    circuitName := "CSACompressor64"
    specFile := "verification/specs/CSACompressor_spec.sv"
    topModule := "CSACompressor_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeCSACompressor64.csacompressor64_sec"
  },
  {
    circuitName := "CSACompressor106"
    specFile := "verification/specs/CSACompressor_spec.sv"
    topModule := "CSACompressor_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeCSACompressor106.csacompressor106_sec"
  },
  {
    circuitName := "ALU32"
    specFile := "verification/specs/ALU32_spec.sv"
    topModule := "ALU32_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeALU32.alu32_sec"
  },
  {
    circuitName := "ALU64"
    specFile := "verification/specs/ALU64_spec.sv"
    topModule := "ALU64_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeALU64.alu64_sec"
  },
  {
    circuitName := "PLRU2"
    specFile := "verification/specs/PLRU_spec.sv"
    topModule := "PLRU_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgePLRU2.plru2_sec"
  },
  {
    circuitName := "PLRU4"
    specFile := "verification/specs/PLRU_spec.sv"
    topModule := "PLRU_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgePLRU4.plru4_sec"
  },
  {
    circuitName := "PLRU8"
    specFile := "verification/specs/PLRU_spec.sv"
    topModule := "PLRU_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgePLRU8.plru8_sec"
  },
  {
    circuitName := "CRAT_32x6"
    specFile := "verification/specs/CRAT_32x6_spec.sv"
    topModule := "CRAT_32x6_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeCRAT_32x6.crat_32x6_sec"
  },
  {
    circuitName := "IntRAT_32x6"
    specFile := "verification/specs/IntRAT_32x6_spec.sv"
    topModule := "IntRAT_32x6_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeIntRAT_32x6.intrat_32x6_sec"
  },
  {
    circuitName := "RAT_32x6"
    specFile := "verification/specs/RAT_32x6_spec.sv"
    topModule := "RAT_32x6_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeRAT_32x6.rat_32x6_sec"
  },

  {
    circuitName := "ResetSync"
    specFile := "verification/specs/ResetSync_spec.sv"
    topModule := "ResetSync_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeResetSync.resetsync_sec"
  },
  {
    circuitName := "BootROM"
    specFile := "verification/specs/BootROM_spec.sv"
    topModule := "BootROM_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeBootROM.bootrom_sec"
  },
  {
    circuitName := "GPIO"
    specFile := "verification/specs/GPIO_spec.sv"
    topModule := "GPIO_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeGPIO.gpio_sec"
  },
  {
    circuitName := "UART"
    specFile := "verification/specs/UART_spec.sv"
    topModule := "UART_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeUART.uart_sec"
  },
  {
    circuitName := "ACLINT"
    specFile := "verification/specs/ACLINT_spec.sv"
    topModule := "ACLINT_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeACLINT.aclint_sec"
  },
  {
    circuitName := "APLIC"
    specFile := "verification/specs/APLIC_spec.sv"
    topModule := "APLIC_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeAPLIC.aplic_sec"
  },

  {
    circuitName := "IntegerExecUnit_W2"
    specFile := "verification/specs/IntegerExecUnit_W2_spec.sv"
    topModule := "IntegerExecUnit_W2_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeIntegerExecUnit_W2.integerexecunit_w2_sec"
  },
  {
    circuitName := "IntegerExecUnit_W2_64"
    specFile := "verification/specs/IntegerExecUnit_W2_64_spec.sv"
    topModule := "IntegerExecUnit_W2_64_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeIntegerExecUnit_W2_64.integerexecunit_w2_64_sec"
  },
  -- Equivalence established by randomised differential co-simulation
  -- (`//verification:spec_equiv_all`); these carry no bv_decide proof.
  {
    circuitName := "BusyTable_W2"
    specFile := "verification/specs/BusyTable_W2_spec.sv"
    topModule := "BusyTable_W2_spec"
    coSimulated := true
  },
  {
    circuitName := "FPBusyTable"
    specFile := "verification/specs/FPBusyTable_spec.sv"
    topModule := "FPBusyTable_spec"
    coSimulated := true
  },
  {
    circuitName := "Mul32x32To64"
    specFile := "verification/specs/Mul32x32To64_spec.sv"
    topModule := "Mul32x32To64_spec"
    coSimulated := true
  },
  {
    circuitName := "BranchExecUnit"
    specFile := "verification/specs/BranchExecUnit_spec.sv"
    topModule := "BranchExecUnit_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeBranchExecUnit.branchexecunit_sec"
  },
  {
    circuitName := "MemoryExecUnit"
    specFile := "verification/specs/MemoryExecUnit_spec.sv"
    topModule := "MemoryExecUnit_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeMemoryExecUnit.memoryexecunit_sec"
  },
  {
    circuitName := "MemoryExecUnitDecoupled"
    specFile := "verification/specs/MemoryExecUnitDecoupled_spec.sv"
    topModule := "MemoryExecUnitDecoupled_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeMemoryExecUnitDecoupled.memoryexecunitdecoupled_sec"
  },
  {
    circuitName := "CDBMux_FD_W2"
    specFile := "verification/specs/CDBMux_FD_W2_spec.sv"
    topModule := "CDBMux_FD_W2_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeCDBMux_FD_W2.cdbmux_fd_w2_sec"
  },

  {
    circuitName := "Queue1_1"
    specFile := "verification/specs/Queue1_spec.sv"
    topModule := "Queue1_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeQueue1_1.queue1_1_sec"
  },
  {
    circuitName := "Queue1Flow_39"
    specFile := "verification/specs/Queue1Flow_spec.sv"
    topModule := "Queue1Flow_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeQueue1Flow_39.queue1flow_39_sec"
  },
  {
    circuitName := "Queue1Flow_43"
    specFile := "verification/specs/Queue1Flow_spec.sv"
    topModule := "Queue1Flow_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeQueue1Flow_43.queue1flow_43_sec"
  },
  {
    circuitName := "Queue1Flow_44"
    specFile := "verification/specs/Queue1Flow_spec.sv"
    topModule := "Queue1Flow_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeQueue1Flow_44.queue1flow_44_sec"
  },
  {
    circuitName := "Queue1Flow_70"
    specFile := "verification/specs/Queue1Flow_spec.sv"
    topModule := "Queue1Flow_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeQueue1Flow_70.queue1flow_70_sec"
  },
  {
    circuitName := "Queue1Flow_71"
    specFile := "verification/specs/Queue1Flow_spec.sv"
    topModule := "Queue1Flow_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeQueue1Flow_71.queue1flow_71_sec"
  },
  {
    circuitName := "Queue1Flow_72"
    specFile := "verification/specs/Queue1Flow_spec.sv"
    topModule := "Queue1Flow_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeQueue1Flow_72.queue1flow_72_sec"
  },
  {
    circuitName := "Queue1Flow_75"
    specFile := "verification/specs/Queue1Flow_spec.sv"
    topModule := "Queue1Flow_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeQueue1Flow_75.queue1flow_75_sec"
  },
  {
    circuitName := "Queue1Flow_76"
    specFile := "verification/specs/Queue1Flow_spec.sv"
    topModule := "Queue1Flow_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeQueue1Flow_76.queue1flow_76_sec"
  },
  {
    circuitName := "Queue1Flow_103"
    specFile := "verification/specs/Queue1Flow_spec.sv"
    topModule := "Queue1Flow_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeQueue1Flow_103.queue1flow_103_sec"
  },
  {
    circuitName := "Queue1Flow_104"
    specFile := "verification/specs/Queue1Flow_spec.sv"
    topModule := "Queue1Flow_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeQueue1Flow_104.queue1flow_104_sec"
  },
  {
    circuitName := "PriorityArbiter2"
    specFile := "verification/specs/PriorityArbiter_spec.sv"
    topModule := "PriorityArbiter_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgePriorityArbiter2.priorityarbiter2_sec"
  },
  {
    circuitName := "PriorityArbiter8"
    specFile := "verification/specs/PriorityArbiter_spec.sv"
    topModule := "PriorityArbiter_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgePriorityArbiter8.priorityarbiter8_sec"
  },
  {
    circuitName := "PriorityArbiter64"
    specFile := "verification/specs/PriorityArbiter_spec.sv"
    topModule := "PriorityArbiter_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgePriorityArbiter64.priorityarbiter64_sec"
  },
  {
    circuitName := "OneHotEncoder64"
    specFile := "verification/specs/OneHotEncoder_spec.sv"
    topModule := "OneHotEncoder_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeOneHotEncoder64.onehotencoder64_sec"
  },
  {
    circuitName := "Popcount8"
    specFile := "verification/specs/Popcount_spec.sv"
    topModule := "Popcount_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgePopcount8.popcount8_sec"
  },
  {
    circuitName := "QueuePointer_3"
    specFile := "verification/specs/QueuePointer_spec.sv"
    topModule := "QueuePointer_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeQueuePointer_3.queuepointer_3_sec"
  },
  {
    circuitName := "QueuePointerLoadable_3"
    specFile := "verification/specs/QueuePointerLoadable_spec.sv"
    topModule := "QueuePointerLoadable_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeQueuePointerLoadable_3.queuepointerloadable_3_sec"
  },
  {
    circuitName := "QueueCounterLoadable_4"
    specFile := "verification/specs/QueueCounterLoadable_spec.sv"
    topModule := "QueueCounterLoadable_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeQueueCounterLoadable_4.queuecounterloadable_4_sec"
  },
  {
    circuitName := "Queue16x32_DualPort"
    specFile := "verification/specs/Queue16x32_DualPort_spec.sv"
    topModule := "Queue16x32_DualPort_spec"
    hasProof := true
    proofRef := "ShoumeiSec.BridgeQueue16x32_DualPort.queue16x32_dualport_sec"
  },
]

/-- Look up a registered spec by circuit name. -/
def findSpec (name : String) : Option DualRTLSpec :=
  allSpecs.find? (·.circuitName == name)

/-- Compute the status of a circuit given the filesystem presence of its spec file. -/
def computeStatus (circuitName : String) (specFileExists : Bool) : SpecStatus :=
  match findSpec circuitName with
  | none => if specFileExists then .specExists else .missing
  | some spec =>
    if spec.hasProof then
      .secVerified
    else if spec.coSimulated && specFileExists then
      .coSimVerified
    else if specFileExists then
      .specExists
    else
      .missing

/-- Manifest entry for reporting. -/
structure ManifestEntry where
  circuitName : String
  status      : SpecStatus
  specFile    : String
  proofRef    : String
  deriving Repr

/-- Generate the manifest for a list of circuits. -/
def generateManifest (circuits : List Circuit) : IO (List ManifestEntry) := do
  circuits.mapM fun c => do
    let specOpt := findSpec c.name
    let defaultPath := s!"verification/specs/{c.name}_spec.sv"
    let specPath := specOpt.map (·.specFile) |>.getD defaultPath
    let fileExists ← (System.FilePath.mk specPath).pathExists
    let status := computeStatus c.name fileExists
    let proofRef := specOpt.map (·.proofRef) |>.getD ""
    pure {
      circuitName := c.name
      status := status
      specFile := specPath
      proofRef := proofRef
    }

/-- Print the Dual-RTL specification manifest and coverage summary. -/
def printManifest (circuits : List Circuit) : IO Unit := do
  let entries ← generateManifest circuits
  let verified := entries.filter (·.status == .secVerified) |>.length
  let coSim    := entries.filter (·.status == .coSimVerified) |>.length
  let specOnly := entries.filter (·.status == .specExists) |>.length
  let missing  := entries.filter (·.status == .missing) |>.length
  let total    := entries.length

  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  証明 Shoumei RTL - Dual-RTL SystemVerilog Specification Manifest"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""
  IO.println "STATUS       | CIRCUIT                          | SPEC FILE"
  IO.println "-------------+----------------------------------+-------------------------------------"
  for e in entries do
    let statusStr := match e.status with
      | .secVerified   => "✓ VERIFIED  "
      | .coSimVerified => "≈ CO-SIM    "
      | .specExists    => "○ SPEC_ONLY "
      | .missing       => "✗ MISSING   "
    let padLen := if e.circuitName.length < 32 then 32 - e.circuitName.length else 0
    let circPadded := e.circuitName ++ String.ofList (List.replicate padLen ' ')
    IO.println s!"{statusStr} | {circPadded} | {e.specFile}"

  IO.println "-------------+----------------------------------+-------------------------------------"
  IO.println s!"Summary: {verified} SEC-verified, {coSim} co-sim-verified, {specOnly} spec-only, {missing} missing (Total: {total})"
  let pct := if total > 0 then (verified * 100) / total else 0
  IO.println s!"Dual-RTL SEC Bridge Coverage: {verified}/{total} ({pct}%)"
  let withEvidence := verified + coSim
  let epct := if total > 0 then (withEvidence * 100) / total else 0
  IO.println s!"Dual-RTL equivalence evidence (SEC or co-sim): {withEvidence}/{total} ({epct}%)"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

/-- Gate on specification evidence.

Circuits with no spec at all are reported but not fatal — the missing set is an
agreed out-of-scope boundary (Tier D).  A spec that exists with no equivalence
evidence *is* fatal: writing a spec without securing evidence for it is the
regression this check exists to catch, and the recorded statuses move only in
one direction (`//verification:sec_bridge_test` / `//verification:spec_equiv_all`). -/
def checkSpecs (circuits : List Circuit) : IO UInt32 := do
  let entries ← generateManifest circuits
  let unbacked := entries.filter (·.status == .specExists)
  let missing  := entries.filter (·.status == .missing)
  let verified := entries.filter (·.status == .secVerified) |>.length
  let cosim    := entries.filter (·.status == .coSimVerified) |>.length
  IO.println s!"{verified} SEC-verified, {cosim} co-sim-verified, {unbacked.length} spec-only, {missing.length} without a spec (of {entries.length})"
  if unbacked.isEmpty then
    IO.println s!"✓ Every registered specification carries equivalence evidence."
    pure 0
  else
    IO.eprintln s!"✗ {unbacked.length} specification(s) have no equivalence evidence (neither SEC nor co-simulation):"
    for e in unbacked do
      IO.eprintln s!"  {e.circuitName} ({e.specFile})"
    IO.eprintln "  Add an SEC bridge in scripts/gen-bridges.py, or list the module under"
    IO.eprintln "  EXTRA_SPEC_ONLY in scripts/spec-equiv.py and mark it coSimulated := true."
    pure 1

end Shoumei.Verification.DualRTL
