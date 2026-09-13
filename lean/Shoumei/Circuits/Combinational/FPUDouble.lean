/-
Circuits/Combinational/FPUDouble.lean - IEEE 754 Double-Precision Floating-Point Unit

Behavioral model for IEEE 754 binary64 double-precision arithmetic.
Full compliance with RISC-V D extension semantics including:
- All 5 rounding modes (RNE, RTZ, RDN, RUP, RMM)
- All 5 exception flags (NV, DZ, OF, UF, NX)
- Full subnormal support
- Canonical NaN generation (0x7FF8000000000000)
- Fused multiply-add with single rounding
- Conversions between Double, Single, and 32-bit integers
-/

import Shoumei.RISCV.ISA
import Shoumei.Circuits.Combinational.FPU

namespace Shoumei.Circuits.Combinational.FPUDouble

open Shoumei.Circuits.Combinational.FPU

/-! ## Constants -/

def dpBias : Nat := 1023
def dpExpBits : Nat := 11
def dpMantBits : Nat := 52
def dpMaxExp : Nat := 2047  -- 0x7FF (all 1s)

def canonicalNaN64 : UInt64 := 0x7FF8000000000000
def posInf64 : UInt64 := 0x7FF0000000000000
def negInf64 : UInt64 := 0xFFF0000000000000
def posZero64 : UInt64 := 0x0000000000000000
def negZero64 : UInt64 := 0x8000000000000000

/-! ## Unpacked Double Representation -/

structure UnpackedDouble where
  sign : Bool
  biasedExp : Nat
  mantissa : Nat
  deriving Repr, BEq

def unpack64 (bits : UInt64) : UnpackedDouble :=
  { sign := (bits >>> 63).toNat != 0
    biasedExp := ((bits >>> 52) &&& 0x7FF).toNat
    mantissa := (bits &&& 0xFFFFFFFFFFFFF).toNat }

def pack64 (f : UnpackedDouble) : UInt64 :=
  let s := if f.sign then (1 : UInt64) <<< 63 else 0
  let e := (UInt64.ofNat (f.biasedExp % 2048)) <<< 52
  let m := UInt64.ofNat (f.mantissa % (2^52))
  s ||| e ||| m

def classify64 (bits : UInt64) : FPClass :=
  let f := unpack64 bits
  if f.biasedExp == dpMaxExp then
    if f.mantissa == 0 then
      if f.sign then .NegInf else .PosInf
    else
      if f.mantissa &&& (2^51) != 0 then .QNaN else .SNaN
  else if f.biasedExp == 0 then
    if f.mantissa == 0 then
      if f.sign then .NegZero else .PosZero
    else
      if f.sign then .NegSubnormal else .PosSubnormal
  else
    if f.sign then .NegNormal else .PosNormal

def isNaN64 (bits : UInt64) : Bool :=
  match classify64 bits with
  | .QNaN | .SNaN => true
  | _ => false

def isSNaN64 (bits : UInt64) : Bool :=
  classify64 bits == .SNaN

def isInf64 (bits : UInt64) : Bool :=
  match classify64 bits with
  | .PosInf | .NegInf => true
  | _ => false

def isZero64 (bits : UInt64) : Bool :=
  match classify64 bits with
  | .PosZero | .NegZero => true
  | _ => false

def getSign64 (bits : UInt64) : Bool :=
  (bits >>> 63).toNat != 0

/-! ## Double-Precision FP Result Type -/

structure FPResult64 where
  value : UInt64
  exceptions : FPExceptions := {}
  deriving Repr

/-! ## NaN Handling -/

def propagateNaN2_64 (a b : UInt64) : Option FPResult64 :=
  let aNaN := isNaN64 a
  let bNaN := isNaN64 b
  if aNaN || bNaN then
    let nv := isSNaN64 a || isSNaN64 b
    some { value := canonicalNaN64, exceptions := { nv := nv } }
  else
    none

def propagateNaN3_64 (a b c : UInt64) : Option FPResult64 :=
  let nv := isSNaN64 a || isSNaN64 b || isSNaN64 c
  if isNaN64 a || isNaN64 b || isNaN64 c then
    some { value := canonicalNaN64, exceptions := { nv := nv } }
  else
    none

/-! ## Extended Float Conversion & Rounding -/

def toExtended64 (bits : UInt64) : ExtendedFloat :=
  let f := unpack64 bits
  if f.biasedExp == dpMaxExp then
    { sign := f.sign, significand := 0, exponent := 0, isInf := true }
  else if f.biasedExp == 0 then
    if f.mantissa == 0 then
      { sign := f.sign, significand := 0, exponent := 0, isZero := true }
    else
      -- Subnormal: (-1)^s × mantissa × 2^(-1022 - 52) = (-1)^s × mantissa × 2^(-1074)
      { sign := f.sign, significand := f.mantissa, exponent := -1074 }
  else
    -- Normal: (-1)^s × (2^52 + mantissa) × 2^(biasedExp - 1023 - 52)
    { sign := f.sign, significand := (2^52) + f.mantissa,
      exponent := (f.biasedExp : Int) - 1075 }

def roundToDP (ef : ExtendedFloat) (rm : RoundingMode) : FPResult64 :=
  if ef.isZero then
    { value := if ef.sign then negZero64 else posZero64 }
  else if ef.isInf then
    { value := if ef.sign then negInf64 else posInf64 }
  else
    let sig := ef.significand
    let sigBits := Nat.log2 sig + 1
    let shiftRight := if sigBits > 53 then sigBits - 53 else 0
    let shiftLeft := if sigBits <= 53 then 53 - sigBits else 0
    let adjExp : Int := ef.exponent + (shiftRight : Int) - (shiftLeft : Int)
    let biasedExpInt : Int := adjExp + 1075

    let (sig53, guard, round_, sticky) :=
      if shiftRight > 0 then
        let shifted := sig >>> shiftRight
        let guardBit := if shiftRight >= 1 then (sig >>> (shiftRight - 1)) % 2 == 1 else false
        let roundBit := if shiftRight >= 2 then (sig >>> (shiftRight - 2)) % 2 == 1 else false
        let stickyMask := if shiftRight >= 2 then (1 <<< (shiftRight - 2)) - 1 else 0
        let stickyBit := (sig &&& stickyMask) != 0
        (shifted, guardBit, roundBit, stickyBit)
      else
        (sig <<< shiftLeft, false, false, false)

    let inexact := guard || round_ || sticky

    let roundUp := match rm with
      | .RNE => guard && (round_ || sticky || sig53 % 2 == 1)
      | .RTZ => false
      | .RDN => ef.sign && inexact
      | .RUP => !ef.sign && inexact
      | .RMM => guard

    let sig53' := if roundUp then sig53 + 1 else sig53

    let (sigFinal, biasedExpFinal) :=
      if sig53' >= (2^53) then
        (sig53' >>> 1, biasedExpInt + 1)
      else
        (sig53', biasedExpInt)

    if biasedExpFinal >= 2047 then
      let overflowToInf := match rm with
        | .RTZ => false
        | .RDN => ef.sign
        | .RUP => !ef.sign
        | _ => true
      if overflowToInf then
        { value := if ef.sign then negInf64 else posInf64,
          exceptions := { of := true, nx := true } }
      else
        let maxVal := if ef.sign then 0xFFEFFFFFFFFFFFFF else 0x7FEFFFFFFFFFFFFF
        { value := maxVal, exceptions := { of := true, nx := true } }
    else if biasedExpFinal <= 0 then
      let extraShift := (1 - biasedExpFinal).toNat
      if extraShift >= 53 then
        let flushSign := match rm with
          | .RDN => true
          | _ => ef.sign
        { value := if flushSign then negZero64 else posZero64,
          exceptions := { uf := true, nx := inexact } }
      else
        let subSig := sigFinal >>> extraShift
        let subGuard := if extraShift >= 1 then (sigFinal >>> (extraShift - 1)) % 2 == 1 else false
        let subSticky := (sigFinal &&& ((1 <<< (extraShift - 1)) - 1)) != 0 || inexact
        let subRoundUp := match rm with
          | .RNE => subGuard && (subSticky || subSig % 2 == 1)
          | .RTZ => false
          | .RDN => ef.sign && (subGuard || subSticky)
          | .RUP => !ef.sign && (subGuard || subSticky)
          | .RMM => subGuard
        let subSig' := if subRoundUp then subSig + 1 else subSig
        if subSig' >= (2^52) then
          let packed := pack64 { sign := ef.sign, biasedExp := 1, mantissa := subSig' - 2^52 }
          { value := packed, exceptions := { uf := true, nx := inexact || subGuard || subSticky } }
        else
          let packed := pack64 { sign := ef.sign, biasedExp := 0, mantissa := subSig' }
          let isUnderflow := inexact || subGuard || subSticky
          { value := packed, exceptions := if isUnderflow then { uf := true, nx := true } else {} }
    else
      let mant := sigFinal - (2^52)
      let packed := pack64 { sign := ef.sign, biasedExp := biasedExpFinal.toNat, mantissa := mant }
      { value := packed, exceptions := if inexact then { nx := true } else {} }

/-! ## Arithmetic Operations -/

def dpAddSub (a b : UInt64) (op_sub : Bool) (rm : RoundingMode) : FPResult64 :=
  let bEff := if op_sub then b ^^^ 0x8000000000000000 else b
  match propagateNaN2_64 a bEff with
  | some r => r
  | none =>
  let aInf := isInf64 a
  let bInf := isInf64 bEff
  let aSign := getSign64 a
  let bSign := getSign64 bEff
  if aInf && bInf then
    if aSign != bSign then
      { value := canonicalNaN64, exceptions := { nv := true } }
    else
      { value := if aSign then negInf64 else posInf64 }
  else if aInf then
    { value := if aSign then negInf64 else posInf64 }
  else if bInf then
    { value := if bSign then negInf64 else posInf64 }
  else
    let ea := toExtended64 a
    let eb := toExtended64 bEff
    if ea.isZero && eb.isZero then
      let resultSign := match rm with
        | .RDN => ea.sign || eb.sign
        | _ => ea.sign && eb.sign
      { value := if resultSign then negZero64 else posZero64 }
    else if ea.isZero then
      roundToDP eb rm
    else if eb.isZero then
      roundToDP ea rm
    else
      let minExp := min ea.exponent eb.exponent
      let aShift := (ea.exponent - minExp).toNat
      let bShift := (eb.exponent - minExp).toNat
      let aSig := ea.significand <<< aShift
      let bSig := eb.significand <<< bShift
      if ea.sign == eb.sign then
        let resultSig := aSig + bSig
        roundToDP { sign := ea.sign, significand := resultSig, exponent := minExp } rm
      else
        if aSig >= bSig then
          let resultSig := aSig - bSig
          if resultSig == 0 then
            let resultSign := match rm with
              | .RDN => true
              | _ => false
            { value := if resultSign then negZero64 else posZero64 }
          else
            roundToDP { sign := ea.sign, significand := resultSig, exponent := minExp } rm
        else
          let resultSig := bSig - aSig
          roundToDP { sign := eb.sign, significand := resultSig, exponent := minExp } rm

def dpMul (a b : UInt64) (rm : RoundingMode) : FPResult64 :=
  match propagateNaN2_64 a b with
  | some r => r
  | none =>
  let resultSign := getSign64 a != getSign64 b
  let aInf := isInf64 a
  let bInf := isInf64 b
  let aZero := isZero64 a
  let bZero := isZero64 b
  if (aInf && bZero) || (bInf && aZero) then
    { value := canonicalNaN64, exceptions := { nv := true } }
  else if aInf || bInf then
    { value := if resultSign then negInf64 else posInf64 }
  else if aZero || bZero then
    { value := if resultSign then negZero64 else posZero64 }
  else
    let ea := toExtended64 a
    let eb := toExtended64 b
    let prodSig := ea.significand * eb.significand
    let prodExp := ea.exponent + eb.exponent
    roundToDP { sign := resultSign, significand := prodSig, exponent := prodExp } rm

def dpFMA (a b c : UInt64) (rm : RoundingMode) : FPResult64 :=
  match propagateNaN3_64 a b c with
  | some r => r
  | none =>
  let abSign := getSign64 a != getSign64 b
  let aInf := isInf64 a
  let bInf := isInf64 b
  let cInf := isInf64 c
  let aZero := isZero64 a
  let bZero := isZero64 b
  if (aInf && bZero) || (bInf && aZero) then
    { value := canonicalNaN64, exceptions := { nv := true } }
  else if (aInf || bInf) && cInf then
    if abSign != getSign64 c then
      { value := canonicalNaN64, exceptions := { nv := true } }
    else
      { value := if abSign then negInf64 else posInf64 }
  else if aInf || bInf then
    { value := if abSign then negInf64 else posInf64 }
  else if cInf then
    { value := if getSign64 c then negInf64 else posInf64 }
  else
    let ea := toExtended64 a
    let eb := toExtended64 b
    let ec := toExtended64 c
    if ea.isZero || eb.isZero then
      if ec.isZero then
        let resultSign := match rm with
          | .RDN => abSign || ec.sign
          | _ => abSign && ec.sign
        { value := if resultSign then negZero64 else posZero64 }
      else
        roundToDP ec rm
    else
      let prodSig := ea.significand * eb.significand
      let prodExp := ea.exponent + eb.exponent
      if ec.isZero then
        roundToDP { sign := abSign, significand := prodSig, exponent := prodExp } rm
      else
        let minExp := min prodExp ec.exponent
        let prodShift := (prodExp - minExp).toNat
        let cShift := (ec.exponent - minExp).toNat
        let prodAligned := prodSig <<< prodShift
        let cAligned := ec.significand <<< cShift
        if abSign == ec.sign then
          let resultSig := prodAligned + cAligned
          roundToDP { sign := abSign, significand := resultSig, exponent := minExp } rm
        else
          if prodAligned >= cAligned then
            let resultSig := prodAligned - cAligned
            if resultSig == 0 then
              let s := match rm with | .RDN => true | _ => false
              { value := if s then negZero64 else posZero64 }
            else
              roundToDP { sign := abSign, significand := resultSig, exponent := minExp } rm
          else
            let resultSig := cAligned - prodAligned
            roundToDP { sign := ec.sign, significand := resultSig, exponent := minExp } rm

def dpDiv (a b : UInt64) (rm : RoundingMode) : FPResult64 :=
  match propagateNaN2_64 a b with
  | some r => r
  | none =>
  let resultSign := getSign64 a != getSign64 b
  let aInf := isInf64 a
  let bInf := isInf64 b
  let aZero := isZero64 a
  let bZero := isZero64 b
  if (aInf && bInf) || (aZero && bZero) then
    { value := canonicalNaN64, exceptions := { nv := true } }
  else if aInf then
    { value := if resultSign then negInf64 else posInf64 }
  else if bInf then
    { value := if resultSign then negZero64 else posZero64 }
  else if bZero then
    { value := if resultSign then negInf64 else posInf64, exceptions := { dz := true } }
  else if aZero then
    { value := if resultSign then negZero64 else posZero64 }
  else
    let ea := toExtended64 a
    let eb := toExtended64 b
    let numShift : Nat := 120
    let shiftedNum := ea.significand <<< numShift
    let quot := shiftedNum / eb.significand
    let rem := shiftedNum % eb.significand
    let quotExp := ea.exponent - eb.exponent - (numShift : Int)
    let sigWithSticky := if rem != 0 then (quot <<< 1) ||| 1 else (quot <<< 1)
    roundToDP { sign := resultSign, significand := sigWithSticky, exponent := quotExp - 1 } rm

private def isqrt (n : Nat) : Nat :=
  if n == 0 then 0
  else
    let rec loop (x : Nat) (iter : Nat) : Nat :=
      if iter == 0 then x
      else
        let nextX := (x + n / x) / 2
        if nextX >= x then x
        else loop nextX (iter - 1)
    loop (n / 2 + 1) 100

def dpSqrt (a : UInt64) (rm : RoundingMode) : FPResult64 :=
  if isNaN64 a then
    let nv := isSNaN64 a
    { value := canonicalNaN64, exceptions := { nv := nv } }
  else if isZero64 a then
    { value := a }
  else if getSign64 a then
    { value := canonicalNaN64, exceptions := { nv := true } }
  else if isInf64 a then
    { value := posInf64 }
  else
    let ea := toExtended64 a
    let (adjSig, adjExp) :=
      if ea.exponent % 2 != 0 then
        (ea.significand <<< 1, ea.exponent - 1)
      else
        (ea.significand, ea.exponent)
    let numShift : Nat := 120
    let shiftedSig := adjSig <<< numShift
    let root := isqrt shiftedSig
    let rootSq := root * root
    let rem := shiftedSig - rootSq
    let rootExp := adjExp / 2 - (numShift / 2 : Int)
    let sigWithSticky := if rem != 0 then (root <<< 1) ||| 1 else (root <<< 1)
    roundToDP { sign := false, significand := sigWithSticky, exponent := rootExp - 1 } rm

/-! ## Comparisons & Classification -/

def dpCompare (a b : UInt64) (isEq isLt isLe : Bool) : FPResult :=
  let aNaN := isNaN64 a
  let bNaN := isNaN64 b
  if aNaN || bNaN then
    let nv := if isEq then isSNaN64 a || isSNaN64 b else true
    { value := 0, exceptions := { nv := nv } }
  else
    let ea := toExtended64 a
    let eb := toExtended64 b
    let (aIs0, bIs0) := (ea.isZero, eb.isZero)
    let eq := (aIs0 && bIs0) || (ea.sign == eb.sign && ea.isInf == eb.isInf && ea.significand == eb.significand && ea.exponent == eb.exponent)
    let lt :=
      if aIs0 && bIs0 then false
      else if ea.sign && !eb.sign then true
      else if !ea.sign && eb.sign then false
      else if ea.sign then
        if ea.isInf && eb.isInf then false
        else if ea.isInf then true
        else if eb.isInf then false
        else
          let minExp := min ea.exponent eb.exponent
          (ea.significand <<< (ea.exponent - minExp).toNat) > (eb.significand <<< (eb.exponent - minExp).toNat)
      else
        if ea.isInf && eb.isInf then false
        else if ea.isInf then false
        else if eb.isInf then true
        else
          let minExp := min ea.exponent eb.exponent
          (ea.significand <<< (ea.exponent - minExp).toNat) < (eb.significand <<< (eb.exponent - minExp).toNat)
    let le := eq || lt
    let res := if isEq then eq else if isLt then lt else if isLe then le else false
    { value := if res then 1 else 0 }

def dpClassify (a : UInt64) : UInt32 :=
  match classify64 a with
  | .NegInf       => 0x001
  | .NegNormal    => 0x002
  | .NegSubnormal => 0x004
  | .NegZero      => 0x008
  | .PosZero      => 0x010
  | .PosSubnormal => 0x020
  | .PosNormal    => 0x040
  | .PosInf       => 0x080
  | .SNaN         => 0x100
  | .QNaN         => 0x200

def dpMin (a b : UInt64) : FPResult64 :=
  let aNaN := isNaN64 a
  let bNaN := isNaN64 b
  if aNaN && bNaN then
    { value := canonicalNaN64, exceptions := { nv := isSNaN64 a || isSNaN64 b } }
  else if aNaN then
    { value := b, exceptions := { nv := isSNaN64 a } }
  else if bNaN then
    { value := a, exceptions := { nv := isSNaN64 b } }
  else if isZero64 a && isZero64 b then
    { value := if getSign64 a || getSign64 b then negZero64 else posZero64 }
  else
    let cmp := dpCompare a b false true false
    { value := if cmp.value == 1 then a else b }

def dpMax (a b : UInt64) : FPResult64 :=
  let aNaN := isNaN64 a
  let bNaN := isNaN64 b
  if aNaN && bNaN then
    { value := canonicalNaN64, exceptions := { nv := isSNaN64 a || isSNaN64 b } }
  else if aNaN then
    { value := b, exceptions := { nv := isSNaN64 a } }
  else if bNaN then
    { value := a, exceptions := { nv := isSNaN64 b } }
  else if isZero64 a && isZero64 b then
    { value := if !getSign64 a || !getSign64 b then posZero64 else negZero64 }
  else
    let cmp := dpCompare a b false true false
    { value := if cmp.value == 1 then b else a }

def dpSgnj (a b : UInt64) : UInt64 :=
  (a &&& 0x7FFFFFFFFFFFFFFF) ||| (b &&& 0x8000000000000000)

def dpSgnjn (a b : UInt64) : UInt64 :=
  (a &&& 0x7FFFFFFFFFFFFFFF) ||| ((b ^^^ 0x8000000000000000) &&& 0x8000000000000000)

def dpSgnjx (a b : UInt64) : UInt64 :=
  a ^^^ (b &&& 0x8000000000000000)

/-! ## Conversions -/

def dpToInt32 (a : UInt64) (rm : RoundingMode) : FPResult :=
  if isSNaN64 a || isNaN64 a then
    { value := 0x7FFFFFFF, exceptions := { nv := true } }
  else if isInf64 a then
    if getSign64 a then
      { value := 0x80000000, exceptions := { nv := true } }
    else
      { value := 0x7FFFFFFF, exceptions := { nv := true } }
  else if isZero64 a then
    { value := 0 }
  else
    let ea := toExtended64 a
    let (intVal, inexact) :=
      if ea.exponent >= 0 then
        (ea.significand <<< ea.exponent.toNat, false)
      else
        let shift := (-ea.exponent).toNat
        let truncated := ea.significand >>> shift
        let lost := ea.significand &&& ((1 <<< shift) - 1)
        let halfBit := if shift >= 1 then (ea.significand >>> (shift - 1)) % 2 == 1 else false
        let roundUp := match rm with
          | .RNE => halfBit && ((if shift >= 2 then (ea.significand &&& ((1 <<< (shift - 1)) - 1)) != 0 else false) || truncated % 2 == 1)
          | .RTZ => false
          | .RDN => if ea.sign then lost != 0 else false
          | .RUP => if !ea.sign then lost != 0 else false
          | .RMM => halfBit
        let rounded := if roundUp then truncated + 1 else truncated
        (rounded, lost != 0)
    if ea.sign then
      if intVal > 2^31 then
        { value := 0x80000000, exceptions := { nv := true } }
      else
        { value := UInt32.ofNat ((2^32) - intVal), exceptions := if inexact then { nx := true } else {} }
    else
      if intVal >= 2^31 then
        { value := 0x7FFFFFFF, exceptions := { nv := true } }
      else
        { value := UInt32.ofNat intVal, exceptions := if inexact then { nx := true } else {} }

def dpToUInt32 (a : UInt64) (rm : RoundingMode) : FPResult :=
  if isSNaN64 a || isNaN64 a then
    { value := 0xFFFFFFFF, exceptions := { nv := true } }
  else if isInf64 a then
    if getSign64 a then
      { value := 0, exceptions := { nv := true } }
    else
      { value := 0xFFFFFFFF, exceptions := { nv := true } }
  else if isZero64 a then
    { value := 0 }
  else
    let ea := toExtended64 a
    if ea.sign then
      { value := 0, exceptions := { nv := true } }
    else
      let (intVal, inexact) :=
        if ea.exponent >= 0 then
          (ea.significand <<< ea.exponent.toNat, false)
        else
          let shift := (-ea.exponent).toNat
          let truncated := ea.significand >>> shift
          let lost := ea.significand &&& ((1 <<< shift) - 1)
          let halfBit := if shift >= 1 then (ea.significand >>> (shift - 1)) % 2 == 1 else false
          let roundUp := match rm with
            | .RNE => halfBit && ((if shift >= 2 then (ea.significand &&& ((1 <<< (shift - 1)) - 1)) != 0 else false) || truncated % 2 == 1)
            | .RTZ => false
            | .RDN => false
            | .RUP => lost != 0
            | .RMM => halfBit
          let rounded := if roundUp then truncated + 1 else truncated
          (rounded, lost != 0)
      if intVal >= 2^32 then
        { value := 0xFFFFFFFF, exceptions := { nv := true } }
      else
        { value := UInt32.ofNat intVal, exceptions := if inexact then { nx := true } else {} }

def int32ToDP (a : UInt32) : FPResult64 :=
  if a == 0 then
    { value := posZero64 }
  else
    let sign := (a >>> 31).toNat != 0
    let magnitude := if sign then ((0xFFFFFFFF - a.toNat + 1) % (2^32)) else a.toNat
    roundToDP { sign := sign, significand := magnitude, exponent := 0 } .RNE

def uint32ToDP (a : UInt32) : FPResult64 :=
  if a == 0 then
    { value := posZero64 }
  else
    roundToDP { sign := false, significand := a.toNat, exponent := 0 } .RNE

def dpToSP (a : UInt64) (rm : RoundingMode) : FPResult64 :=
  if isNaN64 a then
    let nv := isSNaN64 a
    let boxed := (0xFFFFFFFF : UInt64) <<< 32 ||| UInt64.ofNat canonicalNaN.toNat
    { value := boxed, exceptions := { nv := nv } }
  else
    let ea := toExtended64 a
    let spRes := roundToSP ea rm
    let boxed := (0xFFFFFFFF : UInt64) <<< 32 ||| UInt64.ofNat spRes.value.toNat
    { value := boxed, exceptions := spRes.exceptions }

def spToDP (a : UInt64) : FPResult64 :=
  let isBoxed := (a >>> 32) == 0xFFFFFFFF
  let spVal : UInt32 := if isBoxed then UInt32.ofNat (a.toNat &&& 0xFFFFFFFF) else canonicalNaN
  if isNaN spVal then
    let nv := isSNaN spVal
    { value := canonicalNaN64, exceptions := { nv := nv } }
  else
    let ea := toExtended spVal
    roundToDP ea .RNE

end Shoumei.Circuits.Combinational.FPUDouble
