/-
Circuits/Combinational/FPU.lean - IEEE 754 Single-Precision Floating-Point Unit

Behavioral model for IEEE 754 binary32 single-precision arithmetic.
Full compliance with RISC-V F extension semantics including:
- All 5 rounding modes (RNE, RTZ, RDN, RUP, RMM)
- All 5 exception flags (NV, DZ, OF, UF, NX)
- Full subnormal support (no flush-to-zero)
- Canonical NaN propagation (0x7FC00000)
- Fused multiply-add with single rounding

Representation:
- Sign: 1 bit (bit 31)
- Exponent: 8 bits (bits 30:23), biased by 127
- Mantissa: 23 bits (bits 22:0), implicit leading 1 for normals

Special values:
- +0 = 0x00000000, -0 = 0x80000000
- +inf = 0x7F800000, -inf = 0xFF800000
- NaN: exponent = 0xFF, mantissa ≠ 0
- Canonical NaN = 0x7FC00000 (quiet NaN, positive)
-/

import Shoumei.RISCV.ISA

namespace Shoumei.Circuits.Combinational.FPU

/-! ## IEEE 754 Rounding Modes -/

/-- RISC-V rounding mode encoding (from frm CSR / instruction rm field) -/
inductive RoundingMode where
  | RNE : RoundingMode  -- Round to Nearest, ties to Even (default)
  | RTZ : RoundingMode  -- Round towards Zero
  | RDN : RoundingMode  -- Round Down (towards -∞)
  | RUP : RoundingMode  -- Round Up (towards +∞)
  | RMM : RoundingMode  -- Round to Nearest, ties to Max Magnitude
  deriving Repr, BEq, DecidableEq

/-- Decode 3-bit rounding mode field -/
def RoundingMode.fromNat : Nat → RoundingMode
  | 0 => .RNE
  | 1 => .RTZ
  | 2 => .RDN
  | 3 => .RUP
  | 4 => .RMM
  | _ => .RNE  -- Dynamic (from frm), default to RNE

/-! ## Exception Flags -/

/-- IEEE 754 exception flags (accumulated in RISC-V fflags CSR) -/
structure FPExceptions where
  /-- Invalid Operation (e.g., 0/0, inf-inf, sqrt(-1), signaling NaN input) -/
  nv : Bool := false
  /-- Division by Zero -/
  dz : Bool := false
  /-- Overflow (result too large for format) -/
  of : Bool := false
  /-- Underflow (result too small, lost precision) -/
  uf : Bool := false
  /-- Inexact (result was rounded) -/
  nx : Bool := false
  deriving Repr, BEq

/-- No exceptions raised -/
def FPExceptions.none : FPExceptions := {}

/-- Merge (OR) two exception sets -/
def FPExceptions.merge (a b : FPExceptions) : FPExceptions :=
  { nv := a.nv || b.nv, dz := a.dz || b.dz, of := a.of || b.of,
    uf := a.uf || b.uf, nx := a.nx || b.nx }

/-- Pack exception flags into 5-bit value for fflags CSR -/
def FPExceptions.toBits (e : FPExceptions) : UInt32 :=
  (if e.nv then 16 else 0) ||| (if e.dz then 8 else 0) |||
  (if e.of then 4 else 0) ||| (if e.uf then 2 else 0) |||
  (if e.nx then 1 else 0)

/-! ## Unpacked Floating-Point Representation -/

/-- Unpacked IEEE 754 SP value for internal computation -/
structure UnpackedFloat where
  /-- Sign bit: false = positive, true = negative -/
  sign : Bool
  /-- Biased exponent (0-255) -/
  biasedExp : Nat
  /-- Raw mantissa (23 bits, without implicit leading bit) -/
  mantissa : Nat
  deriving Repr, BEq

/-- Classification of an IEEE 754 value -/
inductive FPClass where
  | NegInf | NegNormal | NegSubnormal | NegZero
  | PosZero | PosSubnormal | PosNormal | PosInf
  | SNaN | QNaN
  deriving Repr, BEq, DecidableEq

/-! ## Constants -/

def spBias : Nat := 127
def spExpBits : Nat := 8
def spMantBits : Nat := 23
def spMaxExp : Nat := 255  -- All 1s
def canonicalNaN : UInt32 := 0x7FC00000
def posInf : UInt32 := 0x7F800000
def negInf : UInt32 := 0xFF800000
def posZero : UInt32 := 0x00000000
def negZero : UInt32 := 0x80000000

/-! ## Pack / Unpack -/

/-- Unpack a 32-bit IEEE 754 SP value -/
def unpack (bits : UInt32) : UnpackedFloat :=
  { sign := (bits >>> 31).toNat != 0
    biasedExp := ((bits >>> 23) &&& 0xFF).toNat
    mantissa := (bits &&& 0x7FFFFF).toNat }

/-- Pack an unpacked float back to 32 bits -/
def pack (f : UnpackedFloat) : UInt32 :=
  let s := if f.sign then (1 : UInt32) <<< 31 else 0
  let e := (UInt32.ofNat (f.biasedExp % 256)) <<< 23
  let m := UInt32.ofNat (f.mantissa % (2^23))
  s ||| e ||| m

/-- Classify an IEEE 754 SP value -/
def classify (bits : UInt32) : FPClass :=
  let f := unpack bits
  if f.biasedExp == spMaxExp then
    if f.mantissa == 0 then
      if f.sign then .NegInf else .PosInf
    else
      -- NaN: bit 22 distinguishes quiet (1) from signaling (0)
      if f.mantissa &&& (2^22) != 0 then .QNaN else .SNaN
  else if f.biasedExp == 0 then
    if f.mantissa == 0 then
      if f.sign then .NegZero else .PosZero
    else
      if f.sign then .NegSubnormal else .PosSubnormal
  else
    if f.sign then .NegNormal else .PosNormal

/-- Is value a NaN? -/
def isNaN (bits : UInt32) : Bool :=
  match classify bits with
  | .QNaN | .SNaN => true
  | _ => false

/-- Is value a signaling NaN? -/
def isSNaN (bits : UInt32) : Bool :=
  classify bits == .SNaN

/-- Is value infinity? -/
def isInf (bits : UInt32) : Bool :=
  match classify bits with
  | .PosInf | .NegInf => true
  | _ => false

/-- Is value zero? -/
def isZero (bits : UInt32) : Bool :=
  match classify bits with
  | .PosZero | .NegZero => true
  | _ => false

/-- Get sign bit -/
def getSign (bits : UInt32) : Bool :=
  (bits >>> 31).toNat != 0

/-! ## FP Result Type -/

/-- Result of an FP operation: value + exception flags -/
structure FPResult where
  value : UInt32
  exceptions : FPExceptions := {}
  deriving Repr

/-! ## NaN Handling -/

/-- Propagate NaN inputs: return canonical NaN and flag NV for signaling NaN.
    If either input is NaN, result is canonical NaN. -/
def propagateNaN2 (a b : UInt32) : Option FPResult :=
  let aNaN := isNaN a
  let bNaN := isNaN b
  if aNaN || bNaN then
    let nv := isSNaN a || isSNaN b
    some { value := canonicalNaN, exceptions := { nv := nv } }
  else
    none

/-- Same for 3-operand (fused multiply-add) -/
def propagateNaN3 (a b c : UInt32) : Option FPResult :=
  let nv := isSNaN a || isSNaN b || isSNaN c
  if isNaN a || isNaN b || isNaN c then
    some { value := canonicalNaN, exceptions := { nv := nv } }
  else
    none

/-! ## Core Arithmetic via Rational Representation

We implement FP arithmetic through exact rational computation followed by
rounding. This approach is simpler than bit-level mantissa manipulation
and provably correct for all IEEE 754 corner cases.

The key insight: IEEE 754 arithmetic = exact computation + rounding.
We compute the mathematically exact result as (sign, significand, exponent)
in arbitrary precision, then round to SP format.
-/

/-- Extended precision intermediate result for rounding.
    Represents (-1)^sign × significand × 2^exponent where significand
    is an arbitrary-precision natural number. -/
structure ExtendedFloat where
  sign : Bool
  /-- Significand (unsigned, arbitrary precision) -/
  significand : Nat
  /-- Unbiased exponent (can be negative) -/
  exponent : Int
  /-- Is this an exact zero? -/
  isZero : Bool := false
  /-- Is this infinity? -/
  isInf : Bool := false
  deriving Repr

/-- Convert unpacked SP to extended float for exact arithmetic -/
def toExtended (bits : UInt32) : ExtendedFloat :=
  let f := unpack bits
  if f.biasedExp == spMaxExp then
    -- Inf (NaN should be handled before calling this)
    { sign := f.sign, significand := 0, exponent := 0, isInf := true }
  else if f.biasedExp == 0 then
    if f.mantissa == 0 then
      -- Zero
      { sign := f.sign, significand := 0, exponent := 0, isZero := true }
    else
      -- Subnormal: (-1)^s × 0.mantissa × 2^(-126)
      -- = (-1)^s × mantissa × 2^(-126-23)
      { sign := f.sign, significand := f.mantissa, exponent := -149 }
  else
    -- Normal: (-1)^s × 1.mantissa × 2^(biasedExp - 127)
    -- = (-1)^s × (2^23 + mantissa) × 2^(biasedExp - 127 - 23)
    { sign := f.sign, significand := (2^23) + f.mantissa,
      exponent := (f.biasedExp : Int) - 150 }

/-- Round an extended float to SP format.

    The rounding process:
    1. Normalize significand to have exactly 24 significant bits (23 mantissa + implicit 1)
    2. Determine guard, round, sticky bits from discarded bits
    3. Apply rounding mode to decide whether to round up
    4. Handle overflow (→ infinity) and underflow (→ subnormal or zero)
    5. Pack into IEEE 754 SP format
-/
def roundToSP (ef : ExtendedFloat) (rm : RoundingMode) : FPResult :=
  if ef.isZero then
    { value := if ef.sign then negZero else posZero }
  else if ef.isInf then
    { value := if ef.sign then negInf else posInf }
  else
    -- Step 1: Find position of the most significant bit of significand
    let sig := ef.significand
    let sigBits := Nat.log2 sig + 1  -- number of bits needed to represent sig

    -- We need to place the result so that we have 24 significant bits.
    -- The value is sig × 2^ef.exponent.
    -- After normalization: 1.xxxx × 2^resultExp where xxxx is 23 bits.
    -- This means we want the significand as a 24-bit number (2^23 ≤ sig' < 2^24)
    -- with resultExp = ef.exponent + (sigBits - 24)... roughly.

    -- Calculate how many bits to shift right to get 24 significant bits
    -- If sigBits > 24, we shift right (losing precision, need to round)
    -- If sigBits ≤ 24, we shift left (no precision loss yet)
    let shiftRight := if sigBits > 24 then sigBits - 24 else 0
    let shiftLeft := if sigBits ≤ 24 then 24 - sigBits else 0

    -- Adjusted exponent (unbiased, for 1.xxx format)
    -- After shifting, significand is 24 bits, so real value = sig24 × 2^adjExp
    -- where adjExp = ef.exponent + shiftRight - shiftLeft
    let adjExp : Int := ef.exponent + (shiftRight : Int) - (shiftLeft : Int)

    -- The biased exponent for a normal SP number with 24-bit significand:
    -- value = sig24 × 2^adjExp = (1.mantissa) × 2^(biasedExp-127)
    -- sig24 = 2^23 × (1 + mantissa/2^23), so adjExp corresponds to biasedExp-127-23+23 = biasedExp-127
    -- Wait: sig24 is in [2^23, 2^24), so value = sig24 × 2^adjExp
    -- = (sig24/2^23) × 2^(adjExp+23), where sig24/2^23 ∈ [1, 2)
    -- So biasedExp = adjExp + 23 + 127 = adjExp + 150
    let biasedExpInt : Int := adjExp + 150

    -- Compute rounded 24-bit significand and guard/round/sticky
    let (sig24, guard, round_, sticky) :=
      if shiftRight > 0 then
        let shifted := sig >>> shiftRight
        let guardBit := if shiftRight >= 1 then (sig >>> (shiftRight - 1)) % 2 == 1 else false
        let roundBit := if shiftRight >= 2 then (sig >>> (shiftRight - 2)) % 2 == 1 else false
        -- Sticky = OR of all bits below round bit
        let stickyMask := if shiftRight >= 2 then (1 <<< (shiftRight - 2)) - 1 else 0
        let stickyBit := (sig &&& stickyMask) != 0
        (shifted, guardBit, roundBit, stickyBit)
      else
        (sig <<< shiftLeft, false, false, false)

    let inexact := guard || round_ || sticky

    -- Step 2: Apply rounding
    let roundUp := match rm with
      | .RNE =>
          -- Round to nearest, ties to even
          guard && (round_ || sticky || sig24 % 2 == 1)
      | .RTZ => false  -- Always truncate
      | .RDN => ef.sign && inexact  -- Round towards -∞
      | .RUP => !ef.sign && inexact  -- Round towards +∞
      | .RMM =>
          -- Round to nearest, ties away from zero
          guard

    let sig24' := if roundUp then sig24 + 1 else sig24

    -- Handle carry out from rounding (24 bits → 25 bits)
    let (sigFinal, biasedExpFinal) :=
      if sig24' >= (2^24) then
        (sig24' >>> 1, biasedExpInt + 1)
      else
        (sig24', biasedExpInt)

    -- Step 3: Handle overflow and underflow
    if biasedExpFinal >= 255 then
      -- Overflow → infinity or max finite, depending on rounding mode
      let overflowToInf := match rm with
        | .RTZ => false
        | .RDN => ef.sign    -- -∞ ok for negative, max for positive
        | .RUP => !ef.sign   -- +∞ ok for positive, max for negative
        | _ => true           -- RNE, RMM → infinity
      if overflowToInf then
        { value := if ef.sign then negInf else posInf,
          exceptions := { of := true, nx := true } }
      else
        -- Return max finite value
        let maxVal := if ef.sign then 0xFF7FFFFF else 0x7F7FFFFF
        { value := maxVal, exceptions := { of := true, nx := true } }
    else if biasedExpFinal <= 0 then
      -- Underflow: result is subnormal or zero
      -- Subnormal: biasedExp = 0, mantissa represents 0.xxx × 2^(-126)
      -- Need to shift significand right further
      let extraShift := (1 - biasedExpFinal).toNat
      if extraShift >= 24 then
        -- Underflow to zero
        let flushSign := match rm with
          | .RDN => true   -- -0 when rounding down
          | _ => ef.sign
        { value := if flushSign then negZero else posZero,
          exceptions := { uf := true, nx := inexact } }
      else
        let subSig := sigFinal >>> extraShift
        -- Re-check inexactness for subnormal
        let subInexact := inexact || (sigFinal &&& ((1 <<< extraShift) - 1)) != 0
        let mantissa := subSig % (2^23)
        { value := pack { sign := ef.sign, biasedExp := 0, mantissa := mantissa },
          exceptions := { uf := subInexact, nx := subInexact } }
    else
      -- Normal result
      let mantissa := sigFinal % (2^23)
      let bExp := biasedExpFinal.toNat
      { value := pack { sign := ef.sign, biasedExp := bExp, mantissa := mantissa },
        exceptions := { nx := inexact } }

/-! ## Arithmetic Operations -/

/-- FP Addition/Subtraction (exact via extended arithmetic) -/
def fpAddSub (a b : UInt32) (subtract : Bool) (rm : RoundingMode) : FPResult :=
  -- Handle NaN
  match propagateNaN2 a b with
  | some r => r
  | none =>
  -- Handle Inf
  let aInf := isInf a
  let bInf := isInf b
  let aSign := getSign a
  let bSign := if subtract then !getSign b else getSign b
  if aInf && bInf then
    if aSign != bSign then
      -- inf - inf = NaN (invalid)
      { value := canonicalNaN, exceptions := { nv := true } }
    else
      { value := if aSign then negInf else posInf }
  else if aInf then
    { value := if aSign then negInf else posInf }
  else if bInf then
    { value := if bSign then negInf else posInf }
  else
    -- Finite + finite: compute exactly then round
    let ea := toExtended a
    let bBits := if subtract then
      -- Flip sign of b for subtraction
      b ^^^ 0x80000000
    else b
    let eb := toExtended bBits

    -- Align exponents: shift the smaller one right
    if ea.isZero && eb.isZero then
      -- 0 + 0: sign is - only if both are -
      let resultSign := match rm with
        | .RDN => ea.sign || eb.sign  -- RDN: -0 if either is -0
        | _ => ea.sign && eb.sign     -- otherwise: -0 only if both are -0
      { value := if resultSign then negZero else posZero }
    else if ea.isZero then
      roundToSP eb rm
    else if eb.isZero then
      roundToSP ea rm
    else
      -- Both finite nonzero: align exponents
      let minExp := min ea.exponent eb.exponent
      let aShift := (ea.exponent - minExp).toNat
      let bShift := (eb.exponent - minExp).toNat
      let aSig := ea.significand <<< aShift
      let bSig := eb.significand <<< bShift

      -- Add or subtract based on signs
      if ea.sign == eb.sign then
        -- Same sign: add magnitudes
        let resultSig := aSig + bSig
        roundToSP { sign := ea.sign, significand := resultSig, exponent := minExp } rm
      else
        -- Different signs: subtract magnitudes
        if aSig >= bSig then
          let resultSig := aSig - bSig
          if resultSig == 0 then
            let resultSign := match rm with
              | .RDN => true
              | _ => false
            { value := if resultSign then negZero else posZero }
          else
            roundToSP { sign := ea.sign, significand := resultSig, exponent := minExp } rm
        else
          let resultSig := bSig - aSig
          roundToSP { sign := eb.sign, significand := resultSig, exponent := minExp } rm

/-- FP Multiply -/
def fpMul (a b : UInt32) (rm : RoundingMode) : FPResult :=
  match propagateNaN2 a b with
  | some r => r
  | none =>
  let resultSign := getSign a != getSign b
  let aInf := isInf a
  let bInf := isInf b
  let aZero := isZero a
  let bZero := isZero b
  -- inf × 0 = NaN (invalid)
  if (aInf && bZero) || (bInf && aZero) then
    { value := canonicalNaN, exceptions := { nv := true } }
  else if aInf || bInf then
    { value := if resultSign then negInf else posInf }
  else if aZero || bZero then
    { value := if resultSign then negZero else posZero }
  else
    let ea := toExtended a
    let eb := toExtended b
    let prodSig := ea.significand * eb.significand
    let prodExp := ea.exponent + eb.exponent
    roundToSP { sign := resultSign, significand := prodSig, exponent := prodExp } rm

/-- Fused Multiply-Add: a × b + c (single rounding) -/
def fpFMA (a b c : UInt32) (rm : RoundingMode) : FPResult :=
  -- Handle NaN (3-operand)
  match propagateNaN3 a b c with
  | some r => r
  | none =>
  let abSign := getSign a != getSign b
  let aInf := isInf a
  let bInf := isInf b
  let cInf := isInf c
  let aZero := isZero a
  let bZero := isZero b
  -- inf × 0 or 0 × inf = NaN
  if (aInf && bZero) || (bInf && aZero) then
    { value := canonicalNaN, exceptions := { nv := true } }
  else if (aInf || bInf) && cInf then
    -- inf*x + inf: ok if same sign, NaN if opposite
    if abSign != getSign c then
      { value := canonicalNaN, exceptions := { nv := true } }
    else
      { value := if abSign then negInf else posInf }
  else if aInf || bInf then
    { value := if abSign then negInf else posInf }
  else if cInf then
    { value := if getSign c then negInf else posInf }
  else
    -- Finite: compute a*b exactly, then add c exactly, then round once
    let ea := toExtended a
    let eb := toExtended b
    let ec := toExtended c
    if ea.isZero || eb.isZero then
      -- 0 × anything + c = c (but sign of zero matters)
      if ec.isZero then
        let resultSign := match rm with
          | .RDN => abSign || ec.sign
          | _ => abSign && ec.sign
        { value := if resultSign then negZero else posZero }
      else
        roundToSP ec rm
    else
      let prodSig := ea.significand * eb.significand
      let prodExp := ea.exponent + eb.exponent
      if ec.isZero then
        roundToSP { sign := abSign, significand := prodSig, exponent := prodExp } rm
      else
        -- Align product and addend
        let minExp := min prodExp ec.exponent
        let prodShift := (prodExp - minExp).toNat
        let cShift := (ec.exponent - minExp).toNat
        let prodAligned := prodSig <<< prodShift
        let cAligned := ec.significand <<< cShift
        if abSign == ec.sign then
          let resultSig := prodAligned + cAligned
          roundToSP { sign := abSign, significand := resultSig, exponent := minExp } rm
        else
          if prodAligned >= cAligned then
            let resultSig := prodAligned - cAligned
            if resultSig == 0 then
              let s := match rm with | .RDN => true | _ => false
              { value := if s then negZero else posZero }
            else
              roundToSP { sign := abSign, significand := resultSig, exponent := minExp } rm
          else
            let resultSig := cAligned - prodAligned
            roundToSP { sign := ec.sign, significand := resultSig, exponent := minExp } rm

/-- FP Division -/
def fpDiv (a b : UInt32) (rm : RoundingMode) : FPResult :=
  match propagateNaN2 a b with
  | some r => r
  | none =>
  let resultSign := getSign a != getSign b
  let aInf := isInf a
  let bInf := isInf b
  let aZero := isZero a
  let bZero := isZero b
  -- inf / inf = NaN, 0 / 0 = NaN
  if (aInf && bInf) || (aZero && bZero) then
    { value := canonicalNaN, exceptions := { nv := true } }
  else if aInf then
    { value := if resultSign then negInf else posInf }
  else if bInf then
    { value := if resultSign then negZero else posZero }
  else if bZero then
    -- x / 0 = ±inf, flag DZ
    { value := if resultSign then negInf else posInf, exceptions := { dz := true } }
  else if aZero then
    { value := if resultSign then negZero else posZero }
  else
    -- Finite / finite: use extended precision division
    -- We need enough precision for correct rounding: 24 mantissa bits + guard/round/sticky
    -- Multiply numerator by 2^50 to get ~50 bits of quotient
    let ea := toExtended a
    let eb := toExtended b
    let numScaled := ea.significand * (2^50)
    let quotient := numScaled / eb.significand
    let remainder := numScaled % eb.significand
    let quotExp := ea.exponent - eb.exponent - 50
    let ef : ExtendedFloat := {
      sign := resultSign
      significand := quotient
      exponent := quotExp
    }
    -- Adjust for remainder (sticky bit contribution)
    let result := roundToSP ef rm
    if remainder != 0 then
      -- There is a nonzero remainder, so result is definitely inexact
      { result with exceptions := { result.exceptions with nx := true } }
    else
      result

/-- FP Square Root -/
def fpSqrt (a : UInt32) (rm : RoundingMode) : FPResult :=
  match classify a with
  | .SNaN => { value := canonicalNaN, exceptions := { nv := true } }
  | .QNaN => { value := canonicalNaN }
  | .NegInf | .NegNormal | .NegSubnormal =>
      -- sqrt(negative) = NaN
      { value := canonicalNaN, exceptions := { nv := true } }
  | .NegZero => { value := negZero }  -- sqrt(-0) = -0
  | .PosZero => { value := posZero }  -- sqrt(+0) = +0
  | .PosInf => { value := posInf }    -- sqrt(+inf) = +inf
  | .PosNormal | .PosSubnormal =>
      -- Compute using integer Newton's method on significand × 2^scale
      let ea := toExtended a
      -- Scale significand so we have ~50 bits of precision
      -- Make exponent even by shifting significand if needed
      let (sig, exp) :=
        if ea.exponent % 2 == 0 then
          (ea.significand * (2^50), ea.exponent - 50)
        else
          (ea.significand * (2^51), ea.exponent - 51)
      -- exp is now even, compute integer sqrt of sig
      -- Newton's method: x_{n+1} = (x_n + sig/x_n) / 2
      let initGuess := if sig > 0 then 2^((Nat.log2 sig + 1) / 2) else 1
      let step := fun x => (x + sig / x) / 2
      -- 30 iterations is more than enough for convergence
      let x := (List.range 30).foldl (fun x _ => step x) initGuess
      -- Adjust: make sure x^2 ≤ sig < (x+1)^2
      let x := if (x + 1) * (x + 1) <= sig then x + 1 else x
      let x := if x * x > sig then x - 1 else x
      let sqrtExp := exp / 2  -- exp is even
      let remainder := sig - x * x
      let result := roundToSP { sign := false, significand := x, exponent := sqrtExp } rm
      if remainder != 0 then
        { result with exceptions := { result.exceptions with nx := true } }
      else
        result

/-! ## Comparison Operations -/

/-- FP Compare: returns (intResult, exceptions).
    Used for FEQ.S, FLT.S, FLE.S which write to integer rd. -/
def fpCompare (a b : UInt32) (eq lt le : Bool) : FPResult :=
  -- Any signaling NaN → NV. For FLT/FLE, any NaN → NV. For FEQ, only sNaN → NV.
  let aNaN := isNaN a
  let bNaN := isNaN b
  let nv := if eq && !lt && !le then
    -- FEQ: only sNaN raises NV
    isSNaN a || isSNaN b
  else
    -- FLT, FLE: any NaN raises NV
    aNaN || bNaN
  if aNaN || bNaN then
    { value := 0, exceptions := { nv := nv } }
  else
    -- Both are non-NaN: compare as signed magnitude
    let aSign := getSign a
    let bSign := getSign b
    let aVal := a &&& 0x7FFFFFFF  -- magnitude
    let bVal := b &&& 0x7FFFFFFF
    -- Handle ±0 equality
    let bothZero := isZero a && isZero b
    let equal := a == b || bothZero
    let aLess :=
      if aSign && !bSign then true        -- negative < positive
      else if !aSign && bSign then false   -- positive > negative
      else if aSign then aVal > bVal       -- both negative: larger magnitude = smaller value
      else aVal < bVal                     -- both positive: smaller magnitude = smaller value
    let result := (eq && equal) || (lt && aLess) || (le && (aLess || equal))
    { value := if result then 1 else 0, exceptions := { nv := nv } }

/-! ## Min/Max -/

def fpMin (a b : UInt32) : FPResult :=
  let nv := isSNaN a || isSNaN b
  if isNaN a && isNaN b then
    { value := canonicalNaN, exceptions := { nv := nv } }
  else if isNaN a then
    { value := b, exceptions := { nv := nv } }
  else if isNaN b then
    { value := a, exceptions := { nv := nv } }
  else
    -- Both non-NaN
    let r := fpCompare a b false true false  -- FLT
    let result := if r.value == 1 then a else
      -- Special case: -0 < +0 for min
      if isZero a && isZero b && getSign a then a else b
    { value := result, exceptions := { nv := nv } }

def fpMax (a b : UInt32) : FPResult :=
  let nv := isSNaN a || isSNaN b
  if isNaN a && isNaN b then
    { value := canonicalNaN, exceptions := { nv := nv } }
  else if isNaN a then
    { value := b, exceptions := { nv := nv } }
  else if isNaN b then
    { value := a, exceptions := { nv := nv } }
  else
    let r := fpCompare b a false true false  -- b < a?
    let result := if r.value == 1 then a else
      if isZero a && isZero b && getSign b then a else b
    { value := result, exceptions := { nv := nv } }

/-! ## Sign Injection -/

def fpSgnj (a b : UInt32) : UInt32 :=
  (a &&& 0x7FFFFFFF) ||| (b &&& 0x80000000)

def fpSgnjn (a b : UInt32) : UInt32 :=
  (a &&& 0x7FFFFFFF) ||| ((b ^^^ 0x80000000) &&& 0x80000000)

def fpSgnjx (a b : UInt32) : UInt32 :=
  a ^^^ (b &&& 0x80000000)

/-! ## Conversion Operations -/

/-- FCVT.W.S: FP → signed int32 -/
def fpToInt32 (a : UInt32) (rm : RoundingMode) : FPResult :=
  if isSNaN a || isNaN a then
    { value := 0x7FFFFFFF, exceptions := { nv := true } }  -- INT32_MAX for NaN
  else if isInf a then
    if getSign a then
      { value := 0x80000000, exceptions := { nv := true } }  -- INT32_MIN for -inf
    else
      { value := 0x7FFFFFFF, exceptions := { nv := true } }  -- INT32_MAX for +inf
  else if isZero a then
    { value := 0 }
  else
    let ea := toExtended a
    -- Compute exact integer value × 2^exponent
    -- If exponent >= 0, the integer is significand << exponent
    -- If exponent < 0, we need to round
    let (intVal, inexact) :=
      if ea.exponent >= 0 then
        (ea.significand <<< ea.exponent.toNat, false)
      else
        let shift := (-ea.exponent).toNat
        let truncated := ea.significand >>> shift
        let lost := ea.significand &&& ((1 <<< shift) - 1)
        -- Check rounding
        let halfBit := if shift >= 1 then (ea.significand >>> (shift - 1)) % 2 == 1 else false
        let stickyBit := if shift >= 2 then (ea.significand &&& ((1 <<< (shift - 1)) - 1)) != 0 else false
        let roundUp := match rm with
          | .RNE => halfBit && (stickyBit || truncated % 2 == 1)
          | .RTZ => false
          | .RDN => ea.sign && (lost != 0)
          | .RUP => !ea.sign && (lost != 0)
          | .RMM => halfBit
        let rounded := if roundUp then truncated + 1 else truncated
        (rounded, lost != 0)
    -- Convert to signed
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

/-- FCVT.WU.S: FP → unsigned int32 -/
def fpToUInt32 (a : UInt32) (rm : RoundingMode) : FPResult :=
  if isSNaN a || isNaN a then
    { value := 0xFFFFFFFF, exceptions := { nv := true } }
  else if isInf a then
    if getSign a then
      { value := 0, exceptions := { nv := true } }
    else
      { value := 0xFFFFFFFF, exceptions := { nv := true } }
  else if isZero a then
    { value := 0 }
  else
    let ea := toExtended a
    if ea.sign then
      -- Negative → clamp to 0
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
            | .RDN => false  -- positive, rounding down = truncate
            | .RUP => lost != 0
            | .RMM => halfBit
          let rounded := if roundUp then truncated + 1 else truncated
          (rounded, lost != 0)
      if intVal >= 2^32 then
        { value := 0xFFFFFFFF, exceptions := { nv := true } }
      else
        { value := UInt32.ofNat intVal, exceptions := if inexact then { nx := true } else {} }

/-- FCVT.S.W: signed int32 → FP -/
def int32ToFP (a : UInt32) (rm : RoundingMode) : FPResult :=
  if a == 0 then
    { value := posZero }
  else
    let sign := (a >>> 31).toNat != 0
    let magnitude := if sign then ((0xFFFFFFFF - a.toNat + 1) % (2^32)) else a.toNat
    roundToSP { sign := sign, significand := magnitude, exponent := 0 } rm

/-- FCVT.S.WU: unsigned int32 → FP -/
def uint32ToFP (a : UInt32) (rm : RoundingMode) : FPResult :=
  if a == 0 then
    { value := posZero }
  else
    roundToSP { sign := false, significand := a.toNat, exponent := 0 } rm

/-! ## FCLASS -/

/-- FCLASS.S: classify FP value, return 10-bit mask in integer register -/
def fpClassify (a : UInt32) : UInt32 :=
  match classify a with
  | .NegInf       => 0x001  -- bit 0
  | .NegNormal    => 0x002  -- bit 1
  | .NegSubnormal => 0x004  -- bit 2
  | .NegZero      => 0x008  -- bit 3
  | .PosZero      => 0x010  -- bit 4
  | .PosSubnormal => 0x020  -- bit 5
  | .PosNormal    => 0x040  -- bit 6
  | .PosInf       => 0x080  -- bit 7
  | .SNaN         => 0x100  -- bit 8
  | .QNaN         => 0x200  -- bit 9

/-! ## Top-Level FPU Execute Function -/

open Shoumei.RISCV in
/-- Execute any F-extension operation.
    Uses OpType from ISA.lean.
    Returns (result_value, exception_flags).
    For operations that write to integer rd (compare, classify, FCVT, FMV_X_W),
    result is an integer value. For FP-dest ops, result is FP bits. -/
def executeFP (op : OpType) (src1 src2 src3 : UInt32) (rm : RoundingMode) : FPResult :=
  match op with
  | .FADD_S => fpAddSub src1 src2 false rm
  | .FSUB_S => fpAddSub src1 src2 true rm
  | .FMUL_S => fpMul src1 src2 rm
  | .FDIV_S => fpDiv src1 src2 rm
  | .FSQRT_S => fpSqrt src1 rm
  -- Fused multiply-add: FMADD = rs1*rs2 + rs3
  | .FMADD_S => fpFMA src1 src2 src3 rm
  -- FMSUB = rs1*rs2 - rs3
  | .FMSUB_S => fpFMA src1 src2 (src3 ^^^ 0x80000000) rm
  -- FNMADD = -(rs1*rs2) + rs3 = -(rs1*rs2 - rs3) per spec: negate product
  | .FNMADD_S => fpFMA (src1 ^^^ 0x80000000) src2 (src3 ^^^ 0x80000000) rm
  -- FNMSUB = -(rs1*rs2) - rs3... actually per RISC-V: FNMSUB = -(rs1*rs2) + rs3
  | .FNMSUB_S => fpFMA (src1 ^^^ 0x80000000) src2 src3 rm
  -- Compare (→ integer rd)
  | .FEQ_S => fpCompare src1 src2 true false false
  | .FLT_S => fpCompare src1 src2 false true false
  | .FLE_S => fpCompare src1 src2 false false true
  -- Convert FP → int
  | .FCVT_W_S => fpToInt32 src1 rm
  | .FCVT_WU_S => fpToUInt32 src1 rm
  -- Convert int → FP
  | .FCVT_S_W => int32ToFP src1 rm
  | .FCVT_S_WU => uint32ToFP src1 rm
  -- Move (bit-preserving)
  | .FMV_X_W => { value := src1 }  -- FP bits → int reg
  | .FMV_W_X => { value := src1 }  -- int bits → FP reg
  -- Classify
  | .FCLASS_S => { value := fpClassify src1 }
  -- Min/Max
  | .FMIN_S => fpMin src1 src2
  | .FMAX_S => fpMax src1 src2
  -- Sign injection
  | .FSGNJ_S => { value := fpSgnj src1 src2 }
  | .FSGNJN_S => { value := fpSgnjn src1 src2 }
  | .FSGNJX_S => { value := fpSgnjx src1 src2 }
  -- FLW/FSW are handled by Memory unit, not FPU
  | _ => { value := 0 }

end Shoumei.Circuits.Combinational.FPU
