namespace Doom

/-- Signed 16.16 storage. Arithmetic explicitly wraps to 32 bits. -/
structure Fixed where
  raw : Int32
  deriving BEq, DecidableEq, Repr, Inhabited

namespace Fixed

def ofInt (n : Int) : Fixed := ⟨Int32.ofInt (n * 65536)⟩
def ofFloat (n : Float) : Fixed := ⟨(n * 65536.0).toInt32⟩
def toFloat (n : Fixed) : Float := n.raw.toInt64.toFloat / 65536.0
def add (a b : Fixed) : Fixed := ⟨a.raw + b.raw⟩
def sub (a b : Fixed) : Fixed := ⟨a.raw - b.raw⟩

/-- Euclidean division by 2^16 matches an arithmetic right shift, including negatives. -/
def mul (a b : Fixed) : Fixed :=
  ⟨Int32.ofInt ((a.raw.toInt * b.raw.toInt) / 65536)⟩

/-- Truncate toward zero, then wrap. Explicitly fail on zero; not vanilla's saturation policy. -/
def div? (a b : Fixed) : Option Fixed :=
  if b.raw == 0 then none
  else some ⟨Int32.ofInt ((a.raw.toInt * 65536).tdiv b.raw.toInt)⟩

inductive DivisionError where
  /-- The original DOS IDIV instruction raises #DE for these outcomes. -/
  | divideByZero
  | quotientOverflow
  deriving BEq, DecidableEq, Repr

/-- Two's-complement absolute value: INT_MIN stays negative, as in DOS DOOM. -/
def absWrap (n : Int32) : Int32 := if n < 0 then -n else n

/-- Original DOS DOOM 1.9 FixedDiv, including its wrapping absolute-value guard.
The guard saturates; IDIV truncates toward zero and faults rather than wrapping
an out-of-range quotient. Represent #DE as an explicit error, not a host crash.
Proved against the original instruction bytes in Doom.Proofs.OriginalDiv.
Reference implementation derived from id Software (1993-1996), Simon Howard
(2005-2014), GPL-2.0-or-later; see COPYING.md and tests/reference/manifest.json.
This deliberately differs from the diagnostic div? above. -/
def divChecked (a b : Fixed) : Except DivisionError Fixed :=
  if (absWrap a.raw >>> 14) ≥ absWrap b.raw then
    .ok ⟨if (a.raw ^^^ b.raw) < 0 then -2147483648 else 2147483647⟩
  else if b.raw == 0 then .error .divideByZero
  else
    let q := (a.raw.toInt * 65536).tdiv b.raw.toInt
    if q < -2147483648 || q > 2147483647 then .error .quotientOverflow
    else .ok ⟨Int32.ofInt q⟩

instance : Add Fixed := ⟨add⟩
instance : Sub Fixed := ⟨sub⟩
instance : Mul Fixed := ⟨mul⟩

end Fixed

/-- One full turn is 2^32. Addition wraps naturally. -/
structure Angle where
  raw : UInt32
  deriving BEq, Repr, Inhabited

def Angle.ofDegrees (degrees : Int) : Angle :=
  ⟨UInt32.ofNat (((degrees % 360) * 4294967296 / 360).toNat)⟩

def Angle.radians (angle : Angle) : Float :=
  angle.raw.toFloat * (6.283185307179586 / 4294967296.0)

def Angle.turn (angle : Angle) (radians : Float) : Angle :=
  ⟨angle.raw + (radians * (4294967296.0 / 6.283185307179586)).toInt64.toUInt64.toUInt32⟩

end Doom
