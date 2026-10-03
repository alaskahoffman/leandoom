namespace Doom

/-- Signed 16.16 storage. Arithmetic explicitly wraps to 32 bits. -/
structure Fixed where
  raw : Int32
  deriving BEq, Repr, Inhabited

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
  /-- The reference's abs(INT_MIN) is undefined in C; DOS evidence is pending. -/
  | unverifiedAbsOverflow
  deriving BEq, Repr

/-- FixedDiv on the reference's verified operand domain. The guard saturates
before division (including zero divisors); the remaining quotient truncates
toward zero. Refuse abs(INT_MIN) inputs rather than inventing DOS behavior.
Reference: Chocolate Doom 3.1.1 src/m_fixed.c, pinned in tests/reference/manifest.json.
Derived from id Software (1993-1996), Simon Howard (2005-2014), GPL-2.0-or-later;
see COPYING.md. This differs deliberately from the diagnostic div? above. -/
def divChecked (a b : Fixed) : Except DivisionError Fixed :=
  if a.raw == -2147483648 || b.raw == -2147483648 then
    .error .unverifiedAbsOverflow
  else if a.raw.toInt.natAbs / 16384 ≥ b.raw.toInt.natAbs then
    .ok ⟨if (a.raw ^^^ b.raw) < 0 then -2147483648 else 2147483647⟩
  else .ok ⟨Int32.ofInt ((a.raw.toInt * 65536).tdiv b.raw.toInt)⟩

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
