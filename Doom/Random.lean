/-
Arithmetic/BSP/RNG ports refer to Chocolate Doom 3.1.1, commit
410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996) and Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later
See COPYING.md and tests/reference/manifest.json.
-/

import Init.Data.UInt.Lemmas

namespace Doom

/-- Vanilla lookup table, checked in full against the pinned reference. -/
def randomTable : Array Nat := #[0,   8, 109, 220, 222, 241, 149, 107,  75, 248, 254, 140,  16,  66 ,
    74,  21, 211,  47,  80, 242, 154,  27, 205, 128, 161,  89,  77,  36 ,
    95, 110,  85,  48, 212, 140, 211, 249,  22,  79, 200,  50,  28, 188 ,
    52, 140, 202, 120,  68, 145,  62,  70, 184, 190,  91, 197, 152, 224 ,
    149, 104,  25, 178, 252, 182, 202, 182, 141, 197,   4,  81, 181, 242 ,
    145,  42,  39, 227, 156, 198, 225, 193, 219,  93, 122, 175, 249,   0 ,
    175, 143,  70, 239,  46, 246, 163,  53, 163, 109, 168, 135,   2, 235 ,
    25,  92,  20, 145, 138,  77,  69, 166,  78, 176, 173, 212, 166, 113 ,
    94, 161,  41,  50, 239,  49, 111, 164,  70,  60,   2,  37, 171,  75 ,
    136, 156,  11,  56,  42, 146, 138, 229,  73, 146,  77,  61,  98, 196 ,
    135, 106,  63, 197, 195,  86,  96, 203, 113, 101, 170, 247, 181, 113 ,
    80, 250, 108,   7, 255, 237, 129, 226,  79, 107, 112, 166, 103, 241 ,
    24, 223, 239, 120, 198,  58,  60,  82, 128,   3, 184,  66, 143, 224 ,
    145, 224,  81, 206, 163,  45,  63,  90, 168, 114,  59,  33, 159,  95 ,
    28, 139, 123,  98, 125, 196,  15,  70, 194, 253,  54,  14, 109, 226 ,
    71,  17, 161,  93, 186,  87, 244, 138,  20,  52, 123, 251,  26,  36 ,
    17,  46,  52, 231, 232,  76,  31, 221,  84,  37, 216, 165, 212, 106 ,
    197, 242,  98,  43,  39, 175, 254, 145, 190,  84, 118, 222, 187, 136 ,
    120, 163, 236, 249]

set_option maxRecDepth 2048 in
theorem randomTable_size : randomTable.size = 256 := by decide

/-- Every byte index is in bounds; no panic/default branch is needed. -/
def randomAt (index : UInt8) : Nat :=
  randomTable[index.toNat]'(by rw [randomTable_size]; exact index.toNat_lt)


/-- P_Random and M_Random have independent, wrapping byte indices. -/
structure DoomRandom where
  play : UInt8 := 0
  misc : UInt8 := 0
  deriving BEq, DecidableEq, Repr, Inhabited

namespace DoomRandom

def nextPlay (r : DoomRandom) : Nat × DoomRandom :=
  let index := r.play + 1
  (randomAt index, { r with play := index })

def nextMisc (r : DoomRandom) : Nat × DoomRandom :=
  let index := r.misc + 1
  (randomAt index, { r with misc := index })

/-- P_SubRandom sequences the first draw before the second explicitly. -/
def subPlay (r : DoomRandom) : Int × DoomRandom :=
  let (first, r) := r.nextPlay
  let (second, r) := r.nextPlay
  (Int.ofNat first - Int.ofNat second, r)

def clear (_ : DoomRandom) : DoomRandom := {}

/-- A presentation draw cannot advance the gameplay stream. -/
theorem nextMisc_preserves_play (r : DoomRandom) :
    r.nextMisc.2.play = r.play := rfl

/-- A gameplay draw cannot advance the presentation stream. -/
theorem nextPlay_preserves_misc (r : DoomRandom) :
    r.nextPlay.2.misc = r.misc := rfl

/-- Presentation draws cannot affect the next gameplay value or gameplay index. -/
theorem nextPlay_after_nextMisc (r : DoomRandom) :
    r.nextMisc.2.nextPlay.1 = r.nextPlay.1 ∧
    r.nextMisc.2.nextPlay.2.play = r.nextPlay.2.play := ⟨rfl, rfl⟩

end DoomRandom
end Doom
