import Doom.Proofs.E1M1WeaponRejection
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Doom.Verification.WeaponRejectionFixture
open Doom Doom.Proofs X86 X86Memory X86Control BlockSummary

def p : Word := 0x600101
def tables (a : Word) : BitVec 8 :=
  if (0x15a7c≤a.toNat ∧ a.toNat<0x15a98) ∨ (0x15b5c≤a.toNat ∧ a.toNat<0x15b78) ∨
      (0x15c3c≤a.toNat ∧ a.toNat<0x15c58) then E1M1WeaponRejection.stateMemory a
  else E1M1WeaponFire.tableMemory a
/-- A live player, unaligned structure, and a stack crossing address zero. -/
def initial (i : Nat) : X86Memory.State :=
  ⟨fun r => if r=0 then p else if r=4 then 1 else BitVec.ofNat 32 (10+r.val),
    ([(p+4,0),(p+32,100),(p+112,if i=0 then 1 else 2),(p+116,10),(p+128,1),
      (p+160,if i=0 then 2 else 0),(p+156,if i=1 then 7 else 0),
      (p+256,0x200000),(1,0x2d38d)] : List (Word × Word)).foldl
        (fun m pair => store32 m pair.1 pair.2) tables⟩
def lower (i : Nat) := E1M1WeaponRejection.fallback (initial i)
def callback (i : Nat) := E1M1WeaponRejection.lowerCall (lower i).core
def afterLower (i : Nat) := E1M1WeaponRejection.lowerReturn (lower i).core
def setterReturn (i : Nat) :=
  let r := E1M1PspriteSetter.resumed (afterLower i).core
  PspriteSetter.returned r.core r.flags

theorem empty (i : Fin 3) : ¬E1M1WeaponFire.Enough (initial i.val) := by
  have cases : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases cases with rfl | rfl | rfl <;> decide
theorem inventory (i : Fin 3) : WeaponFallback.Inventory (E1M1WeaponFire.afterCheck (initial i.val)).core := by
  have cases : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases cases with rfl | rfl | rfl <;> (constructor <;> decide)
theorem lower_inputs (i : Fin 3) : E1M1WeaponRejection.LowerReturns (lower i.val).core (setterReturn i.val) := by
  have cases : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases cases with rfl | rfl | rfl <;>
    (refine ⟨by decide,by decide,by decide,?_⟩;
     simp only [E1M1WeaponReady.finishSetter];
     rw [if_pos (by rfl),if_pos (by decide)]; rfl)
theorem setter_pc (i : Fin 3) : (setterReturn i.val).pc=0x2d2aa := by
  have cases : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases cases with rfl | rfl | rfl <;> decide
theorem ammo_pc (i : Fin 3) : (WeaponFallback.returned (setterReturn i.val).core).pc=0x2d41a := by
  have cases : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases cases with rfl | rfl | rfl <;> decide

theorem whole_rejection (i : Fin 3) : ∃ n, n≤122 ∧
    X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponRejection.program [] n ⟨initial i.val,none,0x2d410⟩
      (E1M1WeaponRejection.rejected (setterReturn i.val)) :=
  E1M1WeaponRejection.rejected_execution _ _ _ (empty i) (inventory i) (lower_inputs i) (setter_pc i) (ammo_pc i)

def final (i : Nat) := E1M1WeaponRejection.rejected (setterReturn i)
example : (final 0).pc=0x2d38d ∧ (final 0).core.regs 4=5 ∧ (final 0).core.regs 0=0 ∧
    load32 (final 0).core.memory (p+116)=2 ∧ load32 (final 1).core.memory (p+116)=1 ∧
    load32 (final 2).core.memory (p+116)=0 ∧ load32 (final 0).core.memory (p+256)=0x260000 ∧
    load32 (final 0).core.memory (p+248)=1 := by decide
example : load32 (callback 0).core.memory (p+4)=0 := by decide

/-- The boundary is the height after addition, with signed wrap semantics. -/
def heightState (y : Word) : X86Memory.State :=
  ⟨fun r => if r=2 then p+244 else if r=4 then 1 else 0,
    store32 (store32 (fun _ => 0) (p+256) y) 1 0x2d095⟩
example : WeaponLower.below (heightState 0x79ffff) := by decide
example : ¬WeaponLower.below (heightState 0x7a0000) := by decide
example : WeaponLower.below (heightState 0x7fffffff) := by decide
example : ¬WeaponLower.below (heightState 0x799999 |>
    fun s => {s with regs := write (write s.regs 4 (p+260)) 3 0x7a0000}) := by decide
end Doom.Verification.WeaponRejectionFixture
