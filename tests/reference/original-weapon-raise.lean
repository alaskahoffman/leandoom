import Doom.Proofs.OriginalWeaponRaise
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary WeaponRaise
namespace WeaponRaiseChecks
def initial (sp : Word) : X86Memory.State :=
  ⟨write (write (write (fun _ => 0) 0 0x600101) 2 0x600201) 4 sp,
    store32 (store32 (store32 (store32 (fun _ => 0)
      0x60020d 0x260000) 0x600171 2) 0x12dcc 18) sp 0x2d095⟩
def height : Fixed := ⟨0x260000⟩
-- Unaligned player and psprite, with stack writes wrapping through address zero.
example : Inputs (initial 5) 2 height := by
  constructor <;> (try unfold Apart) <;> decide
example : ¬ Inputs (initial 0x60020d) 2 height := by
  intro h
  exact h.separate 0 4 (by decide) 0 0 (by decide)
example : (Weapon.raiseStep height).2=true := by decide
example : (Weapon.raiseStep ⟨0x260001⟩).2=false := by decide
example : (Weapon.raiseStep ⟨Int32.ofInt (-2147483648)⟩).2=false := by decide
example : (Weapon.raiseStep ⟨Int32.ofInt (-2147090432)⟩).2=true := by decide
example : ∃ n, n ≤ 17 ∧ X86Routine.Prefix program [] n
    ⟨initial 5,none,0x2d4d0⟩ (result (initial 5)) := execution _ _
example : (result (initial 5)).core.regs 3=18 := by
  have h : Inputs (initial 5) 2 height := by constructor <;> (try unfold Apart) <;> decide
  have post := (live_result _ _ _ h).2
  have ready : (Weapon.raiseStep height).2=true := by decide
  simpa [Weapon.ready,WeaponData.PUNCH,WeaponData.PISTOL,WeaponData.SGUN] using post.2.2.2.1
end WeaponRaiseChecks
