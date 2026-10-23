import Doom.Proofs.E1M1PspriteChain
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.PspriteChainDriver
open Verification X86 X86Memory X86Control

/-- A reusable state-chain driver. An advance must be separately proved against
the original program; the driver never supplies a callback's behavior itself. -/
def chain (advance : X86Memory.State → Option X86Control.State) : Nat → X86Control.State → Option X86Control.State
  | 0,_ => none
  | fuel+1,s =>
    if s.pc=0x2d055 then some (PspriteSetter.returned (PspriteSetter.cleared s.core) s.flags)
    else if s.pc=0x2d0ac then some (PspriteSetter.returned s.core s.flags)
    else if s.pc=0x2d05e then (advance s.core).bind (chain advance fuel)
    else none

theorem execution (p : X86Routine.Program) (advance : X86Memory.State → Option X86Control.State) (cost : Nat)
    (contains : ∀ pc, PspriteSetter.program pc≠none → p pc=PspriteSetter.program pc)
    (stepSound : ∀ s f t, advance s=some t → ∃ n, n ≤ cost ∧ X86CodeMemory.Prefix FloorCaller.cm p [] n ⟨s,f,0x2d05e⟩ t)
    (fuel : Nat) (s t : X86Control.State) (ok : chain advance fuel s=some t) :
    ∃ n, n ≤ cost*fuel+4 ∧ X86CodeMemory.Prefix FloorCaller.cm p [] n s t := by
  induction fuel generalizing s with
  | zero => simp [chain] at ok
  | succ fuel ih =>
    simp only [chain] at ok
    split at ok
    · rename_i pc
      have e : s=⟨s.core,s.flags,0x2d055⟩ := by rw [←pc]
      have out := Option.some.inj ok
      rw [←out,e]
      exact ⟨4,by omega,(X86CodeMemory.lift_success (PspriteSetter.clear_execution _ _) FloorCaller.cm).transfer p [] contains (by simp)⟩
    · split at ok
      · rename_i pc
        have e : s=⟨s.core,s.flags,0x2d0ac⟩ := by rw [←pc]
        have out := Option.some.inj ok
        rw [←out,e]
        exact ⟨3,by omega,(X86CodeMemory.lift_success (PspriteSetter.return_execution _ _) FloorCaller.cm).transfer p [] contains (by simp)⟩
      · split at ok
        · rename_i pc
          cases result : advance s.core with
          | none => simp [result] at ok
          | some u =>
            simp only [result,Option.bind] at ok
            obtain ⟨n,hn,a⟩ := stepSound s.core s.flags u result
            have e : s=⟨s.core,s.flags,0x2d05e⟩ := by rw [←pc]
            rw [←e] at a
            obtain ⟨m,hm,b⟩ := ih u ok
            exact ⟨n+m,by simp only [Nat.mul_succ]; omega,E1M1PspriteStep.prefix_trans a b⟩
        · cases ok

theorem mono (advance : X86Memory.State → Option X86Control.State) (fuel extra : Nat)
    (s t : X86Control.State) (ok : chain advance fuel s=some t) : chain advance (fuel+extra) s=some t := by
  induction fuel generalizing s with
  | zero => simp [chain] at ok
  | succ fuel ih =>
    rw [Nat.succ_add]
    simp only [chain] at ok ⊢
    split at ok <;> simp_all only [↓reduceIte]
    split at ok <;> simp_all only [↓reduceIte]
    split at ok
    · rename_i pc
      rw [if_pos pc]
      cases result : advance s.core with
      | none => simp [result] at ok
      | some u =>
        simp only [result,Option.bind] at ok ⊢
        exact ih u ok
    · cases ok

end Doom.Proofs.PspriteChainDriver
