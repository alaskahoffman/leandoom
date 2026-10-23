import Doom.Proofs.OriginalDamageRejected
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.DeathStack
open Verification X86 X86Memory X86Control BlockSummary

/-- Provenance of the two nested caller frames. Separation is a condition on
initial addresses; the return word itself is established by the actual CALL. -/
structure Saved (s : X86Memory.State) (pc : Nat) (m : Memory)
    (outerWrites returnWrites : List Word) : Prop where
  outer : PlayerHeight.Frame (PlayerDamageEntry.saved s pc) m outerWrites
  killReturn : (∀ b, b ∈ returnWrites → Apart (s.regs 4-32) b) →
    load32 m (s.regs 4-32)=0x2a6b1

theorem Saved.then_frame (s : X86Memory.State) (pc : Nat) (m n : Memory)
    (ow rw more : List Word) (h : Saved s pc m ow rw)
    (frame : PlayerHeight.Frame m n more) : Saved s pc n (ow++more) (rw++more) := by
  constructor
  · intro a safe
    rw [frame a (fun b hb => safe b (List.mem_append_right _ hb))]
    exact h.outer a (fun b hb => safe b (List.mem_append_left _ hb))
  · intro safe
    rw [frame _ (fun b hb => safe b (List.mem_append_right _ hb))]
    exact h.killReturn (fun b hb => safe b (List.mem_append_left _ hb))

/-- Distinct word slots in a 128-byte stack window, including wraparound. -/
theorem slots_apart (sp : Word) (a b : Fin 32) (h : a≠b) :
    Apart (sp-BitVec.ofNat 32 (4*a.val)) (sp-BitVec.ofNat 32 (4*b.val)) := by
  intro i j eq
  have aa := a.isLt; have bb := b.isLt; have ii := i.isLt; have jj := j.isLt
  have h' : a.val≠b.val := fun e => h (Fin.ext e)
  rw [BitVec.sub_eq_add_neg,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.add_assoc] at eq
  have eq := (BitVec.add_right_inj sp).mp eq
  have eq' := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_add,BitVec.toNat_neg,BitVec.toNat_ofNat] at eq'
  omega
end Doom.Proofs.DeathStack
