import Doom.Verification.X86Routine
import Doom.Proofs.BlockSummary
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.HalfMemory
open Verification X86 X86Memory BlockSummary

/-- Separation for exact byte widths, with wrapping 32-bit addresses. -/
def Separate (n k : Nat) (a b : Word) : Prop :=
  ∀ i : Fin n, ∀ j : Fin k, a+BitVec.ofNat 32 i.val≠b+BitVec.ofNat 32 j.val

theorem translate (p a b : Word) (n k : Nat) (h : Separate n k a b) :
    Separate n k (p+a) (p+b) := by
  intro i j eq
  rw [BitVec.add_assoc,BitVec.add_assoc] at eq
  exact h i j ((BitVec.add_right_inj p).mp eq)

theorem byte_frame (m : Memory) (a b : Word) (v : BitVec 16)
    (h0 : b≠a) (h1 : b≠a+1) : X86Routine.store16 m a v b=m b := by
  simp only [X86Routine.store16,if_neg h0,if_neg h1]

theorem half_frame (m : Memory) (a b : Word) (v : BitVec 16) (h : Separate 2 2 b a) :
    load16 (X86Routine.store16 m a v) b=load16 m b := by
  have h00 : b≠a := by simpa using h ⟨0,by decide⟩ ⟨0,by decide⟩
  have h01 : b≠a+1 := by simpa using h ⟨0,by decide⟩ ⟨1,by decide⟩
  have h10 : b+1≠a := by simpa using h ⟨1,by decide⟩ ⟨0,by decide⟩
  have h11 : b+1≠a+1 := by simpa using h ⟨1,by decide⟩ ⟨1,by decide⟩
  simp only [load16,byte_frame _ _ _ _ h00 h01,byte_frame _ _ _ _ h10 h11]

theorem word_frame (m : Memory) (a b : Word) (v : BitVec 16) (h : Separate 4 2 b a) :
    load32 (X86Routine.store16 m a v) b=load32 m b := by
  have keep (i : Fin 4) : X86Routine.store16 m a v (b+BitVec.ofNat 32 i.val)=m (b+BitVec.ofNat 32 i.val) := by
    apply byte_frame
    · simpa using h i ⟨0,by decide⟩
    · simpa using h i ⟨1,by decide⟩
  have k0 := keep ⟨0,by decide⟩; have k1 := keep ⟨1,by decide⟩
  have k2 := keep ⟨2,by decide⟩; have k3 := keep ⟨3,by decide⟩
  simp only [Fin.val_mk] at k0 k1 k2 k3
  simp only [BitVec.add_zero] at k0
  simp [load32,k0,k1,k2,k3]

theorem readback (m : Memory) (a : Word) (v : BitVec 16) :
    load16 (X86Routine.store16 m a v) a=v := by
  have ne : a+1≠a := by
    intro eq
    have zero : (1#32)=(0#32) := (BitVec.add_right_eq_self (x:=a) (y:=1)).mp eq
    exact (by decide : (1#32)≠(0#32)) zero
  simp only [load16,X86Routine.store16,if_pos rfl,if_neg ne,ite_true]
  exact BitVec.extractLsb'_append_extractLsb' (x:=v) (w:=8) (len:=8)

end Doom.Proofs.HalfMemory
