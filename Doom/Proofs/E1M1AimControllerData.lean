import Doom.Proofs.E1M1AimControllerEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.E1M1AimControllerData
open Verification X86 X86Memory X86Control BlockSummary
open E1M1AimControllerEntry (entry writes frame)
attribute [local irreducible] load32 store32

/-- Protection of the original table image against the five prologue stores. -/
def TableSafe (s : X86Memory.State) : Prop :=
  (∀ b∈writes s, Apart 0x13584 b) ∧
  ∀ i : Fin 10240, ∀ b∈writes s, Apart (0x5a84+BitVec.ofNat 32 (i.val*4)) b

theorem tables (s : X86Memory.State) (f : Option Flags)
    (before : ThrustTables s.memory) (safe : TableSafe s) :
    ThrustTables (entry s f).core.memory := by
  exact ⟨(frame s f _ safe.1).trans before.cosinePointer,
    fun i => (frame s f _ (safe.2 i)).trans (before.entries i)⟩

/-- The same separation guard transports either future epoch, including wrap. -/
theorem fresh (s : X86Memory.State) (f : Option Flags) (lines epoch : Word) (count : Nat)
    (before : E1M1AimStampImage.Fresh s.memory lines epoch count)
    (safe : ∀ j<count, ∀ b∈writes s, Apart (OriginalLineVisits.stamp lines j) b) :
    E1M1AimStampImage.Fresh (entry s f).core.memory lines epoch count := by
  intro j bound
  rw [frame s f _ (safe j bound)]
  exact before j bound

/-- The current stamp counter also comes from original memory when protected. -/
theorem counter (s : X86Memory.State) (f : Option Flags) (epoch : Word)
    (before : load32 s.memory 0x13580=epoch)
    (safe : ∀ b∈writes s, Apart 0x13580 b) :
    load32 (entry s f).core.memory 0x13580=epoch :=
  (frame s f _ safe).trans before
end Doom.Proofs.E1M1AimControllerData
