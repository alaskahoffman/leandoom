import Doom.Proofs.E1M1AimActorController
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.E1M1AimControllerInputs
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1CellWalkInvariant (Context Cell)
open E1M1AimControllerEntry (entry writes frame)
attribute [local irreducible] load32 store32

/-- Original memory with the explicit first-call register layout. This view
executes no memory writes and assumes no reached query state. -/
def layout (s : X86Memory.State) (angle : Angle) : X86Memory.State :=
  put (put (put (put (put s 4 (s.regs 4-20)) 6 (s.regs 0))
    1 angle.raw.toBitVec) 3 0x04000000) 2 angle.raw.toBitVec

/-- The actual prologue realizes this register layout under the existing angle guard. -/
theorem registers (s : X86Memory.State) (f : Option Flags) (angle : Angle)
    (value : load32 s.memory (s.regs 0+32)=angle.raw.toBitVec)
    (safe : ∀ b∈OriginalBulletSlope.saveWrites s, Apart (s.regs 0+32) b) :
    (entry s f).core.regs=(layout s angle).regs := by
  funext r
  by_cases h4 : r=4 <;> simp [h4,entry,OriginalBulletSlope.firstCall,OriginalBulletSlope.saved,X86Routine.pushWord,
    put,write,layout,OriginalBulletSlope.initial_angle s angle value safe,BitVec.sub_sub]

/-- Only finite input reads must avoid the five real prologue stores. -/
def SafeReads (s : X86Memory.State) (addresses : List Word) : Prop :=
  ∀ a∈addresses, ∀ b∈writes s, Apart a b

theorem kept (s : X86Memory.State) (f : Option Flags) (angle : Angle)
    (addresses : List Word) (safe : SafeReads s addresses) :
    ∀ a∈addresses, load32 (entry s f).core.memory a=load32 (layout s angle).memory a := by
  intro a member
  exact frame s f a (safe a member)

/-- Blockmap globals and 16-bit map words now come from original entry memory. -/
theorem map (s : X86Memory.State) (f : Option Flags) (angle : Angle)
    (base lines : Word) (words : Array Nat) (width height : Nat)
    (regs : (entry s f).core.regs=(layout s angle).regs)
    (before : E1M1PathMapQuery.MapInputs (layout s angle) base lines words width height)
    (safe : SafeReads s (E1M1AimRetryData.mapReads base words)) :
    E1M1PathMapQuery.MapInputs (entry s f).core base lines words width height := by
  exact E1M1AimRetryData.map _ _ base lines words width height
    (congrFun regs 4) before (kept s f angle _ safe)

/-- Cell line encodings, actor bounds and linked-list heads survive the prologue. -/
theorem payload (q : Context) (c : Cell) (s : X86Memory.State) (f : Option Flags) (angle : Angle)
    (regs : (entry s f).core.regs=(layout s angle).regs)
    (before : E1M1QueryImages.Payload s.memory q c ∧ E1M1AimPreRayMemory.PayloadSafe (layout s angle) q c)
    (safe : SafeReads s (E1M1AimRetryData.cellReads q c)) :
    E1M1QueryImages.Payload (entry s f).core.memory q c ∧ E1M1AimPreRayMemory.PayloadSafe (entry s f).core q c := by
  exact ⟨E1M1AimRetryData.payload s.memory _ q c before.1 (kept s f angle _ safe),
    E1M1AimRetryData.payload_safe _ _ q c (congrFun regs 4) before.2⟩

/-- Aiming catalogs use original actor and opening values; setup-created globals
are still created by setup rather than required to survive it. -/
theorem catalog (q : Context) (s : X86Memory.State) (f : Option Flags) (angle : Angle)
    (scene : Scene) (shooter : Nat) (hits : Array Intercept)
    (portals : Nat → Option E1M1AimCatalog.Portal) (walls : Nat → Prop) (who : Word)
    (regs : (entry s f).core.regs=(layout s angle).regs)
    (before : E1M1AimPreRayCatalog.Initial q (layout s angle) scene shooter hits portals walls who)
    (safe : SafeReads s (E1M1AimRetryCatalog.reads hits (E1M1ThingFinish.resolve q.lines q.objects) portals)) :
    E1M1AimPreRayCatalog.Initial q (entry s f).core scene shooter hits portals walls who := by
  exact E1M1AimRetryCatalog.initial q _ _ scene shooter hits portals walls who
    (congrFun regs 4) (congrFun regs 0) before (kept s f angle _ safe)
end Doom.Proofs.E1M1AimControllerInputs
