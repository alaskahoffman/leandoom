import Doom.Proofs.E1M1AimEntryCatalog
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimQueryCatalog
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1CellWalkInvariant (Context)
open E1M1AimCatalog (Portal)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- Exactly the three address conditions accepted by the continuous query's
proved memory image. None refers to a future machine-memory value. -/
def Protected (q : Context) (s : X86Memory.State) (a : Word) : Prop :=
  E1M1PathMapSetup.Safe s a ∧ E1M1FiringMapState.Safe q.sp q.lines a ∧
    E1M1AimEntryFrame.SafeWord (q.sp-112) a

/-- Specification view: query-entry memory paired with the known callback stack
address. This is not a machine step, an executed state, or a register reset. -/
def view (q : Context) (s : X86Memory.State) : X86Memory.State := put s 4 (q.sp-140)

theorem image (q : Context) (s : X86Memory.State) (out : X86Control.State)
    (frame : ∀ a, E1M1PathMapSetup.Safe s a → E1M1FiringMapState.Safe q.sp q.lines a →
      E1M1AimEntryFrame.SafeWord (q.sp-112) a → load32 out.core.memory a=load32 s.memory a) :
    E1M1AimEntryCatalog.Image (view q s).memory out.core.memory (Protected q s) := by
  intro a safe
  exact frame a safe.1 safe.2.1 safe.2.2

theorem live_stack (q : Context) (s : X86Memory.State) (hits : Array Intercept)
    (resolve : Intercept → Word) (out : X86Control.State)
    (outcome : E1M1AimFirstSelection.Outcome hits resolve (q.sp-136) out)
    (live : out.pc=0x2b760) : out.core.regs 4=(view q s).regs 4 := by
  rcases outcome with empty|⟨best,chosen,far,pc⟩|⟨fraction,j,selected⟩
  · have pc := empty.2.1; omega
  · omega
  · simpa [view,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc] using selected.ready.stack

/-- Transport all three catalogs from query-entry memory at the actual live
callback. Stack-dependent guards are checked at the callback's static address;
the reached stack is derived from the proved first-scan outcome. -/
theorem catalogs (q : Context) (s : X86Memory.State) (out : X86Control.State)
    (scene : Scene) (shooter : Nat) (hits : Array Intercept) (resolve : Intercept → Word)
    (who : Word) (solid : Nat → Prop) (openings : Nat → Option Portal)
    (outcome : E1M1AimFirstSelection.Outcome hits resolve (q.sp-136) out)
    (live : out.pc=0x2b760)
    (frame : ∀ a, E1M1PathMapSetup.Safe s a → E1M1FiringMapState.Safe q.sp q.lines a →
      E1M1AimEntryFrame.SafeWord (q.sp-112) a → load32 out.core.memory a=load32 s.memory a)
    (actorReads : E1M1AimEntryCatalog.ActorReads hits resolve (Protected q s))
    (wallReads : E1M1AimEntryCatalog.WallReads hits resolve solid (Protected q s))
    (portalReads : E1M1AimEntryCatalog.PortalReads hits resolve openings (Protected q s))
    (actors : E1M1AimActorCatalog.Catalog (view q s) scene shooter hits resolve who)
    (walls : E1M1AimWallCatalog.Catalog (view q s) hits resolve solid)
    (portals : E1M1AimCatalog.Catalog (view q s) hits resolve openings) :
    E1M1AimActorCatalog.Catalog out.core scene shooter hits resolve who ∧
    E1M1AimWallCatalog.Catalog out.core hits resolve solid ∧
    E1M1AimCatalog.Catalog out.core hits resolve openings := by
  have kept := image q s out frame
  have stack := live_stack q s hits resolve out outcome live
  exact ⟨E1M1AimEntryCatalog.actors _ _ scene shooter hits resolve who _ kept stack actorReads actors,
    E1M1AimEntryCatalog.walls _ _ hits resolve solid _ kept stack wallReads walls,
    E1M1AimEntryCatalog.portals _ _ hits resolve openings _ kept stack portalReads portals⟩

/-- Initial query globals travel through the same image, including zero target
and both unmodified initial clipping bounds. This supplies values, not the
remaining persistent layout/slot invariants. -/
theorem globals (q : Context) (s : X86Memory.State) (out : X86Control.State)
    (distance z : Fixed)
    (frame : ∀ a, E1M1PathMapSetup.Safe s a → E1M1FiringMapState.Safe q.sp q.lines a →
      E1M1AimEntryFrame.SafeWord (q.sp-112) a → load32 out.core.memory a=load32 s.memory a)
    (safe : ∀ a∈[(0x2b9b8#32),0x2b9a8,0x2c1e4,0x2c1e8,0x2b9f8], Protected q s a)
    (range : load32 s.memory 0x2b9b8=distance.raw.toBitVec)
    (eye : load32 s.memory 0x2b9a8=z.raw.toBitVec)
    (bottom : load32 s.memory 0x2c1e4=aimBottomSlope.raw.toBitVec)
    (top : load32 s.memory 0x2c1e8=aimTopSlope.raw.toBitVec)
    (null : load32 s.memory 0x2b9f8=0) :
    load32 out.core.memory 0x2b9b8=distance.raw.toBitVec ∧
    load32 out.core.memory 0x2b9a8=z.raw.toBitVec ∧
    load32 out.core.memory 0x2c1e4=aimBottomSlope.raw.toBitVec ∧
    load32 out.core.memory 0x2c1e8=aimTopSlope.raw.toBitVec ∧
    load32 out.core.memory 0x2b9f8=0 := by
  have keep (a : Word) (ha : a∈[(0x2b9b8#32),0x2b9a8,0x2c1e4,0x2c1e8,0x2b9f8]) :=
    image q s out frame a (safe a ha)
  exact ⟨(keep _ (by simp)).trans range,(keep _ (by simp)).trans eye,
    (keep _ (by simp)).trans bottom,(keep _ (by simp)).trans top,(keep _ (by simp)).trans null⟩
end Doom.Proofs.E1M1AimQueryCatalog
