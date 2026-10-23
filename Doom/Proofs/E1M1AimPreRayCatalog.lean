import Doom.Proofs.E1M1AimPreRayMemory
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimPreRayCatalog
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1CellWalkInvariant (Context)
open E1M1AimCatalog (Portal)
open E1M1AimQueryCatalog (view)
open E1M1AimPreRayMemory (Read Later)
open E1M1PathMapQuery (traversal)
open E1M1ThingFinish (resolve)
open E1M1AimQueryCaller (callerSlots)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- Initial memory catalogs plus address-only guards. The shooter global is
not assumed initially: setup writes it from EAX. Actor entries and pointer/ID
correspondence are still explicit initial representation obligations. -/
structure Initial (q : Context) (s : X86Memory.State) (scene : Scene) (shooter : Nat)
    (hits : Array Intercept) (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word) : Prop where
  layout : E1M1AimCycleInvariant.Layout (view q s) hits
  query : ∀ a∈[(0x2b9b8#32),0x2b9a8], E1M1AimMapFrame.StableWord (view q s) a
  clip : E1M1AimNextLine.ClipGlobalsSafe (view q s)
  portalReads : E1M1AimEntryCatalog.PortalReads hits (resolve q.lines q.objects) portals (Read q s)
  portals : E1M1AimCatalog.Catalog (view q s) hits (resolve q.lines q.objects) portals
  valueReads : ∀ a∈[(0x2b9b8#32),0x2b9a8], Later q s a
  actorReads : ∀ i<hits.size, hits[i]!.isLine=false →
    ∀ a∈[resolve q.lines q.objects hits[i]!+104,resolve q.lines q.objects hits[i]!+20,
      resolve q.lines q.objects hits[i]!+68], Read q s a
  shooterReg : s.regs 0=who
  shooterSafe : E1M1AimMapFrame.StableWord (view q s) 0x2b9ac
  shooterLater : Later q s 0x2b9ac
  saveSafe : E1M1AimActorReturn.Safe (view q s)
  actors : ∀ i<hits.size, hits[i]!.isLine=false →
    hits[i]!.id<scene.things.size ∧ (resolve q.lines q.objects hits[i]! = who ↔ hits[i]!.id=shooter) ∧
    E1M1AimActorCatalog.Entry (view q s) (resolve q.lines q.objects hits[i]!) scene.things[hits[i]!.id]!
  wallReads : E1M1AimEntryCatalog.WallReads hits (resolve q.lines q.objects) walls (Read q s)
  walls : E1M1AimWallCatalog.Catalog (view q s) hits (resolve q.lines q.objects) walls
  targetSafe : E1M1AimMapFrame.StableWord (view q s) 0x2b9f8
  savedSafe : ∀ a∈E1M1AimSavedCaller.words (q.sp-136), E1M1AimSavedWords.Protect (view q s) a
  globalReads : ∀ a∈[(0x2c1e4#32),0x2c1e8,0x2b9f8], Later q s a
  callerReads : ∀ off∈callerSlots, Later q s ((q.sp-136)+off)

/-- Setup obtains the shooter word from the original EAX. Requiring its old
memory value to be preserved would be incorrect because this word is written. -/
theorem shooter (s : X86Memory.State) (thing : SolidThing) (angle : Angle) (distance ox oy : Fixed)
    (geometry : E1M1AimGeometry.Inputs s thing angle distance ox oy) :
    load32 (traversal s).core.memory 0x2b9ac=s.regs 0 := by
  have input := E1M1AimGeometry.setup_inputs s thing angle distance ox oy geometry
  exact (OriginalAimSetup.stored_shooter _ input.separated).trans (E1M1AimGeometry.ray_registers s).1

/-- Reuse the catalog image proofs with an initial-memory view at the callback
stack address. All bytes/halfwords/words come from the same setup frame. -/
theorem remaining (q : Context) (s : X86Memory.State) (scene : Scene) (shooterId : Nat)
    (thing : SolidThing) (angle : Angle) (distance : Fixed) (hits : Array Intercept)
    (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (geometry : E1M1AimGeometry.Inputs s thing angle distance
      (Fixed.ofInt q.world.grid.origin.x) (Fixed.ofInt q.world.grid.origin.y))
    (h : Initial q s scene shooterId hits portals walls who) :
    E1M1AimSetupCatalog.Remaining q (traversal s).core scene shooterId hits portals walls who := by
  have stack : (view q (traversal s).core).regs 4=(view q s).regs 4 := rfl
  have kept := E1M1AimPreRayMemory.image q s
  have later (a : Word) (h : Later q s a) := E1M1AimPreRayMemory.later q s a h
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · refine ⟨E1M1AimEntryPersistent.layout _ _ hits stack h.layout,
      fun a ha => E1M1AimMapFrame.stable_word _ _ a stack (h.query a ha),
      E1M1AimNextLine.clip_globals _ _ stack h.clip,?_,?_,fun a ha => later a (h.valueReads a ha)⟩
    · intro i hi p hp a ha
      exact later a (h.portalReads i hi p hp a ha).2
    · exact E1M1AimEntryCatalog.portals _ _ hits _ portals (Read q s) kept stack h.portalReads h.portals
  · exact ⟨later _ h.shooterLater,fun i hi kind a ha => later a (h.actorReads i hi kind a ha).2⟩
  · intro i hi wall; exact later _ (h.wallReads i hi wall).2
  · refine ⟨E1M1AimMapFrame.stable_word _ _ _ stack h.shooterSafe,
      (shooter s thing angle distance _ _ geometry).trans h.shooterReg,
      E1M1AimActorStop.safe_transfer _ _ stack h.saveSafe,?_⟩
    intro i hi kind
    obtain ⟨valid,identity,entry⟩ := h.actors i hi kind
    exact ⟨valid,identity,E1M1AimEntryCatalog.actor_entry _ _ (Read q s) kept stack _ _
      (h.actorReads i hi kind) entry⟩
  · exact E1M1AimEntryCatalog.walls _ _ hits _ walls (Read q s) kept stack h.wallReads h.walls
  · exact E1M1AimMapFrame.stable_word _ _ _ stack h.targetSafe
  · intro a ha; exact E1M1AimSavedWords.transport _ _ a stack (h.savedSafe a ha)
  · intro a ha; exact later a (h.globalReads a ha)
  · intro off ho; exact later _ (h.callerReads off ho)
end Doom.Proofs.E1M1AimPreRayCatalog
