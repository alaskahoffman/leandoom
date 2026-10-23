import Doom.Proofs.E1M1AimRetryCollection
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimRetryCatalog
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1CellWalkInvariant (Context)
open E1M1AimCatalog (Portal)
open E1M1AimQueryCatalog (view)
open E1M1AimPreRayMemory (Read Later layout)
open E1M1ThingFinish (resolve)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- Read only the hit's flags/dimensions and any represented opening. Query
outputs and the shooter global are deliberately absent: setup rewrites them. -/
def reads (hits : Array Intercept) (lookup : Intercept → Word)
    (portals : Nat → Option Portal) : List Word :=
  (List.range hits.size).flatMap fun i =>
    (if hits[i]!.isLine then [lookup hits[i]!+16]
     else [lookup hits[i]!+104,lookup hits[i]!+20,lookup hits[i]!+68]) ++
    (match portals i with
     | none => []
     | some p => (lookup hits[i]!+16)::E1M1OpeningHeights.reads (lookup hits[i]!) p.front p.back)

theorem actor_reads (hits : Array Intercept) (lookup : Intercept → Word)
    (portals : Nat → Option Portal) (i : Nat) (hi : i<hits.size) (kind : hits[i]!.isLine=false)
    (a : Word) (member : a∈[lookup hits[i]!+104,lookup hits[i]!+20,lookup hits[i]!+68]) :
    a∈reads hits lookup portals := by
  apply List.mem_flatMap.mpr
  refine ⟨i,List.mem_range.mpr hi,List.mem_append_left _ ?_⟩
  simpa only [kind,Bool.false_eq_true,if_false] using member

theorem wall_reads (hits : Array Intercept) (lookup : Intercept → Word)
    (portals : Nat → Option Portal) (i : Nat) (hi : i<hits.size) (kind : hits[i]!.isLine=true) :
    lookup hits[i]!+16∈reads hits lookup portals := by
  apply List.mem_flatMap.mpr
  refine ⟨i,List.mem_range.mpr hi,List.mem_append_left _ ?_⟩
  simp only [kind,ite_true,List.mem_singleton]

theorem portal_reads (hits : Array Intercept) (lookup : Intercept → Word)
    (portals : Nat → Option Portal) (i : Nat) (hi : i<hits.size) (p : Portal) (listed : portals i=some p)
    (a : Word) (member : a∈(lookup hits[i]!+16)::E1M1OpeningHeights.reads (lookup hits[i]!) p.front p.back) :
    a∈reads hits lookup portals := by
  apply List.mem_flatMap.mpr
  refine ⟨i,List.mem_range.mpr hi,List.mem_append_right _ ?_⟩
  simpa only [listed] using member

/-- These guards depend on the restored stack, not mutable query outputs. -/
theorem later (q : Context) (s t : X86Memory.State) (a : Word)
    (stack : t.regs 4=s.regs 4) (h : Later q s a) : Later q t a := by
  refine ⟨?_,h.2⟩
  simpa only [E1M1PathMapSetup.Safe,OriginalPathInit.writes,layout,E1M1PathMapQuery.withStack,
    write,ite_true,stack] using h.1

theorem read (q : Context) (s t : X86Memory.State) (a : Word)
    (stack : t.regs 4=s.regs 4) (h : Read q s a) : Read q t a :=
  ⟨E1M1AimRetryData.safe s t a stack h.1,later q s t a stack h.2⟩

theorem callback (q : Context) (s t : X86Memory.State)
    (stack : t.regs 4=s.regs 4) (h : E1M1QueryCallback.CallbackSafe q (layout s)) :
    E1M1QueryCallback.CallbackSafe q (layout t) := by
  refine ⟨?_,h.walk,h.records⟩
  simpa only [E1M1PathMapSetup.Safe,OriginalPathInit.writes,layout,E1M1PathMapQuery.withStack,
    write,ite_true,stack] using h.initial

theorem saved (s t : X86Memory.State) (stack : t.regs 4=s.regs 4)
    (h : E1M1AimCallerRegisters.SavedSafe s) : E1M1AimCallerRegisters.SavedSafe t := by
  simpa only [E1M1AimCallerRegisters.SavedSafe,OriginalAimSetup.writes,E1M1PathMapQuery.withStack,
    write,ite_true,stack] using h

/-- Reconstruct all pre-ray actor/wall/portal catalogs from the old memory and
finite read image. The shooter is supplied by the actual request register;
no target, slope, clipping bound or shooter-global value is transported. -/
theorem initial (q : Context) (s t : X86Memory.State) (scene : Scene) (shooter : Nat)
    (hits : Array Intercept) (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (stack : t.regs 4=s.regs 4) (actor : t.regs 0=s.regs 0)
    (h : E1M1AimPreRayCatalog.Initial q s scene shooter hits portals walls who)
    (kept : ∀ a∈reads hits (resolve q.lines q.objects) portals, load32 t.memory a=load32 s.memory a) :
    E1M1AimPreRayCatalog.Initial q t scene shooter hits portals walls who := by
  have same : (view q t).regs 4=(view q s).regs 4 := rfl
  have image : E1M1AimEntryCatalog.Image (view q s).memory (view q t).memory
      (fun a => a∈reads hits (resolve q.lines q.objects) portals) := kept
  refine ⟨E1M1AimEntryPersistent.layout _ _ hits same h.layout,
    fun a ha => E1M1AimMapFrame.stable_word _ _ a same (h.query a ha),
    E1M1AimNextLine.clip_globals _ _ same h.clip,?_,?_,
    fun a ha => later q s t a stack (h.valueReads a ha),?_,actor.trans h.shooterReg,
    E1M1AimMapFrame.stable_word _ _ _ same h.shooterSafe,later q s t _ stack h.shooterLater,
    E1M1AimActorStop.safe_transfer _ _ same h.saveSafe,?_,?_,?_,
    E1M1AimMapFrame.stable_word _ _ _ same h.targetSafe,
    fun a ha => E1M1AimSavedWords.transport _ _ a same (h.savedSafe a ha),
    fun a ha => later q s t a stack (h.globalReads a ha),
    fun off ho => later q s t _ stack (h.callerReads off ho)⟩
  · intro i hi p hp a ha
    exact read q s t a stack (h.portalReads i hi p hp a ha)
  · exact E1M1AimEntryCatalog.portals _ _ hits _ portals _ image same
      (portal_reads hits _ portals) h.portals
  · intro i hi kind a ha
    exact read q s t a stack (h.actorReads i hi kind a ha)
  · intro i hi kind
    obtain ⟨valid,identity,entry⟩ := h.actors i hi kind
    exact ⟨valid,identity,E1M1AimEntryCatalog.actor_entry _ _ _ image same _ _
      (actor_reads hits _ portals i hi kind) entry⟩
  · intro i hi wall
    exact read q s t _ stack (h.wallReads i hi wall)
  · exact E1M1AimEntryCatalog.walls _ _ hits _ walls _ image same
      (fun i hi wall => wall_reads hits _ portals i hi (h.walls i hi wall).1) h.walls
end Doom.Proofs.E1M1AimRetryCatalog
