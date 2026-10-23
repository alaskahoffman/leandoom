import Doom.Proofs.E1M1AimReturnedTarget
import Doom.Proofs.E1M1AimActorOrdered
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimActorCaller
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMinimum (minimum)
open E1M1AimCatalog (Portal)
open E1M1AimSourceCatalog (Represents)
open E1M1AimIteration
open E1M1AimActorBoundary (Boundary)
open E1M1AimSynchronizedCycle (AlignedNext)
open E1M1AimActorCatalog (Catalog)
open E1M1AimPortalPrefix (Position)
open E1M1AimActorSelect (program)
open E1M1AimHitOutcome (Arithmetic)
open E1M1AimActorHit (Exit Outcome)
open E1M1AimOrderedLoop (Available)
open E1M1AimMapFrame (StableWord)
open E1M1AimMixedExit (Ready)
open E1M1AimStackShape (Shape)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

attribute [local irreducible] E1M1AimCompletedReturn.result E1M1AimTraversalReturn.result
/-- A selected record is an actor, not merely a record with a matching ID. -/
structure Image (initial : Array Intercept) (resolve : Intercept → Word)
    (out : X86Control.State) (answer : AimResult) : Prop where
  absent : answer.target=none → load32 out.core.memory 0x2b9f8=0
  selected : ∀ id, answer.target=some id → ∃ j<initial.size, initial[j]!.id=id ∧
    initial[j]!.isLine=false ∧ load32 out.core.memory 0x2b9f8=resolve initial[j]! ∧
    load32 out.core.memory 0x2b9b4=answer.slope.raw.toBitVec

theorem weaken (initial : Array Intercept) (resolve : Intercept → Word)
    (out : X86Control.State) (answer : AimResult) (image : Image initial resolve out answer) :
    E1M1AimReturnedTarget.Image initial resolve out answer := by
  refine ⟨image.absent,?_⟩
  intro id chosen
  obtain ⟨j,bound,identity,kind,pointer,slope⟩ := image.selected id chosen
  exact ⟨j,bound,identity,pointer,slope⟩

/-- The return chain preserves the stronger witness; it writes only the cursor. -/
theorem returned (initial : Array Intercept) (resolve : Intercept → Word)
    (s : X86Control.State) (answer : AimResult) (exit : Exit initial resolve s answer) :
    Image initial resolve (E1M1AimCompletedReturn.result s) answer := by
  have target := E1M1AimReturnedTarget.word s 0x2b9f8 (by unfold Apart; decide)
  have slope := E1M1AimReturnedTarget.word s 0x2b9b4 (by unfold Apart; decide)
  refine ⟨fun absent => target.trans (exit.2 absent).1,?_⟩
  intro id chosen
  obtain ⟨j,bound,identity,kind,pointer,value⟩ := exit.1.2 id chosen
  exact ⟨j,bound,identity,kind,target.trans pointer,slope.trans value⟩

/-- Resolve the retained actor tag to the actual DOS object pointer. Line IDs
may overlap actor IDs; neither ID disjointness nor pointer equality is assumed. -/
theorem object_pointer (initial : Array Intercept) (lines : Word) (objects : Nat → Word)
    (out : X86Control.State) (answer : AimResult)
    (image : Image initial (E1M1ThingFinish.resolve lines objects) out answer)
    (id : Nat) (chosen : answer.target=some id) :
    load32 out.core.memory 0x2b9f8=objects id ∧
    load32 out.core.memory 0x2b9b4=answer.slope.raw.toBitVec := by
  obtain ⟨j,bound,identity,kind,pointer,slope⟩ := image.selected id chosen
  refine ⟨pointer.trans ?_,slope⟩
  simp only [E1M1ThingFinish.resolve,kind,Bool.false_eq_true,if_false,identity]

/-- The actual first-scan alternatives enter the exhaustive mixed-hit loop and
real return chain. No resumed-callback alignment or fictitious origin state is
assumed. Callback catalogs and write guards are required only when the callback is actually entered; terminal queries need only return-chain cursor separation. -/
theorem execution (scene : Scene) (shooter : Nat) (thing : SolidThing) (path original : PathResult)
    (distance : Fixed) (resolve : Intercept → Word) (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (represented : Represents scene original.collected portals)
    (wallMap : E1M1AimWallCatalog.Represents scene original.collected walls)
    (covered : E1M1AimLineCoverage.Coverage original.collected walls portals)
    (empty : original.visited=#[]) (query : E1M1QuerySource.visitHits original (fun _ _ => true)=.ok path)
    (available : Available scene shooter original.collected portals distance thing.shootHeight)
    (base : Word)
    (s : X86Control.State)
    (outcome : E1M1AimFirstSelection.Outcome original.collected resolve base s)
    (persistent : s.pc=0x2b760 → E1M1AimTraversalInvariant.Persistent s.core
      original.collected original.collected resolve portals distance thing.shootHeight)
    (bottom : load32 s.core.memory (0x2c1e4#32)=aimBottomSlope.raw.toBitVec)
    (top : load32 s.core.memory (0x2c1e8#32)=aimTopSlope.raw.toBitVec)
    (actors : s.pc=0x2b760 → Catalog s.core scene shooter original.collected resolve who)
    (wallCatalog : s.pc=0x2b760 → E1M1AimWallCatalog.Catalog s.core original.collected resolve walls)
    (targetSafe : s.pc=0x2b760 → StableWord s.core 0x2b9f8) (null : load32 s.core.memory (0x2b9f8#32)=0)
    (protect : s.pc=0x2b760 → ∀ addr∈E1M1AimSavedCaller.words base, E1M1AimSavedWords.Protect s.core addr)
    (cursorSafe : E1M1AimCallerCursor.CursorSafe base)
    (shape : Shape base s)
    (nonnull : ∀ j<original.collected.size, resolve original.collected[j]!≠0)
    (first : load32 s.core.memory (base+20)=0x2cb0b)
    (second : load32 s.core.memory (base+84)=0x2bbff) :
    ∃ n≤original.collected.size*(157+7*original.collected.size)+21, ∃ out answer,
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimCompletedReturn.program [] n s out ∧
      out.core.regs 0=answer.slope.raw.toBitVec ∧
      E1M1AimSavedCaller.Restores s base out ∧
      E1M1AimSource.afterPath scene shooter thing path distance=.ok answer ∧
      Image original.collected resolve out answer ∧
      E1M1BulletAim.ProbeResult out.core answer := by
  let a : Position := ⟨original.collected,aimBottomSlope,aimTopSlope,#[]⟩
  have boundary := E1M1AimInitialBoundary.boundary scene shooter thing path original distance
    resolve portals base s outcome shape empty query persistent
  obtain ⟨steps,bound,finish,answer,run,exit,image,stack,source⟩ := E1M1AimActorOrdered.execution
    scene shooter thing path original distance resolve portals walls who represented wallMap covered empty query
    available (E1M1AimSavedCaller.words base) original.collected.size a s.core s [] #[]
    (by simp) .nil boundary bottom top
    (by
      intro fraction j chosen within
      have selected := E1M1AimActorBoundary.next_callback s.core scene shooter thing path original distance
        original.collected [] #[] resolve portals aimBottomSlope aimTopSlope #[] s .nil empty query
        boundary fraction j chosen within
      have live := selected.1.ready.pc
      exact ⟨actors live,wallCatalog live,targetSafe live,protect live⟩) null base shape
  obtain ⟨n,hn,all,value,restored⟩ := E1M1AimCallerCursor.execution original.collected resolve s finish base steps answer
    run (E1M1AimActorHit.weaken _ _ _ _ exit) nonnull image stack cursorSafe first second
  have targetImage := returned original.collected resolve finish answer exit
  refine ⟨n,by omega,E1M1AimCompletedReturn.result finish,answer,all,value,restored,?_,targetImage,
    E1M1AimReturnedTarget.probe original.collected resolve _ answer (weaken _ _ _ _ targetImage) nonnull value⟩
  rw [E1M1AimIteration.live]
  simpa only [List.length_nil,Nat.sub_zero] using source
end Doom.Proofs.E1M1AimActorCaller
