import Doom.Proofs.E1M1AimActorCaller
import Doom.Proofs.E1M1AimCallerFrame
import Doom.Proofs.E1M1AimTargetCaller
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimActorCallerFrame
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
open E1M1AimHitMemory (Exit Outcome)
open E1M1AimOrderedLoop (Available)
open E1M1AimMapFrame (StableWord)
open E1M1AimMixedExit (Ready)
open E1M1AimStackShape (Shape)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

attribute [local irreducible] E1M1AimCompletedReturn.result E1M1AimTraversalReturn.result
/-- Retain arbitrary protected words through every ordered-hit outcome and the
actual return chain, alongside the original target and saved-caller result. -/
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
    (second : load32 s.core.memory (base+84)=0x2bbff)
    (watched : List Word)
    (watchedSafe : s.pc=0x2b760 → ∀ addr∈watched, E1M1AimSavedWords.Protect s.core addr)
    (watchedCursor : ∀ addr∈watched, Apart addr 0x2c028) :
    ∃ n≤original.collected.size*(157+7*original.collected.size)+21, ∃ out answer,
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimCompletedReturn.program [] n s out ∧
      out.core.regs 0=answer.slope.raw.toBitVec ∧
      E1M1AimSavedCaller.Restores s base out ∧
      E1M1AimSource.afterPath scene shooter thing path distance=.ok answer ∧
      E1M1AimActorCaller.Image original.collected resolve out answer ∧
      E1M1BulletAim.ProbeResult out.core answer ∧
      (∀ addr∈watched, load32 out.core.memory addr=load32 s.core.memory addr) := by
  let a : Position := ⟨original.collected,aimBottomSlope,aimTopSlope,#[]⟩
  have boundary := E1M1AimInitialBoundary.boundary scene shooter thing path original distance
    resolve portals base s outcome shape empty query persistent
  obtain ⟨steps,bound,finish,answer,run,exit,image,stack,source⟩ := E1M1AimActorOrdered.execution
    scene shooter thing path original distance resolve portals walls who represented wallMap covered empty query
    available (E1M1AimSavedCaller.words base ++ watched) original.collected.size a s.core s [] #[]
    (by simp) .nil boundary bottom top
    (by
      intro fraction j chosen within
      have selected := E1M1AimActorBoundary.next_callback s.core scene shooter thing path original distance
        original.collected [] #[] resolve portals aimBottomSlope aimTopSlope #[] s .nil empty query
        boundary fraction j chosen within
      have live := selected.1.ready.pc
      refine ⟨actors live,wallCatalog live,targetSafe live,?_⟩
      intro addr member
      rcases List.mem_append.mp member with saved | extra
      · exact protect live addr saved
      · exact watchedSafe live addr extra) null base shape
  obtain ⟨n,hn,all,value,restored⟩ := E1M1AimCallerCursor.execution original.collected resolve s finish base steps answer
    run (E1M1AimActorHit.weaken _ _ _ _ exit) nonnull (fun addr member => image addr (List.mem_append_left _ member)) stack cursorSafe first second
  have targetImage := E1M1AimActorCaller.returned original.collected resolve finish answer exit
  refine ⟨n,by omega,E1M1AimCompletedReturn.result finish,answer,all,value,restored,?_,targetImage,
    E1M1AimReturnedTarget.probe original.collected resolve _ answer (E1M1AimActorCaller.weaken _ _ _ _ targetImage) nonnull value,?_⟩
  · rw [E1M1AimIteration.live]
    simpa only [List.length_nil,Nat.sub_zero] using source
  · intro addr member
    exact (E1M1AimReturnedTarget.word finish addr (watchedCursor addr member)).trans
      (image addr (List.mem_append_right _ member))
end Doom.Proofs.E1M1AimActorCallerFrame
