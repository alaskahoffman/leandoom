import Doom.Proofs.E1M1AimOrderedStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimOrderedCaller
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
/-- Execute every ordered hit and the complete real aiming return. The loop
proves its own final stack pointer and saved-word image from entry conditions;
no final-memory, final-ESP or future branch-sequence premise is supplied.
Initialization/collection and reachable-state establishment remain separate. -/
theorem execution (scene : Scene) (shooter : Nat) (thing : SolidThing) (path original : PathResult)
    (distance : Fixed) (resolve : Intercept → Word) (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (represented : Represents scene original.collected portals)
    (wallMap : E1M1AimWallCatalog.Represents scene original.collected walls)
    (covered : E1M1AimLineCoverage.Coverage original.collected walls portals)
    (empty : original.visited=#[]) (query : E1M1QuerySource.visitHits original (fun _ _ => true)=.ok path)
    (available : Available scene shooter original.collected portals distance thing.shootHeight)
    (base : Word)
    (origin : X86Memory.State) (s : X86Control.State)
    (aligned : AlignedNext origin scene shooter thing path original distance original.collected [] resolve portals aimBottomSlope aimTopSlope #[] s)
    (bottom : load32 s.core.memory (0x2c1e4#32)=aimBottomSlope.raw.toBitVec)
    (top : load32 s.core.memory (0x2c1e8#32)=aimTopSlope.raw.toBitVec)
    (actors : Catalog s.core scene shooter original.collected resolve who)
    (wallCatalog : E1M1AimWallCatalog.Catalog s.core original.collected resolve walls)
    (targetSafe : StableWord s.core 0x2b9f8) (null : load32 s.core.memory (0x2b9f8#32)=0)
    (protect : ∀ addr∈E1M1AimSavedCaller.words base, E1M1AimSavedWords.Protect s.core addr)
    (shape : Shape base s)
    (nonnull : ∀ j<original.collected.size, resolve original.collected[j]!≠0)
    (first : load32 s.core.memory (base+20)=0x2cb0b)
    (second : load32 s.core.memory (base+84)=0x2bbff) :
    ∃ n≤original.collected.size*(157+7*original.collected.size)+21, ∃ out answer,
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimCompletedReturn.program [] n s out ∧
      out.core.regs 0=answer.slope.raw.toBitVec ∧
      E1M1AimSavedCaller.Restores s base out ∧
      E1M1AimSource.afterPath scene shooter thing path distance=.ok answer := by
  obtain ⟨steps,bound,finish,answer,run,exit,image,stack,source⟩ := E1M1AimOrderedStack.initial
    scene shooter thing path original distance resolve portals walls who represented wallMap covered empty query
    available (E1M1AimSavedCaller.words base) origin s aligned bottom top actors wallCatalog targetSafe null protect base shape
  obtain ⟨n,hn,all,value,restored⟩ := E1M1AimSavedCaller.execution original.collected resolve s finish base steps answer
    run exit nonnull image stack protect first second
  exact ⟨n,by omega,E1M1AimCompletedReturn.result finish,answer,all,value,restored,source⟩
end Doom.Proofs.E1M1AimOrderedCaller
