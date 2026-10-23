import Doom.Proofs.E1M1AimActorSavedCycle
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimHitSaved
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMinimum (minimum)
open E1M1InterceptMark (consume)
open E1M1AimCatalog (Portal)
open E1M1AimTraversalInvariant (Persistent)
open E1M1AimSourceCatalog (Represents front back)
open E1M1AimActorCatalog (Catalog)
open E1M1AimIteration
open E1M1AimActorBoundary (Boundary)
open E1M1AimHistoryCycle (Frame)
open E1M1AimPortalPrefix (Position)
open E1M1AimActorSelect (program)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

open E1M1AimHitOutcome (Arithmetic)
open E1M1AimMapFrame (StableWord)

open E1M1AimHitMemory (Outcome)

/-- All line and actor hits preserve protected caller words. -/
theorem execution (scene : Scene) (shooter : Nat) (thing : SolidThing) (path original : PathResult)
    (distance : Fixed) (resolve : Intercept → Word) (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (represented : Represents scene original.collected portals)
    (wallMap : E1M1AimWallCatalog.Represents scene original.collected walls)
    (covered : E1M1AimLineCoverage.Coverage original.collected walls portals)
    (empty : original.visited=#[]) (query : E1M1QuerySource.visitHits original (fun _ _ => true)=.ok path)
    (a : Position) (s : X86Memory.State) (f : Option Flags) (seen : List Nat) (visits : Array Intercept)
    (sp : Word) (fraction : Int32) (j : Nat)
    (history : History original.collected a.work seen visits)
    (selection : Selection original.collected a.work seen resolve 0x2b760 sp ⟨s,f,0x2b760⟩ fraction j)
    (before : Persistent s original.collected a.work resolve portals distance thing.shootHeight)
    (bottom : load32 s.memory (0x2c1e4#32)=a.lower.raw.toBitVec)
    (top : load32 s.memory (0x2c1e8#32)=a.upper.raw.toBitVec)
    (actors : Catalog s scene shooter original.collected resolve who)
    (wallCatalog : E1M1AimWallCatalog.Catalog s original.collected resolve walls)
    (arithmetic : Arithmetic scene shooter portals distance thing.shootHeight a j)
    (null : load32 s.memory (0x2b9f8#32)=0) (targetSafe : StableWord s 0x2b9f8) :
    ∃ n≤157+7*a.work.size, ∃ out,
      E1M1AimSavedWords.Preserved s out ∧
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ out ∧
      Outcome s scene shooter thing path original distance a seen visits resolve portals j out := by
  cases kind : a.work[j]!.isLine with
  | true =>
    obtain ⟨n,hn,out,frame,run,done⟩ := E1M1AimLineFrameCycle.execution s f scene shooter thing path original a.work seen visits
      resolve portals walls distance 0x2b760 sp fraction j history selection before represented wallCatalog wallMap covered kind
      empty query a.lower a.upper arithmetic.floorSlope arithmetic.ceilingSlope a.log bottom top (arithmetic.line kind)
    refine ⟨n,hn,out,E1M1AimSavedWords.from_cycle s out j frame
      (selection.ready.pointer.trans selection.argument) (by have := selection.inside; have := before.bounded; omega),
      run.transfer program [] E1M1AimActorReturn.contains_repeat (by simp),?_⟩
    cases decision : E1M1AimLineDispatch.dispatch scene a.work[j]! distance a.lower a.upper arithmetic.floorSlope arithmetic.ceilingSlope with
    | none => simp only [decision] at done
    | some choice =>
      cases choice with
      | stop lo hi =>
        simp only [decision] at done
        have zero := (E1M1AimMapFrame.word s out j 0x2b9f8 frame
          (selection.ready.pointer.trans selection.argument) (by have := selection.inside; have := before.bounded; omega) targetSafe).trans null
        exact Or.inl ⟨{path:=E1M1AimSource.stopped path (seen.length+1)},⟨⟨Or.inr done.1,by intro id h; cases h⟩,by intro _; exact ⟨zero,rfl⟩⟩,done.2.2.2⟩
      | next lo hi entry =>
        simp only [decision] at done
        let b : Position := ⟨consume a.work j,lo,hi,a.log.push entry⟩
        have boundary := E1M1AimMixedBoundary.from_line s scene shooter thing path original distance b (j::seen)
          (visits.push a.work[j]!) resolve portals out done.1 empty query done.2.1
        exact Or.inr ⟨b,rfl,done.1,boundary,done.2.2.1,done.2.2.2.1,done.2.2.2.2.2.1,done.2.2.2.2.1⟩
  | false =>
    obtain ⟨n,hn,out,frame,run,done⟩ := E1M1AimActorSavedCycle.execution s f scene shooter thing path original distance
      a.lower a.upper arithmetic.topSlope arithmetic.bottomSlope a.log a.work seen visits resolve 0x2b760 sp who fraction j
      history selection portals before empty query bottom top kind actors (arithmetic.actorTop kind) (arithmetic.actorBottom kind)
    refine ⟨n,by omega,out,frame,run,?_⟩
    cases decision : E1M1AimActorDispatch.dispatch scene shooter a.work[j]! a.lower a.upper arithmetic.topSlope arithmetic.bottomSlope <;>
      simp only [decision,E1M1AimActorCycle.Outcome] at done
    · exact Or.inr ⟨E1M1AimMixedStep.skip a j,rfl,done.2.2.1,done.2.2.2.1,done.1,done.2.1,done.2.2.2.2.1,done.2.2.2.2.2.1⟩
    · exact Or.inr ⟨E1M1AimMixedStep.skip a j,rfl,done.2.2.1,done.2.2.2.1,done.1,done.2.1,done.2.2.2.2.1,done.2.2.2.2.2.1⟩
    · exact Or.inr ⟨E1M1AimMixedStep.skip a j,rfl,done.2.2.1,done.2.2.2.1,done.1,done.2.1,done.2.2.2.2.1,done.2.2.2.2.2.1⟩
    · obtain ⟨lo,hi,pc,zero,stack,records,targetStore,slopeStore,source⟩ := done
      let answer := E1M1AimActorSelectEntry.answer scene thing path distance a.lower a.upper arithmetic.topSlope arithmetic.bottomSlope a.log seen.length a.work[j]!
      refine Or.inl ⟨answer,⟨⟨Or.inr pc,?_⟩,by intro h; cases h⟩,source⟩
      intro id target
      have identity : a.work[j]!.id=id := Option.some.inj target
      exact ⟨j,selection.inside,by rw [← selection.original]; exact identity,targetStore,slopeStore⟩
end Doom.Proofs.E1M1AimHitSaved
