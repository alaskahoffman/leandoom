import Doom.Proofs.E1M1AimMixedBlocking
import Doom.Proofs.E1M1AimLineCycle
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimHitOutcome
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

/-- Source division facts for one admitted hit. Branch conclusions, machine
states and correspondence are not premises. Unreached divisions stay conditional. -/
structure Arithmetic (scene : Scene) (shooter : Nat) (portals : Nat → Option Portal)
    (distance z : Fixed) (a : Position) (j : Nat) where
  floorSlope : Fixed
  ceilingSlope : Fixed
  topSlope : Fixed
  bottomSlope : Fixed
  line : a.work[j]!.isLine=true → ∀ p, portals j=some p →
    max (front p).floor.raw (back p).floor.raw < min (front p).ceiling.raw (back p).ceiling.raw →
    ((front p).floor≠(back p).floor → checkedPathDiv (⟨max (front p).floor.raw (back p).floor.raw⟩-z)
      (distance*a.work[j]!.frac)=.ok floorSlope) ∧
    ((front p).ceiling≠(back p).ceiling → checkedPathDiv (⟨min (front p).ceiling.raw (back p).ceiling.raw⟩-z)
      (distance*a.work[j]!.frac)=.ok ceilingSlope)
  actorTop : a.work[j]!.isLine=false → a.work[j]!.id≠shooter → scene.things[a.work[j]!.id]!.shootable=true →
    checkedPathDiv (scene.things[a.work[j]!.id]!.z+scene.things[a.work[j]!.id]!.height-z)
      (distance*a.work[j]!.frac)=.ok topSlope
  actorBottom : a.work[j]!.isLine=false → a.work[j]!.id≠shooter → scene.things[a.work[j]!.id]!.shootable=true →
    ¬topSlope.raw<a.lower.raw → checkedPathDiv (scene.things[a.work[j]!.id]!.z-z)
      (distance*a.work[j]!.frac)=.ok bottomSlope

/-- Real traversal exit and, whenever a target exists, exact target/slope stores.
This does not assert the no-target globals were initialized or cleared. -/
def Exit (initial : Array Intercept) (resolve : Intercept → Word) (out : X86Control.State) (answer : AimResult) : Prop :=
  (out.pc=0x2c887 ∨ out.pc=0x2c88c) ∧
  (∀ id, answer.target=some id → ∃ j<initial.size, initial[j]!.id=id ∧
    load32 out.core.memory (0x2b9f8#32)=resolve initial[j]! ∧
    load32 out.core.memory (0x2b9b4#32)=answer.slope.raw.toBitVec)

def Outcome (s : X86Memory.State) (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path original : PathResult) (distance : Fixed) (a : Position) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (portals : Nat → Option Portal) (j : Nat) (out : X86Control.State) : Prop :=
  (∃ answer, Exit original.collected resolve out answer ∧
    remaining scene shooter thing path distance (List.range' seen.length (path.visited.size-seen.length)) a.lower a.upper a.log=.ok answer) ∨
  (∃ b : Position, b.work=consume a.work j ∧
    History original.collected b.work (j::seen) (visits.push a.work[j]!) ∧
    Boundary s scene shooter thing path original distance b.work (j::seen) resolve portals b.lower b.upper b.log out ∧
    load32 out.core.memory (0x2c1e4#32)=b.lower.raw.toBitVec ∧
    load32 out.core.memory (0x2c1e8#32)=b.upper.raw.toBitVec ∧ Frame s out ∧
    remaining scene shooter thing path distance (List.range' seen.length (path.visited.size-seen.length)) a.lower a.upper a.log=
    remaining scene shooter thing path distance (List.range' (seen.length+1) (path.visited.size-(seen.length+1))) b.lower b.upper b.log)

/-- Exhaustive callback dispatch derives stop/continue from line kind and source
comparisons. No branch decision or sequence is supplied by the caller. -/
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
    (arithmetic : Arithmetic scene shooter portals distance thing.shootHeight a j) :
    ∃ n≤157+7*a.work.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ out ∧
      Outcome s scene shooter thing path original distance a seen visits resolve portals j out := by
  cases kind : a.work[j]!.isLine with
  | true =>
    obtain ⟨n,hn,out,run,done⟩ := E1M1AimLineCycle.execution s f scene shooter thing path original a.work seen visits
      resolve portals walls distance 0x2b760 sp fraction j history selection before represented wallCatalog wallMap covered kind
      empty query a.lower a.upper arithmetic.floorSlope arithmetic.ceilingSlope a.log bottom top (arithmetic.line kind)
    refine ⟨n,hn,out,run.transfer program [] E1M1AimActorReturn.contains_repeat (by simp),?_⟩
    cases decision : E1M1AimLineDispatch.dispatch scene a.work[j]! distance a.lower a.upper arithmetic.floorSlope arithmetic.ceilingSlope with
    | none => simp only [decision] at done
    | some choice =>
      cases choice with
      | stop lo hi =>
        simp only [decision] at done
        exact Or.inl ⟨{path:=E1M1AimSource.stopped path (seen.length+1)},⟨Or.inr done.1,by intro id h; cases h⟩,done.2.2.2⟩
      | next lo hi entry =>
        simp only [decision] at done
        let b : Position := ⟨consume a.work j,lo,hi,a.log.push entry⟩
        have boundary := E1M1AimMixedBoundary.from_line s scene shooter thing path original distance b (j::seen)
          (visits.push a.work[j]!) resolve portals out done.1 empty query done.2.1
        exact Or.inr ⟨b,rfl,done.1,boundary,done.2.2.1,done.2.2.2.1,done.2.2.2.2.2.1,done.2.2.2.2.1⟩
  | false =>
    obtain ⟨n,hn,out,run,done,_⟩ := E1M1AimActorCatalogCycle.execution s f scene shooter thing path original distance
      a.lower a.upper arithmetic.topSlope arithmetic.bottomSlope a.log a.work seen visits resolve 0x2b760 sp who fraction j
      history selection portals before empty query bottom top kind actors (arithmetic.actorTop kind) (arithmetic.actorBottom kind)
    refine ⟨n,by omega,out,run,?_⟩
    cases decision : E1M1AimActorDispatch.dispatch scene shooter a.work[j]! a.lower a.upper arithmetic.topSlope arithmetic.bottomSlope <;>
      simp only [decision,E1M1AimActorCycle.Outcome] at done
    · exact Or.inr ⟨E1M1AimMixedStep.skip a j,rfl,done.2.2.1,done.2.2.2.1,done.1,done.2.1,done.2.2.2.2.1,done.2.2.2.2.2.1⟩
    · exact Or.inr ⟨E1M1AimMixedStep.skip a j,rfl,done.2.2.1,done.2.2.2.1,done.1,done.2.1,done.2.2.2.2.1,done.2.2.2.2.2.1⟩
    · exact Or.inr ⟨E1M1AimMixedStep.skip a j,rfl,done.2.2.1,done.2.2.2.1,done.1,done.2.1,done.2.2.2.2.1,done.2.2.2.2.2.1⟩
    · obtain ⟨lo,hi,pc,zero,stack,records,targetStore,slopeStore,source⟩ := done
      let answer := E1M1AimActorSelectEntry.answer scene thing path distance a.lower a.upper arithmetic.topSlope arithmetic.bottomSlope a.log seen.length a.work[j]!
      refine Or.inl ⟨answer,⟨Or.inr pc,?_⟩,source⟩
      intro id target
      have identity : a.work[j]!.id=id := Option.some.inj target
      exact ⟨j,selection.inside,by rw [← selection.original]; exact identity,targetStore,slopeStore⟩
end Doom.Proofs.E1M1AimHitOutcome
