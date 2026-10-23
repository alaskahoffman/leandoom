import Doom.Proofs.E1M1AimActorPortalPrefix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimMixedStep
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMinimum (minimum)
open E1M1InterceptMark (consume)
open E1M1AimCatalog (Portal)
open E1M1AimTraversalInvariant (Persistent)
open E1M1AimSourceCatalog (Represents front back)
open E1M1AimActorCatalog (Catalog)
open E1M1AimIteration
open E1M1AimSynchronizedCycle (AlignedNext)
open E1M1AimPortalPrefix (Position advance)
open E1M1AimActorSelect (program)
open E1M1AimActorDispatch (dispatch)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

def skip (a : Position) (j : Nat) : Position :=
  ⟨consume a.work j,a.lower,a.upper,a.log⟩

/-- Continuing source branches only. No constructor assumes a machine execution
or a next-state invariant. Actors retain the source short-circuit division guards. -/
inductive Step (scene : Scene) (shooter : Nat) (portals : Nat → Option Portal) (distance z : Fixed) :
    Position → Nat → Position → Prop
  | portal (a : Position) (j : Nat) (p : Portal) (floorSlope ceilingSlope : Fixed)
      (listed : portals j=some p)
      (pass : max (front p).floor.raw (back p).floor.raw < min (front p).ceiling.raw (back p).ceiling.raw)
      (floorOk : (front p).floor≠(back p).floor →
        checkedPathDiv (⟨max (front p).floor.raw (back p).floor.raw⟩-z)
          (distance*a.work[j]!.frac)=.ok floorSlope)
      (ceilingOk : (front p).ceiling≠(back p).ceiling →
        checkedPathDiv (⟨min (front p).ceiling.raw (back p).ceiling.raw⟩-z)
          (distance*a.work[j]!.frac)=.ok ceilingSlope)
      (go : (advance a j p distance floorSlope ceilingSlope).lower.raw <
        (advance a j p distance floorSlope ceilingSlope).upper.raw) :
      Step scene shooter portals distance z a j (advance a j p distance floorSlope ceilingSlope)
  | actor (a : Position) (j : Nat) (topSlope bottomSlope : Fixed)
      (isThing : a.work[j]!.isLine=false)
      (topOk : a.work[j]!.id≠shooter → scene.things[a.work[j]!.id]!.shootable=true →
        checkedPathDiv (scene.things[a.work[j]!.id]!.z+scene.things[a.work[j]!.id]!.height-z)
          (distance*a.work[j]!.frac)=.ok topSlope)
      (bottomOk : a.work[j]!.id≠shooter → scene.things[a.work[j]!.id]!.shootable=true →
        ¬topSlope.raw<a.lower.raw → checkedPathDiv (scene.things[a.work[j]!.id]!.z-z)
          (distance*a.work[j]!.frac)=.ok bottomSlope)
      (go : dispatch scene shooter a.work[j]! a.lower a.upper topSlope bottomSlope≠.selected) :
      Step scene shooter portals distance z a j (skip a j)

/-- Either continuing kind reaches the same callback interface. The two catalogs
are transported from entry; the next admitted minimum rules out early exhaustion. -/
theorem execution (scene : Scene) (shooter : Nat) (thing : SolidThing) (path original : PathResult)
    (distance : Fixed) (resolve : Intercept → Word) (portals : Nat → Option Portal) (who : Word)
    (represented : Represents scene original.collected portals) (empty : original.visited=#[])
    (query : E1M1QuerySource.visitHits original (fun _ _ => true)=.ok path)
    (a b : Position) (j : Nat) (step : Step scene shooter portals distance thing.shootHeight a j b)
    (s : X86Memory.State) (f : Option Flags) (seen : List Nat) (visits : Array Intercept)
    (sp : Word) (fraction : Int32)
    (history : History original.collected a.work seen visits)
    (selection : Selection original.collected a.work seen resolve 0x2b760 sp ⟨s,f,0x2b760⟩ fraction j)
    (before : Persistent s original.collected a.work resolve portals distance thing.shootHeight)
    (bottom : load32 s.memory (0x2c1e4#32)=a.lower.raw.toBitVec)
    (top : load32 s.memory (0x2c1e8#32)=a.upper.raw.toBitVec)
    (catalog : Catalog s scene shooter original.collected resolve who)
    (nextFraction : Int32) (k : Nat) (chosen : minimum b.work=.ok (nextFraction,some k))
    (within : ¬nextFraction>65536) :
    ∃ n≤157+7*a.work.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ out ∧
      History original.collected b.work (j::seen) (visits.push a.work[j]!) ∧
      AlignedNext s scene shooter thing path original distance b.work (j::seen) resolve portals b.lower b.upper b.log out ∧
      load32 out.core.memory (0x2c1e4#32)=b.lower.raw.toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=b.upper.raw.toBitVec ∧
      Catalog out.core scene shooter original.collected resolve who ∧
      remaining scene shooter thing path distance
        (List.range' seen.length (path.visited.size-seen.length)) a.lower a.upper a.log =
      remaining scene shooter thing path distance
        (List.range' (seen.length+1) (path.visited.size-(seen.length+1))) b.lower b.upper b.log := by
  cases step with
  | portal p floorSlope ceilingSlope listed pass floorOk ceilingOk go =>
    obtain ⟨n,hn,out,run,done,low,high,source,frame⟩ := E1M1AimSynchronizedCycle.execution s f scene shooter thing
      path original a.work seen visits resolve portals distance 0x2b760 sp fraction j p history selection before represented
      listed empty query a.lower a.upper floorSlope ceilingSlope a.log bottom top pass floorOk ceilingOk
    have openWindow : (bottomAfter (front p) (back p) a.lower floorSlope).raw <
        (topAfter (front p) (back p) a.upper ceilingSlope).raw := go
    simp only [if_pos openWindow] at done source
    have next := E1M1AimSynchronizedCycle.next_callback s scene shooter thing path original distance
      _ (j::seen) (visits.push a.work[j]!) resolve portals _ _ _ out done.1 empty query done.2 nextFraction k chosen within
    have stack := E1M1AimCycleInvariant.stack s original.collected _ (j::seen) resolve 0x2b760 out nextFraction k next.1
    have bound : j<128 := by have := selection.inside; have := before.bounded; omega
    have carried := E1M1AimActorCatalog.preserved s out j scene shooter original.collected resolve who frame stack
      (selection.ready.pointer.trans selection.argument) bound catalog
    exact ⟨n,hn,out,run.transfer program [] E1M1AimActorReturn.contains_repeat (by simp),
      done.1,done.2,low,high,carried,source⟩
  | actor topSlope bottomSlope isThing topOk bottomOk go =>
    obtain ⟨n,hn,out,run,outcome,carry⟩ := E1M1AimActorCatalogCycle.execution s f scene shooter thing path original
      distance a.lower a.upper topSlope bottomSlope a.log a.work seen visits resolve 0x2b760 sp who fraction j history
      selection portals before empty query bottom top isThing catalog topOk bottomOk
    have continuing :
        History original.collected (skip a j).work (j::seen) (visits.push a.work[j]!) ∧
        E1M1AimActorBoundary.Boundary s scene shooter thing path original distance (skip a j).work (j::seen)
          resolve portals a.lower a.upper a.log out := by
      cases decision : dispatch scene shooter a.work[j]! a.lower a.upper topSlope bottomSlope <;>
        simp only [decision,E1M1AimActorCycle.Outcome] at outcome
      · exact ⟨outcome.2.2.1,outcome.2.2.2.1⟩
      · exact ⟨outcome.2.2.1,outcome.2.2.2.1⟩
      · exact ⟨outcome.2.2.1,outcome.2.2.2.1⟩
      · exact False.elim (go decision)
    have next := E1M1AimActorBoundary.next_callback s scene shooter thing path original distance
      _ (j::seen) (visits.push a.work[j]!) resolve portals a.lower a.upper a.log out continuing.1 empty query
      continuing.2 nextFraction k chosen within
    have aligned := E1M1AimActorBoundary.line_boundary s scene shooter thing path original distance
      _ (j::seen) (visits.push a.work[j]!) resolve portals a.lower a.upper a.log out continuing.1 empty query
      continuing.2 nextFraction k chosen within
    refine ⟨n,by omega,out,run,continuing.1,aligned,outcome.1,outcome.2.1,carry go _ _ next.1,?_⟩
    cases decision : dispatch scene shooter a.work[j]! a.lower a.upper topSlope bottomSlope <;>
      simp only [decision,E1M1AimActorCycle.Outcome] at outcome
    · exact outcome.2.2.2.2.2.1
    · exact outcome.2.2.2.2.2.1
    · exact outcome.2.2.2.2.2.1
    · exact False.elim (go decision)
end Doom.Proofs.E1M1AimMixedStep
