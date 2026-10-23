import Doom.Proofs.E1M1AimMixedSelected
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimMixedBoundary
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

open E1M1AimActorBoundary (Boundary)
open E1M1AimHistoryCycle (Frame)
open E1M1AimMixedStep (Step skip)

/-- Retain the actual exit PC as well as the live callback interface. -/
theorem from_line (origin : X86Memory.State) (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path original : PathResult) (distance : Fixed) (a : Position) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (portals : Nat → Option Portal) (s : X86Control.State)
    (history : History original.collected a.work seen visits) (empty : original.visited=#[])
    (query : E1M1QuerySource.visitHits original (fun _ _ => true)=.ok path)
    (aligned : AlignedNext origin scene shooter thing path original distance a.work seen resolve portals a.lower a.upper a.log s) :
    Boundary origin scene shooter thing path original distance a.work seen resolve portals a.lower a.upper a.log s := by
  rcases aligned.1 with exhausted|⟨best,chosen,far,pc,rest⟩|⟨fraction,j,selection,persistent⟩
  · have done : seen.length=original.collected.size ∨ ∃ best, minimum a.work=.ok best ∧ best.1>65536 := Or.inl exhausted.1
    have terminal := E1M1AimPortalPrefixExit.terminal origin scene shooter thing path original distance a seen visits
      resolve portals s history empty query aligned done
    have finished := E1M1AimPathBridge.finished scene shooter thing path original distance a.lower a.upper a.log
      a.work seen visits history empty done query
    exact Or.inl ⟨terminal.1,finished.1,terminal.2⟩
  · have finished := E1M1AimPathBridge.finished scene shooter thing path original distance a.lower a.upper a.log
      a.work seen visits history empty (Or.inr ⟨best,chosen,far⟩) query
    exact Or.inl ⟨pc,finished⟩
  · have hit := E1M1AimPathBridge.selected original path a.work seen visits resolve 0x2b760 (origin.regs 4+4)
      s fraction j history selection empty query
    exact Or.inr ⟨fraction,j,selection,persistent,hit.1,hit.2.1⟩

/-- Continuing source hits may end at another callback or at the normal exit.
No admitted successor is assumed. The frame remains available for transport. -/
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
    (catalog : Catalog s scene shooter original.collected resolve who) :
    ∃ n≤157+7*a.work.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ out ∧
      History original.collected b.work (j::seen) (visits.push a.work[j]!) ∧
      Boundary s scene shooter thing path original distance b.work (j::seen) resolve portals b.lower b.upper b.log out ∧
      load32 out.core.memory (0x2c1e4#32)=b.lower.raw.toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=b.upper.raw.toBitVec ∧
      Frame s out ∧
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
    have boundary := from_line s scene shooter thing path original distance
      (advance a j p distance floorSlope ceilingSlope) (j::seen) (visits.push a.work[j]!) resolve portals out done.1 empty query done.2
    exact ⟨n,hn,out,run.transfer program [] E1M1AimActorReturn.contains_repeat (by simp),
      done.1,boundary,low,high,frame,source⟩
  | actor topSlope bottomSlope isThing topOk bottomOk go =>
    obtain ⟨n,hn,out,run,outcome,carry⟩ := E1M1AimActorCatalogCycle.execution s f scene shooter thing path original
      distance a.lower a.upper topSlope bottomSlope a.log a.work seen visits resolve 0x2b760 sp who fraction j history
      selection portals before empty query bottom top isThing catalog topOk bottomOk
    cases decision : dispatch scene shooter a.work[j]! a.lower a.upper topSlope bottomSlope <;>
      simp only [decision,E1M1AimActorCycle.Outcome] at outcome
    · exact ⟨n,by omega,out,run,outcome.2.2.1,outcome.2.2.2.1,outcome.1,outcome.2.1,outcome.2.2.2.2.1,outcome.2.2.2.2.2.1⟩
    · exact ⟨n,by omega,out,run,outcome.2.2.1,outcome.2.2.2.1,outcome.1,outcome.2.1,outcome.2.2.2.2.1,outcome.2.2.2.2.2.1⟩
    · exact ⟨n,by omega,out,run,outcome.2.2.1,outcome.2.2.2.1,outcome.1,outcome.2.1,outcome.2.2.2.2.1,outcome.2.2.2.2.2.1⟩
    · exact False.elim (go decision)
end Doom.Proofs.E1M1AimMixedBoundary
