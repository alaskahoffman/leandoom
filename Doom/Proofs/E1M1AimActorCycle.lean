import Doom.Proofs.E1M1AimActorDispatch
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimActorCycle
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMark (consume)
open E1M1AimCatalog (Portal)
open E1M1AimTraversalInvariant (Persistent)
open E1M1AimWall (Safe)
open E1M1AimHistoryCycle (Frame)
open E1M1AimIteration
open E1M1AimActorSelect (program)
open E1M1AimActorDispatch (Decision dispatch)
open E1M1AimActorBoundary (Boundary)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

theorem contains_reject (pc : Nat) (h : E1M1AimActorReject.program pc≠none) :
    program pc=E1M1AimActorReject.program pc := by
  have old := E1M1AimActorBottom.contains_prior pc h
  exact (E1M1AimActorSelect.contains_prior pc (by rw [old]; exact h)).trans old

theorem contains_skip (pc : Nat) (h : E1M1AimActorSkip.program pc≠none) :
    program pc=E1M1AimActorSkip.program pc := by
  have a := E1M1AimActorTop.contains_skip pc h
  have b := E1M1AimActorReject.contains_top pc (by rw [a]; exact h)
  exact (contains_reject pc (by rw [b,a]; exact h)).trans (b.trans a)

/-- Unified actor postcondition. A continuing hit is consumed once, with the
same bounds/log and a reusable next boundary; a selected hit stops unmarked. -/
def Outcome (decision : Decision) (s : X86Memory.State)
    (scene : Scene) (shooter : Nat) (thing : SolidThing) (path original : PathResult)
    (distance lower upper topSlope bottomSlope : Fixed) (log : Array AutoAim.Portal)
    (work : Array Intercept) (seen : List Nat) (visits : Array Intercept) (j : Nat)
    (resolve : Intercept → Word) (portals : Nat → Option Portal) (out : X86Control.State) : Prop :=
  load32 out.core.memory (0x2c1e4#32)=lower.raw.toBitVec ∧
  load32 out.core.memory (0x2c1e8#32)=upper.raw.toBitVec ∧
  match decision with
  | .selected =>
    out.pc=0x2c88c ∧ out.core.regs 0=0 ∧ out.core.regs 4=s.regs 4+4 ∧
    OriginalLineFinish.Encodes out.core.memory 0x2ba20 resolve work ∧
    load32 out.core.memory (0x2b9f8#32)=resolve original.collected[j]! ∧
    load32 out.core.memory (0x2b9b4#32)=
      (E1M1AimActorSelectEntry.answer scene thing path distance lower upper topSlope bottomSlope log seen.length work[j]!).slope.raw.toBitVec ∧
    remaining scene shooter thing path distance
      (List.range' seen.length (path.visited.size-seen.length)) lower upper log =
      .ok (E1M1AimActorSelectEntry.answer scene thing path distance lower upper topSlope bottomSlope log seen.length work[j]!)
  | _ =>
    History original.collected (consume work j) (j::seen) (visits.push work[j]!) ∧
    Boundary s scene shooter thing path original distance (consume work j) (j::seen) resolve portals lower upper log out ∧
    Frame s out ∧
    remaining scene shooter thing path distance
      (List.range' seen.length (path.visited.size-seen.length)) lower upper log =
      remaining scene shooter thing path distance
        (List.range' (seen.length+1) (path.visited.size-(seen.length+1))) lower upper log ∧
    (∀ nextFraction k, Selection original.collected (consume work j) (j::seen) resolve 0x2b760
      (s.regs 4+4) out nextFraction k → E1M1AimActorReturn.Safe s → E1M1AimActorReturn.Safe out.core)

/-- Dispatch is determined by source identity, flags and strict slope comparisons.
Arithmetic premises are needed only on paths that actually execute each division. -/
theorem execution (s : X86Memory.State) (f : Option Flags)
    (scene : Scene) (shooter : Nat) (thing : SolidThing) (path original : PathResult)
    (distance lower upper topSlope bottomSlope : Fixed) (log : Array AutoAim.Portal)
    (work : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (target sp who : Word) (fraction : Int32) (j : Nat)
    (history : History original.collected work seen visits)
    (selection : Selection original.collected work seen resolve target sp ⟨s,f,0x2b760⟩ fraction j)
    (portals : Nat → Option Portal)
    (before : Persistent s original.collected work resolve portals distance thing.shootHeight)
    (empty : original.visited=#[])
    (query : E1M1QuerySource.visitHits original (fun _ _ => true)=.ok path)
    (bottom : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec)
    (top : load32 s.memory (0x2c1e8#32)=upper.raw.toBitVec)
    (isThing : (work[j]!).isLine=false)
    (shooterSafe : Safe (s.regs 4) 0x2b9ac)
    (flagsSafe : Safe (s.regs 4) (resolve original.collected[j]!+104))
    (shooterWord : load32 s.memory 0x2b9ac=who)
    (identity : resolve original.collected[j]! = who ↔ (work[j]!).id=shooter)
    (flags : (s.memory (resolve original.collected[j]!+104) &&& (4#8) != 0)=scene.things[work[j]!.id]!.shootable)
    (topSafe : E1M1AimActorTopEntry.ReadSafe s (resolve original.collected[j]!))
    (safe : E1M1AimActorBottomEntry.ReadSafe s (resolve original.collected[j]!))
    (z0 : load32 s.memory (resolve original.collected[j]!+20)=scene.things[work[j]!.id]!.z.raw.toBitVec)
    (ht : load32 s.memory (resolve original.collected[j]!+68)=scene.things[work[j]!.id]!.height.raw.toBitVec)
    (topOk : (work[j]!).id≠shooter → scene.things[work[j]!.id]!.shootable=true →
      checkedPathDiv (scene.things[work[j]!.id]!.z+scene.things[work[j]!.id]!.height-thing.shootHeight)
      (distance*(work[j]!).frac)=.ok topSlope)
    (bottomOk : (work[j]!).id≠shooter → scene.things[work[j]!.id]!.shootable=true →
      ¬topSlope.raw<lower.raw → checkedPathDiv (scene.things[work[j]!.id]!.z-thing.shootHeight)
      (distance*(work[j]!).frac)=.ok bottomSlope)
    (saveSafe : E1M1AimActorReturn.Safe s) :
    ∃ n≤115+7*work.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ out ∧
      Outcome (dispatch scene shooter work[j]! lower upper topSlope bottomSlope) s
        scene shooter thing path original distance lower upper topSlope bottomSlope log work seen visits j resolve portals out := by
  have carry (out : X86Control.State) (nextFraction : Int32) (k : Nat)
      (nextSelection : Selection original.collected (consume work j) (j::seen) resolve 0x2b760
        (s.regs 4+4) out nextFraction k) (safe : E1M1AimActorReturn.Safe s) : E1M1AimActorReturn.Safe out.core :=
    E1M1AimActorStop.safe_transfer s out.core
      (E1M1AimCycleInvariant.stack s original.collected (consume work j) (j::seen) resolve 0x2b760 out nextFraction k nextSelection) safe
  by_cases ignored : (work[j]!).id=shooter ∨ scene.things[work[j]!.id]!.shootable=false
  · obtain ⟨n,hn,out,run,advanced,next,lo,hi,frame,source⟩ := E1M1AimActorSkipCycle.execution
      s f scene shooter thing path original distance lower upper log work seen visits resolve target sp who fraction j
      history selection portals before empty query bottom top isThing shooterSafe flagsSafe shooterWord identity flags ignored
    have boundary := E1M1AimActorBoundary.skipped s scene shooter thing path original distance (consume work j) (j::seen)
      (visits.push work[j]!) resolve portals lower upper log out advanced empty query next
    refine ⟨n,by omega,out,run.transfer program [] contains_skip (by simp),?_⟩
    rw [E1M1AimActorDispatch.ignored scene shooter work[j]! lower upper topSlope bottomSlope ignored]
    exact ⟨lo,hi,advanced,boundary,frame,source,carry out⟩
  · have different : (work[j]!).id≠shooter := fun eq => ignored (Or.inl eq)
    have shootable : scene.things[work[j]!.id]!.shootable=true := by
      cases eq : scene.things[work[j]!.id]!.shootable
      · exact False.elim (ignored (Or.inr eq))
      · rfl
    have topOk := topOk different shootable
    have decision := E1M1AimActorDispatch.eligible scene shooter work[j]! lower upper topSlope bottomSlope different shootable
    by_cases below : topSlope.raw<lower.raw
    · obtain ⟨n,hn,out,run,advanced,next,lo,hi,frame,source⟩ := E1M1AimActorRejectCycle.execution
        s f scene shooter thing path original distance lower upper topSlope log work seen visits resolve target sp who fraction j
        history selection portals before empty query bottom top isThing shooterSafe flagsSafe shooterWord identity flags different
        shootable topSafe z0 ht topOk below
      have boundary := E1M1AimActorBoundary.top_rejected s scene shooter thing path original distance (consume work j) (j::seen)
        (visits.push work[j]!) resolve portals lower upper log out advanced empty query next
      refine ⟨n,by omega,out,run.transfer program [] contains_reject (by simp),?_⟩
      rw [decision,if_pos below]
      exact ⟨lo,hi,advanced,boundary,frame,source,carry out⟩
    · have bottomOk := bottomOk different shootable below
      by_cases above : upper.raw<bottomSlope.raw
      · obtain ⟨n,hn,out,run,advanced,next,lo,hi,frame,source⟩ := E1M1AimActorBottomCycle.execution
          s f scene shooter thing path original distance lower upper topSlope bottomSlope log work seen visits resolve target sp who fraction j
          history selection portals before empty query bottom top isThing shooterSafe flagsSafe shooterWord identity flags different
          shootable topSafe safe z0 ht topOk below bottomOk above
        have boundary := E1M1AimActorBoundary.bottom_rejected s scene shooter thing path original distance (consume work j) (j::seen)
          (visits.push work[j]!) resolve portals lower upper log out advanced empty query next
        refine ⟨n,hn,out,run.transfer program [] E1M1AimActorSelect.contains_prior (by simp),?_⟩
        rw [decision,if_neg below,if_pos above]
        exact ⟨lo,hi,advanced,boundary,frame,source,carry out⟩
      · obtain ⟨n,hn,out,run,pc,zero,stack,records,targetOut,slopeOut,lo,hi,source⟩ := E1M1AimActorStop.execution
          s f scene shooter thing path original distance lower upper topSlope bottomSlope log work seen visits resolve target sp who fraction j
          history selection portals before empty query bottom top isThing shooterSafe flagsSafe shooterWord identity flags different
          shootable topSafe safe z0 ht topOk below bottomOk above saveSafe
        refine ⟨n,by omega,out,run,?_⟩
        rw [decision,if_neg below,if_neg above]
        exact ⟨lo,hi,pc,zero,stack,records,targetOut,slopeOut,source⟩
end Doom.Proofs.E1M1AimActorCycle
