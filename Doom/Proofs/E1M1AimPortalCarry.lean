import Doom.Proofs.E1M1AimPortalPrefix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimPortalCarry
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMinimum (minimum)
open E1M1InterceptMark (consume)
open E1M1AimCatalog (Portal)
open E1M1AimTraversalInvariant (Persistent)
open E1M1AimSourceCatalog (Represents front back)
open E1M1AimIteration
open E1M1AimSynchronizedCycle (AlignedNext)
open E1M1AimRepeatProgram (program)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

open E1M1AimPortalPrefix (Position advance Sequence)

/-- An admitted final selection ensures that a continuing prefix starts at an
admitted selection too. This rules out terminal boundaries during transport. -/
theorem next_choice {portals : Nat → Option Portal} {distance z : Fixed}
    {a final : Position} {count : Nat} (sequence : Sequence portals distance z a final count)
    (fraction : Int32) (j : Nat) (chosen : minimum final.work=.ok (fraction,some j))
    (within : ¬fraction>65536) :
    ∃ first index, minimum a.work=.ok (first,some index) ∧ ¬first>65536 := by
  cases sequence with
  | nil => exact ⟨fraction,j,chosen,within⟩
  | cons first index _ _ _ selected admitted => exact ⟨first,index,selected,admitted⟩

/-- Carry an additional frame-preserved property through an entire prefix to an
admitted next callback. This reuses the synchronized step, and derives all later
selections and properties rather than requesting them as assumptions. -/
theorem execution (scene : Scene) (shooter : Nat) (thing : SolidThing) (path result : PathResult)
    (distance : Fixed) (resolve : Intercept → Word) (portals : Nat → Option Portal)
    (represented : Represents scene result.collected portals) (empty : result.visited=#[])
    (query : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok path)
    (a final : Position) (count : Nat) (sequence : Sequence portals distance thing.shootHeight a final count)
    (origin : X86Memory.State) (s : X86Control.State) (seen : List Nat) (visits : Array Intercept)
    (history : History result.collected a.work seen visits)
    (aligned : AlignedNext origin scene shooter thing path result distance a.work seen resolve portals a.lower a.upper a.log s)
    (bottom : load32 s.core.memory (0x2c1e4#32)=a.lower.raw.toBitVec)
    (top : load32 s.core.memory (0x2c1e8#32)=a.upper.raw.toBitVec)
    (Carry : X86Memory.State → Prop)
    (preserve : ∀ before out marked, E1M1AimHistoryCycle.Frame before out →
      out.core.regs 4=before.regs 4 → before.regs 3=E1M1MinimumScan.address marked →
      marked<128 → Carry before → Carry out.core)
    (carried : Carry s.core)
    (fraction : Int32) (j : Nat) (chosen : minimum final.work=.ok (fraction,some j))
    (within : ¬fraction>65536) :
    ∃ n≤count*(157+7*result.collected.size), ∃ out finalOrigin finalSeen finalVisits,
      X86CodeMemory.Prefix FloorCaller.cm program [] n s out ∧
      History result.collected final.work finalSeen finalVisits ∧
      finalSeen.length=seen.length+count ∧
      AlignedNext finalOrigin scene shooter thing path result distance final.work finalSeen resolve portals
        final.lower final.upper final.log out ∧
      load32 out.core.memory (0x2c1e4#32)=final.lower.raw.toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=final.upper.raw.toBitVec ∧
      Carry out.core ∧
      Selection result.collected final.work finalSeen resolve 0x2b760 (finalOrigin.regs 4+4) out fraction j ∧
      Persistent out.core result.collected final.work resolve portals distance thing.shootHeight ∧
      remaining scene shooter thing path distance
        (List.range' seen.length (path.visited.size-seen.length)) a.lower a.upper a.log =
      remaining scene shooter thing path distance
        (List.range' finalSeen.length (path.visited.size-finalSeen.length)) final.lower final.upper final.log := by
  induction sequence generalizing origin s seen visits with
  | nil a =>
    have selected := E1M1AimSynchronizedCycle.next_callback origin scene shooter thing path result distance
      a.work seen visits resolve portals a.lower a.upper a.log s history empty query aligned fraction j chosen within
    exact ⟨0,by omega,s,origin,seen,visits,.nil _,history,by omega,aligned,bottom,top,carried,selected.1,selected.2.1,rfl⟩
  | @cons a final count hitFraction hitIndex p floorSlope ceilingSlope hitChosen hitWithin listed pass floorOk ceilingOk go tail ih =>
    obtain ⟨selection,persistent,_,_⟩ := E1M1AimSynchronizedCycle.next_callback origin scene shooter thing
      path result distance a.work seen visits resolve portals a.lower a.upper a.log s history empty query aligned
      hitFraction hitIndex hitChosen hitWithin
    have pc : s.pc=0x2b760 := selection.ready.pc
    have atCallback : s=⟨s.core,s.flags,0x2b760⟩ := by cases s; simp_all
    have selected : Selection result.collected a.work seen resolve 0x2b760 (origin.regs 4+4)
        ⟨s.core,s.flags,0x2b760⟩ hitFraction hitIndex := by rw [← atCallback]; exact selection
    obtain ⟨n,hn,middle,run,done,low,high,sourceStep,frame⟩ := E1M1AimSynchronizedCycle.execution s.core s.flags
      scene shooter thing path result a.work seen visits resolve portals distance 0x2b760 (origin.regs 4+4)
      hitFraction hitIndex p history selected persistent represented listed empty query a.lower a.upper floorSlope ceilingSlope
      a.log bottom top pass floorOk ceilingOk
    have openWindow : (bottomAfter (front p) (back p) a.lower floorSlope).raw <
        (topAfter (front p) (back p) a.upper ceilingSlope).raw := go
    simp only [if_pos openWindow] at done sourceStep
    rw [← atCallback] at run
    obtain ⟨nextFraction,nextIndex,nextChosen,nextWithin⟩ := next_choice tail fraction j chosen within
    have next := E1M1AimSynchronizedCycle.next_callback s.core scene shooter thing path result distance
      (advance a hitIndex p distance floorSlope ceilingSlope).work (hitIndex::seen) (visits.push a.work[hitIndex]!) resolve portals
      (advance a hitIndex p distance floorSlope ceilingSlope).lower (advance a hitIndex p distance floorSlope ceilingSlope).upper
      (advance a hitIndex p distance floorSlope ceilingSlope).log middle done.1 empty query done.2 nextFraction nextIndex nextChosen nextWithin
    have stack := E1M1AimCycleInvariant.stack s.core result.collected _ (hitIndex::seen) resolve 0x2b760 middle nextFraction nextIndex next.1
    have bound : hitIndex<128 := by have := selection.inside; have := persistent.bounded; omega
    have carryNext := preserve s.core middle hitIndex frame stack (selection.ready.pointer.trans selection.argument) bound carried
    obtain ⟨m,hm,out,finalOrigin,finalSeen,finalVisits,restRun,finalHistory,length,finalAligned,finalLow,finalHigh,finalCarry,finalSelection,finalPersistent,sourceTail⟩ :=
      ih s.core middle (hitIndex::seen) (visits.push a.work[hitIndex]!) done.1 done.2 low high carryNext chosen
    have size := (E1M1SelectionHistory.image history).size
    refine ⟨n+m,?_,out,finalOrigin,finalSeen,finalVisits,E1M1PspriteStep.prefix_trans run restRun,
      finalHistory,?_,finalAligned,finalLow,finalHigh,finalCarry,finalSelection,finalPersistent,?_⟩
    · rw [Nat.add_mul,Nat.one_mul]
      omega
    · simp only [List.length_cons] at length
      omega
    · exact sourceStep.trans (by simpa only [List.length_cons,advance] using sourceTail)

end Doom.Proofs.E1M1AimPortalCarry
