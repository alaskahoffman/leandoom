import Doom.Proofs.E1M1AimMixedStep
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimMixedPrefix
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMinimum (minimum)
open E1M1AimCatalog (Portal)
open E1M1AimTraversalInvariant (Persistent)
open E1M1AimSourceCatalog (Represents)
open E1M1AimActorCatalog (Catalog)
open E1M1AimIteration
open E1M1AimSynchronizedCycle (AlignedNext)
open E1M1AimPortalPrefix (Position)
open E1M1AimActorSelect (program)
open E1M1AimMixedStep (Step)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- An arbitrary interleaving of continuing portal and actor hits, selected by
Doom's minimum scan. All premises describe source data, never machine outputs. -/
inductive Sequence (scene : Scene) (shooter : Nat) (portals : Nat → Option Portal) (distance z : Fixed) :
    Position → Position → Nat → Prop
  | nil (a : Position) : Sequence scene shooter portals distance z a a 0
  | cons {a b final : Position} {count : Nat} (fraction : Int32) (j : Nat)
      (chosen : minimum a.work=.ok (fraction,some j)) (within : ¬fraction>65536)
      (step : Step scene shooter portals distance z a j b)
      (tail : Sequence scene shooter portals distance z b final count) :
      Sequence scene shooter portals distance z a final (count+1)

theorem next_choice {scene : Scene} {shooter : Nat} {portals : Nat → Option Portal} {distance z : Fixed}
    {a final : Position} {count : Nat} (sequence : Sequence scene shooter portals distance z a final count)
    (fraction : Int32) (j : Nat) (chosen : minimum final.work=.ok (fraction,some j)) (within : ¬fraction>65536) :
    ∃ first index, minimum a.work=.ok (first,some index) ∧ ¬first>65536 := by
  cases sequence with
  | nil => exact ⟨fraction,j,chosen,within⟩
  | cons first index selected admitted => exact ⟨first,index,selected,admitted⟩

/-- Compose actual instruction prefixes for any continuing mixed sequence that
ends at an admitted callback. Both catalogs, source position and window/log are
carried from the initial boundary; intermediate machine states are constructed. -/
theorem execution (scene : Scene) (shooter : Nat) (thing : SolidThing) (path original : PathResult)
    (distance : Fixed) (resolve : Intercept → Word) (portals : Nat → Option Portal) (who : Word)
    (represented : Represents scene original.collected portals) (empty : original.visited=#[])
    (query : E1M1QuerySource.visitHits original (fun _ _ => true)=.ok path)
    (a final : Position) (count : Nat) (sequence : Sequence scene shooter portals distance thing.shootHeight a final count)
    (origin : X86Memory.State) (s : X86Control.State) (seen : List Nat) (visits : Array Intercept)
    (history : History original.collected a.work seen visits)
    (aligned : AlignedNext origin scene shooter thing path original distance a.work seen resolve portals a.lower a.upper a.log s)
    (bottom : load32 s.core.memory (0x2c1e4#32)=a.lower.raw.toBitVec)
    (top : load32 s.core.memory (0x2c1e8#32)=a.upper.raw.toBitVec)
    (catalog : Catalog s.core scene shooter original.collected resolve who)
    (fraction : Int32) (j : Nat) (chosen : minimum final.work=.ok (fraction,some j)) (within : ¬fraction>65536) :
    ∃ n≤count*(157+7*original.collected.size), ∃ out finalOrigin finalSeen finalVisits,
      X86CodeMemory.Prefix FloorCaller.cm program [] n s out ∧
      History original.collected final.work finalSeen finalVisits ∧ finalSeen.length=seen.length+count ∧
      AlignedNext finalOrigin scene shooter thing path original distance final.work finalSeen resolve portals final.lower final.upper final.log out ∧
      load32 out.core.memory (0x2c1e4#32)=final.lower.raw.toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=final.upper.raw.toBitVec ∧
      Catalog out.core scene shooter original.collected resolve who ∧
      Selection original.collected final.work finalSeen resolve 0x2b760 (finalOrigin.regs 4+4) out fraction j ∧
      Persistent out.core original.collected final.work resolve portals distance thing.shootHeight ∧
      remaining scene shooter thing path distance
        (List.range' seen.length (path.visited.size-seen.length)) a.lower a.upper a.log =
      remaining scene shooter thing path distance
        (List.range' finalSeen.length (path.visited.size-finalSeen.length)) final.lower final.upper final.log := by
  induction sequence generalizing origin s seen visits with
  | nil a =>
    have selected := E1M1AimSynchronizedCycle.next_callback origin scene shooter thing path original distance
      a.work seen visits resolve portals a.lower a.upper a.log s history empty query aligned fraction j chosen within
    exact ⟨0,by omega,s,origin,seen,visits,.nil _,history,by omega,aligned,bottom,top,catalog,selected.1,selected.2.1,rfl⟩
  | @cons a b final count hitFraction hitIndex hitChosen hitWithin step tail ih =>
    obtain ⟨selection,persistent,_,_⟩ := E1M1AimSynchronizedCycle.next_callback origin scene shooter thing
      path original distance a.work seen visits resolve portals a.lower a.upper a.log s history empty query aligned
      hitFraction hitIndex hitChosen hitWithin
    have pc : s.pc=0x2b760 := selection.ready.pc
    have atCallback : s=⟨s.core,s.flags,0x2b760⟩ := by cases s; simp_all
    have selected : Selection original.collected a.work seen resolve 0x2b760 (origin.regs 4+4)
        ⟨s.core,s.flags,0x2b760⟩ hitFraction hitIndex := by rw [← atCallback]; exact selection
    obtain ⟨nextFraction,nextIndex,nextChosen,nextWithin⟩ := next_choice tail fraction j chosen within
    obtain ⟨n,hn,middle,run,done,nextAligned,low,high,carried,source⟩ := E1M1AimMixedStep.execution
      scene shooter thing path original distance resolve portals who represented empty query a b hitIndex step
      s.core s.flags seen visits (origin.regs 4+4) hitFraction history selected persistent bottom top catalog
      nextFraction nextIndex nextChosen nextWithin
    rw [← atCallback] at run
    obtain ⟨m,hm,out,finalOrigin,finalSeen,finalVisits,restRun,finalHistory,length,finalAligned,finalLow,finalHigh,finalCarry,finalSelection,finalPersistent,sourceTail⟩ :=
      ih s.core middle (hitIndex::seen) (visits.push a.work[hitIndex]!) done nextAligned low high carried chosen
    have size := (E1M1SelectionHistory.image history).size
    refine ⟨n+m,?_,out,finalOrigin,finalSeen,finalVisits,E1M1PspriteStep.prefix_trans run restRun,
      finalHistory,?_,finalAligned,finalLow,finalHigh,finalCarry,finalSelection,finalPersistent,?_⟩
    · rw [Nat.add_mul,Nat.one_mul]; omega
    · simp only [List.length_cons] at length; omega
    · exact source.trans (by simpa only [List.length_cons] using sourceTail)

/-- Each continuing hit consumes one distinct record, bounding mixed progress. -/
theorem capacity (scene : Scene) (shooter : Nat) (thing : SolidThing) (path original : PathResult)
    (distance : Fixed) (resolve : Intercept → Word) (portals : Nat → Option Portal) (who : Word)
    (represented : Represents scene original.collected portals) (empty : original.visited=#[])
    (query : E1M1QuerySource.visitHits original (fun _ _ => true)=.ok path)
    (a final : Position) (count : Nat) (sequence : Sequence scene shooter portals distance thing.shootHeight a final count)
    (origin : X86Memory.State) (s : X86Control.State) (seen : List Nat) (visits : Array Intercept)
    (history : History original.collected a.work seen visits)
    (aligned : AlignedNext origin scene shooter thing path original distance a.work seen resolve portals a.lower a.upper a.log s)
    (bottom : load32 s.core.memory (0x2c1e4#32)=a.lower.raw.toBitVec)
    (top : load32 s.core.memory (0x2c1e8#32)=a.upper.raw.toBitVec)
    (catalog : Catalog s.core scene shooter original.collected resolve who)
    (fraction : Int32) (j : Nat) (chosen : minimum final.work=.ok (fraction,some j)) (within : ¬fraction>65536) :
    count≤original.collected.size-seen.length := by
  obtain ⟨_,_,_,_,_,_,_,finalHistory,length,_⟩ := execution scene shooter thing path original distance resolve portals who
    represented empty query a final count sequence origin s seen visits history aligned bottom top catalog fraction j chosen within
  have bound := E1M1TraversalBudget.capacity finalHistory
  omega
end Doom.Proofs.E1M1AimMixedPrefix
