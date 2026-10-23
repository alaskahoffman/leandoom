import Doom.Proofs.E1M1AimMixedBoundary
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimMixedExit
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

open E1M1AimActorBoundary (Boundary)
open E1M1AimHistoryCycle (Frame)
open E1M1AimMixedPrefix (Sequence)

/-- Catalogs are needed at live callbacks, not after the stack has returned to
an exit. Additional frame-preserved data (such as walls) travels with them. -/
def Ready (s : X86Memory.State) (scene : Scene) (shooter : Nat) (initial work : Array Intercept)
    (resolve : Intercept → Word) (who : Word) (Carry : X86Memory.State → Prop) : Prop :=
  ∀ fraction j, minimum work=.ok (fraction,some j) → ¬fraction>65536 →
    Catalog s scene shooter initial resolve who ∧ Carry s

/-- Mixed traversal without an admitted-final-hit premise: preserve either the
next callback or the actual normal exit, along with the exact source suffix. -/
theorem execution (scene : Scene) (shooter : Nat) (thing : SolidThing) (path original : PathResult)
    (distance : Fixed) (resolve : Intercept → Word) (portals : Nat → Option Portal) (who : Word)
    (represented : Represents scene original.collected portals) (empty : original.visited=#[])
    (query : E1M1QuerySource.visitHits original (fun _ _ => true)=.ok path)
    (a final : Position) (count : Nat) (sequence : Sequence scene shooter portals distance thing.shootHeight a final count)
    (origin : X86Memory.State) (s : X86Control.State) (seen : List Nat) (visits : Array Intercept)
    (history : History original.collected a.work seen visits)
    (boundary : Boundary origin scene shooter thing path original distance a.work seen resolve portals a.lower a.upper a.log s)
    (bottom : load32 s.core.memory (0x2c1e4#32)=a.lower.raw.toBitVec)
    (top : load32 s.core.memory (0x2c1e8#32)=a.upper.raw.toBitVec)
    (Carry : X86Memory.State → Prop)
    (preserve : ∀ before out marked, Frame before out → out.core.regs 4=before.regs 4 →
      before.regs 3=E1M1MinimumScan.address marked → marked<128 → Carry before → Carry out.core)
    (ready : Ready s.core scene shooter original.collected a.work resolve who Carry) :
    ∃ n≤count*(157+7*original.collected.size), ∃ out finalOrigin finalSeen finalVisits,
      X86CodeMemory.Prefix FloorCaller.cm program [] n s out ∧
      History original.collected final.work finalSeen finalVisits ∧ finalSeen.length=seen.length+count ∧
      Boundary finalOrigin scene shooter thing path original distance final.work finalSeen resolve portals final.lower final.upper final.log out ∧
      load32 out.core.memory (0x2c1e4#32)=final.lower.raw.toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=final.upper.raw.toBitVec ∧
      Ready out.core scene shooter original.collected final.work resolve who Carry ∧
      remaining scene shooter thing path distance
        (List.range' seen.length (path.visited.size-seen.length)) a.lower a.upper a.log =
      remaining scene shooter thing path distance
        (List.range' finalSeen.length (path.visited.size-finalSeen.length)) final.lower final.upper final.log := by
  induction sequence generalizing origin s seen visits with
  | nil a => exact ⟨0,by omega,s,origin,seen,visits,.nil _,history,by omega,boundary,bottom,top,ready,rfl⟩
  | @cons a b final count hitFraction hitIndex hitChosen hitWithin step tail ih =>
    obtain ⟨selection,persistent,_,_⟩ := E1M1AimActorBoundary.next_callback origin scene shooter thing
      path original distance a.work seen visits resolve portals a.lower a.upper a.log s history empty query boundary
      hitFraction hitIndex hitChosen hitWithin
    obtain ⟨catalog,carried⟩ := ready hitFraction hitIndex hitChosen hitWithin
    have pc : s.pc=0x2b760 := selection.ready.pc
    have atCallback : s=⟨s.core,s.flags,0x2b760⟩ := by cases s; simp_all
    have selected : Selection original.collected a.work seen resolve 0x2b760 (origin.regs 4+4)
        ⟨s.core,s.flags,0x2b760⟩ hitFraction hitIndex := by rw [← atCallback]; exact selection
    obtain ⟨n,hn,middle,run,done,nextBoundary,low,high,frame,source⟩ := E1M1AimMixedBoundary.execution
      scene shooter thing path original distance resolve portals who represented empty query a b hitIndex step
      s.core s.flags seen visits (origin.regs 4+4) hitFraction history selected persistent bottom top catalog
    rw [← atCallback] at run
    have nextReady : Ready middle.core scene shooter original.collected b.work resolve who Carry := by
      intro fraction j chosen within
      have next := E1M1AimActorBoundary.next_callback s.core scene shooter thing path original distance
        b.work (hitIndex::seen) (visits.push a.work[hitIndex]!) resolve portals b.lower b.upper b.log middle
        done empty query nextBoundary fraction j chosen within
      have stack := E1M1AimCycleInvariant.stack s.core original.collected b.work (hitIndex::seen) resolve 0x2b760 middle fraction j next.1
      have bound : hitIndex<128 := by have := selection.inside; have := persistent.bounded; omega
      have pointer := selection.ready.pointer.trans selection.argument
      exact ⟨E1M1AimActorCatalog.preserved s.core middle hitIndex scene shooter original.collected resolve who
        frame stack pointer bound catalog,preserve s.core middle hitIndex frame stack pointer bound carried⟩
    obtain ⟨m,hm,out,finalOrigin,finalSeen,finalVisits,restRun,finalHistory,length,finalBoundary,finalLow,finalHigh,finalReady,sourceTail⟩ :=
      ih s.core middle (hitIndex::seen) (visits.push a.work[hitIndex]!) done nextBoundary low high nextReady
    have size := (E1M1SelectionHistory.image history).size
    refine ⟨n+m,?_,out,finalOrigin,finalSeen,finalVisits,E1M1PspriteStep.prefix_trans run restRun,
      finalHistory,?_,finalBoundary,finalLow,finalHigh,finalReady,?_⟩
    · rw [Nat.add_mul,Nat.one_mul]; omega
    · simp only [List.length_cons] at length; omega
    · exact source.trans (by simpa only [List.length_cons] using sourceTail)

/-- Exhaustion and range rejection after any mixed prefix agree with the source no-target result. -/
theorem completed (scene : Scene) (shooter : Nat) (thing : SolidThing) (path original : PathResult)
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
    (done : seen.length+count=original.collected.size ∨ ∃ best, minimum final.work=.ok best ∧ best.1>65536) :
    ∃ n≤count*(157+7*original.collected.size), ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n s out ∧ out.pc=0x2c887 ∧
      load32 out.core.memory (0x2c1e4#32)=final.lower.raw.toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=final.upper.raw.toBitVec ∧
      remaining scene shooter thing path distance
        (List.range' seen.length (path.visited.size-seen.length)) a.lower a.upper a.log=.ok {path:=path} := by
  have boundary := E1M1AimMixedBoundary.from_line origin scene shooter thing path original distance a seen visits
    resolve portals s history empty query aligned
  obtain ⟨n,hn,out,finalOrigin,finalSeen,finalVisits,run,finalHistory,length,finalBoundary,low,high,_,source⟩ :=
    execution scene shooter thing path original distance resolve portals who represented empty query a final count sequence
      origin s seen visits history boundary bottom top (fun _ => True) (by intros; trivial) (by intro fraction j chosen within; exact ⟨catalog,True.intro⟩)
  have finish := E1M1AimPathBridge.finished scene shooter thing path original distance final.lower final.upper final.log
    final.work finalSeen finalVisits finalHistory empty (by simpa only [length] using done) query
  have pc : out.pc=0x2c887 := by
    rcases finalBoundary with terminal|⟨fraction,j,selected,persistent,inside,hit⟩
    · exact terminal.1
    · have := finish.1; omega
  exact ⟨n,hn,out,run,pc,low,high,source.trans finish.2⟩

end Doom.Proofs.E1M1AimMixedExit
