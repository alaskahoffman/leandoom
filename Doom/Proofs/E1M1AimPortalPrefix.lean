import Doom.Proofs.E1M1AimSynchronizedCycle
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimPortalPrefix
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

structure Position where
  work : Array Intercept
  lower : Fixed
  upper : Fixed
  log : Array AutoAim.Portal

def advance (a : Position) (j : Nat) (p : Portal) (distance floorSlope ceilingSlope : Fixed) : Position :=
  ⟨consume a.work j, bottomAfter (front p) (back p) a.lower floorSlope,
    topAfter (front p) (back p) a.upper ceilingSlope,
    a.log.push (portal (front p) (back p) distance a.work[j]!)⟩

/-- A finite sequence of continuing source portal branches. It supplies only
selection and arithmetic facts, never machine states or callback conclusions.
The prefix may end before an actor, another line branch, or a traversal exit. -/
inductive Sequence (portals : Nat → Option Portal) (distance z : Fixed) :
    Position → Position → Nat → Prop
  | nil (a : Position) : Sequence portals distance z a a 0
  | cons {a final : Position} {count : Nat}
      (fraction : Int32) (j : Nat) (p : Portal) (floorSlope ceilingSlope : Fixed)
      (chosen : minimum a.work=.ok (fraction,some j)) (within : ¬fraction>65536)
      (listed : portals j=some p)
      (pass : max (front p).floor.raw (back p).floor.raw < min (front p).ceiling.raw (back p).ceiling.raw)
      (floorOk : (front p).floor≠(back p).floor →
        checkedPathDiv (⟨max (front p).floor.raw (back p).floor.raw⟩-z)
          (distance*a.work[j]!.frac)=.ok floorSlope)
      (ceilingOk : (front p).ceiling≠(back p).ceiling →
        checkedPathDiv (⟨min (front p).ceiling.raw (back p).ceiling.raw⟩-z)
          (distance*a.work[j]!.frac)=.ok ceilingSlope)
      (go : (advance a j p distance floorSlope ceilingSlope).lower.raw <
        (advance a j p distance floorSlope ceilingSlope).upper.raw)
      (tail : Sequence portals distance z (advance a j p distance floorSlope ceilingSlope) final count) :
      Sequence portals distance z a final (count+1)

/-- A selected initial callback seeds the same boundary relation returned by
subsequent cycles; no fictitious preceding execution is required. -/
theorem seed (scene : Scene) (shooter : Nat) (thing : SolidThing) (path result : PathResult)
    (distance : Fixed) (a : Position) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (portals : Nat → Option Portal)
    (s : X86Control.State) (sp : Word) (fraction : Int32) (j : Nat)
    (history : History result.collected a.work seen visits)
    (selection : Selection result.collected a.work seen resolve 0x2b760 sp s fraction j)
    (before : Persistent s.core result.collected a.work resolve portals distance thing.shootHeight)
    (empty : result.visited=#[])
    (query : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok path) :
    AlignedNext s.core scene shooter thing path result distance a.work seen resolve portals a.lower a.upper a.log s := by
  have stack : sp=s.core.regs 4+4 := by
    rw [selection.ready.stack]
    exact (BitVec.sub_add_cancel sp 4).symm
  have selected : Selection result.collected a.work seen resolve 0x2b760 (s.core.regs 4+4) s fraction j := by
    rw [← stack]; exact selection
  exact E1M1AimSynchronizedCycle.boundary s.core scene shooter thing path result distance a.work seen visits
    resolve portals a.lower a.upper a.log s history empty query (Or.inr (Or.inr ⟨fraction,j,selected,before⟩))

/-- Induction over arbitrarily many continuing portal hits, composing actual
instruction prefixes. Only the first machine boundary is supplied; every later
selection, map/layout invariant and clipped window is derived by execution. -/
theorem execution (scene : Scene) (shooter : Nat) (thing : SolidThing) (path result : PathResult)
    (distance : Fixed) (resolve : Intercept → Word) (portals : Nat → Option Portal)
    (represented : Represents scene result.collected portals) (empty : result.visited=#[])
    (query : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok path)
    (a final : Position) (count : Nat) (sequence : Sequence portals distance thing.shootHeight a final count)
    (origin : X86Memory.State) (s : X86Control.State) (seen : List Nat) (visits : Array Intercept)
    (history : History result.collected a.work seen visits)
    (aligned : AlignedNext origin scene shooter thing path result distance a.work seen resolve portals a.lower a.upper a.log s)
    (bottom : load32 s.core.memory (0x2c1e4#32)=a.lower.raw.toBitVec)
    (top : load32 s.core.memory (0x2c1e8#32)=a.upper.raw.toBitVec) :
    ∃ n≤count*(157+7*result.collected.size), ∃ out finalOrigin finalSeen finalVisits,
      X86CodeMemory.Prefix FloorCaller.cm program [] n s out ∧
      History result.collected final.work finalSeen finalVisits ∧
      finalSeen.length=seen.length+count ∧
      AlignedNext finalOrigin scene shooter thing path result distance final.work finalSeen resolve portals
        final.lower final.upper final.log out ∧
      load32 out.core.memory (0x2c1e4#32)=final.lower.raw.toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=final.upper.raw.toBitVec ∧
      remaining scene shooter thing path distance
        (List.range' seen.length (path.visited.size-seen.length)) a.lower a.upper a.log =
      remaining scene shooter thing path distance
        (List.range' finalSeen.length (path.visited.size-finalSeen.length)) final.lower final.upper final.log := by
  induction sequence generalizing origin s seen visits with
  | nil a => exact ⟨0,by omega,s,origin,seen,visits,.nil _,history,by omega,aligned,bottom,top,rfl⟩
  | @cons a final count fraction j p floorSlope ceilingSlope chosen within listed pass floorOk ceilingOk go tail ih =>
    obtain ⟨selection,persistent,_,_⟩ := E1M1AimSynchronizedCycle.next_callback origin scene shooter thing
      path result distance a.work seen visits resolve portals a.lower a.upper a.log s history empty query aligned
      fraction j chosen within
    have pc : s.pc=0x2b760 := selection.ready.pc
    have atCallback : s=⟨s.core,s.flags,0x2b760⟩ := by cases s; simp_all
    have selected : Selection result.collected a.work seen resolve 0x2b760 (origin.regs 4+4)
        ⟨s.core,s.flags,0x2b760⟩ fraction j := by rw [← atCallback]; exact selection
    obtain ⟨n,hn,middle,run,done,low,high,sourceStep,_⟩ := E1M1AimSynchronizedCycle.execution s.core s.flags
      scene shooter thing path result a.work seen visits resolve portals distance 0x2b760 (origin.regs 4+4)
      fraction j p history selected persistent represented listed empty query a.lower a.upper floorSlope ceilingSlope
      a.log bottom top pass floorOk ceilingOk
    have openWindow : (bottomAfter (front p) (back p) a.lower floorSlope).raw <
        (topAfter (front p) (back p) a.upper ceilingSlope).raw := go
    simp only [if_pos openWindow] at done sourceStep
    rw [← atCallback] at run
    obtain ⟨m,hm,out,finalOrigin,finalSeen,finalVisits,restRun,finalHistory,length,finalAligned,finalLow,finalHigh,sourceTail⟩ :=
      ih s.core middle (j::seen) (visits.push a.work[j]!) done.1 done.2 low high
    have size := (E1M1SelectionHistory.image history).size
    refine ⟨n+m,?_,out,finalOrigin,finalSeen,finalVisits,E1M1PspriteStep.prefix_trans run restRun,
      finalHistory,?_,finalAligned,finalLow,finalHigh,?_⟩
    · rw [Nat.add_mul,Nat.one_mul]
      omega
    · simp only [List.length_cons] at length
      omega
    · exact sourceStep.trans (by simpa only [List.length_cons,advance] using sourceTail)

/-- The prefix length is bounded by the original buffer's remaining distinct
records. This supplies a finite progress measure, independent of instruction fuel. -/
theorem capacity (scene : Scene) (shooter : Nat) (thing : SolidThing) (path result : PathResult)
    (distance : Fixed) (resolve : Intercept → Word) (portals : Nat → Option Portal)
    (represented : Represents scene result.collected portals) (empty : result.visited=#[])
    (query : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok path)
    (a final : Position) (count : Nat) (sequence : Sequence portals distance thing.shootHeight a final count)
    (origin : X86Memory.State) (s : X86Control.State) (seen : List Nat) (visits : Array Intercept)
    (history : History result.collected a.work seen visits)
    (aligned : AlignedNext origin scene shooter thing path result distance a.work seen resolve portals a.lower a.upper a.log s)
    (bottom : load32 s.core.memory (0x2c1e4#32)=a.lower.raw.toBitVec)
    (top : load32 s.core.memory (0x2c1e8#32)=a.upper.raw.toBitVec) :
    count≤result.collected.size-seen.length := by
  obtain ⟨_,_,_,_,_,_,_,finalHistory,length,_⟩ := execution scene shooter thing path result distance resolve portals
    represented empty query a final count sequence origin s seen visits history aligned bottom top
  have bound := E1M1TraversalBudget.capacity finalHistory
  omega

end Doom.Proofs.E1M1AimPortalPrefix
