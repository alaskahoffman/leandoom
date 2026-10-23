import Doom.Proofs.E1M1AimPortalPrefix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimPortalPrefixExit
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMinimum (minimum)
open E1M1AimCatalog (Portal)
open E1M1AimSourceCatalog (Represents front back)
open E1M1AimIteration
open E1M1AimSynchronizedCycle (AlignedNext)
open E1M1AimPortalPrefix (Position advance Sequence)
open E1M1AimRepeatProgram (program)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- The normal traversal exits retain their actual DOS PC, including the
counter-wrap exit, and agree with the source's no-target suffix result. -/
theorem terminal (origin : X86Memory.State) (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path result : PathResult) (distance : Fixed) (a : Position) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (portals : Nat → Option Portal) (s : X86Control.State)
    (history : History result.collected a.work seen visits) (empty : result.visited=#[])
    (query : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok path)
    (aligned : AlignedNext origin scene shooter thing path result distance a.work seen resolve portals a.lower a.upper a.log s)
    (done : seen.length=result.collected.size ∨ ∃ best, minimum a.work=.ok best ∧ best.1>65536) :
    s.pc=0x2c887 ∧
    remaining scene shooter thing path distance
      (List.range' seen.length (path.visited.size-seen.length)) a.lower a.upper a.log=.ok {path:=path} := by
  have finished := E1M1AimPathBridge.finished scene shooter thing path result distance a.lower a.upper a.log
    a.work seen visits history empty done query
  refine ⟨?_,finished.2⟩
  rcases aligned.1 with exhausted|⟨_,_,_,pc,_⟩|⟨fraction,j,selection,_⟩
  · have counter := exhausted.2.2
    rw [exhausted.2.1] at counter
    have counter' : (E1M1AimResume.result origin).core.regs 6-1=0xffffffff := counter
    have zero : (E1M1AimResume.result origin).core.regs 6=0 := by
      calc
        _ = ((E1M1AimResume.result origin).core.regs 6-1)+1 := (BitVec.sub_add_cancel _ _).symm
        _ = 0 := by rw [counter']; decide
    rw [exhausted.2.1]
    simp only [E1M1AimNextSelection.head,zero,ite_true]
  · exact pc
  · have hit := E1M1AimPathBridge.selected result path a.work seen visits resolve 0x2b760 (origin.regs 4+4)
      s fraction j history selection empty query
    have size := finished.1
    omega

/-- A continuing prefix followed by exhaustion or range rejection executes to
the real traversal exit and equals the production source suffix's final result. -/
theorem completed (scene : Scene) (shooter : Nat) (thing : SolidThing) (path result : PathResult)
    (distance : Fixed) (resolve : Intercept → Word) (portals : Nat → Option Portal)
    (represented : Represents scene result.collected portals) (empty : result.visited=#[])
    (query : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok path)
    (a final : Position) (count : Nat) (sequence : Sequence portals distance thing.shootHeight a final count)
    (origin : X86Memory.State) (s : X86Control.State) (seen : List Nat) (visits : Array Intercept)
    (history : History result.collected a.work seen visits)
    (aligned : AlignedNext origin scene shooter thing path result distance a.work seen resolve portals a.lower a.upper a.log s)
    (bottom : load32 s.core.memory (0x2c1e4#32)=a.lower.raw.toBitVec)
    (top : load32 s.core.memory (0x2c1e8#32)=a.upper.raw.toBitVec)
    (done : seen.length+count=result.collected.size ∨ ∃ best, minimum final.work=.ok best ∧ best.1>65536) :
    ∃ n≤count*(157+7*result.collected.size), ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n s out ∧ out.pc=0x2c887 ∧
      load32 out.core.memory (0x2c1e4#32)=final.lower.raw.toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=final.upper.raw.toBitVec ∧
      remaining scene shooter thing path distance
        (List.range' seen.length (path.visited.size-seen.length)) a.lower a.upper a.log=.ok {path:=path} := by
  obtain ⟨n,hn,out,finalOrigin,finalSeen,finalVisits,run,finalHistory,length,finalAligned,low,high,source⟩ :=
    E1M1AimPortalPrefix.execution scene shooter thing path result distance resolve portals represented empty query
      a final count sequence origin s seen visits history aligned bottom top
  have finish := terminal finalOrigin scene shooter thing path result distance final finalSeen finalVisits
    resolve portals out finalHistory empty query finalAligned (by simpa only [length] using done)
  exact ⟨n,hn,out,run,finish.1,low,high,source.trans finish.2⟩

/-- A later open-sector line may close the accumulated aim window. Execute the
whole preceding prefix and that stopping callback; it is visited but not marked
as consumed, and the source result stops at exactly that visit. -/
theorem stopped (scene : Scene) (shooter : Nat) (thing : SolidThing) (path result : PathResult)
    (distance : Fixed) (resolve : Intercept → Word) (portals : Nat → Option Portal)
    (represented : Represents scene result.collected portals) (empty : result.visited=#[])
    (query : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok path)
    (a final : Position) (count : Nat) (sequence : Sequence portals distance thing.shootHeight a final count)
    (origin : X86Memory.State) (s : X86Control.State) (seen : List Nat) (visits : Array Intercept)
    (history : History result.collected a.work seen visits)
    (aligned : AlignedNext origin scene shooter thing path result distance a.work seen resolve portals a.lower a.upper a.log s)
    (bottom : load32 s.core.memory (0x2c1e4#32)=a.lower.raw.toBitVec)
    (top : load32 s.core.memory (0x2c1e8#32)=a.upper.raw.toBitVec)
    (fraction : Int32) (j : Nat) (p : Portal) (floorSlope ceilingSlope : Fixed)
    (chosen : minimum final.work=.ok (fraction,some j)) (within : ¬fraction>65536)
    (listed : portals j=some p)
    (pass : max (front p).floor.raw (back p).floor.raw < min (front p).ceiling.raw (back p).ceiling.raw)
    (floorOk : (front p).floor≠(back p).floor →
      checkedPathDiv (⟨max (front p).floor.raw (back p).floor.raw⟩-thing.shootHeight)
        (distance*final.work[j]!.frac)=.ok floorSlope)
    (ceilingOk : (front p).ceiling≠(back p).ceiling →
      checkedPathDiv (⟨min (front p).ceiling.raw (back p).ceiling.raw⟩-thing.shootHeight)
        (distance*final.work[j]!.frac)=.ok ceilingSlope)
    (closed : ¬(advance final j p distance floorSlope ceilingSlope).lower.raw <
      (advance final j p distance floorSlope ceilingSlope).upper.raw) :
    ∃ n≤(count+1)*(157+7*result.collected.size), ∃ out finalSeen finalVisits,
      X86CodeMemory.Prefix FloorCaller.cm program [] n s out ∧ out.pc=0x2c88c ∧
      History result.collected final.work finalSeen finalVisits ∧ finalSeen.length=seen.length+count ∧
      load32 out.core.memory (0x2c1e4#32)=(advance final j p distance floorSlope ceilingSlope).lower.raw.toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=(advance final j p distance floorSlope ceilingSlope).upper.raw.toBitVec ∧
      remaining scene shooter thing path distance
        (List.range' seen.length (path.visited.size-seen.length)) a.lower a.upper a.log=
        .ok {path:=E1M1AimSource.stopped path (seen.length+count+1)} := by
  obtain ⟨n,hn,middle,finalOrigin,finalSeen,finalVisits,run,finalHistory,length,finalAligned,low,high,source⟩ :=
    E1M1AimPortalPrefix.execution scene shooter thing path result distance resolve portals represented empty query
      a final count sequence origin s seen visits history aligned bottom top
  obtain ⟨selection,persistent,_,_⟩ := E1M1AimSynchronizedCycle.next_callback finalOrigin scene shooter thing path result
    distance final.work finalSeen finalVisits resolve portals final.lower final.upper final.log middle finalHistory empty query
    finalAligned fraction j chosen within
  have pc : middle.pc=0x2b760 := selection.ready.pc
  have atCallback : middle=⟨middle.core,middle.flags,0x2b760⟩ := by cases middle; simp_all
  have selected : Selection result.collected final.work finalSeen resolve 0x2b760 (finalOrigin.regs 4+4)
      ⟨middle.core,middle.flags,0x2b760⟩ fraction j := by rw [← atCallback]; exact selection
  obtain ⟨m,hm,out,tail,done,bottomOut,topOut,sourceStop,_⟩ := E1M1AimSynchronizedCycle.execution middle.core middle.flags
    scene shooter thing path result final.work finalSeen finalVisits resolve portals distance 0x2b760 (finalOrigin.regs 4+4)
    fraction j p finalHistory selected persistent represented listed empty query final.lower final.upper floorSlope ceilingSlope
    final.log low high pass floorOk ceilingOk
  have closedWindow : ¬(bottomAfter (front p) (back p) final.lower floorSlope).raw <
      (topAfter (front p) (back p) final.upper ceilingSlope).raw := closed
  simp only [if_neg closedWindow] at done sourceStop
  rw [← atCallback] at tail
  have size := (E1M1SelectionHistory.image finalHistory).size
  refine ⟨n+m,?_,out,finalSeen,finalVisits,E1M1PspriteStep.prefix_trans run tail,done.2,
    finalHistory,length,bottomOut,topOut,?_⟩
  · rw [Nat.add_mul,Nat.one_mul]; omega
  · exact source.trans (by simpa only [length] using sourceStop)

end Doom.Proofs.E1M1AimPortalPrefixExit
