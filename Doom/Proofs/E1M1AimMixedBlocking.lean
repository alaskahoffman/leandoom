import Doom.Proofs.E1M1AimMixedExit
import Doom.Proofs.E1M1AimWallCatalog
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimMixedBlocking
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMinimum (minimum)
open E1M1AimCatalog (Portal)
open E1M1AimSourceCatalog (Represents front back)
open E1M1AimIteration
open E1M1AimSynchronizedCycle (AlignedNext)
open E1M1AimPortalPrefix (Position advance)
open E1M1AimMixedPrefix (Sequence)
open E1M1AimActorCatalog (Catalog)
open E1M1AimActorSelect (program)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- A mixed prefix followed by a closed sector opening. -/
theorem closed (scene : Scene) (shooter : Nat) (thing : SolidThing) (path result : PathResult)
    (distance : Fixed) (resolve : Intercept → Word) (portals : Nat → Option Portal) (who : Word)
    (represented : Represents scene result.collected portals) (empty : result.visited=#[])
    (query : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok path)
    (a final : Position) (count : Nat) (sequence : Sequence scene shooter portals distance thing.shootHeight a final count)
    (origin : X86Memory.State) (s : X86Control.State) (seen : List Nat) (visits : Array Intercept)
    (history : History result.collected a.work seen visits)
    (aligned : AlignedNext origin scene shooter thing path result distance a.work seen resolve portals a.lower a.upper a.log s)
    (bottom : load32 s.core.memory (0x2c1e4#32)=a.lower.raw.toBitVec)
    (top : load32 s.core.memory (0x2c1e8#32)=a.upper.raw.toBitVec)
    (actors : Catalog s.core scene shooter result.collected resolve who)
    (fraction : Int32) (j : Nat) (p : Portal)
    (chosen : minimum final.work=.ok (fraction,some j)) (within : ¬fraction>65536)
    (listed : portals j=some p)
    (blocked : min (front p).ceiling.raw (back p).ceiling.raw ≤ max (front p).floor.raw (back p).floor.raw) :
    ∃ n≤count*(157+7*result.collected.size)+60, ∃ out finalSeen finalVisits,
      X86CodeMemory.Prefix FloorCaller.cm program [] n s out ∧ out.pc=0x2c88c ∧
      History result.collected final.work finalSeen finalVisits ∧ finalSeen.length=seen.length+count ∧
      load32 out.core.memory (0x2c1e4#32)=final.lower.raw.toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=final.upper.raw.toBitVec ∧
      remaining scene shooter thing path distance
        (List.range' seen.length (path.visited.size-seen.length)) a.lower a.upper a.log=
        .ok {path:=E1M1AimSource.stopped path (seen.length+count+1)} := by
  obtain ⟨n,hn,middle,finalOrigin,finalSeen,finalVisits,run,finalHistory,length,finalAligned,low,high,carried,selection,persistent,source⟩ :=
    E1M1AimMixedPrefix.execution scene shooter thing path result distance resolve portals who represented empty query
      a final count sequence origin s seen visits history aligned bottom top actors fraction j chosen within
  have pc : middle.pc=0x2b760 := selection.ready.pc
  have atCallback : middle=⟨middle.core,middle.flags,0x2b760⟩ := by cases middle; simp_all
  have selected : Selection result.collected final.work finalSeen resolve 0x2b760 (finalOrigin.regs 4+4)
      ⟨middle.core,middle.flags,0x2b760⟩ fraction j := by rw [← atCallback]; exact selection
  obtain ⟨m,hm,out,tail,stopped,_,_,bottomOut,topOut,sourceStop⟩ := E1M1AimBlockingCycle.closed middle.core middle.flags
    scene shooter thing path result final.work finalSeen finalVisits resolve portals distance 0x2b760 (finalOrigin.regs 4+4)
    fraction j p finalHistory selected persistent represented listed empty query final.lower final.upper final.log low high blocked
  rw [← atCallback] at tail
  have tail := tail.transfer program [] E1M1AimActorReturn.contains_repeat (by simp)
  refine ⟨n+m,by omega,out,finalSeen,finalVisits,E1M1PspriteStep.prefix_trans run tail,stopped,
    finalHistory,length,bottomOut,topOut,?_⟩
  exact source.trans (by simpa only [length] using sourceStop)

/-- A mixed prefix followed by a portal that closes the clipped aiming window. -/
theorem stopped (scene : Scene) (shooter : Nat) (thing : SolidThing) (path result : PathResult)
    (distance : Fixed) (resolve : Intercept → Word) (portals : Nat → Option Portal) (who : Word)
    (represented : Represents scene result.collected portals) (empty : result.visited=#[])
    (query : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok path)
    (a final : Position) (count : Nat) (sequence : Sequence scene shooter portals distance thing.shootHeight a final count)
    (origin : X86Memory.State) (s : X86Control.State) (seen : List Nat) (visits : Array Intercept)
    (history : History result.collected a.work seen visits)
    (aligned : AlignedNext origin scene shooter thing path result distance a.work seen resolve portals a.lower a.upper a.log s)
    (bottom : load32 s.core.memory (0x2c1e4#32)=a.lower.raw.toBitVec)
    (top : load32 s.core.memory (0x2c1e8#32)=a.upper.raw.toBitVec)
    (actors : Catalog s.core scene shooter result.collected resolve who)
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
  obtain ⟨n,hn,middle,finalOrigin,finalSeen,finalVisits,run,finalHistory,length,finalAligned,low,high,carried,selection,persistent,source⟩ :=
    E1M1AimMixedPrefix.execution scene shooter thing path result distance resolve portals who represented empty query
      a final count sequence origin s seen visits history aligned bottom top actors fraction j chosen within
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
  have tail := tail.transfer program [] E1M1AimActorReturn.contains_repeat (by simp)
  have size := (E1M1SelectionHistory.image finalHistory).size
  refine ⟨n+m,?_,out,finalSeen,finalVisits,E1M1PspriteStep.prefix_trans run tail,done.2,
    finalHistory,length,bottomOut,topOut,?_⟩
  · rw [Nat.add_mul,Nat.one_mul]; omega
  · exact source.trans (by simpa only [length] using sourceStop)

/-- Wall representation is carried through every earlier line or actor callback. -/
theorem wall (scene : Scene) (shooter : Nat) (thing : SolidThing) (path result : PathResult)
    (distance : Fixed) (resolve : Intercept → Word) (portals : Nat → Option Portal) (who : Word)
    (represented : Represents scene result.collected portals) (empty : result.visited=#[])
    (query : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok path)
    (a final : Position) (count : Nat) (sequence : Sequence scene shooter portals distance thing.shootHeight a final count)
    (origin : X86Memory.State) (s : X86Control.State) (seen : List Nat) (visits : Array Intercept)
    (history : History result.collected a.work seen visits)
    (aligned : AlignedNext origin scene shooter thing path result distance a.work seen resolve portals a.lower a.upper a.log s)
    (bottom : load32 s.core.memory (0x2c1e4#32)=a.lower.raw.toBitVec)
    (top : load32 s.core.memory (0x2c1e8#32)=a.upper.raw.toBitVec)
    (actors : Catalog s.core scene shooter result.collected resolve who)
    (walls : Nat → Prop)
    (catalog : E1M1AimWallCatalog.Catalog s.core result.collected resolve walls)
    (wallMap : E1M1AimWallCatalog.Represents scene result.collected walls)
    (fraction : Int32) (j : Nat)
    (chosen : minimum final.work=.ok (fraction,some j)) (within : ¬fraction>65536)
    (listed : walls j) :
    ∃ n≤count*(157+7*result.collected.size)+24, ∃ out finalSeen finalVisits,
      X86CodeMemory.Prefix FloorCaller.cm program [] n s out ∧ out.pc=0x2c88c ∧
      History result.collected final.work finalSeen finalVisits ∧ finalSeen.length=seen.length+count ∧
      load32 out.core.memory (0x2c1e4#32)=final.lower.raw.toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=final.upper.raw.toBitVec ∧
      remaining scene shooter thing path distance
        (List.range' seen.length (path.visited.size-seen.length)) a.lower a.upper a.log=
        .ok {path:=E1M1AimSource.stopped path (seen.length+count+1)} := by
  have boundary := E1M1AimMixedBoundary.from_line origin scene shooter thing path result distance a seen visits
    resolve portals s history empty query aligned
  obtain ⟨n,hn,middle,finalOrigin,finalSeen,finalVisits,run,finalHistory,length,finalBoundary,low,high,ready,source⟩ :=
    E1M1AimMixedExit.execution scene shooter thing path result distance resolve portals who represented empty query
      a final count sequence origin s seen visits history boundary bottom top
      (fun state => E1M1AimWallCatalog.Catalog state result.collected resolve walls)
      (fun before out marked frame stack pointer bound cat =>
        E1M1AimWallCatalog.preserved before out marked result.collected resolve walls frame stack pointer bound cat)
      (by intro fraction j chosen within; exact ⟨actors,catalog⟩)
  have carried := (ready fraction j chosen within).2
  obtain ⟨selection,persistent,_,_⟩ := E1M1AimActorBoundary.next_callback finalOrigin scene shooter thing path result distance
    final.work finalSeen finalVisits resolve portals final.lower final.upper final.log middle finalHistory empty query
    finalBoundary fraction j chosen within
  have pc : middle.pc=0x2b760 := selection.ready.pc
  have atCallback : middle=⟨middle.core,middle.flags,0x2b760⟩ := by cases middle; simp_all
  have selected : Selection result.collected final.work finalSeen resolve 0x2b760 (finalOrigin.regs 4+4)
      ⟨middle.core,middle.flags,0x2b760⟩ fraction j := by rw [← atCallback]; exact selection
  have inputs := E1M1AimWallCatalog.inputs scene result.collected final.work finalSeen resolve walls 0x2b760
    (finalOrigin.regs 4+4) middle fraction j selection carried wallMap listed
  obtain ⟨out,tail,stopped,_,_,bottomOut,topOut,sourceStop⟩ := E1M1AimBlockingCycle.wall middle.core middle.flags
    scene shooter thing path result final.work finalSeen finalVisits resolve distance 0x2b760 (finalOrigin.regs 4+4)
    fraction j finalHistory selected persistent.layout empty query final.lower final.upper final.log low high
    inputs.1 inputs.2.1 inputs.2.2.1 inputs.2.2.2
  rw [← atCallback] at tail
  have tail := tail.transfer program [] E1M1AimActorReturn.contains_repeat (by simp)
  refine ⟨n+24,by omega,out,finalSeen,finalVisits,E1M1PspriteStep.prefix_trans run tail,stopped,
    finalHistory,length,bottomOut,topOut,?_⟩
  exact source.trans (by simpa only [length] using sourceStop)

end Doom.Proofs.E1M1AimMixedBlocking
