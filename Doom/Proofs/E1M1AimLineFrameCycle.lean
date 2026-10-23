import Doom.Proofs.E1M1AimNoTargetFrame
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimLineFrameCycle
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMark (consume)
open E1M1AimCatalog (Portal)
open E1M1AimTraversalInvariant (Persistent)
open E1M1AimSourceCatalog (Represents front back)
open E1M1AimIteration
open E1M1AimSynchronizedCycle (AlignedNext)
open E1M1AimHistoryCycle (Frame)
open E1M1AimRepeatProgram (program)
open E1M1AimLineDispatch (dispatch)
open E1M1AimLineCoverage (Coverage)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- Retain a word frame for stopping lines as well as continuing lines.
Dispatch every covered selected line by its source flags, opening and clipped
window. Branch outcomes are derived, not supplied. Divisions are required only
for an open sector and a differing height. Continuing callbacks retain the wall
catalog, allowing the next represented line to use this same interface. -/
theorem execution (s : X86Memory.State) (f : Option Flags)
    (scene : Scene) (shooter : Nat) (thing : SolidThing) (path result : PathResult)
    (work : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (portals : Nat → Option Portal) (walls : Nat → Prop) (distance : Fixed)
    (target sp : Word) (fraction : Int32) (j : Nat)
    (history : History result.collected work seen visits)
    (selection : Selection result.collected work seen resolve target sp ⟨s,f,0x2b760⟩ fraction j)
    (before : Persistent s result.collected work resolve portals distance thing.shootHeight)
    (represented : Represents scene result.collected portals)
    (catalog : E1M1AimWallCatalog.Catalog s result.collected resolve walls)
    (wallMap : E1M1AimWallCatalog.Represents scene result.collected walls)
    (covered : Coverage result.collected walls portals) (isLine : (work[j]!).isLine=true)
    (empty : result.visited=#[])
    (query : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok path)
    (lower upper floorSlope ceilingSlope : Fixed) (log : Array AutoAim.Portal)
    (bottom : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec)
    (top : load32 s.memory (0x2c1e8#32)=upper.raw.toBitVec)
    (divisions : ∀ p, portals j=some p →
      max (front p).floor.raw (back p).floor.raw < min (front p).ceiling.raw (back p).ceiling.raw →
      ((front p).floor≠(back p).floor →
        checkedPathDiv (⟨max (front p).floor.raw (back p).floor.raw⟩-thing.shootHeight)
          (distance*work[j]!.frac)=.ok floorSlope) ∧
      ((front p).ceiling≠(back p).ceiling →
        checkedPathDiv (⟨min (front p).ceiling.raw (back p).ceiling.raw⟩-thing.shootHeight)
          (distance*work[j]!.frac)=.ok ceilingSlope)) :
    ∃ n≤157+7*work.size, ∃ out,
      Frame s out ∧
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ out ∧
      match dispatch scene work[j]! distance lower upper floorSlope ceilingSlope with
      | none => False
      | some (.stop lo hi) =>
        out.pc=0x2c88c ∧
        load32 out.core.memory (0x2c1e4#32)=lo.raw.toBitVec ∧
        load32 out.core.memory (0x2c1e8#32)=hi.raw.toBitVec ∧
        remaining scene shooter thing path distance
          (List.range' seen.length (path.visited.size-seen.length)) lower upper log =
          .ok {path:=E1M1AimSource.stopped path (seen.length+1)}
      | some (.next lo hi entry) =>
        History result.collected (consume work j) (j::seen) (visits.push work[j]!) ∧
        AlignedNext s scene shooter thing path result distance (consume work j) (j::seen)
          resolve portals lo hi (log.push entry) out ∧
        load32 out.core.memory (0x2c1e4#32)=lo.raw.toBitVec ∧
        load32 out.core.memory (0x2c1e8#32)=hi.raw.toBitVec ∧
        remaining scene shooter thing path distance
          (List.range' seen.length (path.visited.size-seen.length)) lower upper log =
          remaining scene shooter thing path distance
            (List.range' (seen.length+1) (path.visited.size-(seen.length+1))) lo hi (log.push entry) ∧
        Frame s out ∧
        (∀ nextFraction k, Selection result.collected (consume work j) (j::seen) resolve 0x2b760
          (s.regs 4+4) out nextFraction k → E1M1AimWallCatalog.Catalog out.core result.collected resolve walls) := by
  rcases E1M1AimLineCoverage.selected result.collected work seen resolve walls portals target sp
      ⟨s,f,0x2b760⟩ fraction j selection covered isLine with wall|⟨p,listed⟩
  · have inputs := E1M1AimWallCatalog.inputs scene result.collected work seen resolve walls target sp
      ⟨s,f,0x2b760⟩ fraction j selection catalog wallMap wall
    obtain ⟨out,frame,run,pc,_,_,low,high,source⟩ := E1M1AimNoTargetFrame.wall s f scene shooter thing path result
      work seen visits resolve distance target sp fraction j history selection before.layout empty query
      lower upper log bottom top inputs.1 inputs.2.1 inputs.2.2.1 inputs.2.2.2
    refine ⟨24,by omega,out,frame,run,?_⟩
    rw [E1M1AimLineDispatch.wall scene work[j]! distance lower upper floorSlope ceilingSlope inputs.2.2.2]
    exact ⟨pc,low,high,source⟩
  · have sourceMap := E1M1AimSourceCatalog.entry scene result.collected work seen resolve portals
      target sp ⟨s,f,0x2b760⟩ fraction j p selection represented listed
    by_cases blocked : min (front p).ceiling.raw (back p).ceiling.raw ≤ max (front p).floor.raw (back p).floor.raw
    · obtain ⟨n,hn,out,frame,run,pc,_,_,low,high,source⟩ := E1M1AimNoTargetFrame.closed s f scene shooter thing path result
        work seen visits resolve portals distance target sp fraction j p history selection before represented listed
        empty query lower upper log bottom top blocked
      refine ⟨n,by omega,out,frame,run,?_⟩
      rw [E1M1AimLineDispatch.closed scene work[j]! distance lower upper floorSlope ceilingSlope (back p)
        sourceMap.2.2 sourceMap.2.1 (by simpa only [sourceMap.1] using blocked)]
      exact ⟨pc,low,high,source⟩
    · have pass : max (front p).floor.raw (back p).floor.raw < min (front p).ceiling.raw (back p).ceiling.raw := by
        simp only [Int32.le_iff_toInt_le,Int32.lt_iff_toInt_lt] at blocked ⊢; omega
      have arithmetic := divisions p listed pass
      obtain ⟨n,hn,out,run,done,low,high,source,frame⟩ := E1M1AimSynchronizedCycle.execution s f
        scene shooter thing path result work seen visits resolve portals distance target sp fraction j p history selection
        before represented listed empty query lower upper floorSlope ceilingSlope log bottom top pass arithmetic.1 arithmetic.2
      have decision := E1M1AimLineDispatch.opened scene work[j]! distance lower upper floorSlope ceilingSlope (back p)
        sourceMap.2.2 sourceMap.2.1 (by simpa only [sourceMap.1] using pass)
      simp only [sourceMap.1] at decision
      refine ⟨n,hn,out,frame,run,?_⟩
      rw [decision]
      by_cases go : (bottomAfter (front p) (back p) lower floorSlope).raw < (topAfter (front p) (back p) upper ceilingSlope).raw
      · simp only [if_pos go] at done source ⊢
        refine ⟨done.1,done.2,low,high,source,frame,?_⟩
        intro nextFraction k nextSelection
        have stack := E1M1AimCycleInvariant.stack s result.collected (consume work j) (j::seen)
          resolve 0x2b760 out nextFraction k nextSelection
        have bound : j<128 := by have := selection.inside; have := before.bounded; omega
        exact E1M1AimWallCatalog.preserved s out j result.collected resolve walls frame stack
          (selection.ready.pointer.trans selection.argument) bound catalog
      · simp only [if_neg go] at done source ⊢
        exact ⟨done.2,low,high,source⟩

end Doom.Proofs.E1M1AimLineFrameCycle
