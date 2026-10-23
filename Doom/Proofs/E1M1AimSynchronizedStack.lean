import Doom.Proofs.E1M1AimPortalStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimSynchronizedStack
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMark (consume)
open E1M1AimCatalog (Portal)
open E1M1AimTraversalInvariant (Persistent Next)
open E1M1AimSourceCatalog (Represents front back)
open E1M1AimIteration
open E1M1AimHistoryCycle (Frame)
open E1M1AimRepeatProgram (program)
attribute [local irreducible] load32 store32

open E1M1AimStackShape (Shape)
open E1M1AimSynchronizedCycle (AlignedNext boundary indices)
theorem execution (s : X86Memory.State) (f : Option Flags)
    (scene : Scene) (shooter : Nat) (thing : SolidThing) (path result : PathResult)
    (work : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (portals : Nat → Option Portal) (distance : Fixed)
    (target sp : Word) (fraction : Int32) (j : Nat) (p : Portal)
    (history : History result.collected work seen visits)
    (selection : Selection result.collected work seen resolve target sp ⟨s,f,0x2b760⟩ fraction j)
    (before : Persistent s result.collected work resolve portals distance thing.shootHeight)
    (represented : Represents scene result.collected portals) (listed : portals j=some p)
    (empty : result.visited=#[])
    (query : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok path)
    (lower upper floorSlope ceilingSlope : Fixed) (log : Array AutoAim.Portal)
    (bottom : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec)
    (top : load32 s.memory (0x2c1e8#32)=upper.raw.toBitVec)
    (pass : max (front p).floor.raw (back p).floor.raw < min (front p).ceiling.raw (back p).ceiling.raw)
    (floorOk : (front p).floor≠(back p).floor →
      checkedPathDiv (⟨max (front p).floor.raw (back p).floor.raw⟩-thing.shootHeight)
        (distance*work[j]!.frac)=.ok floorSlope)
    (ceilingOk : (front p).ceiling≠(back p).ceiling →
      checkedPathDiv (⟨min (front p).ceiling.raw (back p).ceiling.raw⟩-thing.shootHeight)
        (distance*work[j]!.frac)=.ok ceilingSlope) :
    let lo := bottomAfter (front p) (back p) lower floorSlope
    let hi := topAfter (front p) (back p) upper ceilingSlope
    let nextLog := log.push (portal (front p) (back p) distance work[j]!)
    ∃ n≤157+7*work.size, ∃ out,
      Shape (s.regs 4+4) out ∧
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ out ∧
      (if lo.raw<hi.raw then
        History result.collected (consume work j) (j::seen) (visits.push work[j]!) ∧
        AlignedNext s scene shooter thing path result distance (consume work j) (j::seen)
          resolve portals lo hi nextLog out
       else out=E1M1AimResume.result s ∧ out.pc=0x2c88c) ∧
      load32 out.core.memory (0x2c1e4#32)=lo.raw.toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=hi.raw.toBitVec ∧
      remaining scene shooter thing path distance
        (List.range' seen.length (path.visited.size-seen.length)) lower upper log =
        (if lo.raw<hi.raw then
          remaining scene shooter thing path distance
            (List.range' (seen.length+1) (path.visited.size-(seen.length+1))) lo hi nextLog
         else .ok {path:=E1M1AimSource.stopped path (seen.length+1)}) ∧ Frame s out := by
  dsimp only
  have sourceMap := E1M1AimSourceCatalog.entry scene result.collected work seen resolve portals
    target sp ⟨s,f,0x2b760⟩ fraction j p selection represented listed
  have inputs := E1M1AimCatalog.inputs ⟨s,f,0x2b760⟩ result.collected work seen visits resolve portals
    target sp fraction j p history selection before.catalog listed before.layout before.query before.globals
  have aligned := E1M1AimPathBridge.selected result path work seen visits resolve target sp
    ⟨s,f,0x2b760⟩ fraction j history selection empty query
  have sourceStep := E1M1AimPathBridge.next_line scene shooter thing path distance
    (List.range' (seen.length+1) (path.visited.size-(seen.length+1))) lower upper floorSlope ceilingSlope
    log (back p) result work seen visits resolve target sp ⟨s,f,0x2b760⟩ fraction j history selection empty query
    inputs.1.isLine sourceMap.2.2 sourceMap.2.1
    (by simpa only [sourceMap.1] using pass)
    (by simpa only [sourceMap.1] using floorOk)
    (by simpa only [sourceMap.1] using ceilingOk)
  simp only [sourceMap.1] at sourceStep
  have words := E1M1AimSourceCatalog.arithmetic p distance thing.shootHeight work[j]!
    lower upper floorSlope ceilingSlope pass floorOk ceilingOk
  obtain ⟨n,hn,out,shape,run,done,low,high,frame⟩ := E1M1AimPortalStack.execution s f
    result.collected work seen visits resolve portals distance thing.shootHeight target sp fraction j p
    history selection before listed lower upper floorSlope ceilingSlope bottom top words.1 words.2.1 words.2.2.1
  simp only [words.2.2.2.1,words.2.2.2.2,← Int32.lt_iff_toInt_lt] at done low high
  refine ⟨n,hn,out,shape,run,?_,low,high,?_,frame⟩
  · by_cases go : (bottomAfter (front p) (back p) lower floorSlope).raw <
        (topAfter (front p) (back p) upper ceilingSlope).raw
    · simp only [if_pos go] at done ⊢
      exact ⟨done.1,boundary s scene shooter thing path result distance (consume work j) (j::seen)
        (visits.push work[j]!) resolve portals _ _ _ out done.1 empty query done.2⟩
    · simpa only [if_neg go] using done
  · rw [indices seen.length path.visited.size aligned.1]
    exact sourceStep

end Doom.Proofs.E1M1AimSynchronizedStack
