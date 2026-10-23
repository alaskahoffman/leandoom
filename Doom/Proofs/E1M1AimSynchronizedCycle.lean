import Doom.Proofs.E1M1AimSourceCatalog
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimSynchronizedCycle
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

/-- Use the actual remaining source indices, not an arbitrary list tail. -/
theorem indices (i size : Nat) (inside : i<size) :
    List.range' i (size-i) = i::List.range' (i+1) (size-(i+1)) := by
  have fuel : size-i=(size-(i+1))+1 := by omega
  rw [fuel,List.range'_succ]

/-- Either the original traversal has finished and so has the source suffix,
or the next original callback carries both its persistent invariant and its
proved position in that same precomputed source path. -/
def AlignedNext (s : X86Memory.State) (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path result : PathResult) (distance : Fixed) (work : Array Intercept) (seen : List Nat)
    (resolve : Intercept → Word) (portals : Nat → Option Portal)
    (lower upper : Fixed) (log : Array AutoAim.Portal) (out : X86Control.State) : Prop :=
  Next s result.collected work seen resolve portals distance thing.shootHeight out ∧
  ((path.visited.size=seen.length ∧
    remaining scene shooter thing path distance
      (List.range' seen.length (path.visited.size-seen.length)) lower upper log=.ok {path:=path}) ∨
   (∃ fraction j, Selection result.collected work seen resolve 0x2b760 (s.regs 4+4) out fraction j ∧
    Persistent out.core result.collected work resolve portals distance thing.shootHeight ∧
    seen.length<path.visited.size ∧ path.visited[seen.length]! = work[j]!))

theorem boundary (s : X86Memory.State) (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path result : PathResult) (distance : Fixed) (work : Array Intercept) (seen : List Nat)
    (visits : Array Intercept) (resolve : Intercept → Word) (portals : Nat → Option Portal)
    (lower upper : Fixed) (log : Array AutoAim.Portal) (out : X86Control.State)
    (history : History result.collected work seen visits) (empty : result.visited=#[])
    (run : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok path)
    (next : Next s result.collected work seen resolve portals distance thing.shootHeight out) :
    AlignedNext s scene shooter thing path result distance work seen resolve portals lower upper log out := by
  refine ⟨next,?_⟩
  rcases next with exhausted|⟨best,chosen,far,_,_⟩|⟨fraction,j,selection,persistent⟩
  · exact Or.inl (E1M1AimPathBridge.finished scene shooter thing path result distance lower upper log
      work seen visits history empty (Or.inl exhausted.1) run)
  · exact Or.inl (E1M1AimPathBridge.finished scene shooter thing path result distance lower upper log
      work seen visits history empty (Or.inr ⟨best,chosen,far⟩) run)
  · have hit := E1M1AimPathBridge.selected result path work seen visits resolve 0x2b760 (s.regs 4+4)
      out fraction j history selection empty run
    exact Or.inr ⟨fraction,j,selection,persistent,hit.1,hit.2.1⟩

/-- An admitted next source selection rules out either terminal boundary.
The reached callback therefore has precisely that fraction/index and carries
the persistent invariant required by another synchronized cycle. -/
theorem next_callback (s : X86Memory.State) (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path result : PathResult) (distance : Fixed) (work : Array Intercept) (seen : List Nat)
    (visits : Array Intercept) (resolve : Intercept → Word) (portals : Nat → Option Portal)
    (lower upper : Fixed) (log : Array AutoAim.Portal) (out : X86Control.State)
    (history : History result.collected work seen visits) (empty : result.visited=#[])
    (query : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok path)
    (aligned : AlignedNext s scene shooter thing path result distance work seen resolve portals lower upper log out)
    (fraction : Int32) (j : Nat)
    (chosen : E1M1InterceptMinimum.minimum work=.ok (fraction,some j)) (within : ¬fraction>65536) :
    Selection result.collected work seen resolve 0x2b760 (s.regs 4+4) out fraction j ∧
    Persistent out.core result.collected work resolve portals distance thing.shootHeight ∧
    seen.length<path.visited.size ∧ path.visited[seen.length]! = work[j]! := by
  rcases aligned.2 with finished|⟨actual,k,selection,persistent,inside,hit⟩
  · have next := E1M1AimPathOrder.next_hit result path work seen visits history fraction j chosen within query
    simp only [empty,Array.size_empty,Nat.zero_add] at next
    have size := finished.1
    omega
  · have pair := Except.ok.inj (selection.chosen.symm.trans chosen)
    have fractionEq : actual=fraction := congrArg Prod.fst pair
    have indexEq : k=j := Option.some.inj (congrArg Prod.snd pair)
    subst actual
    subst k
    exact ⟨selection,persistent,inside,hit⟩

/-- A single synchronized production step: the original binary and the actual
source suffix carry identical clipped bounds, advance the same original hit,
and reach aligned next callbacks or corresponding exits. -/
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
  obtain ⟨n,hn,out,run,done,low,high,frame⟩ := E1M1AimTraversalInvariant.execution s f
    result.collected work seen visits resolve portals distance thing.shootHeight target sp fraction j p
    history selection before listed lower upper floorSlope ceilingSlope bottom top words.1 words.2.1 words.2.2.1
  simp only [words.2.2.2.1,words.2.2.2.2,← Int32.lt_iff_toInt_lt] at done low high
  refine ⟨n,hn,out,run,?_,low,high,?_,frame⟩
  · by_cases go : (bottomAfter (front p) (back p) lower floorSlope).raw <
        (topAfter (front p) (back p) upper ceilingSlope).raw
    · simp only [if_pos go] at done ⊢
      exact ⟨done.1,boundary s scene shooter thing path result distance (consume work j) (j::seen)
        (visits.push work[j]!) resolve portals _ _ _ out done.1 empty query done.2⟩
    · simpa only [if_neg go] using done
  · rw [indices seen.length path.visited.size aligned.1]
    exact sourceStep

end Doom.Proofs.E1M1AimSynchronizedCycle
