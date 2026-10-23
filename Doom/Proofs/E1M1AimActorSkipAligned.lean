import Doom.Proofs.E1M1AimActorSkipCycle
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimActorSkipAligned
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMark (consume)
open E1M1AimCatalog (Portal)
open E1M1AimTraversalInvariant (Persistent)
open E1M1AimActorSkipCycle (Next)
open E1M1AimActorSkip (program)
open E1M1AimWall (Safe)
open E1M1AimHistoryCycle (Frame)
open E1M1AimIteration
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- Either the original traversal has finished and so has the source suffix,
or the next original callback carries both its persistent invariant and its
proved position in that same precomputed source path. -/
def Aligned (s : X86Memory.State) (scene : Scene) (shooter : Nat) (thing : SolidThing)
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
    Aligned s scene shooter thing path result distance work seen resolve portals lower upper log out := by
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
    (aligned : Aligned s scene shooter thing path result distance work seen resolve portals lower upper log out)
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

/-- An admitted successor can feed the existing line/portal cycle directly.
Terminal actor states stay distinct; only the reached callback boundary is shared. -/
theorem line_boundary (s : X86Memory.State) (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path result : PathResult) (distance : Fixed) (work : Array Intercept) (seen : List Nat)
    (visits : Array Intercept) (resolve : Intercept → Word) (portals : Nat → Option Portal)
    (lower upper : Fixed) (log : Array AutoAim.Portal) (out : X86Control.State)
    (history : History result.collected work seen visits) (empty : result.visited=#[])
    (query : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok path)
    (aligned : Aligned s scene shooter thing path result distance work seen resolve portals lower upper log out)
    (fraction : Int32) (j : Nat)
    (chosen : E1M1InterceptMinimum.minimum work=.ok (fraction,some j)) (within : ¬fraction>65536) :
    E1M1AimSynchronizedCycle.AlignedNext s scene shooter thing path result distance work seen
      resolve portals lower upper log out := by
  obtain ⟨selection,persistent,inside,hit⟩ := next_callback s scene shooter thing path result distance
    work seen visits resolve portals lower upper log out history empty query aligned fraction j chosen within
  exact ⟨Or.inr (Or.inr ⟨fraction,j,selection,persistent⟩),
    Or.inr ⟨fraction,j,selection,persistent,inside,hit⟩⟩

/-- Actor rejection now joins the actual DOS scan/CALL and canonical source
boundary, preserving the portal invariant for subsequent mixed traversal work. -/
theorem execution (s : X86Memory.State) (f : Option Flags)
    (scene : Scene) (shooter : Nat) (thing : SolidThing) (path original : PathResult)
    (distance lower upper : Fixed) (log : Array AutoAim.Portal)
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
    (ignored : (work[j]!).id=shooter ∨ scene.things[work[j]!.id]!.shootable=false) :
    ∃ n≤41+7*work.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ out ∧
      History original.collected (consume work j) (j::seen) (visits.push work[j]!) ∧
      Aligned s scene shooter thing path original distance (consume work j) (j::seen)
        resolve portals lower upper log out ∧
      load32 out.core.memory (0x2c1e4#32)=lower.raw.toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=upper.raw.toBitVec ∧ Frame s out ∧
      remaining scene shooter thing path distance
        (List.range' seen.length (path.visited.size-seen.length)) lower upper log =
      remaining scene shooter thing path distance
        (List.range' (seen.length+1) (path.visited.size-(seen.length+1))) lower upper log := by
  obtain ⟨n,hn,out,run,historyNext,next,low,high,frame,source⟩ := E1M1AimActorSkipCycle.execution
    s f scene shooter thing path original distance lower upper log work seen visits resolve target sp who fraction j
    history selection portals before empty query bottom top isThing shooterSafe flagsSafe shooterWord identity flags ignored
  exact ⟨n,hn,out,run,historyNext,
    boundary s scene shooter thing path original distance (consume work j) (j::seen) (visits.push work[j]!)
      resolve portals lower upper log out historyNext empty query next,low,high,frame,source⟩

end Doom.Proofs.E1M1AimActorSkipAligned
