import Doom.Proofs.E1M1AimActorStop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimActorBoundary
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1AimCatalog (Portal)
open E1M1AimTraversalInvariant (Persistent)
open E1M1AimIteration
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- A common post-scan interface for every continuing actor branch. Terminal
cases retain the machine exit PC; live cases retain the exact selected source hit. -/
def Boundary (s : X86Memory.State) (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path original : PathResult) (distance : Fixed) (work : Array Intercept) (seen : List Nat)
    (resolve : Intercept → Word) (portals : Nat → Option Portal)
    (lower upper : Fixed) (log : Array AutoAim.Portal) (out : X86Control.State) : Prop :=
  (out.pc=0x2c887 ∧ path.visited.size=seen.length ∧
    remaining scene shooter thing path distance
      (List.range' seen.length (path.visited.size-seen.length)) lower upper log=.ok {path}) ∨
  (∃ fraction j, Selection original.collected work seen resolve 0x2b760 (s.regs 4+4) out fraction j ∧
    Persistent out.core original.collected work resolve portals distance thing.shootHeight ∧
    seen.length<path.visited.size ∧ path.visited[seen.length]! = work[j]!)

/-- The original exhaustion decrement wraps to all ones only from zero. -/
theorem exhausted_pc (s : X86Memory.State)
    (counter : (E1M1AimNextSelection.head s).core.regs 6=0xffffffff) :
    (E1M1AimNextSelection.head s).pc=0x2c887 := by
  have counter : s.regs 6-1=0xffffffff := by simpa [E1M1AimNextSelection.head,put,write] using counter
  have zero : s.regs 6=0 := by
    have eq := congrArg (fun v : Word => v+1) counter
    simpa only [BitVec.sub_add_cancel,show (0xffffffff : Word)+1=0 by decide] using eq
  simp [E1M1AimNextSelection.head,zero]

theorem skipped (s : X86Memory.State) (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path original : PathResult) (distance : Fixed) (work : Array Intercept) (seen : List Nat)
    (visits : Array Intercept) (resolve : Intercept → Word) (portals : Nat → Option Portal)
    (lower upper : Fixed) (log : Array AutoAim.Portal) (out : X86Control.State)
    (history : History original.collected work seen visits) (empty : original.visited=#[])
    (query : E1M1QuerySource.visitHits original (fun _ _ => true)=.ok path)
    (next : E1M1AimActorSkipCycle.Next s original.collected work seen resolve portals distance thing.shootHeight out) :
    Boundary s scene shooter thing path original distance work seen resolve portals lower upper log out := by
  rcases next with exhausted|⟨best,chosen,far,pc,_⟩|⟨fraction,j,selection,persistent⟩
  · have done := E1M1AimPathBridge.finished scene shooter thing path original distance lower upper log
      work seen visits history empty (Or.inl exhausted.1) query
    have pc : out.pc=0x2c887 := by
      have counter := exhausted.2.2
      rw [exhausted.2.1] at counter
      exact (congrArg X86Control.State.pc exhausted.2.1).trans (exhausted_pc _ counter)
    exact Or.inl ⟨pc,done⟩
  · exact Or.inl ⟨pc,E1M1AimPathBridge.finished scene shooter thing path original distance lower upper log
      work seen visits history empty (Or.inr ⟨best,chosen,far⟩) query⟩
  · have hit := E1M1AimPathBridge.selected original path work seen visits resolve 0x2b760 (s.regs 4+4)
      out fraction j history selection empty query
    exact Or.inr ⟨fraction,j,selection,persistent,hit.1,hit.2.1⟩

theorem top_rejected (s : X86Memory.State) (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path original : PathResult) (distance : Fixed) (work : Array Intercept) (seen : List Nat)
    (visits : Array Intercept) (resolve : Intercept → Word) (portals : Nat → Option Portal)
    (lower upper : Fixed) (log : Array AutoAim.Portal) (out : X86Control.State)
    (history : History original.collected work seen visits) (empty : original.visited=#[])
    (query : E1M1QuerySource.visitHits original (fun _ _ => true)=.ok path)
    (next : E1M1AimActorRejectCycle.Next s original.collected work seen resolve portals distance thing.shootHeight out) :
    Boundary s scene shooter thing path original distance work seen resolve portals lower upper log out := by
  rcases next with exhausted|⟨best,chosen,far,pc,_⟩|⟨fraction,j,selection,persistent⟩
  · have done := E1M1AimPathBridge.finished scene shooter thing path original distance lower upper log
      work seen visits history empty (Or.inl exhausted.1) query
    have pc : out.pc=0x2c887 := by
      have counter := exhausted.2.2
      rw [exhausted.2.1] at counter
      exact (congrArg X86Control.State.pc exhausted.2.1).trans (exhausted_pc _ counter)
    exact Or.inl ⟨pc,done⟩
  · exact Or.inl ⟨pc,E1M1AimPathBridge.finished scene shooter thing path original distance lower upper log
      work seen visits history empty (Or.inr ⟨best,chosen,far⟩) query⟩
  · have hit := E1M1AimPathBridge.selected original path work seen visits resolve 0x2b760 (s.regs 4+4)
      out fraction j history selection empty query
    exact Or.inr ⟨fraction,j,selection,persistent,hit.1,hit.2.1⟩

theorem bottom_rejected (s : X86Memory.State) (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path original : PathResult) (distance : Fixed) (work : Array Intercept) (seen : List Nat)
    (visits : Array Intercept) (resolve : Intercept → Word) (portals : Nat → Option Portal)
    (lower upper : Fixed) (log : Array AutoAim.Portal) (out : X86Control.State)
    (history : History original.collected work seen visits) (empty : original.visited=#[])
    (query : E1M1QuerySource.visitHits original (fun _ _ => true)=.ok path)
    (next : E1M1AimActorBottomCycle.Next s original.collected work seen resolve portals distance thing.shootHeight out) :
    Boundary s scene shooter thing path original distance work seen resolve portals lower upper log out := by
  rcases next with exhausted|⟨best,chosen,far,pc,_⟩|⟨fraction,j,selection,persistent⟩
  · have done := E1M1AimPathBridge.finished scene shooter thing path original distance lower upper log
      work seen visits history empty (Or.inl exhausted.1) query
    have pc : out.pc=0x2c887 := by
      have counter := exhausted.2.2
      rw [exhausted.2.1] at counter
      exact (congrArg X86Control.State.pc exhausted.2.1).trans (exhausted_pc _ counter)
    exact Or.inl ⟨pc,done⟩
  · exact Or.inl ⟨pc,E1M1AimPathBridge.finished scene shooter thing path original distance lower upper log
      work seen visits history empty (Or.inr ⟨best,chosen,far⟩) query⟩
  · have hit := E1M1AimPathBridge.selected original path work seen visits resolve 0x2b760 (s.regs 4+4)
      out fraction j history selection empty query
    exact Or.inr ⟨fraction,j,selection,persistent,hit.1,hit.2.1⟩

/-- A specified next minimum recovers a reusable callback, regardless of which
actor branch produced the common boundary. -/
theorem next_callback (s : X86Memory.State) (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path original : PathResult) (distance : Fixed) (work : Array Intercept) (seen : List Nat)
    (visits : Array Intercept) (resolve : Intercept → Word) (portals : Nat → Option Portal)
    (lower upper : Fixed) (log : Array AutoAim.Portal) (out : X86Control.State)
    (history : History original.collected work seen visits) (empty : original.visited=#[])
    (query : E1M1QuerySource.visitHits original (fun _ _ => true)=.ok path)
    (boundary : Boundary s scene shooter thing path original distance work seen resolve portals lower upper log out)
    (fraction : Int32) (j : Nat)
    (chosen : E1M1InterceptMinimum.minimum work=.ok (fraction,some j)) (within : ¬fraction>65536) :
    Selection original.collected work seen resolve 0x2b760 (s.regs 4+4) out fraction j ∧
    Persistent out.core original.collected work resolve portals distance thing.shootHeight ∧
    seen.length<path.visited.size ∧ path.visited[seen.length]! = work[j]! := by
  rcases boundary with finished|⟨actual,k,selection,persistent,inside,hit⟩
  · have next := E1M1AimPathOrder.next_hit original path work seen visits history fraction j chosen within query
    simp only [empty,Array.size_empty,Nat.zero_add] at next
    have size := finished.2.1
    omega
  · have pair := Except.ok.inj (selection.chosen.symm.trans chosen)
    have fractionEq : actual=fraction := congrArg Prod.fst pair
    have indexEq : k=j := Option.some.inj (congrArg Prod.snd pair)
    subst actual
    subst k
    exact ⟨selection,persistent,inside,hit⟩
theorem line_boundary (s : X86Memory.State) (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path original : PathResult) (distance : Fixed) (work : Array Intercept) (seen : List Nat)
    (visits : Array Intercept) (resolve : Intercept → Word) (portals : Nat → Option Portal)
    (lower upper : Fixed) (log : Array AutoAim.Portal) (out : X86Control.State)
    (history : History original.collected work seen visits) (empty : original.visited=#[])
    (query : E1M1QuerySource.visitHits original (fun _ _ => true)=.ok path)
    (boundary : Boundary s scene shooter thing path original distance work seen resolve portals lower upper log out)
    (fraction : Int32) (j : Nat)
    (chosen : E1M1InterceptMinimum.minimum work=.ok (fraction,some j)) (within : ¬fraction>65536) :
    E1M1AimSynchronizedCycle.AlignedNext s scene shooter thing path original distance work seen
      resolve portals lower upper log out := by
  obtain ⟨selection,persistent,inside,hit⟩ := next_callback s scene shooter thing path original distance
    work seen visits resolve portals lower upper log out history empty query boundary fraction j chosen within
  exact ⟨Or.inr (Or.inr ⟨fraction,j,selection,persistent⟩),
    Or.inr ⟨fraction,j,selection,persistent,inside,hit⟩⟩

end Doom.Proofs.E1M1AimActorBoundary
