import Doom.Proofs.E1M1AimHitOutcome
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimOrderedLoop
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMinimum (minimum)
open E1M1AimCatalog (Portal)
open E1M1AimSourceCatalog (Represents)
open E1M1AimIteration
open E1M1AimActorBoundary (Boundary)
open E1M1AimPortalPrefix (Position)
open E1M1AimActorSelect (program)
open E1M1AimHitOutcome (Arithmetic Exit Outcome)
open E1M1AimMixedExit (Ready)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- Explicit uniform arithmetic obligation over admitted histories/windows.
This is stronger than availability only along one actual play trace. It supplies
source division facts, never a branch outcome or machine execution. Establishing
it (or replacing it by a reachable-state invariant) remains a separate task. -/
def Available (scene : Scene) (shooter : Nat) (initial : Array Intercept)
    (portals : Nat → Option Portal) (distance z : Fixed) : Prop :=
  ∀ (a : Position) (seen : List Nat) (visits : Array Intercept), History initial a.work seen visits →
    ∀ fraction j, minimum a.work=.ok (fraction,some j) → ¬fraction>65536 →
      Nonempty (Arithmetic scene shooter portals distance z a j)

/-- Termination and exhaustive correspondence from an established callback/exit
boundary. Each continuing callback consumes one distinct record. There is no
source Sequence, final branch, selected target, or future machine state premise. -/
theorem execution (scene : Scene) (shooter : Nat) (thing : SolidThing) (path original : PathResult)
    (distance : Fixed) (resolve : Intercept → Word) (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (represented : Represents scene original.collected portals)
    (wallMap : E1M1AimWallCatalog.Represents scene original.collected walls)
    (covered : E1M1AimLineCoverage.Coverage original.collected walls portals)
    (empty : original.visited=#[]) (query : E1M1QuerySource.visitHits original (fun _ _ => true)=.ok path)
    (available : Available scene shooter original.collected portals distance thing.shootHeight)
    (fuel : Nat) (a : Position) (origin : X86Memory.State) (s : X86Control.State)
    (seen : List Nat) (visits : Array Intercept)
    (budget : fuel=original.collected.size-seen.length)
    (history : History original.collected a.work seen visits)
    (boundary : Boundary origin scene shooter thing path original distance a.work seen resolve portals a.lower a.upper a.log s)
    (bottom : load32 s.core.memory (0x2c1e4#32)=a.lower.raw.toBitVec)
    (top : load32 s.core.memory (0x2c1e8#32)=a.upper.raw.toBitVec)
    (ready : Ready s.core scene shooter original.collected a.work resolve who
      (fun state => E1M1AimWallCatalog.Catalog state original.collected resolve walls)) :
    ∃ n≤fuel*(157+7*original.collected.size), ∃ out answer,
      X86CodeMemory.Prefix FloorCaller.cm program [] n s out ∧ Exit original.collected resolve out answer ∧
      remaining scene shooter thing path distance
        (List.range' seen.length (path.visited.size-seen.length)) a.lower a.upper a.log=.ok answer := by
  induction fuel using Nat.strongRecOn generalizing a origin s seen visits with
  | ind fuel ih =>
    rcases boundary with terminal|⟨fraction,j,selection,persistent,inside,hit⟩
    · exact ⟨0,by omega,s,{path},.nil _,⟨Or.inl terminal.1,by intro id h; cases h⟩,terminal.2.2⟩
    · obtain ⟨arithmetic⟩ := available a seen visits history fraction j selection.chosen selection.within
      obtain ⟨actors,wallsBefore⟩ := ready fraction j selection.chosen selection.within
      have pc : s.pc=0x2b760 := selection.ready.pc
      have atCallback : s=⟨s.core,s.flags,0x2b760⟩ := by cases s; simp_all
      have selected : Selection original.collected a.work seen resolve 0x2b760 (origin.regs 4+4)
          ⟨s.core,s.flags,0x2b760⟩ fraction j := by rw [← atCallback]; exact selection
      obtain ⟨n,hn,middle,run,outcome⟩ := E1M1AimHitOutcome.execution scene shooter thing path original distance resolve
        portals walls who represented wallMap covered empty query a s.core s.flags seen visits (origin.regs 4+4) fraction j
        history selected persistent bottom top actors wallsBefore arithmetic
      rw [← atCallback] at run
      have size := (E1M1SelectionHistory.image history).size
      have positive := E1M1TraversalBudget.remaining_step history fraction j selection.chosen selection.within
      rcases outcome with ⟨answer,exit,source⟩|⟨b,work,advanced,nextBoundary,low,high,frame,source⟩
      · have bound : 157+7*original.collected.size≤fuel*(157+7*original.collected.size) := by
          calc
            _ = 1*(157+7*original.collected.size) := by omega
            _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
        exact ⟨n,by omega,middle,answer,run,exit,source⟩
      · have nextReady : Ready middle.core scene shooter original.collected b.work resolve who
            (fun state => E1M1AimWallCatalog.Catalog state original.collected resolve walls) := by
          intro nextFraction k chosen within
          have next := E1M1AimActorBoundary.next_callback s.core scene shooter thing path original distance b.work (j::seen)
            (visits.push a.work[j]!) resolve portals b.lower b.upper b.log middle advanced empty query nextBoundary nextFraction k chosen within
          have stack := E1M1AimCycleInvariant.stack s.core original.collected b.work (j::seen) resolve 0x2b760 middle nextFraction k next.1
          have bound : j<128 := by have := selection.inside; have := persistent.bounded; omega
          have pointer := selection.ready.pointer.trans selection.argument
          exact ⟨E1M1AimActorCatalog.preserved s.core middle j scene shooter original.collected resolve who
            frame stack pointer bound actors,E1M1AimWallCatalog.preserved s.core middle j original.collected resolve walls
            frame stack pointer bound wallsBefore⟩
        have decrease : original.collected.size-(j::seen).length<fuel := by omega
        obtain ⟨m,hm,out,answer,tail,exit,sourceTail⟩ := ih _ decrease b s.core middle (j::seen) (visits.push a.work[j]!)
          rfl advanced nextBoundary low high nextReady
        refine ⟨n+m,?_,out,answer,E1M1PspriteStep.prefix_trans run tail,exit,?_⟩
        · have eq : fuel=(original.collected.size-(j::seen).length)+1 := by omega
          rw [eq,Nat.add_mul,Nat.one_mul]; omega
        · exact source.trans (by simpa only [List.length_cons] using sourceTail)
end Doom.Proofs.E1M1AimOrderedLoop
