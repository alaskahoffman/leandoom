import Doom.Proofs.E1M1AimQuerySelection
import Doom.Proofs.E1M1AimOrderedCaller
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimInitialBoundary
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1AimCatalog (Portal)
open E1M1AimTraversalInvariant (Persistent)
open E1M1AimIteration
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- The initial scan's boundary uses the actual reached state as its stack
anchor. Empty input does not require inventing an earlier callback or resume. -/
theorem boundary (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path original : PathResult) (distance : Fixed) (resolve : Intercept → Word)
    (portals : Nat → Option Portal) (base : Word) (s : X86Control.State)
    (outcome : E1M1AimFirstSelection.Outcome original.collected resolve base s)
    (shape : E1M1AimStackShape.Shape base s)
    (empty : original.visited=#[])
    (query : E1M1QuerySource.visitHits original (fun _ _ => true)=.ok path)
    (persistent : s.pc=0x2b760 → Persistent s.core original.collected original.collected
      resolve portals distance thing.shootHeight) :
    E1M1AimActorBoundary.Boundary s.core scene shooter thing path original distance
      original.collected [] resolve portals aimBottomSlope aimTopSlope #[] s := by
  rcases E1M1AimFirstSelection.source original path resolve base s outcome empty query with
    ⟨pc,same,log⟩|⟨fraction,j,selected,inside,hit⟩
  · refine Or.inl ⟨pc,by simp [log],?_⟩
    simp only [List.length_nil,log,Array.size_empty,Nat.sub_zero,List.range'_zero]
    rfl
  · have pc : s.pc=0x2b760 := selected.ready.pc
    have stack := E1M1AimStackShape.live base s shape pc
    rw [←stack] at selected
    exact Or.inr ⟨fraction,j,selected,persistent pc,inside,hit⟩
end Doom.Proofs.E1M1AimInitialBoundary
