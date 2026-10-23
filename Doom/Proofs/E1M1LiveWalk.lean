import Doom.Proofs.E1M1LoopReplay
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1LiveWalk
open Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1CellWalk (grid)
open E1M1MixedCellWalk (inside Admitted Images budget bound history)
open E1M1GridRoute (sourceRoute)
attribute [local irreducible] load32

/-- The source loop exposed by `E1M1TraversalLoop.live_aiming`, with its numeric
parameters decoded from the DOS gate. This is the actual finite Int32 loop. -/
def source (scene : Collision.Scene) (trace : Collision.Divline) (fuel : Nat)
    (g : E1M1PathAdvance.Cell) (seen : Array Bool) (r : Collision.PathResult) :=
  E1M1TraversalLoop.walk E1M1TraversalSource.aimingScan 3 fuel scene trace
    (Int32.ofBitVec g.endX) (Int32.ofBitVec g.endY)
    (Int32.ofBitVec g.xDirection) (Int32.ofBitVec g.yDirection)
    ⟨Int32.ofBitVec g.xStride⟩ ⟨Int32.ofBitVec g.yStride⟩ (E1M1LoopReplay.pack g seen r)

/-- Continuous DOS collection-loop execution agrees with the loop inside the live
Lean aiming traversal, including the final numeric state and no early return.
Query-entry initialization and reachable encodings/capacity are still separate. -/
theorem execution (q : Context) (pick : Int32 → Int32 → Cell)
    (s : X86Control.State) (r : Collision.PathResult) (seen : Array Bool) (n : Nat)
    (legal : n<64) (counter : (E1M1PathAdvance.observe s.core).count=BitVec.ofNat 32 n)
    (common : Common q) (height : q.world.grid.height=q.height)
    (statics : ∀ c∈sourceRoute pick (64-n) (E1M1PathAdvance.observe s.core), Admitted q c)
    (scenes : ∀ c∈sourceRoute pick (64-n) (E1M1PathAdvance.observe s.core),
      inside q c=true → E1M1CellLineSource.SceneLines q c)
    (state : State q s r seen)
    (images : Images q (sourceRoute pick (64-n) (E1M1PathAdvance.observe s.core)) s.core.memory)
    (entry : s.pc=0x2ca7f)
    (room : r.collected.size+budget q (sourceRoute pick (64-n) (E1M1PathAdvance.observe s.core))≤128) :
    let cells := sourceRoute pick (64-n) (E1M1PathAdvance.observe s.core)
    cells≠[] ∧ cells.length≤64-n ∧
    ∃ out after, (∃ steps≤bound q cells,
      X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] steps s out) ∧
      source q.world q.trace (64-n) (E1M1PathAdvance.observe s.core) seen r=
        .ok (E1M1LoopReplay.pack (E1M1PathAdvance.observe out.core) (history q seen cells) after) ∧
      State q out after (history q seen cells) ∧
      after.collected.size≤r.collected.size+budget q cells ∧
      E1M1PathAdvance.observe out.core=grid (E1M1PathAdvance.observe s.core) cells ∧
      out.pc=0x2cafd ∧
      E1M1CellMapInvariant.Frame q.sp q.lines s.core.memory out.core.memory ∧
      Images q cells out.core.memory := by
  obtain ⟨nonempty,length,out,after,run,collection,outState,size,obs,pc,frame,outImages⟩ :=
    E1M1GeneratedWalk.execution q pick s r seen n legal counter common height statics scenes state images entry room
  refine ⟨nonempty,length,out,after,run,?_,outState,size,obs,pc,frame,outImages⟩
  unfold source
  rw [E1M1LoopReplay.walk_replay q.world q.trace pick,collection,Except.map,←obs]
end Doom.Proofs.E1M1LiveWalk
