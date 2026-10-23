import Doom.Proofs.E1M1GridRoute
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1GeneratedWalk
open Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1CellWalk (grid)
open E1M1MixedCellWalk (inside Admitted Images budget bound history)
open E1M1GridRoute (sourceRoute)
attribute [local irreducible] load32

/-- The numeric gate state determines the route; no supplied itinerary or Follows
premise remains. Metadata, source-scene encodings and aggregate space are still
explicit obligations over the generated route. The execution reaches the actual
DOS loop exit and agrees with logged source collection along that route. -/
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
      E1M1LoggedWalk.collect q.trace q.world cells seen r=.ok (history q seen cells,after) ∧
      State q out after (history q seen cells) ∧
      after.collected.size≤r.collected.size+budget q cells ∧
      E1M1PathAdvance.observe out.core=grid (E1M1PathAdvance.observe s.core) cells ∧
      out.pc=0x2cafd ∧
      E1M1CellMapInvariant.Frame q.sp q.lines s.core.memory out.core.memory ∧
      Images q cells out.core.memory := by
  have eqRoute := E1M1GridRoute.source_eq pick (64-n) n (E1M1PathAdvance.observe s.core) legal rfl counter
  have follows := E1M1GridRoute.follows pick (64-n) (E1M1PathAdvance.observe s.core)
  rw [eqRoute] at follows
  have length := E1M1GridRoute.length_bound pick (64-n) (E1M1PathAdvance.observe s.core)
  rw [eqRoute] at length
  have nonempty : sourceRoute pick (64-n) (E1M1PathAdvance.observe s.core)≠[] := by
    rw [←eqRoute]
    obtain ⟨fuel,hfuel⟩ : ∃ fuel,64-n=fuel+1 := ⟨64-n-1,by omega⟩
    rw [hfuel]
    exact E1M1GridRoute.nonempty pick fuel _
  have exit := E1M1GridRoute.exits pick (64-n) n s.pc (E1M1PathAdvance.observe s.core) legal rfl counter
  rw [eqRoute] at exit
  obtain ⟨out,after,run,collection,outState,size,obs,pc,frame,outImages⟩ :=
    E1M1LoggedWalk.execution q _ s r seen common height statics scenes state images
      (fun _ => entry) follows room
  exact ⟨nonempty,length,out,after,run,collection,outState,size,obs,pc.trans exit,frame,outImages⟩
end Doom.Proofs.E1M1GeneratedWalk
