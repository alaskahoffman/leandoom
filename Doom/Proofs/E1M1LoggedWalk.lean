import Doom.Proofs.E1M1LoggedCell
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1LoggedWalk
open Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1CellWalk (Follows grid stopPc)
open E1M1MixedCellWalk (inside Admitted Images cost instructions budget bound visits history)
attribute [local irreducible] load32

/-- Execute source collection operations for a supplied coordinate itinerary.
This does not construct the itinerary or perform ordered hit visitation. -/
def collect (trace : Collision.Divline) (world : Collision.Scene) :
    List Cell → Array Bool → Collision.PathResult → Except String (Array Bool × Collision.PathResult)
  | [],seen,r => .ok (seen,r)
  | c::rest,seen,r => do
      let (seen,r) ← E1M1LoggedCell.collect trace world c.x c.y seen r
      collect trace world rest seen r

/-- A continuous DOS prefix now agrees with executable source collection over
the same admitted itinerary, including logs and persistent visit history. All
future images and all capacity come from the initial state and one total budget. -/
theorem execution (q : Context) (cells : List Cell) (s : X86Control.State)
    (r : Collision.PathResult) (seen : Array Bool)
    (common : Common q) (height : q.world.grid.height=q.height)
    (statics : ∀ c∈cells, Admitted q c)
    (scenes : ∀ c∈cells, inside q c=true → E1M1CellLineSource.SceneLines q c)
    (state : State q s r seen) (images : Images q cells s.core.memory)
    (entry : cells≠[] → s.pc=0x2ca7f) (follows : Follows (E1M1PathAdvance.observe s.core) cells)
    (room : r.collected.size+budget q cells≤128) :
    ∃ out after, (∃ n≤bound q cells, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
      collect q.trace q.world cells seen r=.ok (history q seen cells,after) ∧
      State q out after (history q seen cells) ∧
      after.collected.size≤r.collected.size+budget q cells ∧
      E1M1PathAdvance.observe out.core=grid (E1M1PathAdvance.observe s.core) cells ∧
      out.pc=stopPc s.pc (E1M1PathAdvance.observe s.core) cells ∧
      E1M1CellMapInvariant.Frame q.sp q.lines s.core.memory out.core.memory ∧
      Images q cells out.core.memory := by
  induction cells generalizing s r seen with
  | nil =>
    exact ⟨s,r,⟨0,by simp [bound],.nil _⟩,rfl,state,by simp [budget],rfl,rfl,
      fun _ _ => rfl,images⟩
  | cons c rest ih =>
    obtain ⟨x,y,continues,followsTail⟩ := follows
    have cellRoom : r.collected.size+cost q c≤128 := by
      simp only [budget,List.map_cons,List.sum_cons] at room; omega
    obtain ⟨middle,production,⟨n,hn,run⟩,middleState,used,obs,outPC,frame⟩ :=
      E1M1LoggedCell.one q c s r seen common height (statics c (by simp)) (scenes c (by simp))
        state (fun d hd => images d (by simp_all)) (entry (by simp)) x y cellRoom
    have allImages := E1M1MixedCellWalk.images_transport q (c::rest) _ _ statics images frame
    have remaining : middle.collected.size+budget q rest≤128 := by
      simp only [budget,List.map_cons,List.sum_cons] at room ⊢; omega
    obtain ⟨out,after,⟨m,hm,tailRun⟩,collection,outState,total,outObs,finalPC,tailFrame,_⟩ :=
      ih (E1M1LoggedCell.next q c s r) middle (visits q c seen)
        (fun d hd => statics d (by simp [hd])) (fun d hd => scenes d (by simp [hd]))
        middleState (fun d hd => allImages d (by simp [hd]))
        (fun nonempty => outPC.trans (continues nonempty))
        (by rw [obs]; exact followsTail) remaining
    have joined := E1M1CellMapInvariant.frame_trans q.sp q.lines _ _ _ frame tailFrame
    refine ⟨out,after,⟨n+m,?_,E1M1PspriteStep.prefix_trans run tailRun⟩,
      ?_,outState,?_,?_,?_,joined,E1M1MixedCellWalk.images_transport q (c::rest) _ _ statics images joined⟩
    · simpa only [bound,List.map_cons,List.sum_cons] using Nat.add_le_add hn hm
    · simpa only [collect,production,Bind.bind,Except.bind,history] using collection
    · simp only [budget,List.map_cons,List.sum_cons] at total ⊢; omega
    · simpa only [grid,obs] using outObs
    · simpa only [stopPc,outPC,obs] using finalPC
end Doom.Proofs.E1M1LoggedWalk
