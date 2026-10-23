import Doom.Proofs.E1M1AimStampWalk
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimStampLiveWalk
open Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1CellWalk (Follows grid stopPc)
open E1M1MixedCellWalk (inside Admitted Images cost instructions budget bound visits history)
open E1M1CollectionLog (log state_log)
open E1M1LoggedCell (prepare)
open E1M1GridRoute (sourceRoute)
attribute [local irreducible] load32

/-- Retain exact stamps while matching the source cell logs in their original order. -/
theorem logged_one (q : Context) (c : Cell) (s : X86Control.State) (r : Collision.PathResult) (seen : Array Bool)
    (common : Common q) (height : q.world.grid.height=q.height)
    (static : Admitted q c) (scene : inside q c=true → E1M1CellLineSource.SceneLines q c)
    (state : State q s r seen) (images : Images q [c] s.core.memory) (pc : s.pc=0x2ca7f)
    (x : (E1M1PathAdvance.observe s.core).mapX=c.x.toBitVec)
    (y : (E1M1PathAdvance.observe s.core).mapY=c.y.toBitVec)
    (room : r.collected.size+cost q c≤128)
    (origin : Memory) (image : E1M1AimStampImage.Image origin s.core.memory q.lines q.epoch seen) :
    let out := E1M1LoggedCell.next q c s r
    ∃ after, E1M1LoggedCell.collect q.trace q.world c.x c.y seen r=.ok (visits q c seen,after) ∧
      (∃ n≤instructions q c, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
      State q out after (visits q c seen) ∧
      after.collected.size≤r.collected.size+cost q c ∧
      E1M1PathAdvance.observe out.core=E1M1PathAdvance.step (E1M1PathAdvance.observe s.core) ∧
      out.pc=E1M1PathAdvance.nextPc (E1M1PathAdvance.observe s.core) ∧
      E1M1CellMapInvariant.Frame q.sp q.lines s.core.memory out.core.memory ∧
      E1M1AimStampImage.Image origin out.core.memory q.lines q.epoch (visits q c seen) := by
  have lineState := state_log q s r seen (true,c.x,c.y) state
  have bothState := state_log q s _ seen (false,c.x,c.y) lineState
  obtain ⟨after,production,run,outState,used,obs,outPC,frame,stampImage⟩ :=
    E1M1AimStampWalk.one q c s (prepare c r) seen common static bothState images pc x y room origin image
  refine ⟨after,?_,run,outState,used,obs,outPC,frame,stampImage⟩
  cases yes : inside q c with
  | false =>
    have eq : after=prepare c r := by simpa [E1M1MixedCellWalk.CellResult,yes] using production
    simp only [E1M1LoggedCell.collect,common.dimension,height,show Collision.pathCellInside c.x c.y q.width q.height=false from yes,
      Bool.false_eq_true,ite_false,visits,yes]
    rw [eq]
    rfl
  | true =>
    have st := static yes
    have lineRoom : r.collected.size+c.cell.ids.length≤128 := by
      have total : r.collected.size+(c.cell.ids.length+c.nodes.length)≤128 := by
        simpa only [cost,yes,ite_true,E1M1CellWalkInvariant.cost] using room
      omega
    have linesOne := E1M1CellLineSource.lines q c s _ seen common st lineState
      (images c (by simp) yes) pc x y lineRoom (scene yes)
    have linesBoth := E1M1CellLineSource.lines q c s (prepare c r) seen common st bothState
      (images c (by simp) yes) pc x y lineRoom (scene yes)
    have commute := E1M1CollectionLog.line_log (false,c.x,c.y) q.trace q.world.lines c.cell.ids.toArray seen (log (true,c.x,c.y) r)
    change E1M1LineSourceLoop.lineCell q.trace q.world.lines c.cell.ids.toArray seen (prepare c r)=_ at commute
    rw [linesBoth,linesOne] at commute
    have logged : E1M1CellWalk.lineResult q c s (prepare c r)=
        log (false,c.x,c.y) (E1M1CellWalk.lineResult q c s (log (true,c.x,c.y) r)) :=
      congrArg Prod.snd (Except.ok.inj commute)
    have objects : E1M1FiringThings.sceneCell q.trace q.world c.x c.y
        (log (false,c.x,c.y) (E1M1CellWalk.lineResult q c s (log (true,c.x,c.y) r)))=.ok after := by
      rw [← logged]
      simpa [E1M1MixedCellWalk.CellResult,yes] using production
    simp only [E1M1LoggedCell.collect,common.dimension,height,show Collision.pathCellInside c.x c.y q.width q.height=true from yes,
      ite_true,(scene yes).ids,E1M1PathMap.live_visits q.words c.cell st.valid,linesOne,Bind.bind,Except.bind,objects,
      visits,yes]
    rfl

/-- Compose the logged cells and their exact images at the same reached state. -/
theorem logged (q : Context) (cells : List Cell) (s : X86Control.State)
    (r : Collision.PathResult) (seen : Array Bool)
    (common : Common q) (height : q.world.grid.height=q.height)
    (statics : ∀ c∈cells, Admitted q c)
    (scenes : ∀ c∈cells, inside q c=true → E1M1CellLineSource.SceneLines q c)
    (state : State q s r seen) (images : Images q cells s.core.memory)
    (entry : cells≠[] → s.pc=0x2ca7f) (follows : Follows (E1M1PathAdvance.observe s.core) cells)
    (room : r.collected.size+budget q cells≤128)
    (origin : Memory) (image : E1M1AimStampImage.Image origin s.core.memory q.lines q.epoch seen) :
    ∃ out after, (∃ n≤bound q cells, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
      E1M1LoggedWalk.collect q.trace q.world cells seen r=.ok (history q seen cells,after) ∧
      State q out after (history q seen cells) ∧
      after.collected.size≤r.collected.size+budget q cells ∧
      E1M1PathAdvance.observe out.core=grid (E1M1PathAdvance.observe s.core) cells ∧
      out.pc=stopPc s.pc (E1M1PathAdvance.observe s.core) cells ∧
      E1M1CellMapInvariant.Frame q.sp q.lines s.core.memory out.core.memory ∧
      Images q cells out.core.memory ∧
      E1M1AimStampImage.Image origin out.core.memory q.lines q.epoch (history q seen cells) := by
  induction cells generalizing s r seen with
  | nil =>
    exact ⟨s,r,⟨0,by simp [bound],.nil _⟩,rfl,state,by simp [budget],rfl,rfl,
      fun _ _ => rfl,images,image⟩
  | cons c rest ih =>
    obtain ⟨x,y,continues,followsTail⟩ := follows
    have cellRoom : r.collected.size+cost q c≤128 := by
      simp only [budget,List.map_cons,List.sum_cons] at room; omega
    obtain ⟨middle,production,⟨n,hn,run⟩,middleState,used,obs,outPC,frame,middleImage⟩ :=
      logged_one q c s r seen common height (statics c (by simp)) (scenes c (by simp))
        state (fun d hd => images d (by simp_all)) (entry (by simp)) x y cellRoom origin image
    have allImages := E1M1MixedCellWalk.images_transport q (c::rest) _ _ statics images frame
    have remaining : middle.collected.size+budget q rest≤128 := by
      simp only [budget,List.map_cons,List.sum_cons] at room ⊢; omega
    obtain ⟨out,after,⟨m,hm,tailRun⟩,collection,outState,total,outObs,finalPC,tailFrame,_,finalImage⟩ :=
      ih (E1M1LoggedCell.next q c s r) middle (visits q c seen)
        (fun d hd => statics d (by simp [hd])) (fun d hd => scenes d (by simp [hd]))
        middleState (fun d hd => allImages d (by simp [hd]))
        (fun nonempty => outPC.trans (continues nonempty))
        (by rw [obs]; exact followsTail) remaining middleImage
    have joined := E1M1CellMapInvariant.frame_trans q.sp q.lines _ _ _ frame tailFrame
    refine ⟨out,after,⟨n+m,?_,E1M1PspriteStep.prefix_trans run tailRun⟩,
      ?_,outState,?_,?_,?_,joined,E1M1MixedCellWalk.images_transport q (c::rest) _ _ statics images joined,finalImage⟩
    · simpa only [bound,List.map_cons,List.sum_cons] using Nat.add_le_add hn hm
    · simpa only [E1M1LoggedWalk.collect,production,Bind.bind,Except.bind,history] using collection
    · simp only [budget,List.map_cons,List.sum_cons] at total ⊢; omega
    · simpa only [grid,obs] using outObs
    · simpa only [stopPc,outPC,obs] using finalPC

/-- Derive the itinerary and exit from the numeric state; no supplied route remains. -/
theorem generated (q : Context) (pick : Int32 → Int32 → Cell)
    (s : X86Control.State) (r : Collision.PathResult) (seen : Array Bool) (n : Nat)
    (legal : n<64) (counter : (E1M1PathAdvance.observe s.core).count=BitVec.ofNat 32 n)
    (common : Common q) (height : q.world.grid.height=q.height)
    (statics : ∀ c∈sourceRoute pick (64-n) (E1M1PathAdvance.observe s.core), Admitted q c)
    (scenes : ∀ c∈sourceRoute pick (64-n) (E1M1PathAdvance.observe s.core),
      inside q c=true → E1M1CellLineSource.SceneLines q c)
    (state : State q s r seen)
    (images : Images q (sourceRoute pick (64-n) (E1M1PathAdvance.observe s.core)) s.core.memory)
    (entry : s.pc=0x2ca7f)
    (room : r.collected.size+budget q (sourceRoute pick (64-n) (E1M1PathAdvance.observe s.core))≤128)
    (origin : Memory) (image : E1M1AimStampImage.Image origin s.core.memory q.lines q.epoch seen) :
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
      Images q cells out.core.memory ∧
      E1M1AimStampImage.Image origin out.core.memory q.lines q.epoch (history q seen cells) := by
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
  obtain ⟨out,after,run,collection,outState,size,obs,pc,frame,outImages,stampImage⟩ :=
    logged q _ s r seen common height statics scenes state images
      (fun _ => entry) follows room origin image
  exact ⟨nonempty,length,out,after,run,collection,outState,size,obs,pc.trans exit,frame,outImages,stampImage⟩

/-- Match the actual finite source collection loop, retaining exact stamp values. -/
theorem live (q : Context) (pick : Int32 → Int32 → Cell)
    (s : X86Control.State) (r : Collision.PathResult) (seen : Array Bool) (n : Nat)
    (legal : n<64) (counter : (E1M1PathAdvance.observe s.core).count=BitVec.ofNat 32 n)
    (common : Common q) (height : q.world.grid.height=q.height)
    (statics : ∀ c∈sourceRoute pick (64-n) (E1M1PathAdvance.observe s.core), Admitted q c)
    (scenes : ∀ c∈sourceRoute pick (64-n) (E1M1PathAdvance.observe s.core),
      inside q c=true → E1M1CellLineSource.SceneLines q c)
    (state : State q s r seen)
    (images : Images q (sourceRoute pick (64-n) (E1M1PathAdvance.observe s.core)) s.core.memory)
    (entry : s.pc=0x2ca7f)
    (room : r.collected.size+budget q (sourceRoute pick (64-n) (E1M1PathAdvance.observe s.core))≤128)
    (origin : Memory) (image : E1M1AimStampImage.Image origin s.core.memory q.lines q.epoch seen) :
    let cells := sourceRoute pick (64-n) (E1M1PathAdvance.observe s.core)
    cells≠[] ∧ cells.length≤64-n ∧
    ∃ out after, (∃ steps≤bound q cells,
      X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] steps s out) ∧
      E1M1LiveWalk.source q.world q.trace (64-n) (E1M1PathAdvance.observe s.core) seen r=
        .ok (E1M1LoopReplay.pack (E1M1PathAdvance.observe out.core) (history q seen cells) after) ∧
      State q out after (history q seen cells) ∧
      after.collected.size≤r.collected.size+budget q cells ∧
      E1M1PathAdvance.observe out.core=grid (E1M1PathAdvance.observe s.core) cells ∧
      out.pc=0x2cafd ∧
      E1M1CellMapInvariant.Frame q.sp q.lines s.core.memory out.core.memory ∧
      Images q cells out.core.memory ∧
      E1M1AimStampImage.Image origin out.core.memory q.lines q.epoch (history q seen cells) := by
  obtain ⟨nonempty,length,out,after,run,collection,outState,size,obs,pc,frame,outImages,stampImage⟩ :=
    generated q pick s r seen n legal counter common height statics scenes state images entry room origin image
  refine ⟨nonempty,length,out,after,run,?_,outState,size,obs,pc,frame,outImages,stampImage⟩
  unfold E1M1LiveWalk.source
  rw [E1M1LoopReplay.walk_replay q.world q.trace pick,collection,Except.map,←obs]
end Doom.Proofs.E1M1AimStampLiveWalk
