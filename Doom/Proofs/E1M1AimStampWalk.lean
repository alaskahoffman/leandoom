import Doom.Proofs.E1M1AimStampCell
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimStampWalk
open Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant (Context Cell Common)
open E1M1CellWalk (Follows grid stopPc)
open E1M1MixedCellWalk (Admitted Images cost instructions budget bound next visits history CellResult Collection images_transport inside)
attribute [local irreducible] load32

/-- Outside bounds returns and the grid step preserve every line-stamp word. -/
theorem outside (q : Context) (s : X86Control.State) (r : Collision.PathResult) (seen : Array Bool)
    (common : Common q) (state : E1M1CellWalkInvariant.State q s r seen)
    (pc : s.pc=0x2ca7f) (x y : Int32)
    (mapX : s.core.regs 6=x.toBitVec) (mapY : s.core.regs 1=y.toBitVec)
    (outMap : Collision.pathCellInside x y q.width q.height=false)
    (origin : Memory) (image : E1M1AimStampImage.Image origin s.core.memory q.lines q.epoch seen) :
    let out := E1M1OutsideCell.result s
    (∃ n≤71, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
    E1M1CellWalkInvariant.State q out r seen ∧
    E1M1PathAdvance.observe out.core=E1M1PathAdvance.step (E1M1PathAdvance.observe s.core) ∧
    out.pc=E1M1PathAdvance.nextPc (E1M1PathAdvance.observe s.core) ∧
    E1M1CellMapInvariant.Frame q.sp q.lines s.core.memory out.core.memory ∧
    E1M1AimStampImage.Image origin out.core.memory q.lines q.epoch seen := by
  obtain ⟨⟨n,hn,lineRun⟩,linePC,lineOk,lineSP,lineObs,lineFrame⟩ :=
    E1M1OutsideLine.execution q s x y common state.stack state.maps pc mapX mapY outMap
  have lineState := E1M1OutsideCell.state_reads q s _ r seen common state lineSP (fun a safe => E1M1OutsideLine.read_word s q.sp a state.stack safe)
  obtain ⟨⟨m,hm,objectRun⟩,objectPC,objectOk,objectState,objectObs,objectFrame⟩ :=
    E1M1OutsideCell.objects q _ r seen common lineState linePC lineOk x y
      ((congrArg E1M1PathAdvance.Cell.mapX lineObs).trans mapX)
      ((congrArg E1M1PathAdvance.Cell.mapY lineObs).trans mapY) outMap
  have obs := objectObs.trans lineObs
  obtain ⟨⟨k,hk,advance⟩,finalSP,finalObs,finalPC,hits,visits⟩ :=
    E1M1CellBoundaryAdvance.execution _ q.sp q.lines q.epoch q.objects (E1M1PathAdvance.observe s.core) r.collected seen
      ⟨objectPC,objectOk,objectState.stack,obs,objectState.tracked,objectState.represented⟩ common.locals
      common.epochSafe.advance (fun j hj => (common.stampSafe j (by simpa only [state.size] using hj)).advance)
  have frame : E1M1CellMapInvariant.Frame q.sp q.lines s.core.memory (E1M1OutsideCell.result s).core.memory :=
    fun a safe => (E1M1CellBoundaryAdvance.frame _ q.sp objectState.stack a safe.advance).trans
      ((objectFrame a safe).trans (lineFrame a safe))
  have exactFrame (a : Word) (safe : E1M1FiringVisitedNext.TailSafe q.sp a) :
      load32 (E1M1OutsideCell.result s).core.memory a=load32 s.core.memory a :=
    (E1M1CellBoundaryAdvance.frame _ q.sp objectState.stack a safe.advance).trans
      ((E1M1CellObjectSelection.read_word _ q.sp lineSP a (safe.caller 116 (by simp))
        (safe.caller 120 (by simp))).trans (E1M1OutsideLine.read_word s q.sp a state.stack safe.caller))
  have exactImage := E1M1AimStampImage.transport origin _ _ q.lines q.epoch seen image
    (exactFrame _ common.epochSafe)
    (fun j hj => exactFrame _ (common.stampSafe j (by simpa only [state.size] using hj)))
  exact ⟨⟨n+m+k,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans lineRun objectRun) advance⟩,
    ⟨finalSP,E1M1CellMapInvariant.transport _ _ q.sp q.base q.lines q.words q.width q.height state.maps common.mapLayout frame,
      hits,visits,state.size⟩,finalObs,finalPC,frame,exactImage⟩

/-- The in-map cell theorem exposes the exact image alongside source hits. -/
theorem inside_one (q : Context) (c : Cell) (s : X86Control.State) (r : Collision.PathResult) (seen : Array Bool)
    (common : Common q) (static : E1M1CellWalkInvariant.Static q c) (state : E1M1CellWalkInvariant.State q s r seen)
    (images : E1M1CellWalkInvariant.Images q [c] s.core.memory) (pc : s.pc=0x2ca7f)
    (x : (E1M1PathAdvance.observe s.core).mapX=c.x.toBitVec)
    (y : (E1M1PathAdvance.observe s.core).mapY=c.y.toBitVec)
    (room : r.collected.size+E1M1CellWalkInvariant.cost c≤128)
    (origin : Memory) (stampImage : E1M1AimStampImage.Image origin s.core.memory q.lines q.epoch seen) :
    let out := E1M1CellWalk.next q c s r
    ∃ after, E1M1FiringThings.sceneCell q.trace q.world c.x c.y (E1M1CellWalk.lineResult q c s r)=.ok after ∧
      (∃ n≤E1M1CellWalkInvariant.instructions c, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
      E1M1CellWalkInvariant.State q out after (E1M1CellWalk.visits q c seen) ∧
      after.collected.size≤r.collected.size+E1M1CellWalkInvariant.cost c ∧
      E1M1PathAdvance.observe out.core=E1M1PathAdvance.step (E1M1PathAdvance.observe s.core) ∧
      out.pc=E1M1PathAdvance.nextPc (E1M1PathAdvance.observe s.core) ∧
      E1M1CellMapInvariant.Frame q.sp q.lines s.core.memory out.core.memory ∧
      E1M1AimStampImage.Image origin out.core.memory q.lines q.epoch (E1M1CellWalk.visits q c seen) := by
  have image := images c (by simp)
  obtain ⟨run,stack,obs,outPC,⟨after,production,size,hits⟩,represented,maps,_,_,frame,exactImage⟩ :=
    E1M1AimStampCell.gate s q.sp q.base q.lines q.epoch q.words q.width q.height q.objects q.trace c.cell c.data c.nodes r seen
      pc state.stack static.valid state.maps common.mapLayout image.1 static.payloadSafe static.contracts static.layout
      c.x c.y x y static.selected static.inside q.links image.2 static.selectionSafe state.tracked
      (E1M1CellWalkInvariant.caller_safe s.core q.sp _ state.stack common.cursor)
      (fun i hi off ho => E1M1CellWalkInvariant.caller_safe s.core q.sp _ state.stack (common.records i (by have := state.tracked.room; omega) off ho))
      (by simpa [E1M1CellWalkInvariant.cost,Nat.add_assoc] using room) state.represented state.size common.stamps common.returns
      common.epochSafe common.stampSafe common.locals q.world common.dimension static.sceneIds static.scene origin stampImage
  refine ⟨after,production,run,⟨stack,maps,⟨hits.encoded,hits.cursor,by have := hits.room; omega⟩,represented,?_⟩,
    by simpa [E1M1CellWalkInvariant.cost,Nat.add_assoc] using size,obs,outPC,frame,exactImage⟩
  simpa only [E1M1CellWalk.visits,OriginalLineVisitedRun.mark_size] using state.size

/-- Select the actual inside/outside path while keeping the same stamp origin. -/
theorem one (q : Context) (c : Cell) (s : X86Control.State) (r : Collision.PathResult) (seen : Array Bool)
    (common : Common q) (static : Admitted q c) (state : E1M1CellWalkInvariant.State q s r seen)
    (images : Images q [c] s.core.memory) (pc : s.pc=0x2ca7f)
    (x : (E1M1PathAdvance.observe s.core).mapX=c.x.toBitVec)
    (y : (E1M1PathAdvance.observe s.core).mapY=c.y.toBitVec)
    (room : r.collected.size+cost q c≤128)
    (origin : Memory) (image : E1M1AimStampImage.Image origin s.core.memory q.lines q.epoch seen) :
    let out := next q c s r
    ∃ after, CellResult q c s r after ∧
      (∃ n≤instructions q c, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
      E1M1CellWalkInvariant.State q out after (visits q c seen) ∧
      after.collected.size≤r.collected.size+cost q c ∧
      E1M1PathAdvance.observe out.core=E1M1PathAdvance.step (E1M1PathAdvance.observe s.core) ∧
      out.pc=E1M1PathAdvance.nextPc (E1M1PathAdvance.observe s.core) ∧
      E1M1CellMapInvariant.Frame q.sp q.lines s.core.memory out.core.memory ∧
      E1M1AimStampImage.Image origin out.core.memory q.lines q.epoch (visits q c seen) := by
  cases h : inside q c with
  | true =>
    simpa only [next,visits,instructions,cost,CellResult,h,ite_true] using
      inside_one q c s r seen common (static h) state (images c (by simp) h) pc x y
        (by simpa only [cost,h,ite_true] using room) origin image
  | false =>
    obtain ⟨run,outState,obs,outPC,frame,exactImage⟩ := outside q s r seen common state pc c.x c.y x y h origin image
    simp only [next,visits,instructions,cost,CellResult,h,Bool.false_eq_true,ite_false,Nat.add_zero]
    exact ⟨r,rfl,run,outState,Nat.le_refl _,obs,outPC,frame,exactImage⟩

/-- Induct across the admitted mixed itinerary. Repeated lines, outside cells,
and grid changes retain exact original words for all still-unvisited lines. -/
theorem execution (q : Context) (cells : List Cell) (s : X86Control.State)
    (r : Collision.PathResult) (seen : Array Bool)
    (common : Common q) (statics : ∀ c∈cells, Admitted q c)
    (state : E1M1CellWalkInvariant.State q s r seen) (images : Images q cells s.core.memory)
    (entry : cells≠[] → s.pc=0x2ca7f) (follows : Follows (E1M1PathAdvance.observe s.core) cells)
    (room : r.collected.size+budget q cells≤128)
    (origin : Memory) (image : E1M1AimStampImage.Image origin s.core.memory q.lines q.epoch seen) :
    ∃ out after, (∃ n≤bound q cells, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
      Collection q cells s r after ∧ E1M1CellWalkInvariant.State q out after (history q seen cells) ∧
      after.collected.size≤r.collected.size+budget q cells ∧
      E1M1PathAdvance.observe out.core=grid (E1M1PathAdvance.observe s.core) cells ∧
      out.pc=stopPc s.pc (E1M1PathAdvance.observe s.core) cells ∧
      E1M1CellMapInvariant.Frame q.sp q.lines s.core.memory out.core.memory ∧
      Images q cells out.core.memory ∧
      E1M1AimStampImage.Image origin out.core.memory q.lines q.epoch (history q seen cells) := by
  induction cells generalizing s r seen with
  | nil =>
    exact ⟨s,r,⟨0,by simp [bound],.nil _⟩,.nil s r,state,by simp [budget],rfl,rfl,
      fun _ _ => rfl,images,image⟩
  | cons c rest ih =>
    obtain ⟨x,y,continues,followsTail⟩ := follows
    have cellRoom : r.collected.size+cost q c≤128 := by
      simp only [budget,List.map_cons,List.sum_cons] at room; omega
    obtain ⟨middle,production,⟨n,hn,run⟩,middleState,used,obs,outPC,frame,middleImage⟩ :=
      one q c s r seen common (statics c (by simp)) state (fun d hd => images d (by simp_all)) (entry (by simp)) x y cellRoom origin image
    have allImages := images_transport q (c::rest) _ _ statics images frame
    have remaining : middle.collected.size+budget q rest≤128 := by
      simp only [budget,List.map_cons,List.sum_cons] at room ⊢; omega
    obtain ⟨out,after,⟨m,hm,tailRun⟩,collection,outState,total,outObs,finalPC,tailFrame,_,finalImage⟩ :=
      ih (next q c s r) middle (visits q c seen)
        (fun d hd => statics d (by simp [hd])) middleState (fun d hd => allImages d (by simp [hd]))
        (fun nonempty => outPC.trans (continues nonempty))
        (by rw [obs]; exact followsTail) remaining middleImage
    have joined := E1M1CellMapInvariant.frame_trans q.sp q.lines _ _ _ frame tailFrame
    refine ⟨out,after,⟨n+m,?_,E1M1PspriteStep.prefix_trans run tailRun⟩,
      .cons c rest s r middle after production collection,outState,?_,?_,?_,joined,
      images_transport q (c::rest) _ _ statics images joined,finalImage⟩
    · simpa only [bound,List.map_cons,List.sum_cons] using Nat.add_le_add hn hm
    · simp only [budget,List.map_cons,List.sum_cons] at total ⊢; omega
    · simpa only [grid,obs] using outObs
    · simpa only [stopPc,outPC,obs] using finalPC
/-- The same mixed-cell execution under the authenticated combined aim program
starts its exact image at entry and derives future freshness from entry words.
This is a conditional itinerary theorem, not yet a whole-query/retry theorem. -/
theorem from_entry (q : Context) (cells : List Cell) (s : X86Control.State)
    (r : Collision.PathResult) (seen : Array Bool)
    (common : Common q) (statics : ∀ c∈cells, Admitted q c)
    (state : E1M1CellWalkInvariant.State q s r seen) (images : Images q cells s.core.memory)
    (entry : cells≠[] → s.pc=0x2ca7f) (follows : Follows (E1M1PathAdvance.observe s.core) cells)
    (room : r.collected.size+budget q cells≤128) :
    ∃ out after, (∃ n≤bound q cells, X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] n s out) ∧
      Collection q cells s r after ∧ E1M1CellWalkInvariant.State q out after (history q seen cells) ∧
      after.collected.size≤r.collected.size+budget q cells ∧
      E1M1PathAdvance.observe out.core=grid (E1M1PathAdvance.observe s.core) cells ∧
      out.pc=stopPc s.pc (E1M1PathAdvance.observe s.core) cells ∧
      E1M1CellMapInvariant.Frame q.sp q.lines s.core.memory out.core.memory ∧
      Images q cells out.core.memory ∧
      E1M1AimStampImage.Image s.core.memory out.core.memory q.lines q.epoch (history q seen cells) ∧
      (E1M1AimStampImage.Fresh s.core.memory q.lines (q.epoch+1) 475 →
        E1M1AimStampImage.Fresh out.core.memory q.lines (load32 out.core.memory 0x13580+1) 475) := by
  obtain ⟨out,after,⟨n,hn,run⟩,collected,outState,size,obs,pc,frame,finalImages,exactImage⟩ :=
    execution q cells s r seen common statics state images entry follows room s.core.memory
      (E1M1AimStampImage.start s.core.memory q.lines q.epoch seen state.represented)
  have query := (run.transfer E1M1TraversalEntry.program []
    E1M1TraversalEntry.contains_collection (by simp)).transfer E1M1FirstIntercept.program []
      E1M1FirstIntercept.contains_entry (by simp)
  have linked := (X86ReturnCleanup.lift query).transfer E1M1AimProgramLink.program
    E1M1AimProgramLink.contains_query
  refine ⟨out,after,⟨n,hn,linked⟩,collected,outState,size,obs,pc,frame,finalImages,exactImage,?_⟩
  intro fresh
  have nextFresh := E1M1AimStampImage.next_fresh s.core.memory out.core.memory q.lines q.epoch
    (history q seen cells) exactImage (by simpa only [outState.size] using fresh)
  simpa only [outState.size] using nextFresh
end Doom.Proofs.E1M1AimStampWalk
