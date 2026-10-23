import Doom.Proofs.E1M1CellWalkInvariant
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1CellWalk
open Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant
open E1M1ScanContracts (candidates)
open OriginalLineVisits (markPrefix)
attribute [local irreducible] load32

def next (q : Context) (c : Cell) (s : X86Control.State) (r : Collision.PathResult) :=
  E1M1CellAdvance.result s q.lines q.trace c.cell c.data c.nodes r

def lineResult (q : Context) (c : Cell) (s : X86Control.State) (r : Collision.PathResult) :=
  let entry := E1M1PathMapCaller.scan s.core
  (E1M1NextLineScan.result entry.core q.lines q.trace c.cell c.data entry.flags r).2

def visits (q : Context) (c : Cell) (seen : Array Bool) :=
  markPrefix (candidates q.trace q.lines c.cell.ids c.data) c.cell.ids.length 0 seen

def history (q : Context) (seen : Array Bool) : List Cell → Array Bool
  | [] => seen
  | c::rest => history q (visits q c seen) rest

def grid (g : E1M1PathAdvance.Cell) : List Cell → E1M1PathAdvance.Cell
  | [] => g
  | _::rest => grid (E1M1PathAdvance.step g) rest

def stopPc (pc : Nat) (g : E1M1PathAdvance.Cell) : List Cell → Nat
  | [] => pc
  | _::rest => stopPc (E1M1PathAdvance.nextPc g) (E1M1PathAdvance.step g) rest

/-- Coordinates must follow the original step. Only the final cell may exit;
a nonempty tail requires the original continuation test to succeed. -/
def Follows (g : E1M1PathAdvance.Cell) : List Cell → Prop
  | [] => True
  | c::rest => g.mapX=c.x.toBitVec ∧ g.mapY=c.y.toBitVec ∧
      (rest≠[] → E1M1PathAdvance.nextPc g=0x2ca7f) ∧ Follows (E1M1PathAdvance.step g) rest

/-- Each object result follows the actual checked line result in that cell.
This deliberately does not assert equality to the production outer line loop. -/
inductive Collection (q : Context) : List Cell → X86Control.State → Collision.PathResult → Collision.PathResult → Prop
  | nil (s r) : Collection q [] s r r
  | cons (c rest s r middle after)
      (cell : E1M1FiringThings.sceneCell q.trace q.world c.x c.y (lineResult q c s r)=.ok middle)
      (tail : Collection q rest (next q c s r) middle after) : Collection q (c::rest) s r after

/-- Repackage the proved cell step with a reusable memory/record invariant. -/
theorem one (q : Context) (c : Cell) (s : X86Control.State) (r : Collision.PathResult) (seen : Array Bool)
    (common : Common q) (static : Static q c) (state : E1M1CellWalkInvariant.State q s r seen)
    (images : Images q [c] s.core.memory) (pc : s.pc=0x2ca7f)
    (x : (E1M1PathAdvance.observe s.core).mapX=c.x.toBitVec)
    (y : (E1M1PathAdvance.observe s.core).mapY=c.y.toBitVec)
    (room : r.collected.size+cost c≤128) :
    let out := next q c s r
    ∃ after, E1M1FiringThings.sceneCell q.trace q.world c.x c.y (lineResult q c s r)=.ok after ∧
      (∃ n≤instructions c, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
      E1M1CellWalkInvariant.State q out after (visits q c seen) ∧
      after.collected.size≤r.collected.size+cost c ∧
      E1M1PathAdvance.observe out.core=E1M1PathAdvance.step (E1M1PathAdvance.observe s.core) ∧
      out.pc=E1M1PathAdvance.nextPc (E1M1PathAdvance.observe s.core) ∧
      E1M1CellMapInvariant.Frame q.sp q.lines s.core.memory out.core.memory := by
  have image := images c (by simp)
  obtain ⟨run,stack,obs,outPC,⟨after,production,size,hits⟩,represented,maps,_,_,frame⟩ :=
    E1M1CellAdvance.execution s q.sp q.base q.lines q.epoch q.words q.width q.height q.objects q.trace c.cell c.data c.nodes r seen
      pc state.stack static.valid state.maps common.mapLayout image.1 static.payloadSafe static.contracts static.layout
      c.x c.y x y static.selected static.inside q.links image.2 static.selectionSafe state.tracked
      (caller_safe s.core q.sp _ state.stack common.cursor)
      (fun i hi off ho => caller_safe s.core q.sp _ state.stack (common.records i (by have := state.tracked.room; omega) off ho))
      (by simpa [cost,Nat.add_assoc] using room) state.represented state.size common.stamps common.returns
      common.epochSafe common.stampSafe common.locals q.world common.dimension static.sceneIds static.scene
  refine ⟨after,production,run,⟨stack,maps,⟨hits.encoded,hits.cursor,by have := hits.room; omega⟩,represented,?_⟩,
    by simpa [cost,Nat.add_assoc] using size,obs,outPC,frame⟩
  simpa only [visits,OriginalLineVisitedRun.mark_size] using state.size

/-- Compose any finite, admitted in-map itinerary from initial images and one
candidate budget. No execution, images or free slots are postulated at a later
cell. The final PC may continue or exit; intermediate PCs must continue. -/
theorem execution (q : Context) (cells : List Cell) (s : X86Control.State)
    (r : Collision.PathResult) (seen : Array Bool)
    (common : Common q) (statics : ∀ c∈cells, Static q c)
    (state : E1M1CellWalkInvariant.State q s r seen) (images : Images q cells s.core.memory)
    (entry : cells≠[] → s.pc=0x2ca7f) (follows : Follows (E1M1PathAdvance.observe s.core) cells)
    (room : r.collected.size+budget cells≤128) :
    ∃ out after, (∃ n≤bound cells, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
      Collection q cells s r after ∧ E1M1CellWalkInvariant.State q out after (history q seen cells) ∧
      after.collected.size≤r.collected.size+budget cells ∧
      E1M1PathAdvance.observe out.core=grid (E1M1PathAdvance.observe s.core) cells ∧
      out.pc=stopPc s.pc (E1M1PathAdvance.observe s.core) cells ∧
      E1M1CellMapInvariant.Frame q.sp q.lines s.core.memory out.core.memory ∧
      Images q cells out.core.memory := by
  induction cells generalizing s r seen with
  | nil =>
    exact ⟨s,r,⟨0,by simp [bound],.nil _⟩,.nil s r,state,by simp [budget],rfl,rfl,
      fun _ _ => rfl,images⟩
  | cons c rest ih =>
    obtain ⟨x,y,continues,followsTail⟩ := follows
    have cellRoom : r.collected.size+cost c≤128 := by
      simp only [budget,List.map_cons,List.sum_cons] at room
      omega
    obtain ⟨middle,production,⟨n,hn,run⟩,middleState,used,obs,outPC,frame⟩ :=
      one q c s r seen common (statics c (by simp)) state (fun d hd => images d (by simp_all)) (entry (by simp)) x y cellRoom
    have allImages := images_transport q (c::rest) _ _ statics images frame
    obtain ⟨out,after,⟨m,hm,tailRun⟩,collection,outState,total,outObs,finalPC,tailFrame,_⟩ :=
      ih (next q c s r) middle (visits q c seen)
        (fun d hd => statics d (by simp [hd])) middleState (fun d hd => allImages d (by simp [hd]))
        (fun nonempty => outPC.trans (continues nonempty))
        (by rw [obs]; exact followsTail) (budget_tail c rest _ _ room used).2
    have joined := E1M1CellMapInvariant.frame_trans q.sp q.lines _ _ _ frame tailFrame
    refine ⟨out,after,⟨n+m,?_,E1M1PspriteStep.prefix_trans run tailRun⟩,
      .cons c rest s r middle after production collection,outState,?_,?_,?_,joined,
      images_transport q (c::rest) _ _ statics images joined⟩
    · simpa only [bound,List.map_cons,List.sum_cons] using Nat.add_le_add hn hm
    · simp only [budget,List.map_cons,List.sum_cons] at total ⊢
      omega
    · simpa only [grid,obs] using outObs
    · simpa only [stopPc,outPC,obs] using finalPC
end Doom.Proofs.E1M1CellWalk
