import Doom.Proofs.E1M1OutsideCell
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1MixedCellWalk
open Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant (Context Cell Common)
open E1M1CellWalk (Follows grid stopPc)
attribute [local irreducible] load32

def inside (q : Context) (c : Cell) := Collision.pathCellInside c.x c.y q.width q.height
/-- Outside cells require neither BLOCKMAP entries nor object table heads. -/
def Admitted (q : Context) (c : Cell) := inside q c=true → E1M1CellWalkInvariant.Static q c
def Images (q : Context) (cells : List Cell) (m : Memory) :=
  ∀ c∈cells, inside q c=true → E1M1CellWalkInvariant.Images q [c] m

def cost (q : Context) (c : Cell) := if inside q c then E1M1CellWalkInvariant.cost c else 0
def instructions (q : Context) (c : Cell) := if inside q c then E1M1CellWalkInvariant.instructions c else 71
def budget (q : Context) (cells : List Cell) := (cells.map (cost q)).sum
def bound (q : Context) (cells : List Cell) := (cells.map (instructions q)).sum

def next (q : Context) (c : Cell) (s : X86Control.State) (r : Collision.PathResult) :=
  if inside q c then E1M1CellWalk.next q c s r else E1M1OutsideCell.result s

def visits (q : Context) (c : Cell) (seen : Array Bool) :=
  if inside q c then E1M1CellWalk.visits q c seen else seen

def history (q : Context) (seen : Array Bool) : List Cell → Array Bool
  | [] => seen
  | c::rest => history q (visits q c seen) rest

/-- An outside cell leaves the entire modeled collection result unchanged. -/
def CellResult (q : Context) (c : Cell) (s : X86Control.State) (r after : Collision.PathResult) :=
  if inside q c then
    E1M1FiringThings.sceneCell q.trace q.world c.x c.y (E1M1CellWalk.lineResult q c s r)=.ok after
  else after=r

inductive Collection (q : Context) : List Cell → X86Control.State → Collision.PathResult → Collision.PathResult → Prop
  | nil (s r) : Collection q [] s r r
  | cons (c rest s r middle after) (cell : CellResult q c s r middle)
      (tail : Collection q rest (next q c s r) middle after) : Collection q (c::rest) s r after

theorem images_transport (q : Context) (cells : List Cell) (m n : Memory)
    (statics : ∀ c∈cells, Admitted q c) (images : Images q cells m)
    (frame : E1M1CellMapInvariant.Frame q.sp q.lines m n) : Images q cells n := by
  intro c member yes
  exact E1M1CellWalkInvariant.images_transport q [c] m n
    (fun d hd => by simpa using (List.mem_singleton.mp hd) ▸ statics c member yes)
    (images c member yes) frame

/-- Select the already proved machine path using the production bounds test. -/
theorem one (q : Context) (c : Cell) (s : X86Control.State) (r : Collision.PathResult) (seen : Array Bool)
    (common : Common q) (static : Admitted q c) (state : E1M1CellWalkInvariant.State q s r seen)
    (images : Images q [c] s.core.memory) (pc : s.pc=0x2ca7f)
    (x : (E1M1PathAdvance.observe s.core).mapX=c.x.toBitVec)
    (y : (E1M1PathAdvance.observe s.core).mapY=c.y.toBitVec)
    (room : r.collected.size+cost q c≤128) :
    let out := next q c s r
    ∃ after, CellResult q c s r after ∧
      (∃ n≤instructions q c, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
      E1M1CellWalkInvariant.State q out after (visits q c seen) ∧
      after.collected.size≤r.collected.size+cost q c ∧
      E1M1PathAdvance.observe out.core=E1M1PathAdvance.step (E1M1PathAdvance.observe s.core) ∧
      out.pc=E1M1PathAdvance.nextPc (E1M1PathAdvance.observe s.core) ∧
      E1M1CellMapInvariant.Frame q.sp q.lines s.core.memory out.core.memory := by
  cases h : inside q c with
  | true =>
    simpa only [next,visits,instructions,cost,CellResult,h,ite_true] using
      E1M1CellWalk.one q c s r seen common (static h) state (images c (by simp) h) pc x y
        (by simpa only [cost,h,ite_true] using room)
  | false =>
    obtain ⟨run,outState,obs,outPC,frame⟩ := E1M1OutsideCell.execution q s r seen common state pc c.x c.y x y h
    simp only [next,visits,instructions,cost,CellResult,h,Bool.false_eq_true,ite_false,Nat.add_zero]
    exact ⟨r,rfl,run,outState,Nat.le_refl _,obs,outPC,frame⟩

/-- Inside and outside cells compose in any admitted order, including boundary
exit and re-entry. Future inside-cell images survive outside-cell stack stores;
outside cells spend no collection budget but still execute the original step. -/
theorem execution (q : Context) (cells : List Cell) (s : X86Control.State)
    (r : Collision.PathResult) (seen : Array Bool)
    (common : Common q) (statics : ∀ c∈cells, Admitted q c)
    (state : E1M1CellWalkInvariant.State q s r seen) (images : Images q cells s.core.memory)
    (entry : cells≠[] → s.pc=0x2ca7f) (follows : Follows (E1M1PathAdvance.observe s.core) cells)
    (room : r.collected.size+budget q cells≤128) :
    ∃ out after, (∃ n≤bound q cells, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
      Collection q cells s r after ∧ E1M1CellWalkInvariant.State q out after (history q seen cells) ∧
      after.collected.size≤r.collected.size+budget q cells ∧
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
    have cellRoom : r.collected.size+cost q c≤128 := by
      simp only [budget,List.map_cons,List.sum_cons] at room; omega
    obtain ⟨middle,production,⟨n,hn,run⟩,middleState,used,obs,outPC,frame⟩ :=
      one q c s r seen common (statics c (by simp)) state (fun d hd => images d (by simp_all)) (entry (by simp)) x y cellRoom
    have allImages := images_transport q (c::rest) _ _ statics images frame
    have remaining : middle.collected.size+budget q rest≤128 := by
      simp only [budget,List.map_cons,List.sum_cons] at room ⊢; omega
    obtain ⟨out,after,⟨m,hm,tailRun⟩,collection,outState,total,outObs,finalPC,tailFrame,_⟩ :=
      ih (next q c s r) middle (visits q c seen)
        (fun d hd => statics d (by simp [hd])) middleState (fun d hd => allImages d (by simp [hd]))
        (fun nonempty => outPC.trans (continues nonempty))
        (by rw [obs]; exact followsTail) remaining
    have joined := E1M1CellMapInvariant.frame_trans q.sp q.lines _ _ _ frame tailFrame
    refine ⟨out,after,⟨n+m,?_,E1M1PspriteStep.prefix_trans run tailRun⟩,
      .cons c rest s r middle after production collection,outState,?_,?_,?_,joined,
      images_transport q (c::rest) _ _ statics images joined⟩
    · simpa only [bound,List.map_cons,List.sum_cons] using Nat.add_le_add hn hm
    · simp only [budget,List.map_cons,List.sum_cons] at total ⊢; omega
    · simpa only [grid,obs] using outObs
    · simpa only [stopPc,outPC,obs] using finalPC
end Doom.Proofs.E1M1MixedCellWalk
