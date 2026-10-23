import Doom.Proofs.E1M1AimStampLiveWalk
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimStampCollection
open Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1MixedCellWalk (inside Admitted Images budget bound history)
open E1M1GridRoute (sourceRoute)
open E1M1QueryCollection (path Entry)
attribute [local irreducible] load32 store32

/-- Initialization increments the counter, but retains each original stamp word.
The all-false history and exact image use the actual query-entry memory. -/
theorem initialized_image (q : Context) (s : X86Memory.State) (sx sy ex ey : Fixed)
    (entry : Entry q s sx sy ex ey) :
    E1M1AimStampImage.Image s.memory (E1M1PathMapSetup.grid s).core.memory q.lines q.epoch
      (Array.replicate q.world.lines.size false) := by
  refine ⟨(E1M1QueryCollection.state q s sx sy ex ey entry).represented.1,?_⟩
  intro j hj
  have bound : j<q.world.lines.size := by simpa only [Array.size_replicate] using hj
  rw [getElem!_pos _ j hj, Array.getElem_replicate]
  simp only [Bool.false_eq_true, if_false]
  exact E1M1PathMapSetup.grid_frame s _ _ sx sy ex ey entry.geometry _ (entry.stampSafe j bound)

/-- Initialization and the generated source collection loop carry the exact
image continuously from query entry to the real ordered-hit setup boundary. -/
theorem collection (q : Context) (pick : Int32 → Int32 → Cell)
    (s : X86Memory.State) (f : Option Flags) (sx sy ex ey : Fixed)
    (entry : Entry q s sx sy ex ey) (profile : E1M1QuerySource.supported q.world=true)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (path q sx sy ex ey).xStep=.ok xout)
    (okY : (path q sx sy ex ey).yStep=.ok yout)
    (common : Common q) (height : q.world.grid.height=q.height)
    (statics : ∀ c∈sourceRoute pick 64 (E1M1FiringGridState.initial (path q sx sy ex ey) xout yout), Admitted q c)
    (scenes : ∀ c∈sourceRoute pick 64 (E1M1FiringGridState.initial (path q sx sy ex ey) xout yout),
      inside q c=true → E1M1CellLineSource.SceneLines q c)
    (payloads : ∀ c∈sourceRoute pick 64 (E1M1FiringGridState.initial (path q sx sy ex ey) xout yout),
      inside q c=true → E1M1QueryImages.Payload s.memory q c ∧ E1M1QueryImages.Protected s q c)
    (room : budget q (sourceRoute pick 64 (E1M1FiringGridState.initial (path q sx sy ex ey) xout yout))≤128) :
    let g := E1M1FiringGridState.initial (path q sx sy ex ey) xout yout
    let cells := sourceRoute pick 64 g
    let seen := Array.replicate q.world.lines.size false
    cells≠[] ∧ cells.length≤64 ∧ ∃ out after,
      (∃ n≤175+bound q cells, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n ⟨s,f,0x2c8a0⟩ out) ∧
      E1M1LiveWalk.source q.world q.trace 64 g seen {trace:=q.trace}=
        .ok (E1M1LoopReplay.pack (E1M1PathAdvance.observe out.core) (history q seen cells) after) ∧
      (∀ visit, q.world.pathTraverse sx sy ex ey 3 visit=E1M1QuerySource.visitHits after visit) ∧
      State q out after (history q seen cells) ∧ after.collected.size≤budget q cells ∧
      E1M1PathAdvance.observe out.core=E1M1CellWalk.grid g cells ∧ out.pc=0x2cafd ∧
      Images q cells out.core.memory ∧
      (∀ a, E1M1PathMapSetup.Safe s a → E1M1FiringMapState.Safe q.sp q.lines a →
        load32 out.core.memory a=load32 s.memory a) ∧
      E1M1AimStampImage.Image s.memory out.core.memory q.lines q.epoch (history q seen cells) := by
  have numeric := E1M1QueryInit.numeric s _ _ sx sy ex ey entry.geometry xout yout okX okY
  change E1M1PathAdvance.observe (E1M1PathMapSetup.grid s).core=
    E1M1FiringGridState.initial (path q sx sy ex ey) xout yout ∧
    (E1M1PathMapSetup.grid s).pc=0x2ca7f ∧ (E1M1PathMapSetup.grid s).core.regs 4=s.regs 4-60 at numeric
  have initialized := E1M1QueryCollection.state q s sx sy ex ey entry
  have images := E1M1QueryImages.images s q _ _ _ sx sy ex ey entry.geometry entry.trace
    entry.options entry.traceSafe entry.activeSafe payloads
  have counter : (E1M1PathAdvance.observe (E1M1PathMapSetup.grid s).core).count=BitVec.ofNat 32 0 := by
    rw [numeric.1]; rfl
  obtain ⟨nonempty,length,out,after,⟨n,hn,run⟩,collection,outState,size,obs,pc,frame,outImages,stampImage⟩ :=
    E1M1AimStampLiveWalk.live q pick (E1M1PathMapSetup.grid s) {trace:=q.trace}
      (Array.replicate q.world.lines.size false) 0 (by decide) counter common height
      (by simpa only [Nat.sub_zero,numeric.1] using statics)
      (by simpa only [Nat.sub_zero,numeric.1] using scenes) initialized
      (by simpa only [Nat.sub_zero,numeric.1] using images) numeric.2.1
      (by simpa only [Nat.sub_zero,numeric.1,Array.size_empty,Nat.zero_add] using room) s.memory (initialized_image q s sx sy ex ey entry)
  simp only [Nat.sub_zero,numeric.1,Array.size_empty,Nat.zero_add] at nonempty length hn collection outState size obs outImages stampImage
  obtain ⟨m,hm,setupRun⟩ := E1M1QueryPrefix.execution s f _ _ sx sy ex ey entry.geometry xout yout okX okY
  refine ⟨nonempty,length,out,after,⟨m+n,by omega,E1M1PspriteStep.prefix_trans setupRun run⟩,
    collection,?_,outState,size,obs,pc,outImages,?_,stampImage⟩
  · intro visit
    exact E1M1QueryCollection.query_tail q sx sy ex ey profile entry.trace xout yout okX okY _ _ after collection visit
  · intro a initSafe loopSafe
    exact (frame a loopSafe).trans
      (E1M1PathMapSetup.grid_frame s _ _ sx sy ex ey entry.geometry a initSafe)

end Doom.Proofs.E1M1AimStampCollection
