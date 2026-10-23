import Doom.Proofs.E1M1QueryPrefix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1QueryCollection
open Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1MixedCellWalk (inside Admitted Images budget bound history)
open E1M1GridRoute (sourceRoute)
attribute [local irreducible] load32

def path (q : Context) (sx sy ex ey : Fixed) :=
  Collision.pathStart (Fixed.ofInt q.world.grid.origin.x) (Fixed.ofInt q.world.grid.origin.y) sx sy ex ey

/-- All dynamic memory facts are stated at P_PathTraverse entry. No completed
initialization, collection-gate state or future callback result is assumed. -/
structure Entry (q : Context) (s : X86Memory.State) (sx sy ex ey : Fixed) : Prop where
  geometry : OriginalPathInit.Inputs s (Fixed.ofInt q.world.grid.origin.x) (Fixed.ofInt q.world.grid.origin.y) sx sy ex ey
  stack : s.regs 4=q.sp-52
  epoch : q.epoch=load32 s.memory 0x13580+1
  trace : q.trace=(path q sx sy ex ey).trace
  lineCount : q.world.lines.size=475
  options : load32 s.memory (s.regs 4+4)=3
  flagSafe : E1M1PathMapSetup.Safe s (E1M1ThingGate.flagWord q.sp)
  map : E1M1PathMapSetup.MapInputs s q.base q.lines q.words q.width q.height
  cursorSafe : E1M1PathMapSetup.StackSafe (s.regs 4-60) 0x2c028
  epochSafe : E1M1PathMapSetup.StackSafe (s.regs 4-60) 0x13580
  stampSafe : ∀ j<q.world.lines.size, E1M1PathMapSetup.Safe s (OriginalLineVisits.stamp q.lines j)
  fresh : ∀ j<q.world.lines.size, load32 s.memory (OriginalLineVisits.stamp q.lines j)≠load32 s.memory 0x13580+1
  traceSafe : ∀ a∈E1M1ThingGeometry.traceReads, E1M1PathMapSetup.StackSafe (s.regs 4-60) a
  activeSafe : E1M1PathMapSetup.StackSafe (s.regs 4-60) 0x2c024

/-- Assemble the complete loop invariant from actual initialization. -/
theorem state (q : Context) (s : X86Memory.State) (sx sy ex ey : Fixed)
    (entry : Entry q s sx sy ex ey) :
    State q (E1M1PathMapSetup.grid s) {trace:=q.trace} (Array.replicate q.world.lines.size false) := by
  refine ⟨?_,E1M1QueryImages.map s q _ _ sx sy ex ey entry.geometry entry.stack entry.options entry.flagSafe entry.map,
    E1M1QueryInit.empty_collection s _ _ sx sy ex ey entry.geometry entry.cursorSafe _,?_,?_⟩
  · rw [E1M1PathMapSetup.grid_stack s _ _ sx sy ex ey entry.geometry,entry.stack]
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  · rw [entry.epoch]
    exact E1M1QueryInit.initial_visits s _ _ sx sy ex ey entry.geometry q.lines q.world.lines.size
      entry.epochSafe entry.stampSafe entry.fresh
  · simpa using entry.lineCount

/-- A proved successful collection leaves exactly the live ordered-hit tail. -/
theorem query_tail (q : Context) (sx sy ex ey : Fixed)
    (profile : E1M1QuerySource.supported q.world=true)
    (trace : q.trace=(path q sx sy ex ey).trace)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (path q sx sy ex ey).xStep=.ok xout)
    (okY : (path q sx sy ex ey).yStep=.ok yout)
    (g : E1M1PathAdvance.Cell) (seen : Array Bool) (after : Collision.PathResult)
    (collected : E1M1LiveWalk.source q.world q.trace 64
      (E1M1FiringGridState.initial (path q sx sy ex ey) xout yout)
      (Array.replicate q.world.lines.size false) {trace:=q.trace} =
      .ok (E1M1LoopReplay.pack g seen after)) (visit : Collision.Intercept → Nat → Bool) :
    q.world.pathTraverse sx sy ex ey 3 visit=E1M1QuerySource.visitHits after visit := by
  rw [E1M1QuerySource.live,E1M1QuerySource.prepare_ok q.world sx sy ex ey profile xout yout okX okY]
  change E1M1QuerySource.runPrepared q.world
    (E1M1QuerySource.prepared q.world (path q sx sy ex ey) xout yout) visit=_
  simp only [E1M1QuerySource.runPrepared,E1M1QuerySource.prepared]
  rw [←trace,collected]
  rfl

/-- Initialization and the complete mixed-cell loop form one original execution.
Its collection equals the actual source query's collection, leaving only the
ordered-hit tail. Reachability, callback arithmetic and capacity are explicit. -/
theorem execution (q : Context) (pick : Int32 → Int32 → Cell)
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
      Images q cells out.core.memory := by
  have numeric := E1M1QueryInit.numeric s _ _ sx sy ex ey entry.geometry xout yout okX okY
  change E1M1PathAdvance.observe (E1M1PathMapSetup.grid s).core=
    E1M1FiringGridState.initial (path q sx sy ex ey) xout yout ∧
    (E1M1PathMapSetup.grid s).pc=0x2ca7f ∧ (E1M1PathMapSetup.grid s).core.regs 4=s.regs 4-60 at numeric
  have initialized := state q s sx sy ex ey entry
  have images := E1M1QueryImages.images s q _ _ _ sx sy ex ey entry.geometry entry.trace
    entry.options entry.traceSafe entry.activeSafe payloads
  have counter : (E1M1PathAdvance.observe (E1M1PathMapSetup.grid s).core).count=BitVec.ofNat 32 0 := by
    rw [numeric.1]; rfl
  obtain ⟨nonempty,length,out,after,⟨n,hn,run⟩,collection,outState,size,obs,pc,_,outImages⟩ :=
    E1M1LiveWalk.execution q pick (E1M1PathMapSetup.grid s) {trace:=q.trace}
      (Array.replicate q.world.lines.size false) 0 (by decide) counter common height
      (by simpa only [Nat.sub_zero,numeric.1] using statics)
      (by simpa only [Nat.sub_zero,numeric.1] using scenes) initialized
      (by simpa only [Nat.sub_zero,numeric.1] using images) numeric.2.1
      (by simpa only [Nat.sub_zero,numeric.1,Array.size_empty,Nat.zero_add] using room)
  simp only [Nat.sub_zero,numeric.1,Array.size_empty,Nat.zero_add] at nonempty length hn collection outState size obs outImages
  obtain ⟨m,hm,setupRun⟩ := E1M1QueryPrefix.execution s f _ _ sx sy ex ey entry.geometry xout yout okX okY
  refine ⟨nonempty,length,out,after,⟨m+n,by omega,E1M1PspriteStep.prefix_trans setupRun run⟩,
    collection,?_,outState,size,obs,pc,outImages⟩
  intro visit
  exact query_tail q sx sy ex ey profile entry.trace xout yout okX okY _ _ after collection visit
end Doom.Proofs.E1M1QueryCollection
