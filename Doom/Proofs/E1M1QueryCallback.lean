import Doom.Proofs.E1M1CallbackEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1QueryCallback
open Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1MixedCellWalk (inside Admitted Images budget bound history)
open E1M1GridRoute (sourceRoute)
open E1M1QueryCollection (path Entry)
open E1M1TraversalEntry (Protected)
open E1M1FirstIntercept (program)
open E1M1CallbackEntry (Outcome)
attribute [local irreducible] load32 store32

/-- Retain the existing collection frame to transport protected query arguments
from entry memory. No assumption about a reached callback is introduced. -/
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
        load32 out.core.memory a=load32 s.memory a) := by
  have numeric := E1M1QueryInit.numeric s _ _ sx sy ex ey entry.geometry xout yout okX okY
  change E1M1PathAdvance.observe (E1M1PathMapSetup.grid s).core=
    E1M1FiringGridState.initial (path q sx sy ex ey) xout yout ∧
    (E1M1PathMapSetup.grid s).pc=0x2ca7f ∧ (E1M1PathMapSetup.grid s).core.regs 4=s.regs 4-60 at numeric
  have initialized := E1M1QueryCollection.state q s sx sy ex ey entry
  have images := E1M1QueryImages.images s q _ _ _ sx sy ex ey entry.geometry entry.trace
    entry.options entry.traceSafe entry.activeSafe payloads
  have counter : (E1M1PathAdvance.observe (E1M1PathMapSetup.grid s).core).count=BitVec.ofNat 32 0 := by
    rw [numeric.1]; rfl
  obtain ⟨nonempty,length,out,after,⟨n,hn,run⟩,collection,outState,size,obs,pc,frame,outImages⟩ :=
    E1M1LiveWalk.execution q pick (E1M1PathMapSetup.grid s) {trace:=q.trace}
      (Array.replicate q.world.lines.size false) 0 (by decide) counter common height
      (by simpa only [Nat.sub_zero,numeric.1] using statics)
      (by simpa only [Nat.sub_zero,numeric.1] using scenes) initialized
      (by simpa only [Nat.sub_zero,numeric.1] using images) numeric.2.1
      (by simpa only [Nat.sub_zero,numeric.1,Array.size_empty,Nat.zero_add] using room)
  simp only [Nat.sub_zero,numeric.1,Array.size_empty,Nat.zero_add] at nonempty length hn collection outState size obs outImages
  obtain ⟨m,hm,setupRun⟩ := E1M1QueryPrefix.execution s f _ _ sx sy ex ey entry.geometry xout yout okX okY
  refine ⟨nonempty,length,out,after,⟨m+n,by omega,E1M1PspriteStep.prefix_trans setupRun run⟩,
    collection,?_,outState,size,obs,pc,outImages,?_⟩
  · intro visit
    exact E1M1QueryCollection.query_tail q sx sy ex ey profile entry.trace xout yout okX okY _ _ after collection visit
  · intro a initSafe loopSafe
    exact (frame a loopSafe).trans
      (E1M1PathMapSetup.grid_frame s _ _ sx sy ex ey entry.geometry a initSafe)

/-- Additional static separation for the callback argument and final CALL push.
The target's value is read from query-entry memory, not assumed at a later seam. -/
structure CallbackSafe (q : Context) (s : X86Memory.State) : Prop where
  initial : E1M1PathMapSetup.Safe s (q.sp-44)
  walk : E1M1FiringMapState.Safe q.sp q.lines (q.sp-44)
  records : ∀ i<128, ∀ off∈[(0#32),4,8],
    Apart (OriginalLineCollection.slot 0x2ba20 i off) (q.sp-140)

/-- Query entry to first callback with its original argument, full hit records
and return address. All intermediate memory and stack facts are derived. -/
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
    (separated : Protected q)
    (callbackSafe : CallbackSafe q s)
    (room : budget q (sourceRoute pick 64 (E1M1FiringGridState.initial (path q sx sy ex ey) xout yout))≤128) :
    let g := E1M1FiringGridState.initial (path q sx sy ex ey) xout yout
    let cells := sourceRoute pick 64 g
    let seen := Array.replicate q.world.lines.size false
    ∃ (collected : X86Control.State) (after : Collision.PathResult) (out : X86Control.State),
      (∃ n≤207+bound q cells+7*after.collected.size,
        X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2c8a0⟩ out) ∧
      E1M1LiveWalk.source q.world q.trace 64 g seen {trace:=q.trace}=
        .ok (E1M1LoopReplay.pack (E1M1PathAdvance.observe collected.core) (history q seen cells) after) ∧
      (∀ visit, q.world.pathTraverse sx sy ex ey 3 visit=E1M1QuerySource.visitHits after visit) ∧
      State q collected after (history q seen cells) ∧
      Outcome after.collected (E1M1ThingFinish.resolve q.lines q.objects)
        (load32 s.memory (q.sp-44)) (q.sp-136) out := by
  obtain ⟨_,_,collected,after,⟨n,hn,run⟩,source,tail,state,_,_,pc,_,frame⟩ :=
    collection q pick s f sx sy ex ey entry profile xout yout okX okY
      common height statics scenes payloads room
  obtain ⟨setupRun,encoded,limit,maximum,exit⟩ :=
    E1M1TraversalEntry.from_collection q collected after _ state pc separated
  have safe : E1M1InterceptSetup.Safe (collected.core.regs 4) 0x2c028 := by
    rw [state.stack]; exact separated.cursor
  have fields := E1M1InterceptSetup.fields collected.core after.collected.size safe
  have sp : (E1M1InterceptSetup.result collected.core after.collected.size).core.regs 4=q.sp-136 := by
    rw [fields.1,state.stack]
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have target : load32 (E1M1InterceptSetup.result collected.core after.collected.size).core.memory
      ((E1M1InterceptSetup.result collected.core after.collected.size).core.regs 4)=
      load32 s.memory (q.sp-44) := by
    rw [fields.2.2.2.2.1]
    unfold OriginalInterceptSetup.callback
    rw [state.stack]
    have addr : q.sp-(112#32)+68=q.sp-44 := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rw [addr]
    exact frame _ callbackSafe.initial callbackSafe.walk
  have bounded : after.collected.size≤128 := by simpa using state.tracked.room
  obtain ⟨m,hm,out,dispatch,outcome⟩ := E1M1CallbackEntry.dispatch
    (E1M1InterceptSetup.result collected.core after.collected.size) after.collected
    (E1M1ThingFinish.resolve q.lines q.objects) bounded limit encoded maximum exit
    (by
      rw [fields.1,state.stack]
      exact FloorCaller.apart_symm (separated.cursor 24 (by simp)))
    (by
      intro i hi off ho
      rw [sp]
      have addr : q.sp-136-4=q.sp-140 := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rw [addr]
      exact callbackSafe.records i (by omega) off ho)
  rw [target,sp] at outcome
  have collectRun := run.transfer E1M1TraversalEntry.program [] E1M1TraversalEntry.contains_collection (by simp)
  have preparedRun := (E1M1PspriteStep.prefix_trans collectRun setupRun).transfer
    program [] E1M1FirstIntercept.contains_entry (by simp)
  exact ⟨collected,after,out,⟨n+23+m,by omega,E1M1PspriteStep.prefix_trans preparedRun dispatch⟩,
    source,tail,state,outcome⟩

/-- The already proved aim caller supplies this exact query argument. This
identifies the target without inserting a callback assumption mid-traversal. -/
theorem aim_argument (s : X86Memory.State) (separated : OriginalAimSetup.Separated s) :
    load32 (OriginalAimSetup.traversal s).core.memory
      ((OriginalAimSetup.traversal s).core.regs 4+8)=0x2b760 := by
  have sp : (OriginalAimSetup.traversal s).core.regs 4=s.regs 4-12 := rfl
  rw [sp]
  have addr : s.regs 4-12+8=s.regs 4-4 := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rw [addr]
  exact OriginalAimSetup.stored_callback s separated

/-- An aim argument in entry memory specializes the continuous theorem's target.
`aim_argument` supplies this premise for the original aim caller. -/
theorem specialize_aim (q : Context) (s : X86Memory.State)
    (hits : Array Collision.Intercept) (resolve : Collision.Intercept → Word)
    (out : X86Control.State) (stack : s.regs 4=q.sp-52)
    (argument : load32 s.memory (s.regs 4+8)=0x2b760)
    (outcome : Outcome hits resolve (load32 s.memory (q.sp-44)) (q.sp-136) out) :
    Outcome hits resolve 0x2b760 (q.sp-136) out := by
  rw [stack] at argument
  have addr : q.sp-52+8=q.sp-44 := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rw [addr] at argument
  rw [argument] at outcome
  exact outcome

/-- Specializing the reached outcome to the aim argument identifies either the
no-hit exit or PTR_AimTraverse entry; it says nothing about its body yet. -/
theorem aim_destination (hits : Array Collision.Intercept) (resolve : Collision.Intercept → Word)
    (sp : Word) (out : X86Control.State) (outcome : Outcome hits resolve 0x2b760 sp out) :
    out.pc=0x2c887 ∨ out.pc=0x2b760 := by
  rcases outcome with empty|far|ready
  · exact Or.inl empty.2
  · obtain ⟨_,_,_,pc⟩ := far; exact Or.inl pc
  · exact Or.inr ready.pc
end Doom.Proofs.E1M1QueryCallback
