import Doom.Proofs.E1M1InterceptSetup
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1TraversalEntry
open Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1MixedCellWalk (inside Admitted budget bound history)
open E1M1GridRoute (sourceRoute)
open E1M1QueryCollection (path Entry)
attribute [local irreducible] load32 store32

def program : X86Routine.Program := fun pc =>
  match E1M1FiringAdvance.program pc with
  | some op => some op
  | none => OriginalInterceptSetup.program pc

theorem contains_collection (pc : Nat) (h : E1M1FiringAdvance.program pc≠none) :
    program pc=E1M1FiringAdvance.program pc := by
  unfold program
  cases eq : E1M1FiringAdvance.program pc <;> simp_all

theorem contains_setup (pc : Nat) (h : OriginalInterceptSetup.program pc≠none) :
    program pc=OriginalInterceptSetup.program pc := by
  have range : (0x2c810≤pc ∧ pc<0x2c841) ∨ (0x2cafd≤pc ∧ pc<0x2cb0b) := by
    by_cases a : 0x2c810≤pc ∧ pc<0x2c841
    · exact Or.inl a
    · by_cases b : 0x2cafd≤pc ∧ pc<0x2cb0b
      · exact Or.inr b
      · simp [OriginalInterceptSetup.program,OriginalInterceptSetup.bytesProgram,a,b] at h
  rcases range with a|b
  · have all : ∀ i : Fin 49, program (0x2c810+i.val)=OriginalInterceptSetup.program (0x2c810+i.val) := by decide
    have eq : 0x2c810+(pc-0x2c810)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2c810,by omega⟩
  · have all : ∀ i : Fin 14, program (0x2cafd+i.val)=OriginalInterceptSetup.program (0x2cafd+i.val) := by decide
    have eq : 0x2cafd+(pc-0x2cafd)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2cafd,by omega⟩

/-- Static separation for the selector's deeper stack frame, stated with the
same caller stack base as the collection invariant. -/
structure Protected (q : Context) : Prop where
  cursor : E1M1InterceptSetup.Safe (q.sp-112) 0x2c028
  records : ∀ i<128, ∀ off∈[(0#32),4,8],
    E1M1InterceptSetup.Safe (q.sp-112) (OriginalLineCollection.slot 0x2ba20 i off)

/-- Collection's actual final invariant supplies count, limit and record bytes.
Only static separation is added; there is no future machine-state premise. -/
theorem from_collection (q : Context) (s : X86Control.State) (r : Collision.PathResult) (seen : Array Bool)
    (state : State q s r seen) (pc : s.pc=0x2cafd) (separated : Protected q) :
    X86CodeMemory.Prefix FloorCaller.cm program [] 23 s (E1M1InterceptSetup.result s.core r.collected.size) ∧
    OriginalLineFinish.Encodes (E1M1InterceptSetup.result s.core r.collected.size).core.memory
      0x2ba20 (E1M1ThingFinish.resolve q.lines q.objects) r.collected ∧
    (E1M1InterceptSetup.result s.core r.collected.size).core.regs 1=E1M1MinimumScan.address r.collected.size ∧
    (E1M1InterceptSetup.result s.core r.collected.size).core.regs 7=65536 ∧
    (E1M1InterceptSetup.result s.core r.collected.size).pc=(if r.collected.size=0 then 0x2c887 else 0x2c841) := by
  have bound : r.collected.size≤128 := by simpa using state.tracked.room
  have limit : load32 s.core.memory 0x2c028=E1M1MinimumScan.address r.collected.size := by
    simpa [OriginalLineFinish.cursor,E1M1MinimumScan.address,BitVec.ofNat_add] using state.tracked.cursor
  have safe : E1M1InterceptSetup.Safe (s.core.regs 4) 0x2c028 := by rw [state.stack]; exact separated.cursor
  have run := (E1M1InterceptSetup.execution s.core s.flags _ bound limit safe).transfer program [] contains_setup (by simp)
  rw [OriginalPathXStep.at_pc _ _ pc] at run
  have fields := E1M1InterceptSetup.fields s.core r.collected.size safe
  exact ⟨run,E1M1InterceptSetup.records s.core _ _ _ state.tracked.encoded (by
    intro i hi off ho
    rw [state.stack]
    exact separated.records i (by omega) off ho),fields.2.1.trans limit,fields.2.2.1,fields.2.2.2.2.2⟩

/-- Query entry through initialization, collection, the traversal CALL and its
count setup. The empty case bypasses the scan; nonempty lists reach its entry. -/
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
    (room : budget q (sourceRoute pick 64 (E1M1FiringGridState.initial (path q sx sy ex ey) xout yout))≤128) :
    let g := E1M1FiringGridState.initial (path q sx sy ex ey) xout yout
    let cells := sourceRoute pick 64 g
    let seen := Array.replicate q.world.lines.size false
    ∃ (collected : X86Control.State) (after : Collision.PathResult),
      (∃ n≤198+bound q cells, X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2c8a0⟩
        (E1M1InterceptSetup.result collected.core after.collected.size)) ∧
      E1M1LiveWalk.source q.world q.trace 64 g seen {trace:=q.trace}=
        .ok (E1M1LoopReplay.pack (E1M1PathAdvance.observe collected.core) (history q seen cells) after) ∧
      (∀ visit, q.world.pathTraverse sx sy ex ey 3 visit=E1M1QuerySource.visitHits after visit) ∧
      State q collected after (history q seen cells) ∧
      OriginalLineFinish.Encodes (E1M1InterceptSetup.result collected.core after.collected.size).core.memory
        0x2ba20 (E1M1ThingFinish.resolve q.lines q.objects) after.collected ∧
      (E1M1InterceptSetup.result collected.core after.collected.size).core.regs 1=E1M1MinimumScan.address after.collected.size ∧
      (E1M1InterceptSetup.result collected.core after.collected.size).core.regs 7=65536 ∧
      (E1M1InterceptSetup.result collected.core after.collected.size).pc=(if after.collected.size=0 then 0x2c887 else 0x2c841) := by
  obtain ⟨_,_,out,after,⟨n,hn,run⟩,collection,tail,state,_,_,pc,_⟩ :=
    E1M1QueryCollection.execution q pick s f sx sy ex ey entry profile xout yout okX okY
      common height statics scenes payloads room
  obtain ⟨setup,records,limit,maximum,exit⟩ := from_collection q out after _ state pc separated
  exact ⟨out,after,⟨n+23,by omega,E1M1PspriteStep.prefix_trans
    (run.transfer program [] contains_collection (by simp)) setup⟩,collection,tail,state,records,limit,maximum,exit⟩
end Doom.Proofs.E1M1TraversalEntry
