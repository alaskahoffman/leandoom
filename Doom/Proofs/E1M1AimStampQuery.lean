import Doom.Proofs.E1M1AimStampCollection
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimStampQuery
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1MixedCellWalk (inside Admitted Images budget bound history)
open E1M1GridRoute (sourceRoute)
open E1M1QueryCollection (path Entry)
open E1M1FirstIntercept (program)
open E1M1QueryCallback (CallbackSafe)
open E1M1AimFirstSelection (Outcome)
open E1M1AimCatalog (Portal)
open E1M1AimQueryCatalog (view)
open E1M1ThingFinish (resolve)
open E1M1AimQueryCaller (Initial Source callerSlots restores)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- The epoch and every linedef stamp, including lines the query never visits. -/
def stampWords (lines : Word) (count : Nat) : List Word :=
  0x13580 :: (List.range count).map (OriginalLineVisits.stamp lines)

/-- A word frame after collection carries the exact image without requiring
stamps to be disjoint from their own earlier line-scan stores. -/
theorem transport (origin m n : Memory) (lines epoch : Word) (seen : Array Bool) (count : Nat)
    (size : seen.size=count) (image : E1M1AimStampImage.Image origin m lines epoch seen)
    (kept : ∀ a∈stampWords lines count, load32 n a=load32 m a) :
    E1M1AimStampImage.Image origin n lines epoch seen := by
  apply E1M1AimStampImage.transport origin m n lines epoch seen image
  · exact kept _ (by simp [stampWords])
  · intro j hj
    apply kept
    have bound : j<count := by omega
    simp only [stampWords,List.mem_cons,List.mem_map,List.mem_range]
    exact Or.inr ⟨j,bound,rfl⟩

/-- Carry the collection image through actual ordered-hit setup and first selection. -/
theorem selection (q : Context) (pick : Int32 → Int32 → Cell)
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
    (separated : E1M1TraversalEntry.Protected q)
    (callbackSafe : CallbackSafe q s)
    (argument : load32 s.memory (s.regs 4+8)=0x2b760)
    (cursorCall : Apart 0x2c028 (q.sp-140))
    (room : budget q (sourceRoute pick 64 (E1M1FiringGridState.initial (path q sx sy ex ey) xout yout))≤128)
    (stampSafe : ∀ a∈stampWords q.lines 475, E1M1AimEntryFrame.SafeWord (q.sp-112) a) :
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
      Outcome after.collected (E1M1ThingFinish.resolve q.lines q.objects) (q.sp-136) out ∧
      E1M1AimStackShape.Shape (q.sp-136) out ∧
      load32 out.core.memory ((q.sp-136)+20)=0x2cb0b ∧
      load32 out.core.memory (q.sp-136)=0x2b760 ∧
      (∀ a, E1M1PathMapSetup.Safe s a → E1M1FiringMapState.Safe q.sp q.lines a →
        E1M1AimEntryFrame.SafeWord (q.sp-112) a →
        load32 out.core.memory a=load32 s.memory a) ∧
      E1M1AimStampImage.Image s.memory out.core.memory q.lines q.epoch (history q seen cells) := by
  obtain ⟨_,_,collected,after,⟨n,hn,run⟩,source,tail,state,_,_,pc,_,frame,stampImage⟩ :=
    E1M1AimStampCollection.collection q pick s f sx sy ex ey entry profile xout yout okX okY
      common height statics scenes payloads room
  have bounded : after.collected.size≤128 := by simpa using state.tracked.room
  have limit : load32 collected.core.memory 0x2c028=E1M1MinimumScan.address after.collected.size := by
    simpa [OriginalLineFinish.cursor,E1M1MinimumScan.address,BitVec.ofNat_add] using state.tracked.cursor
  have sp : collected.core.regs 4-24=q.sp-136 := by
    rw [state.stack]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have pushed : collected.core.regs 4-28=q.sp-140 := by
    rw [state.stack]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have target : OriginalInterceptSetup.callback collected.core=0x2b760 := by
    unfold OriginalInterceptSetup.callback
    rw [state.stack]
    have addr : q.sp-(112#32)+68=q.sp-44 := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rw [addr,frame _ callbackSafe.initial callbackSafe.walk]
    rw [entry.stack] at argument
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using argument
  have protect : E1M1AimFirstSelection.Protected (collected.core.regs 4) after.collected := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · rw [state.stack]; exact separated.cursor
    · intro i hi off ho
      rw [state.stack]; exact separated.records i (by omega) off ho
    · rw [state.stack]; exact FloorCaller.apart_symm (separated.cursor 24 (by simp))
    · rw [pushed]; exact cursorCall
    · intro i hi off ho
      rw [pushed]; exact callbackSafe.records i (by omega) off ho
    · rw [state.stack]; exact FloorCaller.apart_symm (separated.cursor 4 (by simp))
  obtain ⟨m,hm,out,dispatch,outcome,shape,saved,slot,words⟩ :=
    E1M1AimFirstSlot.execution collected.core collected.flags after.collected
      (E1M1ThingFinish.resolve q.lines q.objects) bounded limit state.tracked.encoded protect target
  rw [OriginalPathXStep.at_pc _ _ pc] at dispatch
  rw [sp] at outcome shape saved slot
  have collectRun := (run.transfer E1M1TraversalEntry.program [] E1M1TraversalEntry.contains_collection (by simp)).transfer
    program [] E1M1FirstIntercept.contains_entry (by simp)
  refine ⟨collected,after,out,⟨n+m,by omega,E1M1PspriteStep.prefix_trans collectRun dispatch⟩,
    source,tail,state,outcome,shape,saved,slot,?_,?_⟩
  · intro a initSafe loopSafe callSafe
    exact (words a (by rw [state.stack]; exact callSafe)).trans (frame a initSafe loopSafe)
  · exact transport s.memory collected.core.memory out.core.memory q.lines q.epoch _ 475 state.size stampImage
      (fun a member => words a (by rw [state.stack]; exact stampSafe a member))


/-- Retain the exact image beside the derived live callback invariant. -/
theorem persistent (q : Context) (pick : Int32 → Int32 → Cell)
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
    (separated : E1M1TraversalEntry.Protected q)
    (callbackSafe : CallbackSafe q s)
    (argument : load32 s.memory (s.regs 4+8)=0x2b760)
    (cursorCall : Apart 0x2c028 (q.sp-140))
    (room : budget q (sourceRoute pick 64 (E1M1FiringGridState.initial (path q sx sy ex ey) xout yout))≤128)
    (portals : Nat → Option E1M1AimCatalog.Portal) (distance z : Fixed)
    (initial : ∀ grid stamps after,
      E1M1LiveWalk.source q.world q.trace 64
        (E1M1FiringGridState.initial (path q sx sy ex ey) xout yout)
        (Array.replicate q.world.lines.size false) {trace:=q.trace}=
        .ok (E1M1LoopReplay.pack grid stamps after) →
      E1M1AimEntryPersistent.Initial q s after.collected portals distance z)
    (stampSafe : ∀ a∈stampWords q.lines 475, E1M1AimEntryFrame.SafeWord (q.sp-112) a) :
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
      Outcome after.collected (E1M1ThingFinish.resolve q.lines q.objects) (q.sp-136) out ∧
      E1M1AimStackShape.Shape (q.sp-136) out ∧
      load32 out.core.memory ((q.sp-136)+20)=0x2cb0b ∧
      load32 out.core.memory (q.sp-136)=0x2b760 ∧
      (out.pc=0x2b760 → E1M1AimTraversalInvariant.Persistent out.core after.collected after.collected
        (E1M1ThingFinish.resolve q.lines q.objects) portals distance z) ∧
      (∀ a, E1M1PathMapSetup.Safe s a → E1M1FiringMapState.Safe q.sp q.lines a →
        E1M1AimEntryFrame.SafeWord (q.sp-112) a →
        load32 out.core.memory a=load32 s.memory a) ∧
      E1M1AimStampImage.Image s.memory out.core.memory q.lines q.epoch (history q seen cells) := by
  obtain ⟨collected,after,out,run,source,tail,state,outcome,shape,saved,slot,frame,stampImage⟩ :=
    selection q pick s f sx sy ex ey entry profile xout yout okX okY
      common height statics scenes payloads separated callbackSafe argument cursorCall room stampSafe
  refine ⟨collected,after,out,run,source,tail,state,outcome,shape,saved,slot,?_,frame,stampImage⟩
  intro live
  exact E1M1AimEntryPersistent.persistent q s out after.collected portals distance z
    (initial _ _ after source) (by simpa using state.tracked.room) separated outcome live frame slot

/-- The same complete query executes ordered aiming and returns, retaining its exact
stamp image. Future freshness is conditional on initial words, including on wrap. -/
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
    (separated : E1M1TraversalEntry.Protected q)
    (callbackSafe : CallbackSafe q s)
    (argument : load32 s.memory (s.regs 4+8)=0x2b760)
    (cursorCall : Apart 0x2c028 (q.sp-140))
    (room : budget q (sourceRoute pick 64 (E1M1FiringGridState.initial (path q sx sy ex ey) xout yout))≤128)
    (scene : Scene) (shooter : Nat) (thing : SolidThing) (distance : Fixed)
    (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (initial : ∀ grid stamps after,
      E1M1LiveWalk.source q.world q.trace 64
        (E1M1FiringGridState.initial (path q sx sy ex ey) xout yout)
        (Array.replicate q.world.lines.size false) {trace:=q.trace}=
        .ok (E1M1LoopReplay.pack grid stamps after) →
      Initial q s scene shooter thing after.collected distance portals walls who ∧
      ∃ path, Source q scene shooter thing after path distance portals walls)
    (watched : List Word)
    (watchedRead : ∀ addr∈watched, E1M1AimQueryCatalog.Protected q s addr)
    (watchedSafe : ∀ addr∈watched, E1M1AimSavedWords.Protect (view q s) addr)
    (stampSafe : ∀ a∈stampWords q.lines 475, E1M1AimEntryFrame.SafeWord (q.sp-112) a)
    (stampProtected : ∀ a∈stampWords q.lines 475, E1M1AimSavedWords.Protect (view q s) a) :
    let g := E1M1FiringGridState.initial (path q sx sy ex ey) xout yout
    let cells := sourceRoute pick 64 g
    ∃ (after path : PathResult) (out : X86Control.State) (answer : AimResult) (n : Nat),
      n≤228+bound q cells+7*after.collected.size+
        after.collected.size*(157+7*after.collected.size) ∧
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] n ⟨s,f,0x2c8a0⟩ out ∧
      q.world.pathTraverse sx sy ex ey 3 (fun _ _ => true)=.ok path ∧
      E1M1AimSource.afterPath scene shooter thing path distance=.ok answer ∧
      out.core.regs 0=answer.slope.raw.toBitVec ∧
      E1M1AimSavedCaller.Restores ⟨s,f,0x2c8a0⟩ (q.sp-136) out ∧
      E1M1AimReturnedTarget.Image after.collected (resolve q.lines q.objects) out answer ∧
      E1M1BulletAim.ProbeResult out.core answer ∧
      (∀ addr∈watched, load32 out.core.memory addr=load32 s.memory addr) ∧
      E1M1AimStampImage.Image s.memory out.core.memory q.lines q.epoch
        (history q (Array.replicate q.world.lines.size false) cells) ∧
      (E1M1AimStampImage.Fresh s.memory q.lines (q.epoch+1) 475 →
        E1M1AimStampImage.Fresh out.core.memory q.lines (load32 out.core.memory 0x13580+1) 475) := by
  obtain ⟨collected,after,middle,⟨n,hn,run⟩,source,tail,state,outcome,shape,first,slot,livePersistent,frame,stampImage⟩ :=
    persistent q pick s f sx sy ex ey entry profile xout yout okX okY
      common height statics scenes payloads separated callbackSafe argument cursorCall room
      portals distance thing.shootHeight (by
        intro grid stamps after result
        exact (initial grid stamps after result).1.persistent) stampSafe
  obtain ⟨before,path,model⟩ := initial _ _ after source
  have image := E1M1AimQueryCatalog.image q s middle frame
  have keep (a : Word) (safe : E1M1AimQueryCatalog.Protected q s a) :
      load32 middle.core.memory a=load32 s.memory a := image a safe
  have actors (live : middle.pc=0x2b760) := E1M1AimEntryCatalog.actors
    (view q s) middle.core scene shooter after.collected (resolve q.lines q.objects) who
    (E1M1AimQueryCatalog.Protected q s) image (E1M1AimQueryCatalog.live_stack q s _ _ middle outcome live)
    before.actorReads before.actors
  have wallsBefore (live : middle.pc=0x2b760) := E1M1AimEntryCatalog.walls
    (view q s) middle.core after.collected (resolve q.lines q.objects) walls
    (E1M1AimQueryCatalog.Protected q s) image (E1M1AimQueryCatalog.live_stack q s _ _ middle outcome live)
    before.wallReads before.wallCatalog
  have targetSafe (live : middle.pc=0x2b760) := E1M1AimMapFrame.stable_word
    (view q s) middle.core 0x2b9f8
    (E1M1AimQueryCatalog.live_stack q s _ _ middle outcome live) before.targetSafe
  have protect (live : middle.pc=0x2b760) (a : Word) (member : a∈E1M1AimSavedCaller.words (q.sp-136)) :=
    E1M1AimSavedWords.transport (view q s) middle.core a
      (E1M1AimQueryCatalog.live_stack q s _ _ middle outcome live) (before.savedSafe a member)
  have cursor : E1M1AimCallerCursor.CursorSafe (q.sp-136) := by
    intro a member
    exact (before.savedSafe a member).1.2.2.1
  have combinedSafe (a : Word) (member : a∈watched ++ stampWords q.lines 475) :
      E1M1AimSavedWords.Protect (view q s) a := by
    rcases List.mem_append.mp member with old | stamp
    · exact watchedSafe a old
    · exact stampProtected a stamp
  obtain ⟨m,hm,out,answer,returned,value,restored,answerSource,targetImage,probe,kept⟩ := E1M1AimCallerFrame.execution
    scene shooter thing path after distance (resolve q.lines q.objects) portals walls who
    model.represented model.wallMap model.covered model.empty model.query model.available
    (q.sp-136) middle outcome livePersistent
    ((keep _ (before.globalReads _ (by simp))).trans before.bottom)
    ((keep _ (before.globalReads _ (by simp))).trans before.top)
    actors wallsBefore targetSafe
    ((keep _ (before.globalReads _ (by simp))).trans before.null)
    protect cursor shape model.nonnull first
    ((keep _ (before.callerReads 84 (by simp [callerSlots]))).trans before.second)
    (watched ++ stampWords q.lines 475)
    (fun live addr member => E1M1AimSavedWords.transport (view q s) middle.core addr
      (E1M1AimQueryCatalog.live_stack q s _ _ middle outcome live) (combinedSafe addr member))
    (fun addr member => (combinedSafe addr member).1.2.2.1)
  have finalImage := transport s.memory middle.core.memory out.core.memory q.lines q.epoch _ 475
    state.size stampImage (fun a member => kept a (List.mem_append_right _ member))
  refine ⟨after,path,out,answer,n+m,by omega,
    E1M1AimProgramLink.append FloorCaller.cm [] n m ⟨s,f,0x2c8a0⟩ middle out run returned,
    (tail _).trans model.query,answerSource,value,
    restores q s f middle out image before.callerReads restored,targetImage,probe,
    fun addr member => (kept addr (List.mem_append_left _ member)).trans (keep addr (watchedRead addr member)),finalImage,?_⟩
  intro fresh
  have nextFresh := E1M1AimStampImage.next_fresh s.memory out.core.memory q.lines q.epoch _ finalImage
    (by simpa only [state.size] using fresh)
  simpa only [state.size] using nextFresh
end Doom.Proofs.E1M1AimStampQuery
