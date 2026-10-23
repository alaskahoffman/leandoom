import Doom.Proofs.E1M1AimReadyCaller
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimQueryCaller
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1MixedCellWalk (inside Admitted Images budget bound history)
open E1M1GridRoute (sourceRoute)
open E1M1QueryCollection (path Entry)
open E1M1QueryCallback (CallbackSafe)
open E1M1AimCatalog (Portal)
open E1M1AimQueryCatalog (view Protected)
open E1M1ThingFinish (resolve)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- Caller words that already exist before path traversal. Setup creates its
own inner return address; that address is intentionally absent here. -/
def callerSlots : List Word := [84,96,100,104,108,112]

/-- Initial memory and static layout only. No reached-state contracts, execution
prefix, or result of the machine query is assumed. -/
structure Initial (q : Context) (s : X86Memory.State) (scene : Scene) (shooter : Nat)
    (thing : SolidThing) (hits : Array Intercept) (distance : Fixed)
    (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word) : Prop where
  persistent : E1M1AimEntryPersistent.Initial q s hits portals distance thing.shootHeight
  actorReads : E1M1AimEntryCatalog.ActorReads hits (resolve q.lines q.objects) (Protected q s)
  wallReads : E1M1AimEntryCatalog.WallReads hits (resolve q.lines q.objects) walls (Protected q s)
  actors : E1M1AimActorCatalog.Catalog (view q s) scene shooter hits (resolve q.lines q.objects) who
  wallCatalog : E1M1AimWallCatalog.Catalog (view q s) hits (resolve q.lines q.objects) walls
  targetSafe : E1M1AimMapFrame.StableWord (view q s) 0x2b9f8
  savedSafe : ∀ a∈E1M1AimSavedCaller.words (q.sp-136), E1M1AimSavedWords.Protect (view q s) a
  globalReads : ∀ a∈[(0x2c1e4#32),0x2c1e8,0x2b9f8], Protected q s a
  bottom : load32 s.memory 0x2c1e4=aimBottomSlope.raw.toBitVec
  top : load32 s.memory 0x2c1e8=aimTopSlope.raw.toBitVec
  null : load32 s.memory 0x2b9f8=0
  callerReads : ∀ off∈callerSlots, Protected q s ((q.sp-136)+off)
  second : load32 s.memory ((q.sp-136)+84)=0x2bbff

/-- Remaining source-side and pointer obligations for the collected hits. These
are not established for all reachable E1M1 states by this module. -/
structure Source (q : Context) (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (original path : PathResult) (distance : Fixed)
    (portals : Nat → Option Portal) (walls : Nat → Prop) : Prop where
  represented : E1M1AimSourceCatalog.Represents scene original.collected portals
  wallMap : E1M1AimWallCatalog.Represents scene original.collected walls
  covered : E1M1AimLineCoverage.Coverage original.collected walls portals
  empty : original.visited=#[]
  query : E1M1QuerySource.visitHits original (fun _ _ => true)=.ok path
  available : E1M1AimOrderedLoop.Available scene shooter original.collected portals distance thing.shootHeight
  nonnull : ∀ j<original.collected.size, resolve q.lines q.objects original.collected[j]!≠0

/-- Carry caller restoration back to the memory at query entry, rather than
claiming only restoration from the intermediate first-scan state. -/
theorem restores (q : Context) (s : X86Memory.State) (f : Option Flags)
    (middle out : X86Control.State)
    (frame : E1M1AimEntryCatalog.Image s.memory middle.core.memory (Protected q s))
    (reads : ∀ off∈callerSlots, Protected q s ((q.sp-136)+off))
    (restored : E1M1AimSavedCaller.Restores middle (q.sp-136) out) :
    E1M1AimSavedCaller.Restores ⟨s,f,0x2c8a0⟩ (q.sp-136) out := by
  obtain ⟨sp,pc,bp,di,si,cx⟩ := restored
  have keep (off : Word) (member : off∈callerSlots) := frame _ (reads off member)
  exact ⟨sp,pc.trans (congrArg BitVec.toNat (keep 112 (by simp [callerSlots]))),
    bp.trans (keep 96 (by simp [callerSlots])),di.trans (keep 100 (by simp [callerSlots])),
    si.trans (keep 104 (by simp [callerSlots])),cx.trans (keep 108 (by simp [callerSlots]))⟩

/-- Query prefix and complete hit-loop/return share exactly the same middle
state. All caller-entry facts are derived from initial contracts. The two
program maps are explicit: their single-program linkage remains separate. -/
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
      ∃ path, Source q scene shooter thing after path distance portals walls) :
    let g := E1M1FiringGridState.initial (path q sx sy ex ey) xout yout
    let cells := sourceRoute pick 64 g
    ∃ (after path : PathResult) (middle out : X86Control.State) (answer : AimResult) (n m : Nat),
      n≤207+bound q cells+7*after.collected.size ∧
      m≤after.collected.size*(157+7*after.collected.size)+21 ∧
      X86CodeMemory.Prefix FloorCaller.cm E1M1FirstIntercept.program [] n ⟨s,f,0x2c8a0⟩ middle ∧
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimCompletedReturn.program [] m middle out ∧
      q.world.pathTraverse sx sy ex ey 3 (fun _ _ => true)=.ok path ∧
      E1M1AimSource.afterPath scene shooter thing path distance=.ok answer ∧
      out.core.regs 0=answer.slope.raw.toBitVec ∧
      E1M1AimSavedCaller.Restores ⟨s,f,0x2c8a0⟩ (q.sp-136) out := by
  obtain ⟨collected,after,middle,⟨n,hn,run⟩,source,tail,state,outcome,shape,first,slot,persistent,frame⟩ :=
    E1M1AimQueryPersistent.execution q pick s f sx sy ex ey entry profile xout yout okX okY
      common height statics scenes payloads separated callbackSafe argument cursorCall room
      portals distance thing.shootHeight (by
        intro grid stamps after result
        exact (initial grid stamps after result).1.persistent)
  obtain ⟨before,path,model⟩ := initial _ _ after source
  have image := E1M1AimQueryCatalog.image q s middle frame
  have keep (a : Word) (safe : Protected q s a) :
      load32 middle.core.memory a=load32 s.memory a := image a safe
  have actors (live : middle.pc=0x2b760) := E1M1AimEntryCatalog.actors
    (view q s) middle.core scene shooter after.collected (resolve q.lines q.objects) who
    (Protected q s) image (E1M1AimQueryCatalog.live_stack q s _ _ middle outcome live)
    before.actorReads before.actors
  have wallsBefore (live : middle.pc=0x2b760) := E1M1AimEntryCatalog.walls
    (view q s) middle.core after.collected (resolve q.lines q.objects) walls
    (Protected q s) image (E1M1AimQueryCatalog.live_stack q s _ _ middle outcome live)
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
  obtain ⟨m,hm,out,answer,returned,value,restored,answerSource⟩ := E1M1AimReadyCaller.execution
    scene shooter thing path after distance (resolve q.lines q.objects) portals walls who
    model.represented model.wallMap model.covered model.empty model.query model.available
    (q.sp-136) middle outcome persistent
    ((keep _ (before.globalReads _ (by simp))).trans before.bottom)
    ((keep _ (before.globalReads _ (by simp))).trans before.top)
    actors wallsBefore targetSafe
    ((keep _ (before.globalReads _ (by simp))).trans before.null)
    protect cursor shape model.nonnull first
    ((keep _ (before.callerReads 84 (by simp [callerSlots]))).trans before.second)
  exact ⟨after,path,middle,out,answer,n,m,hn,hm,run,returned,
    (tail _).trans model.query,answerSource,value,restores q s f middle out image before.callerReads restored⟩
end Doom.Proofs.E1M1AimQueryCaller
