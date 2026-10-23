import Doom.Proofs.E1M1AimActorCaller
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimActorQuery
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

open E1M1AimQueryCaller (Initial Source callerSlots restores)

/-- The continuous query now discharges the controller's ProbeResult premise.
The selected actor-tagged record/pointer image, slope, and caller restoration all belong to
this same execution. Initial contracts are unchanged; no endpoint target fact
is assumed. Earlier ray setup and reachable-state justification remain separate. -/
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
    ∃ (after path : PathResult) (out : X86Control.State) (answer : AimResult) (n : Nat),
      n≤228+bound q cells+7*after.collected.size+
        after.collected.size*(157+7*after.collected.size) ∧
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] n ⟨s,f,0x2c8a0⟩ out ∧
      q.world.pathTraverse sx sy ex ey 3 (fun _ _ => true)=.ok path ∧
      E1M1AimSource.afterPath scene shooter thing path distance=.ok answer ∧
      out.core.regs 0=answer.slope.raw.toBitVec ∧
      E1M1AimSavedCaller.Restores ⟨s,f,0x2c8a0⟩ (q.sp-136) out ∧
      E1M1AimActorCaller.Image after.collected (resolve q.lines q.objects) out answer ∧
      E1M1BulletAim.ProbeResult out.core answer := by
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
  obtain ⟨m,hm,out,answer,returned,value,restored,answerSource,targetImage,probe⟩ := E1M1AimActorCaller.execution
    scene shooter thing path after distance (resolve q.lines q.objects) portals walls who
    model.represented model.wallMap model.covered model.empty model.query model.available
    (q.sp-136) middle outcome persistent
    ((keep _ (before.globalReads _ (by simp))).trans before.bottom)
    ((keep _ (before.globalReads _ (by simp))).trans before.top)
    actors wallsBefore targetSafe
    ((keep _ (before.globalReads _ (by simp))).trans before.null)
    protect cursor shape model.nonnull first
    ((keep _ (before.callerReads 84 (by simp [callerSlots]))).trans before.second)
  exact ⟨after,path,out,answer,n+m,by omega,
    E1M1AimProgramLink.append FloorCaller.cm [] n m ⟨s,f,0x2c8a0⟩ middle out run returned,
    (tail _).trans model.query,answerSource,value,
    restores q s f middle out image before.callerReads restored,targetImage,probe⟩
end Doom.Proofs.E1M1AimActorQuery
