import Doom.Proofs.E1M1AimStampRestart
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimNextContext
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1CellWalkInvariant (Context Cell Common)
open E1M1QueryCollection (path)
open E1M1AimRetryGeometry (nextAngle)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- Retry changes the trace and visit epoch, not the world or allocation layout. -/
def context (q : Context) (thing : SolidThing) (angle : Angle) (second : Bool) : Context :=
  {q with epoch:=q.epoch+1, trace:=(path q thing.x thing.y
    (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).1
    (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).2).trace}

/-- Numeric stepping determines which metadata the next query will actually use. -/
def route (q : Context) (pick : Int32 → Int32 → Cell) (thing : SolidThing)
    (angle : Angle) (second : Bool) (nextX nextY : Int32 × Fixed × Fixed) :=
  E1M1GridRoute.sourceRoute pick 64 (E1M1FiringGridState.initial
    (path q thing.x thing.y (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).1
      (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).2) nextX nextY)

/-- Common memory-layout obligations do not depend on the current trace/epoch. -/
theorem common (q : Context) (thing : SolidThing) (angle : Angle) (second : Bool) (h : Common q) :
    Common (context q thing angle second) :=
  ⟨h.mapLayout,h.stamps,h.returns,h.epochSafe,h.stampSafe,h.locals,h.cursor,h.records,h.dimension⟩

/-- Existing payload data and its setup guards are independent of trace/epoch.
New trace words are supplied by the next initialization, not by this payload. -/
theorem payload (q : Context) (thing : SolidThing) (angle : Angle) (second : Bool)
    (s : X86Memory.State) (c : Cell)
    (data : E1M1QueryImages.Payload s.memory q c)
    (safe : E1M1AimPreRayMemory.PayloadSafe s q c) :
    E1M1QueryImages.Payload s.memory (context q thing angle second) c ∧
    E1M1AimPreRayMemory.PayloadSafe s (context q thing angle second) c :=
  ⟨⟨data.encoded,data.back,data.objects,data.linked,data.selection⟩,
    ⟨safe.lines,safe.back,safe.objects,safe.links,safe.global,safe.selected⟩⟩

/-- Reconstruct the entire next pre-ray input contract from the restored request,
prepared data and prior exact stamp history. No input field is postulated at next. -/
theorem inputs (q : Context) (s : X86Memory.State) (next : X86Control.State)
    (thing : SolidThing) (angle : Angle) (distance : Fixed) (second : Bool) (cells : List Cell)
    (h : E1M1AimSetupEntry.Inputs q s thing angle distance)
    (request : E1M1AimRetryRequest.Request second s next)
    (data : E1M1AimRetryInputs.Prepared q next.core thing (nextAngle second angle) cells)
    (seen : Array Bool) (size : seen.size=475)
    (image : E1M1AimStampImage.Image s.memory next.core.memory q.lines q.epoch seen)
    (before : E1M1AimStampImage.Fresh s.memory q.lines (q.epoch+1) 475) :
    E1M1AimSetupEntry.Inputs (context q thing angle second) next.core thing
      (nextAngle second angle) (Fixed.ofInt 1024) := by
  have fresh := E1M1AimStampImage.next_fresh s.memory next.core.memory q.lines q.epoch seen image
    (by simpa only [size] using before)
  refine ⟨data.geometry,request.stack.trans h.stack,?_,rfl,h.lineCount,?_,data.map,?_,
    E1M1AimRetryData.safe s next.core _ request.stack h.epochSafe,?_,?_,?_,?_⟩
  · change q.epoch+1=load32 next.core.memory 0x13580+1
    rw [image.counter]
  · simpa only [context,E1M1PathMapSetup.Safe,OriginalPathInit.writes,E1M1PathMapQuery.withStack,
      write,ite_true,request.stack] using h.flagSafe
  · simpa only [request.stack] using h.cursorSafe
  · intro j hj
    exact E1M1AimRetryData.safe s next.core _ request.stack (h.stampSafe j hj)
  · intro j hj
    exact fresh j (by change j<q.world.lines.size at hj; rw [h.lineCount] at hj; simpa only [size] using hj)
  · simpa only [request.stack] using h.traceSafe
  · simpa only [request.stack] using h.activeSafe

/-- The established next input contract supplies every path-traversal entry field. -/
theorem entry (q : Context) (s : X86Memory.State) (next : X86Control.State)
    (thing : SolidThing) (angle : Angle) (distance : Fixed) (second : Bool) (cells : List Cell)
    (h : E1M1AimSetupEntry.Inputs q s thing angle distance)
    (request : E1M1AimRetryRequest.Request second s next)
    (data : E1M1AimRetryInputs.Prepared q next.core thing (nextAngle second angle) cells)
    (seen : Array Bool) (size : seen.size=475)
    (image : E1M1AimStampImage.Image s.memory next.core.memory q.lines q.epoch seen)
    (before : E1M1AimStampImage.Fresh s.memory q.lines (q.epoch+1) 475) :
    E1M1QueryCollection.Entry (context q thing angle second) (E1M1PathMapQuery.traversal next.core).core
      thing.x thing.y (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).1
      (thing.attackEndpoint (nextAngle second angle) (Fixed.ofInt 1024)).2 :=
  E1M1AimSetupEntry.entry _ next.core thing _ _
    (inputs q s next thing angle distance second cells h request data seen size image before)
end Doom.Proofs.E1M1AimNextContext
