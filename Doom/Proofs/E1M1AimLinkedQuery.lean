import Doom.Proofs.E1M1AimProgramLink
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimLinkedQuery
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

open E1M1AimQueryCaller (Initial Source)

/-- One continuous machine execution under a single compatible instruction map,
from path-query entry through collection, all ordered hits, and the real return
chain. Initial memory/source contracts remain explicit; no middle state or
execution prefix is assumed. Earlier ray setup and reachability are separate. -/
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
      E1M1AimSavedCaller.Restores ⟨s,f,0x2c8a0⟩ (q.sp-136) out := by
  obtain ⟨after,path,middle,out,answer,n,m,hn,hm,query,returned,pathSource,aimSource,value,restored⟩ :=
    E1M1AimQueryCaller.execution q pick s f sx sy ex ey entry profile xout yout okX okY
      common height statics scenes payloads separated callbackSafe argument cursorCall room
      scene shooter thing distance portals walls who initial
  exact ⟨after,path,out,answer,n+m,by omega,
    E1M1AimProgramLink.append FloorCaller.cm [] n m ⟨s,f,0x2c8a0⟩ middle out query returned,
    pathSource,aimSource,value,restored⟩
end Doom.Proofs.E1M1AimLinkedQuery
