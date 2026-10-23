import Doom.Proofs.E1M1AimQueryTarget
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimTargetDecision
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32

/-- The existing linked query map already contains the controller instructions.
Their decoded operations and lengths are unchanged by this connection. -/
theorem contains (pc : Nat) (present : X86ReturnCleanup.embed OriginalBulletSlope.program pc≠none) :
    E1M1AimProgramLink.program pc=X86ReturnCleanup.embed OriginalBulletSlope.program pc := by
  have inside : 0x2d7c0≤pc ∧ pc<0x2d823 := by
    by_cases inside : 0x2d7c0≤pc ∧ pc<0x2d823
    · exact inside
    · simp [X86ReturnCleanup.embed,OriginalBulletSlope.program,OriginalBulletSlope.bytesProgram,inside] at present
  have all : ∀ i : Fin 99, E1M1AimProgramLink.program (0x2d7c0+i.val)=
      X86ReturnCleanup.embed OriginalBulletSlope.program (0x2d7c0+i.val) := by decide
  have same : 0x2d7c0+(pc-0x2d7c0)=pc := by omega
  simpa only [same] using all ⟨pc-0x2d7c0,by omega⟩

/-- After a center or right probe, execute the real four-instruction target test
and slope store. A zero slope does not choose the retry branch when a target exists. -/
theorem decision (second : Bool) (out : X86Control.State) (answer : AimResult)
    (related : E1M1BulletAim.ProbeResult out.core answer)
    (resume : out.pc=if second then 0x2d7f8 else 0x2d7d5) :
    X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] 4 out
      (OriginalBulletSlope.decision second out.core) ∧
    load32 (OriginalBulletSlope.decision second out.core).core.memory 0x2c0c0=answer.slope.raw.toBitVec ∧
    (OriginalBulletSlope.decision second out.core).pc=
      if answer.target.isSome then 0x2d81e else (if second then 0x2d807 else 0x2d7e4) := by
  have run := (X86ReturnCleanup.lift (X86CodeMemory.lift_success
    (OriginalBulletSlope.decision_execution second out.core out.flags) FloorCaller.cm)).transfer
    E1M1AimProgramLink.program contains
  have atReturn : out=⟨out.core,out.flags,if second then 0x2d7f8 else 0x2d7d5⟩ := by rw [←resume]
  rw [←atReturn] at run
  refine ⟨run,?_,?_⟩
  · change load32 (OriginalBulletSlope.stored out.core).memory 0x2c0c0=answer.slope.raw.toBitVec
    exact (OriginalBulletSlope.stored_slope out.core).trans related.slope
  · by_cases miss : OriginalBulletSlope.target out.core=0
    · have no : answer.target.isSome=false := by
        cases eq : answer.target.isSome with
        | false => rfl
        | true => exact False.elim ((related.presence.mpr eq) miss)
      simp only [OriginalBulletSlope.decision,miss,if_pos,no,Bool.false_eq_true,if_false]
    · have yes := related.presence.mp miss
      simp only [OriginalBulletSlope.decision,miss,if_false,yes,if_true]

open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1MixedCellWalk (inside Admitted Images budget bound history)
open E1M1GridRoute (sourceRoute)
open E1M1QueryCollection (path Entry)
open E1M1QueryCallback (CallbackSafe)
open E1M1AimCatalog (Portal)
open E1M1AimQueryCatalog (view Protected)
open E1M1ThingFinish (resolve)
attribute [local irreducible] SolidThing.shootHeight

open E1M1AimQueryCaller (Initial Source callerSlots restores)

/-- The complete continuous query supplies its own target-presence evidence and
returns to the controller address saved in initial memory. Append the actual
branch and stored bullet slope without an endpoint PC or target premise. This
covers one center/right probe decision, not all three autoaim queries. -/
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
    (second : Bool)
    (resume : (load32 s.memory ((q.sp-136)+112)).toNat=if second then 0x2d7f8 else 0x2d7d5) :
    let g := E1M1FiringGridState.initial (path q sx sy ex ey) xout yout
    let cells := sourceRoute pick 64 g
    ∃ (after path : PathResult) (out : X86Control.State) (answer : AimResult) (n : Nat),
      n≤232+bound q cells+7*after.collected.size+
        after.collected.size*(157+7*after.collected.size) ∧
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimProgramLink.program [] n ⟨s,f,0x2c8a0⟩ out ∧
      q.world.pathTraverse sx sy ex ey 3 (fun _ _ => true)=.ok path ∧
      E1M1AimSource.afterPath scene shooter thing path distance=.ok answer ∧
      load32 out.core.memory 0x2c0c0=answer.slope.raw.toBitVec ∧
      out.pc=(if answer.target.isSome then 0x2d81e else (if second then 0x2d807 else 0x2d7e4)) := by
  obtain ⟨after,path,returned,answer,n,hn,run,pathSource,aimSource,value,restored,image,related⟩ :=
    E1M1AimQueryTarget.execution q pick s f sx sy ex ey entry profile xout yout okX okY
      common height statics scenes payloads separated callbackSafe argument cursorCall room
      scene shooter thing distance portals walls who initial
  have pc := restored.2.1.trans resume
  obtain ⟨tail,slope,branch⟩ := decision second returned answer related pc
  exact ⟨after,path,OriginalBulletSlope.decision second returned.core,answer,n+4,by omega,
    run.trans tail,pathSource,aimSource,slope,branch⟩
end Doom.Proofs.E1M1AimTargetDecision
