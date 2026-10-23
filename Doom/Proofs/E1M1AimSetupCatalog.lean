import Doom.Proofs.E1M1AimSetupEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimSetupCatalog
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1CellWalkInvariant (Context)
open E1M1AimCatalog (Portal)
open E1M1AimQueryCatalog (view Protected)
open E1M1AimCycleInvariant (Layout)
open E1M1AimMapFrame (StableWord)
open E1M1ThingFinish (resolve)
open E1M1AimQueryCaller (callerSlots)
open E1M1PathMapQuery (traversal)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- Catalog and protection obligations still needed at the computed traversal
boundary. The range and eye-height values are supplied by executed setup. -/
structure Persistent (q : Context) (s : X86Memory.State) (hits : Array Intercept)
    (portals : Nat → Option Portal) : Prop where
  layout : Layout (view q s) hits
  query : ∀ a∈[(0x2b9b8#32),0x2b9a8], StableWord (view q s) a
  globals : E1M1AimNextLine.ClipGlobalsSafe (view q s)
  portalReads : E1M1AimEntryCatalog.PortalReads hits (resolve q.lines q.objects) portals (Protected q s)
  catalog : E1M1AimCatalog.Catalog (view q s) hits (resolve q.lines q.objects) portals
  valueReads : ∀ a∈[(0x2b9b8#32),0x2b9a8], Protected q s a

/-- Explicit residual boundary contracts, not a claim that all of them have
been transported from aim-entry memory. Generated globals/return are omitted. -/
structure Remaining (q : Context) (s : X86Memory.State) (scene : Scene) (shooter : Nat)
    (hits : Array Intercept)
    (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word) : Prop where
  persistent : Persistent q s hits portals
  actorReads : E1M1AimEntryCatalog.ActorReads hits (resolve q.lines q.objects) (Protected q s)
  wallReads : E1M1AimEntryCatalog.WallReads hits (resolve q.lines q.objects) walls (Protected q s)
  actors : E1M1AimActorCatalog.Catalog (view q s) scene shooter hits (resolve q.lines q.objects) who
  wallCatalog : E1M1AimWallCatalog.Catalog (view q s) hits (resolve q.lines q.objects) walls
  targetSafe : E1M1AimMapFrame.StableWord (view q s) 0x2b9f8
  savedSafe : ∀ a∈E1M1AimSavedCaller.words (q.sp-136), E1M1AimSavedWords.Protect (view q s) a
  globalReads : ∀ a∈[(0x2c1e4#32),0x2c1e8,0x2b9f8], Protected q s a
  callerReads : ∀ off∈callerSlots, Protected q s ((q.sp-136)+off)

/-- Fill the generated parts of the query contract using actual setup stores.
No assumed target nullness, clipping values, eye height, range or inner return. -/
theorem initial (q : Context) (s : X86Memory.State) (scene : Scene) (shooter : Nat)
    (thing : SolidThing) (angle : Angle) (distance : Fixed) (hits : Array Intercept)
    (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (h : E1M1AimSetupEntry.Inputs q s thing angle distance)
    (remaining : Remaining q (traversal s).core scene shooter hits portals walls who) :
    E1M1AimQueryCaller.Initial q (traversal s).core scene shooter thing hits distance portals walls who := by
  obtain ⟨range,eye,bottom,top,target⟩ := E1M1AimSetupEntry.globals s thing angle distance _ _ h.geometry
  have saved := congrArg Prod.fst (E1M1AimSetupEntry.call s thing angle distance _ _ h.geometry)
  have sp := (E1M1AimSetupEntry.entry q s thing angle distance h).stack
  have slot : (q.sp-136)+84=(traversal s).core.regs 4 := by
    rw [sp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  refine ⟨?_,remaining.actorReads,remaining.wallReads,remaining.actors,remaining.wallCatalog,
    remaining.targetSafe,remaining.savedSafe,remaining.globalReads,bottom,top,target,
    remaining.callerReads,?_⟩
  · exact ⟨remaining.persistent.layout,remaining.persistent.query,remaining.persistent.globals,
      remaining.persistent.portalReads,remaining.persistent.catalog,remaining.persistent.valueReads,range,eye⟩
  · rw [slot]; exact saved
/-- The original aim caller's return word survives the prologue and setup.
The address is the original ESP, not an arbitrary reached return slot. -/
theorem return_address (q : Context) (s : X86Memory.State)
    (stack : s.regs 4=q.sp-24) (safe : E1M1PathMapQuery.Safe s (s.regs 4)) :
    load32 (traversal s).core.memory ((q.sp-136)+112)=load32 s.memory (s.regs 4) := by
  have slot : (q.sp-136)+112=s.regs 4 := by
    rw [stack]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rw [slot]
  exact E1M1PathMapQuery.traversal_frame s _ safe
end Doom.Proofs.E1M1AimSetupCatalog
