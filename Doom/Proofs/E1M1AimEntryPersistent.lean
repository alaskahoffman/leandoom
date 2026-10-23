import Doom.Proofs.E1M1AimQuerySlot
import Doom.Proofs.E1M1AimQueryCatalog
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimEntryPersistent
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1CellWalkInvariant (Context)
open E1M1AimCatalog (Portal)
open E1M1AimQueryCatalog (view Protected)
open E1M1AimCycleInvariant (Layout QuerySafe)
open E1M1AimMapFrame (StableWord)
open E1M1ThingFinish (resolve)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- Initial memory and static callback-layout contracts. This contains neither
a reached state nor the callback-slot value: setup creates that slot later. -/
structure Initial (q : Context) (s : X86Memory.State) (hits : Array Intercept)
    (portals : Nat → Option Portal) (distance z : Fixed) : Prop where
  layout : Layout (view q s) hits
  query : ∀ a∈[(0x2b9b8#32),0x2b9a8], StableWord (view q s) a
  globals : E1M1AimNextLine.ClipGlobalsSafe (view q s)
  portalReads : E1M1AimEntryCatalog.PortalReads hits (resolve q.lines q.objects) portals (Protected q s)
  catalog : E1M1AimCatalog.Catalog (view q s) hits (resolve q.lines q.objects) portals
  valueReads : ∀ a∈[(0x2b9b8#32),0x2b9a8], Protected q s a
  range : load32 s.memory 0x2b9b8=distance.raw.toBitVec
  eye : load32 s.memory 0x2b9a8=z.raw.toBitVec

/-- Rebase the static layout without marking or pretending to consume a hit. -/
theorem layout (s t : X86Memory.State) (hits : Array Intercept)
    (sameStack : t.regs 4=s.regs 4) (safe : Layout s hits) : Layout t hits := by
  rcases safe with ⟨ret,records,cursor,floor,ceiling,helper,target,store,record,bounds,slot⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [E1M1AimReturnFrame.Safe,sameStack] using ret
  · simpa only [E1M1AimRecordFrame.RecordsSafe,E1M1AimRecordFrame.ReadSafe,sameStack] using records
  · simpa only [E1M1AimRecordFrame.ReadSafe,sameStack] using cursor
  · simpa only [E1M1AimFloorEntry.ReadSafe,sameStack] using floor
  · simpa only [E1M1AimCeilingEntry.ReadSafe,sameStack] using ceiling
  · simpa only [E1M1AimOpening.CallerSafe,sameStack] using helper
  · simpa only [sameStack] using target
  · simpa only [sameStack] using store
  · simpa only [sameStack] using record
  · simpa only [sameStack] using bounds
  · simpa only [E1M1AimRecordFrame.ReadSafe,sameStack] using slot

/-- The first selected argument supplies EBX, so the query globals' separation
from the current fraction mark follows from their static buffer protection. -/
theorem query_safe (s : X86Memory.State) (out : X86Control.State) (hits : Array Intercept)
    (lookup : Intercept → Word) (base : Word) (fraction : Int32) (j : Nat)
    (bounded : hits.size≤128) (stack : out.core.regs 4=s.regs 4)
    (selection : E1M1HistoryDispatch.Selection hits hits [] lookup 0x2b760 base out fraction j)
    (safe : ∀ a∈[(0x2b9b8#32),0x2b9a8], StableWord s a) : QuerySafe out.core := by
  have pointer := selection.ready.pointer.trans selection.argument
  have inside : j<128 := by have := selection.inside; omega
  intro a member
  have prior := E1M1AimMapFrame.stable_word s out.core a stack (safe a member)
  exact ⟨prior.1,by rw [pointer]; exact prior.2.1 j inside,prior.2.2.2⟩

/-- Setup's existing record protection separates its callback slot from every
future fraction mark. No new slot-mark premise is needed at the callback. -/
theorem slot_marks (q : Context) (hits : Array Intercept) (bounded : hits.size≤128)
    (separated : E1M1TraversalEntry.Protected q) :
    ∀ i<hits.size, Apart (q.sp-136) (E1M1MinimumScan.address i) := by
  intro i hi
  have safe := separated.records i (by omega) 0 (by simp) 24 (by simp)
  have addr : q.sp-112-24=q.sp-136 := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rw [addr] at safe
  exact FloorCaller.apart_symm (by simpa [OriginalLineCollection.slot,E1M1MinimumScan.address,BitVec.ofNat_add] using safe)

/-- The real mixed line/actor resolver ignores fraction marks by definition. -/
theorem resolver (lines : Word) (objects : Nat → Word) (hit : Intercept) :
    resolve lines objects {hit with frac := ⟨2147483647⟩}=resolve lines objects hit := by
  rfl

/-- Assemble all Persistent fields from initial contracts, actual selection,
query memory transport and the slot written by setup. Nothing here supposes a
prior callback has run. The slot premise is supplied by QuerySlot.execution. -/
theorem persistent (q : Context) (s : X86Memory.State) (out : X86Control.State)
    (hits : Array Intercept) (portals : Nat → Option Portal) (distance z : Fixed)
    (initial : Initial q s hits portals distance z)
    (bounded : hits.size≤128) (separated : E1M1TraversalEntry.Protected q)
    (outcome : E1M1AimFirstSelection.Outcome hits (resolve q.lines q.objects) (q.sp-136) out)
    (live : out.pc=0x2b760)
    (frame : ∀ a, E1M1PathMapSetup.Safe s a → E1M1FiringMapState.Safe q.sp q.lines a →
      E1M1AimEntryFrame.SafeWord (q.sp-112) a → load32 out.core.memory a=load32 s.memory a)
    (slot : load32 out.core.memory (q.sp-136)=0x2b760) :
    E1M1AimTraversalInvariant.Persistent out.core hits hits (resolve q.lines q.objects) portals distance z := by
  have stack := E1M1AimQueryCatalog.live_stack q s hits (resolve q.lines q.objects) out outcome live
  have base : out.core.regs 4+4=q.sp-136 := by
    rw [stack]; simp [view,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have kept := E1M1AimQueryCatalog.image q s out frame
  have catalog := E1M1AimEntryCatalog.portals (view q s) out.core hits (resolve q.lines q.objects)
    portals (Protected q s) kept stack initial.portalReads initial.catalog
  rcases outcome with empty|⟨best,chosen,far,pc⟩|⟨fraction,j,selected⟩
  · have pc := empty.2.1; omega
  · omega
  · refine ⟨bounded,layout _ _ hits stack initial.layout,
      query_safe _ out hits _ _ fraction j bounded stack selected initial.query,
      E1M1AimNextLine.clip_globals _ _ stack initial.globals,catalog,
      (kept _ (initial.valueReads _ (by simp))).trans initial.range,
      (kept _ (initial.valueReads _ (by simp))).trans initial.eye,?_,?_,?_⟩
    · rw [base]; exact slot
    · rw [base]; exact slot_marks q hits bounded separated
    · intro i hi; exact resolver q.lines q.objects hits[i]!
end Doom.Proofs.E1M1AimEntryPersistent
