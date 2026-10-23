import Doom.Proofs.E1M1NoiseFuelBound
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1NoiseMap
open Verification X86 X86Memory X86Control BlockSummary E1M1NoisePreservation E1M1NoiseFootprint
open E1M1NoiseLineProgress

/-- A sector's original line-count/pointer fields and ordered line-pointer array.
This describes machine memory, not a replacement graph-search algorithm. -/
structure SectorLines where
  address : Word
  base : Word
  lines : List Word
  deriving DecidableEq, Repr

def entryAddress (e : SectorLines) (i : Nat) : Word := e.base+BitVec.ofNat 32 (4*i)
def reads (e : SectorLines) : List Word :=
  [e.address+(78#32),e.address+(82#32)] ++ (List.range e.lines.length).map (entryAddress e)
def mapReads (table : List SectorLines) : List Word := table.flatMap reads

structure Rep (e : SectorLines) (mem : Memory) : Prop where
  count : load32 mem (e.address+(78#32))=BitVec.ofNat 32 e.lines.length
  pointer : load32 mem (e.address+(82#32))=e.base
  entries : ∀ i : Fin e.lines.length, load32 mem (entryAddress e i.val)=e.lines[i.val]

def MapRep (table : List SectorLines) (mem : Memory) : Prop := ∀ e, e ∈ table → Rep e mem

def Bounded (table : List SectorLines) (limit : Nat) : Prop :=
  ∀ e, e ∈ table → e.lines.length≤limit ∧ e.lines.length≤2147483647

theorem entry_mem (e : SectorLines) (i : Fin e.lines.length) : entryAddress e i.val ∈ reads e := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨i.val,List.mem_range.mpr i.isLt,rfl⟩

theorem Rep.frame {e before after writes} (rep : Rep e before)
    (frame : PlayerHeight.Frame before after writes)
    (safe : E1M1NoiseLedger.Protect (reads e) writes) : Rep e after := by
  refine ⟨?_,?_,?_⟩
  · exact (frame _ (safe _ (by simp [reads]))).trans rep.count
  · exact (frame _ (safe _ (by simp [reads]))).trans rep.pointer
  · intro i
    exact (frame _ (safe _ (entry_mem e i))).trans (rep.entries i)

theorem MapRep.frame {table before after writes} (rep : MapRep table before)
    (frame : PlayerHeight.Frame before after writes)
    (safe : E1M1NoiseLedger.Protect (mapReads table) writes) : MapRep table after := by
  intro e he
  exact (rep e he).frame frame (fun a ha => safe a (List.mem_flatMap.mpr ⟨e,he,ha⟩))

theorem MapRep.sector_step {table s} (rep : MapRep table s.memory)
    (safe : E1M1NoiseLedger.Protect (mapReads table) (sectorWrites s)) :
    MapRep table (E1M1NoiseAlert.sectorResult s).core.memory := rep.frame (sector_frame s) safe

theorem MapRep.dispatch_step {table s} (rep : MapRep table s.memory)
    (safe : E1M1NoiseLedger.Protect (mapReads table) (lineWrites s)) :
    MapRep table (E1M1NoiseIteration.dispatched s).core.memory := rep.frame (dispatch_frame s) safe

theorem MapRep.traversal {table phase s t w} (rep : MapRep table s.core.memory)
    (trace : Trace phase s t w) (safe : E1M1NoiseLedger.Protect (mapReads table) w) :
    MapRep table t.core.memory := rep.frame trace.frame safe

/-- A live loop cursor: ESI is the array index and EBP its wrapping byte offset.
No monotonicity or successor cursor is assumed. -/
structure Cursor (e : SectorLines) (s : X86Memory.State) : Prop where
  sector : s.regs 3=e.address
  live : (s.regs 6).toNat<e.lines.length
  offset : s.regs 5=BitVec.ofNat 32 (4*(s.regs 6).toNat)

theorem Rep.count_nat {e s} (rep : Rep e s.memory) (sector : s.regs 3=e.address)
    (small : e.lines.length≤2147483647) : E1M1NoiseLineProgress.count s=e.lines.length := by
  simp only [E1M1NoiseLineProgress.count,sector,rep.count,BitVec.toNat_ofNat]
  omega

theorem Cursor.selected {e s} (cursor : Cursor e s) (rep : Rep e s.memory) :
    (NoiseTraversal.selected s).regs 2=e.lines[(s.regs 6).toNat]'cursor.live := by
  simp only [NoiseTraversal.selected,put,write,ite_true,cursor.sector,rep.pointer,cursor.offset]
  exact rep.entries ⟨(s.regs 6).toNat,cursor.live⟩

theorem Cursor.remaining_eq {e s} (cursor : Cursor e s.core) (rep : Rep e s.core.memory)
    (small : e.lines.length≤2147483647) : remaining s=e.lines.length-(s.core.regs 6).toNat := by
  rw [remaining,rep.count_nat cursor.sector small]

private theorem next_index {e s} (cursor : Cursor e s.core) (small : e.lines.length≤2147483647) :
    ((advance s).core.regs 6).toNat=(s.core.regs 6).toNat+1 := by
  change (s.core.regs 6+(1#32)).toNat=_
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
  have := cursor.live
  omega

/-- The actual signed branch agrees with the next index in the finite array. -/
theorem Cursor.advance_branch {e s} (cursor : Cursor e s.core) (rep : Rep e s.core.memory)
    (small : e.lines.length≤2147483647) :
    (advance s).pc=0x26fa8 ↔ (s.core.regs 6).toNat+1<e.lines.length := by
  have idx := next_index cursor small
  have natCount := rep.count_nat cursor.sector small
  have stepInt : (s.core.regs 6+(1#32)).toInt=Int.ofNat ((s.core.regs 6).toNat+1) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by
      change 2*((advance s).core.regs 6).toNat<2^32
      rw [idx]; have := cursor.live; omega)]
    change Int.ofNat ((advance s).core.regs 6).toNat=_
    rw [idx]
  have countInt : (load32 s.core.memory (s.core.regs 3+(78#32))).toInt=Int.ofNat e.lines.length := by
    rw [BitVec.toInt_eq_toNat_of_lt (by change 2*count s.core<2^32; rw [natCount]; omega)]
    change Int.ofNat (count s.core)=_; rw [natCount]
  simp [advance,NoiseTraversal.advanced,put,write,stepInt,countInt]
  omega

theorem Cursor.after_advance {e s} (cursor : Cursor e s.core) (rep : Rep e s.core.memory)
    (small : e.lines.length≤2147483647) (more : (advance s).pc=0x26fa8) : Cursor e (advance s).core := by
  have idx := next_index cursor small
  refine ⟨?_,?_,?_⟩
  · simpa [advance,NoiseTraversal.advanced,put,write] using cursor.sector
  · rw [idx]; exact (cursor.advance_branch rep small).mp more
  · change s.core.regs 5+(4#32)=_
    rw [cursor.offset,idx]
    simp [Nat.mul_add,BitVec.ofNat_add]

theorem Cursor.after_dispatch {e s} (cursor : Cursor e s)
    (safe : DispatchSafe s) : Cursor e (E1M1NoiseIteration.dispatched s).core := by
  have regs := dispatch_regs s safe
  exact ⟨regs.1.trans cursor.sector,by simpa only [regs.2.1] using cursor.live,
    by simpa only [regs.2.1,regs.2.2] using cursor.offset⟩

/-- Actual child-frame restoration recovers the same parent's array cursor. -/
theorem Cursor.after_child {layout e s u w n} (cursor : Cursor e s.core)
    (dispatchSafe : DispatchSafe s.core)
    (child : E1M1NoiseAccounting.CheckedTrace layout .sector (dispatch s) u w n)
    (frameSafe : E1M1NoisePreservation.SectorSafe (dispatch s).core w) : Cursor e u.core := by
  have before := cursor.after_dispatch dispatchSafe
  have restored := child.restores_sector frameSafe
  exact ⟨restored.b.trans before.sector,by simpa only [restored.si] using before.live,
    by simpa only [restored.bp,restored.si] using before.offset⟩

private theorem apart_translate (p a b : Word) (h : Apart a b) : Apart (p+a) (p+b) := by
  intro i j eq
  rw [BitVec.add_assoc,BitVec.add_assoc] at eq
  exact h i j ((BitVec.add_right_inj p).mp eq)

private theorem updated_lines (s : X86Memory.State) :
    load32 (NoiseAlert.updated s).core.memory (s.regs 3+(78#32))=NoiseAlert.lines s := by
  change load32 (store32 (NoiseAlert.costMemory s) (s.regs 3+(22#32)) _) _=_
  rw [load_store_apart _ _ _ _ (apart_translate _ _ _ (by unfold Apart; decide))]
  unfold NoiseAlert.costMemory
  rw [load_store_apart _ _ _ _ (apart_translate _ _ _ (by unfold Apart; decide))]
  rfl

private theorem updated_positive (s : X86Memory.State) (more : (NoiseAlert.updated s).pc=0x26fa6) :
    0<(load32 (NoiseAlert.updated s).core.memory (s.regs 3+(78#32))).toInt := by
  rw [updated_lines]
  simp only [NoiseAlert.updated] at more
  split at more <;> omega

/-- Sector entry derives a live index-zero cursor from the actual nonempty
branch, including zero-length descriptors: those cannot reach that branch. -/
theorem start_step {table e s limit} (member : e ∈ table) (rep : MapRep table s.core.memory)
    (input : s.core.regs 0=e.address) (bounds : Bounded table limit)
    (mapSafe : E1M1NoiseLedger.Protect (mapReads table) (sectorWrites s.core))
    (more : (sector s).pc=0x26fa6) :
    MapRep table (startLines s).core.memory ∧ Cursor e (startLines s).core ∧ remaining (startLines s)≤limit := by
  have after := rep.sector_step mapSafe
  have ch := E1M1NoiseLedger.sector_more_charge s.core more
  have enter : (NoiseAlert.gate (NoiseAlert.prepared s.core)).pc=0x26f83 := by
    by_cases h : E1M1NoiseLedger.admitted s.core
    · exact h
    · simp [E1M1NoiseLedger.charge,h] at ch
  have gateSector : (NoiseAlert.gate (NoiseAlert.prepared s.core)).core.regs 3=e.address := by
    simp only [NoiseAlert.gate]; split <;>
      simpa [NoiseAlert.prepared,NoiseAlert.prepareTail,NoiseAlert.saveThree,
        NoiseAlert.saveTwo,X86Routine.pushWord,put,write] using input
  have regs : (startLines s).core.regs 3=e.address ∧ (startLines s).core.regs 6=0 ∧
      (startLines s).core.regs 5=0 := by
    simp [startLines,sector,E1M1NoiseAlert.sectorResult,enter,NoiseAlert.updated,
      NoiseTraversal.initialized,put,write,gateSector]
  have pos : 0<e.lines.length := by
    have known := (after e member).count
    simp only [sector,E1M1NoiseAlert.sectorResult,if_pos enter] at more known
    have positive := updated_positive _ more
    rw [gateSector,known] at positive
    by_cases zero : e.lines.length=0
    · simp [zero] at positive
    · omega
  have cursor : Cursor e (startLines s).core :=
    ⟨regs.1,by simpa [regs.2.1] using pos,
      by simp [regs.2.1,regs.2.2]⟩
  refine ⟨after,cursor,?_⟩
  rw [cursor.remaining_eq (after e member) (bounds e member).2]
  have := (bounds e member).1
  omega

/-- Derive both the next cursor and strict remaining-line decrease for a skip
from one map representation and the actual write footprint. -/
theorem skip_step {table e s} (member : e ∈ table) (rep : MapRep table s.core.memory)
    (cursor : Cursor e s.core) (small : e.lines.length≤2147483647)
    (dispatchSafe : DispatchSafe s.core)
    (mapSafe : E1M1NoiseLedger.Protect (mapReads table) (lineWrites s.core))
    (more : (advance (dispatch s)).pc=0x26fa8) :
    MapRep table (advance (dispatch s)).core.memory ∧ Cursor e (advance (dispatch s)).core ∧
    remaining (advance (dispatch s))+1=remaining s := by
  have after := rep.dispatch_step mapSafe
  have cur := cursor.after_dispatch dispatchSafe
  refine ⟨after,cur.after_advance (after e member) small more,?_⟩
  apply skip_remaining s dispatchSafe
  · intro b hb
    apply mapSafe _ (List.mem_flatMap.mpr ⟨e,member,?_⟩) b hb
    simpa only [cursor.sector] using (show e.address+(78#32) ∈ reads e by simp [reads])
  · rw [(rep e member).count_nat cursor.sector small]; exact cursor.live
  · rw [(rep e member).count_nat cursor.sector small]; exact small

/-- The same derived facts after a nested child. No post-child map or cursor
relation is a premise. Saved-frame and map-word separation remain explicit. -/
theorem child_step {table layout e s u w n} (member : e ∈ table) (rep : MapRep table s.core.memory)
    (cursor : Cursor e s.core) (small : e.lines.length≤2147483647)
    (dispatchSafe : DispatchSafe s.core)
    (child : E1M1NoiseAccounting.CheckedTrace layout .sector (dispatch s) u w n)
    (frameSafe : E1M1NoisePreservation.SectorSafe (dispatch s).core w)
    (mapSafe : E1M1NoiseLedger.Protect (mapReads table) (lineWrites s.core++w))
    (more : (advance u).pc=0x26fa8) :
    MapRep table (advance u).core.memory ∧ Cursor e (advance u).core ∧ remaining (advance u)+1=remaining s := by
  have afterDispatch := rep.dispatch_step (fun a ha b hb => mapSafe a ha b (List.mem_append_left _ hb))
  have after := afterDispatch.traversal child.trace (fun a ha b hb => mapSafe a ha b (List.mem_append_right _ hb))
  have cur := cursor.after_child dispatchSafe child frameSafe
  refine ⟨after,cur.after_advance (after e member) small more,?_⟩
  apply E1M1NoiseLineProgress.child_remaining child dispatchSafe frameSafe
  · intro b hb
    apply mapSafe _ (List.mem_flatMap.mpr ⟨e,member,?_⟩) b hb
    simpa only [cursor.sector] using (show e.address+(78#32) ∈ reads e by simp [reads])
  · rw [(rep e member).count_nat cursor.sector small]; exact cursor.live
  · rw [(rep e member).count_nat cursor.sector small]; exact small
end Doom.Proofs.E1M1NoiseMap
