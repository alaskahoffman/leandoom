import Doom.Proofs.OriginalLineDispatchAppend
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.OriginalLineCollection
open Verification X86 X86Memory X86Control BlockSummary

def slot (base : Word) (i : Nat) (off : Word) := base+BitVec.ofNat 32 (12*i)+off

theorem slots_apart (base : Word) (i j : Nat) (hi : i<128) (hj : j<128) (ne : i≠j)
    (a b : Word) (ha : a∈[(0#32),4,8]) (hb : b∈[(0#32),4,8]) :
    Apart (base+BitVec.ofNat 32 (12*i)+a) (base+BitVec.ofNat 32 (12*j)+b) := by
  intro x y eq
  have eq' : BitVec.ofNat 32 (12*i)+a+BitVec.ofNat 32 x.val =
      BitVec.ofNat 32 (12*j)+b+BitVec.ofNat 32 y.val := by
    have cancel (u : Word) : base+u-base=u := by
      rw [BitVec.add_comm,BitVec.add_sub_cancel]
    have sub := congrArg (fun v : Word => v-base) eq
    simpa only [BitVec.add_assoc,cancel] using sub
  have value (k off : Nat) (hk : k<128) (ho : off≤8) (z : Fin 4) :
      (BitVec.ofNat 32 (12*k)+BitVec.ofNat 32 off+BitVec.ofNat 32 z.val).toNat=12*k+off+z.val := by
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    have hz := z.isLt
    omega
  have num := congrArg BitVec.toNat eq'
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha hb
  rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl
  all_goals
    try simp only [show (4 : Word)=(4#32) by decide,show (8 : Word)=(8#32) by decide] at num
    rw [value i _ hi (by decide) x,value j _ hj (by decide) y] at num
    have hx := x.isLt
    have hy := y.isLt
    omega

/-- The reserve counts remaining candidate visits, so a duplicate or rejection
can release a slot while an append consumes one. All arithmetic is natural. -/
structure Tracks (s : X86Memory.State) (base : Word) (resolve : Collision.Intercept → Word)
    (hits : Array Collision.Intercept) (reserve : Nat) : Prop where
  encoded : OriginalLineFinish.Encodes s.memory base resolve hits
  cursor : OriginalLineFinish.cursor s=base+BitVec.ofNat 32 (12*hits.size)
  room : hits.size+reserve≤128

/-- Array storage is separated from dispatch and callback scratch writes, and
from the mutable cursor global. Distinct record separation is derived below. -/
structure Layout (s : X86Memory.State) (base : Word) : Prop where
  dispatch : ∀ i<128, ∀ off∈[(0#32),4,8], OriginalLineDispatch.Safe s (slot base i off)
  side : ∀ i<128, ∀ off∈[(0#32),4,8], OriginalLineCrossing.SideSafe (OriginalLineDispatch.view s) (slot base i off)
  scratch : ∀ i<128, ∀ off∈[(0#32),4,8], OriginalLineCrossing.ScratchSafe (OriginalLineDispatch.view s) (slot base i off)
  metadata : ∀ i<128, ∀ off∈[(0#32),4,8], Apart (slot base i off) (0x2c028#32)

theorem capacity (s : X86Memory.State) (base : Word) (resolve : Collision.Intercept → Word)
    (hits : Array Collision.Intercept) (reserve : Nat) (h : Tracks s base resolve hits (reserve+1)) :
    hits.size<128 := by have bound := h.room; omega

/-- An old slot cannot alias the next append, even if the base address wraps. -/
theorem old_record_safe (s : X86Memory.State) (base : Word) (resolve : Collision.Intercept → Word)
    (hits : Array Collision.Intercept) (reserve : Nat) (h : Tracks s base resolve hits (reserve+1))
    (layout : Layout s base) (i : Nat) (hi : i<hits.size) (off : Word) (ho : off∈[(0#32),4,8]) :
    OriginalLineCrossing.Protected (OriginalLineDispatch.view s) (slot base i off) := by
  have cap := capacity s base resolve hits reserve h
  refine ⟨layout.side i (by omega) off ho,layout.scratch i (by omega) off ho,?_⟩
  intro addr ha
  change addr∈[OriginalLineFinish.cursor s,OriginalLineFinish.cursor s+(4#32),
    OriginalLineFinish.cursor s+(8#32),(0x2c028#32)] at ha
  rw [h.cursor] at ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl
  · simpa only [slot,BitVec.add_zero] using slots_apart base i hits.size (by omega) cap (by omega) off (0#32) ho (by simp)
  · exact slots_apart base i hits.size (by omega) cap (by omega) off (4#32) ho (by simp)
  · exact slots_apart base i hits.size (by omega) cap (by omega) off (8#32) ho (by simp)
  · exact layout.metadata i (by omega) off ho

/-- This transition derives capacity and old/new slot separation from the
collection invariant. The production append and original memory agree. -/
theorem append (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (frac : Fixed) (flags : Nat) (p v w : Word)
    (ready : OriginalLineDispatch.Ready s trace line frac flags p v w)
    (r : Collision.PathResult) (id : Nat) (base : Word) (resolve : Collision.Intercept → Word) (reserve : Nat)
    (tracked : Tracks s base resolve r.collected (reserve+1)) (layout : Layout s base)
    (nonnegative : ¬frac.raw<0) (clear : (flags &&& 4 != 0 && frac.raw<65536 && line.back.isNone)=false)
    (pointer : resolve ⟨frac,true,id⟩=p) :
    Collision.appendIntercept r ⟨frac,true,id⟩=.ok {r with collected:=r.collected.push ⟨frac,true,id⟩} ∧
    Tracks (OriginalLineDispatch.result s).core base resolve (r.collected.push ⟨frac,true,id⟩) reserve := by
  have cap := capacity s base resolve r.collected reserve tracked
  obtain ⟨live,encoded,cursor⟩ := OriginalLineDispatchAppend.live_append s trace line frac flags p v w ready
    r id base resolve nonnegative clear cap tracked.encoded tracked.cursor pointer
    (by intro off ho; rw [tracked.cursor]; exact layout.metadata r.collected.size cap off ho)
    (fun i hi off ho => layout.dispatch i (by omega) off ho)
    (fun i hi off ho => old_record_safe s base resolve r.collected reserve tracked layout i hi off ho)
  refine ⟨live,encoded,?_,?_⟩
  · simpa only [OriginalLineFinish.cursor,Array.size_push] using cursor
  · have bound := tracked.room
    simp only [Array.size_push]; omega

/-- The collection transition belongs to the actual original execution, and
returns to the list header with its cursor advanced exactly once. -/
theorem append_execution (s : X86Memory.State) (f : Option Flags)
    (trace : Collision.Divline) (line : Collision.Line) (frac : Fixed) (flags : Nat) (p v w : Word)
    (ready : OriginalLineDispatch.Ready s trace line frac flags p v w)
    (r : Collision.PathResult) (id : Nat) (base : Word) (resolve : Collision.Intercept → Word) (reserve : Nat)
    (tracked : Tracks s base resolve r.collected (reserve+1)) (layout : Layout s base)
    (nonnegative : ¬frac.raw<0) (clear : (flags &&& 4 != 0 && frac.raw<65536 && line.back.isNone)=false)
    (pointer : resolve ⟨frac,true,id⟩=p)
    (saved : OriginalLineTail.RecordSafe (OriginalLineDispatch.view s) ((OriginalLineDispatch.view s).regs 4-(12#32))) :
    (∃ steps≤281, X86Routine.Prefix OriginalLineDispatch.program [] steps ⟨s,f,0x2c57f⟩ (OriginalLineDispatch.result s)) ∧
    (OriginalLineDispatch.result s).pc=0x2c57f ∧
    (OriginalLineDispatch.result s).core.regs 2=s.regs 2+(2#32) ∧
    (OriginalLineDispatch.result s).core.regs 4=s.regs 4 ∧
    Tracks (OriginalLineDispatch.result s).core base resolve (r.collected.push ⟨frac,true,id⟩) reserve := by
  have obs := OriginalLineDispatch.continued s trace line frac flags p v w ready saved (Or.inr clear)
  exact ⟨OriginalLineDispatch.execution s trace line frac flags p v w ready f,obs.1,obs.2.1,obs.2.2,
    (append s trace line frac flags p v w ready r id base resolve reserve tracked layout nonnegative clear pointer).2⟩

/-- A no-append visit releases its conservative reserve without changing the
represented ordered records or cursor. -/
theorem preserve (s t : X86Memory.State) (base : Word) (resolve : Collision.Intercept → Word)
    (hits : Array Collision.Intercept) (reserve : Nat) (h : Tracks s base resolve hits (reserve+1))
    (cursor : OriginalLineFinish.cursor t=OriginalLineFinish.cursor s)
    (memory : ∀ i<hits.size, ∀ off∈[(0#32),4,8], load32 t.memory (slot base i off)=load32 s.memory (slot base i off)) :
    Tracks t base resolve hits reserve := by
  refine ⟨?_,cursor.trans h.cursor,?_⟩
  · intro i hi
    simp only [slot] at memory
    have old := h.encoded i hi
    unfold OriginalLineFinish.RecordAt at old ⊢
    rw [show load32 t.memory (base+BitVec.ofNat 32 (12*i))=load32 s.memory (base+BitVec.ofNat 32 (12*i)) by
      simpa only [slot,BitVec.add_zero] using memory i hi (0#32) (by simp),memory i hi (4#32) (by simp),memory i hi (8#32) (by simp)]
    exact old
  · have bound := h.room; omega

theorem duplicate (s : X86Memory.State) (base : Word) (resolve : Collision.Intercept → Word)
    (hits : Array Collision.Intercept) (reserve : Nat) (h : Tracks s base resolve hits (reserve+1))
    (last : OriginalLineCell.itemWord s≠(0xffffffff#32))
    (seen : OriginalLineCell.already (OriginalLineCell.header s).core) :
    Tracks (OriginalLineCell.visit s).core base resolve hits reserve := by
  have memory := (OriginalLineCell.skip_observe s last seen).1
  exact preserve s (OriginalLineCell.visit s).core base resolve hits reserve h
    (by unfold OriginalLineFinish.cursor; rw [memory]) (by intro i hi off ho; rw [memory])

theorem rejected (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line) (p v w : Word)
    (ready : OriginalLineReject.Ready s trace line p v w)
    (base : Word) (resolve : Collision.Intercept → Word) (hits : Array Collision.Intercept) (reserve : Nat)
    (h : Tracks s base resolve hits (reserve+1)) (layout : Layout s base)
    (cursor : OriginalLineDispatch.Safe s (0x2c028#32) ∧
      OriginalLineCrossing.SideSafe (OriginalLineDispatch.view s) (0x2c028#32)) :
    Tracks (OriginalLineReject.result s).core base resolve hits reserve := by
  have cap := capacity s base resolve hits reserve h
  apply preserve s (OriginalLineReject.result s).core base resolve hits reserve h
  · exact OriginalLineReject.frame s trace line p v w ready _ cursor.1 cursor.2
  · intro i hi off ho
    exact OriginalLineReject.frame s trace line p v w ready _ (layout.dispatch i (by omega) off ho)
      (layout.side i (by omega) off ho)

end Doom.Proofs.OriginalLineCollection
