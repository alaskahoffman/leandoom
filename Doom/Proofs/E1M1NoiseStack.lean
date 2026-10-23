import Doom.Proofs.E1M1NoiseAllocation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1NoiseStack
open Verification X86 X86Memory X86Control E1M1NoiseRecursive E1M1NoisePreservation
open E1M1NoiseLedger E1M1NoiseAccounting E1M1NoiseFootprint E1M1NoiseAllocation
open E1M1NoiseMap E1M1NoiseMapGuards

/-- Each admitted recursive level costs 28 bytes (CALL, saved registers and
scratch). The extra allowance also covers a final pruned child and the opening
helper. This bounds a supplied finite trace; it does not assert termination. -/
def need (phase : Phase) (admissions : Nat) : Nat :=
  28*admissions + match phase with | .sector => 20 | .lines => 24

def Reserve (stack : Region) (phase : Phase) (n : Nat) (s : X86Control.State) : Prop :=
  stack.lo+need phase n ≤ (s.core.regs 4).toNat ∧
  (s.core.regs 4).toNat+4 ≤ stack.hi ∧ stack.hi ≤ 2^32

def ceiling (phase : Phase) (s : X86Control.State) : Nat :=
  (s.core.regs 4).toNat + match phase with | .sector => 0 | .lines => 4

/-- All stack writes end at or below this byte boundary; the other writes are
confined to allocated sector objects and the four opening globals. -/
def WritesBelow (table : List SectorLines) (top : Nat) (w : List Word) : Prop :=
  ∀ b ∈ w, (Region.mk 0 top).Contains b ∨
    (∃ e ∈ table, (sectorRegion e.address).Contains b) ∨ globals.Contains b

theorem WritesBelow.append {table top a b} (ha : WritesBelow table top a)
    (hb : WritesBelow table top b) : WritesBelow table top (a++b) := by
  intro x hx
  rcases List.mem_append.mp hx with h|h
  · exact ha x h
  · exact hb x h

theorem WritesBelow.mono {table lo hi w} (h : WritesBelow table lo w)
    (le : lo≤hi) (bound : hi≤2^32) : WritesBelow table hi w := by
  intro b hb
  rcases h b hb with stack|other
  · apply Or.inl
    simp only [Region.Contains] at stack ⊢
    exact ⟨by omega,by omega,bound⟩
  · exact Or.inr other

private theorem sub_nat (a : Word) (n : Nat) (low : n≤a.toNat) :
    (a-BitVec.ofNat 32 n).toNat=a.toNat-n := by
  have := a.isLt
  simp [BitVec.toNat_sub,BitVec.toNat_ofNat]
  omega

theorem Reserve.room {stack phase n s} (h : Reserve stack phase n s) : StackRoom stack s.core := by
  apply stack_room (high:=h.2.1) (bound:=h.2.2)
  rcases h with ⟨low,_,_⟩
  cases phase <;> simp only [need] at low <;> omega

theorem Reserve.mono {stack phase n m s} (h : Reserve stack phase m s) (le : n≤m) :
    Reserve stack phase n s := by
  refine ⟨?_,h.2⟩
  have low := h.1
  cases phase <;> simp only [need] at low ⊢ <;> omega

private theorem Reserve.low {stack phase n s} (h : Reserve stack phase n s) : 20≤(s.core.regs 4).toNat := by
  have := h.1
  cases phase <;> simp only [need] at * <;> omega

private theorem Reserve.cap {stack phase n s} (h : Reserve stack phase n s) : ceiling phase s≤2^32 := by
  have hi := h.2.1; have bound := h.2.2
  cases phase <;> simp only [ceiling] <;> omega

theorem Reserve.start {stack n s} (h : Reserve stack .sector (n+1) s) :
    Reserve stack .lines n (startLines s) := by
  have low := h.1
  simp only [need] at low
  have sp : ((startLines s).core.regs 4).toNat=(s.core.regs 4).toNat-24 := by
    rw [start_sp]; exact sub_nat _ 24 (by omega)
  simp only [Reserve,need,sp]
  exact ⟨by omega,by have := h.2.1; omega,h.2.2⟩

private theorem dispatch_call_sp {s : X86Control.State} (call : (dispatch s).pc=0x26f60) :
    (dispatch s).core.regs 4=s.core.regs 4-(4#32) := by
  simp only [dispatch,dispatch_sp,call,ite_true]

private theorem dispatch_skip_sp {s : X86Control.State} (skip : (dispatch s).pc=0x27006) :
    (dispatch s).core.regs 4=s.core.regs 4 := by
  rw [dispatch,dispatch_sp]
  have no : (dispatch s).pc≠0x26f60 := by omega
  exact if_neg no

/-- Stack pointer restoration is structural: the epilogue never pops ESP. It
holds even before proving preservation of the saved register values. -/
theorem child_stack {s u w n} {ls : List Word}
    (child : CheckedTrace ls .sector (dispatch s) u w n) (call : (dispatch s).pc=0x26f60) :
    u.core.regs 4=s.core.regs 4 := by
  have view := child.trace.view.stack
  simpa [base,dispatch_call_sp call,BitVec.sub_eq_add_neg,BitVec.add_assoc] using view

theorem Reserve.child {stack n s} (h : Reserve stack .lines n s)
    (call : (dispatch s).pc=0x26f60) : Reserve stack .sector n (dispatch s) := by
  have low := h.1
  simp only [need] at low
  have sp : ((dispatch s).core.regs 4).toNat=(s.core.regs 4).toNat-4 := by
    rw [dispatch_call_sp call]; exact sub_nat _ 4 (by omega)
  simp only [Reserve,need,sp]
  exact ⟨by omega,by have := h.2.1; omega,h.2.2⟩

private theorem mark_below {table stack top s} (a : Allocation table stack)
    (member : s.regs 0∈layout table) : WritesBelow table top (markWrites s) := by
  obtain ⟨e,he,input⟩ := List.mem_map.mp member
  intro b hb
  apply Or.inr; apply Or.inl; refine ⟨e,he,?_⟩
  simp only [markWrites,←input,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl
  · exact sector_contains (a.sectorBound e he) 66 (by decide)
  · exact sector_contains (a.sectorBound e he) 18 (by decide)
  · exact sector_contains (a.sectorBound e he) 22 (by decide)

private theorem sector_below {table stack n s} (a : Allocation table stack)
    (reserve : Reserve stack .sector n s) (member : s.core.regs 0∈layout table) :
    WritesBelow table (ceiling .sector s) (sectorWrites s.core) := by
  change WritesBelow table (ceiling .sector s) (stackWrites s.core++markWrites s.core)
  apply WritesBelow.append _ (mark_below a member)
  intro b hb
  apply Or.inl
  simp only [stackWrites,List.mem_cons,List.not_mem_nil,or_false] at hb
  have low := reserve.low; have cap := reserve.cap
  rcases hb with rfl|rfl|rfl|rfl|rfl <;>
    simp [Region.Contains,ceiling,BitVec.toNat_sub] at cap ⊢ <;> omega

private theorem line_below {table stack n s} (reserve : Reserve stack .lines n s) :
    WritesBelow table (ceiling .lines s) (lineWrites s.core) := by
  intro b hb
  simp only [lineWrites,List.mem_cons,List.not_mem_nil,or_false] at hb
  have low := reserve.low; have cap := reserve.cap
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
  | { apply Or.inl; simp [Region.Contains,ceiling,BitVec.toNat_sub] at cap ⊢; omega }
  | { apply Or.inr; apply Or.inr; apply globals_contains; simp [E1M1NoiseLineProgress.openingGlobals] }

/-- The extra post-prologue protection needed only for sector entry. -/
def FrameBound (table : List SectorLines) (phase : Phase) (s : X86Control.State) (w : List Word) : Prop :=
  match phase with | .sector => BelowFrame table s.core w | .lines => True

/-- A single entry stack budget replaces all per-node stack-room and child
footprint assumptions on an existing checked trace. -/
theorem checked_guards {table stack phase s t w n} (a : Allocation table stack)
    (h : CheckedTrace (layout table) phase s t w n) (reserve : Reserve stack phase n s) :
    MemoryGuards table h ∧ WritesBelow table (ceiling phase s) w ∧ FrameBound table phase s w := by
  induction h with
  | sectorDone s done safe =>
    refine ⟨.sectorDone s done safe (a.map_sector reserve.room safe.member),sector_below a reserve safe.member,?_⟩
    exact mark_below a safe.member
  | sectorMore s t w n more safe body ih =>
    have charge := sector_more_charge s.core more
    have parent : Reserve stack .sector (n+1) s := by simpa only [charge] using reserve
    obtain ⟨guards,writes,frame⟩ := ih parent.start
    have sp : ((startLines s).core.regs 4).toNat=(s.core.regs 4).toNat-24 := by
      rw [start_sp]; exact sub_nat _ 24 (by have := parent.1; simp only [need] at *; omega)
    have boundary : ceiling .lines (startLines s)=(s.core.regs 4).toNat-20 := by
      have := parent.1; simp only [need] at this
      simp only [ceiling,sp]; omega
    refine ⟨.sectorMore s t w n more safe body (a.map_sector reserve.room safe.member) guards,
      (sector_below a reserve safe.member).append (writes.mono ?_ reserve.cap),?_⟩
    · rw [boundary]
      simp only [ceiling,Nat.add_zero]
      omega
    · change WritesBelow table ((s.core.regs 4).toNat-20) ((sectorWrites s.core++w).drop 5)
      have tail := (mark_below (top:=(s.core.regs 4).toNat-20) a safe.member).append (by simpa only [boundary] using writes)
      simpa only [sectorWrites,markWrites,List.cons_append,List.drop] using tail
  | lineDone s opening skip done safe =>
    exact ⟨.lineDone s opening skip done safe (a.map_line reserve.room),line_below reserve,trivial⟩
  | lineMore s t w n opening skip more safe body ih =>
    have sp : (advance (dispatch s)).core.regs 4=s.core.regs 4 := by rw [advance_sp,dispatch_skip_sp skip]
    have next : Reserve stack .lines n (advance (dispatch s)) := by simpa only [Reserve,sp] using reserve
    obtain ⟨guards,writes,_⟩ := ih next
    refine ⟨.lineMore s t w n opening skip more safe body (a.map_line reserve.room)
      (a.dispatch_safe reserve.room) guards,(line_below reserve).append ?_,trivial⟩
    simpa only [ceiling,sp] using writes
  | childDone s u w n opening call safe child ret done ih =>
    have next := reserve.child call
    obtain ⟨guards,writes,_⟩ := ih next
    refine ⟨.childDone s u w n opening call safe child ret done (a.map_line reserve.room) guards,
      (line_below reserve).append (writes.mono ?_ reserve.cap),trivial⟩
    have sp := sub_nat (s.core.regs 4) 4 (by have := reserve.low; omega)
    simp only [ceiling,dispatch_call_sp call,sp]; omega
  | childMore s u t w v n m opening call safe child ret more body ci bi =>
    have childReserve := (reserve.mono (Nat.le_add_right n m)).child call
    obtain ⟨cg,cw,cf⟩ := ci childReserve
    have sp := child_stack child call
    have bodyReserve : Reserve stack .lines m (advance u) := by
      simpa only [Reserve,advance_sp,sp] using reserve.mono (Nat.le_add_left m n)
    obtain ⟨bg,bw,_⟩ := bi bodyReserve
    refine ⟨.childMore s u t w v n m opening call safe child ret more body (a.map_line reserve.room)
      (a.dispatch_safe reserve.room) (a.frame_safe childReserve.room childReserve.low cf) cg bg,
      ((line_below reserve).append (cw.mono ?_ reserve.cap)).append ?_,trivial⟩
    · have sub := sub_nat (s.core.regs 4) 4 (by have := reserve.low; omega)
      simp only [ceiling,dispatch_call_sp call,sub]; omega
    · simpa only [ceiling,advance_sp,sp] using bw

/-- The existing two-credit ledger bound gives a sufficient entry reserve of
56*N+20 bytes below ESP, plus its four-byte incoming return word. No trace-
specific admission count needs to be known by the caller of this theorem. -/
theorem sector_reserve {table stack s t w n}
    (h : CheckedTrace (layout table) .sector s t w n)
    (generation : Word) (xs : Ledger) (shape : addresses xs=layout table)
    (ledger : Represents generation s.core.memory xs)
    (low : stack.lo+56*table.length+20 ≤ (s.core.regs 4).toNat)
    (high : (s.core.regs 4).toNat+4 ≤ stack.hi) (bound : stack.hi≤2^32) :
    Reserve stack .sector n s := by
  have count : n≤2*table.length := by
    simpa only [layout,List.length_map] using h.admission_bound generation xs shape ledger
  refine ⟨?_,high,bound⟩
  simp only [need]
  omega

/-- Derive every extra memory annotation and the full caller-frame restoration
from static allocation, one entry-space bound and the initial ledger. The
finite CheckedTrace (including its own ledger guards) remains a premise. -/
theorem sector_guards {table stack s t w n} (a : Allocation table stack)
    (h : CheckedTrace (layout table) .sector s t w n)
    (generation : Word) (xs : Ledger) (shape : addresses xs=layout table)
    (ledger : Represents generation s.core.memory xs)
    (low : stack.lo+56*table.length+20 ≤ (s.core.regs 4).toNat)
    (high : (s.core.regs 4).toNat+4 ≤ stack.hi) (bound : stack.hi≤2^32) :
    MemoryGuards table h ∧ Restored s.core t := by
  have reserve := sector_reserve h generation xs shape ledger low high bound
  obtain ⟨guards,_,frame⟩ := checked_guards a h reserve
  exact ⟨guards,a.restores h reserve.room reserve.low frame⟩

/-- Stack allocation, visit credit and the shared map description combine into
an explicit evaluator-fuel guarantee, with no supplied MemoryGuards, LoopGuards
or child-footprint annotations. This still concerns a supplied finite trace. -/
theorem sector_budget {table stack s t w n} (a : Allocation table stack)
    (h : CheckedTrace (layout table) .sector s t w n)
    (generation : Word) (xs : Ledger) (shape : addresses xs=layout table)
    (ledger : Represents generation s.core.memory xs)
    (low : stack.lo+56*table.length+20 ≤ (s.core.regs 4).toNat)
    (high : (s.core.regs 4).toNat+4 ≤ stack.hi) (bound : stack.hi≤2^32)
    (limit : Nat) (bounds : Bounded table limit) (map : MapRep table s.core.memory) :
    Restored s.core t ∧ MapRep table t.core.memory ∧
    eval (2*table.length*(limit+1)+1) .sector s=some t := by
  obtain ⟨guards,restored⟩ := sector_guards a h generation xs shape ledger low high bound
  exact ⟨restored,guards.preserves_map map,
    E1M1NoiseMapGuards.sector_budget h guards limit bounds map generation xs shape ledger⟩

end Doom.Proofs.E1M1NoiseStack
