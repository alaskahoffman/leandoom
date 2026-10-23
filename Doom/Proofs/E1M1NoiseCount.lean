import Doom.Proofs.E1M1NoiseGraphAllocation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1NoiseCount
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoisePreservation E1M1NoiseAccounting E1M1NoiseRecursive E1M1NoiseFootprint
open E1M1NoiseAllocation E1M1NoiseStack E1M1NoiseMap E1M1NoiseMapGuards E1M1NoiseLedger

/-- Incoming sector arguments use EDX; the active parent's count lives in ECX. -/
def Legal (count : Word) : Prop := count=0 ∨ count=1
def Entry : Phase → X86Control.State → Prop
  | .sector,s => Legal (s.core.regs 2)
  | .lines,s => Legal (s.core.regs 1)

/-- The original prologue copies the argument, including on a pruned visit. -/
theorem start_count (s : X86Control.State) :
    (startLines s).core.regs 1=s.core.regs 2 := by
  have gate (q : X86Memory.State) : (NoiseAlert.gate q).core.regs 1=q.regs 1 := by
    simp only [NoiseAlert.gate]; split <;> simp [put,write]
  have update (q : X86Memory.State) : (NoiseAlert.updated q).core.regs 1=q.regs 1 := by
    simp [NoiseAlert.updated,write]
  change (sector s).core.regs 1=s.core.regs 2
  simp only [sector,E1M1NoiseAlert.sectorResult]
  split <;> simp [update,gate,NoiseAlert.prepared,NoiseAlert.prepareTail,
    NoiseAlert.saveThree,NoiseAlert.saveTwo,X86Routine.pushWord,put,write]

theorem advance_count (s : X86Control.State) : (advance s).core.regs 1=s.core.regs 1 := by
  simp [advance,NoiseTraversal.advanced,put,write]

private theorem neighbor_count (s : X86Memory.State) :
    (E1M1NoiseOpening.neighbor s).core.regs 1=s.regs 1 := by
  simp only [E1M1NoiseOpening.neighbor]
  split <;> simp [NoiseOpening.neighborGate,NoiseOpening.neighborInputs,
    NoiseOpening.backNeighbor,NoiseOpening.frontNeighbor,put,write]

private theorem line_count (s : X86Memory.State) (f : Option Flags)
    (safe : E1M1NoiseOpeningFrame.CallerSafe s) :
    (E1M1NoiseOpening.lineResult s f).core.regs 1=s.regs 1 := by
  have h := (E1M1NoiseOpeningFrame.opened s f safe).1
  simp only [E1M1NoiseOpening.lineResult]; split
  · simpa only [neighbor_count,NoiseTraversal.openingGate] using h
  · exact h

private theorem block_parent (s : X86Memory.State) :
    (NoiseTraversal.blockResult s).core.regs 1=s.regs 1 := by
  simp only [NoiseTraversal.blockResult]; split
  · simp [NoiseTraversal.recursiveCall,X86Routine.pushWord,put,write]
  · split <;> simp [NoiseTraversal.recursiveCall,X86Routine.pushWord,put,write]

/-- A call passes the parent's count unchanged, or crosses the first sound
blocker (0 to 1). It never crosses a second blocker. This is the actual branch. -/
theorem block_child (s : X86Memory.State) (call : (NoiseTraversal.blockResult s).pc=0x26f60) :
    (NoiseTraversal.blockResult s).core.regs 2=s.regs 1 ∨
    (s.regs 1=0 ∧ (NoiseTraversal.blockResult s).core.regs 2=1) := by
  simp only [NoiseTraversal.blockResult] at call ⊢
  split
  · simp [NoiseTraversal.recursiveCall,X86Routine.pushWord,put,write]
  · split <;> simp_all [NoiseTraversal.recursiveCall,X86Routine.pushWord,put,write]

/-- The helper's saved ECX, neighbor lookup and recursive CALL all preserve
parent ECX, even if the child receives a different EDX argument. -/
theorem dispatch_count (s : X86Memory.State) (safe : E1M1NoiseOpeningFrame.CallerSafe s) :
    (E1M1NoiseIteration.dispatched s).core.regs 1=s.regs 1 := by
  have gate : (NoiseTraversal.lineGate s).core.regs 1=s.regs 1 := by
    simp [NoiseTraversal.lineGate,NoiseTraversal.selected,put,write]
  have h := line_count (NoiseTraversal.lineGate s).core (NoiseTraversal.lineGate s).flags (by
    simpa [E1M1NoiseOpeningFrame.CallerSafe,NoiseTraversal.lineGate,NoiseTraversal.selected,put,write] using safe)
  rw [gate] at h
  simp only [E1M1NoiseIteration.dispatched]; split
  · simp only [E1M1NoiseOpening.blockResult]; split
    · simpa only [block_parent] using h
    · exact h
  · exact gate

theorem dispatch_child (s : X86Memory.State) (safe : E1M1NoiseOpeningFrame.CallerSafe s)
    (call : (E1M1NoiseIteration.dispatched s).pc=0x26f60) :
    (E1M1NoiseIteration.dispatched s).core.regs 2=s.regs 1 ∨
    (s.regs 1=0 ∧ (E1M1NoiseIteration.dispatched s).core.regs 2=1) := by
  have h := line_count (NoiseTraversal.lineGate s).core (NoiseTraversal.lineGate s).flags (by
    simpa [E1M1NoiseOpeningFrame.CallerSafe,NoiseTraversal.lineGate,NoiseTraversal.selected,put,write] using safe)
  have gate : (NoiseTraversal.lineGate s).core.regs 1=s.regs 1 := by
    simp [NoiseTraversal.lineGate,NoiseTraversal.selected,put,write]
  rw [gate] at h
  have endpoints (q : X86Memory.State) (f : Option Flags) :
      (E1M1NoiseOpening.lineResult q f).pc=0x26fee ∨
      (E1M1NoiseOpening.lineResult q f).pc=0x27006 := by
    simp only [E1M1NoiseOpening.lineResult]; split
    · simp only [E1M1NoiseOpening.neighbor]; split <;> exact Or.inl rfl
    · rename_i no
      simp only [NoiseTraversal.openingGate] at no ⊢
      split <;> simp_all
  by_cases two : (NoiseTraversal.lineGate s).pc=0x26fb4
  · simp only [E1M1NoiseIteration.dispatched,if_pos two,E1M1NoiseOpening.blockResult] at call ⊢
    by_cases pass : (E1M1NoiseOpening.lineResult (NoiseTraversal.lineGate s).core (NoiseTraversal.lineGate s).flags).pc=0x26fee
    · simp only [if_pos pass] at call ⊢
      simpa only [h] using block_child _ call
    · simp only [if_neg pass] at call
      have ends := endpoints (NoiseTraversal.lineGate s).core (NoiseTraversal.lineGate s).flags
      omega
  · simp only [E1M1NoiseIteration.dispatched,if_neg two] at call
    have ends := E1M1NoiseIteration.line_gate_pc s
    omega

/-- Child epilogues restore the parent's exact count, not the child's incoming
argument. The saved-word protection is derived from allocation and reserve. -/
theorem resume_count {table stack s u w n} (a : Allocation table stack)
    (child : CheckedTrace (layout table) .sector (dispatch s) u w n)
    (reserve : Reserve stack .lines n s) (call : (dispatch s).pc=0x26f60) :
    (advance u).core.regs 1=s.core.regs 1 := by
  have cr := reserve.child call
  have below := (checked_guards a child cr).2.2
  have low : 20≤((dispatch s).core.regs 4).toNat := by
    have := cr.1
    simp only [need] at this
    omega
  have saved := child.restores_sector (a.frame_safe cr.room low below)
  exact (advance_count u).trans (saved.c.trans (dispatch_count s.core (E1M1NoiseOpeningFrame.allocation_safe a reserve.room)))

/-- Reusable annotation of every sector/line entry in a finite machine trace.
Both a recursive child and the resumed parent's remaining lines are included. -/
inductive Every (P : Phase → X86Control.State → Prop) :
    {phase : Phase} → {s t : X86Control.State} → {w : List Word} → Trace phase s t w → Prop
  | sectorDone {s done} : P .sector s → Every P (.sectorDone s done)
  | sectorMore {s t w more} {body : Trace .lines (startLines s) t w} :
      P .sector s → Every P body → Every P (.sectorMore s t w more body)
  | lineDone {s opening skip done} : P .lines s → Every P (.lineDone s opening skip done)
  | lineMore {s t w opening skip more} {body : Trace .lines (advance (dispatch s)) t w} :
      P .lines s → Every P body → Every P (.lineMore s t w opening skip more body)
  | childDone {s u w opening call ret done} {child : Trace .sector (dispatch s) u w} :
      P .lines s → Every P child → Every P (.childDone s u w opening call child ret done)
  | childMore {s u t w v opening call ret more} {child : Trace .sector (dispatch s) u w}
      {body : Trace .lines (advance u) t v} :
      P .lines s → Every P child → Every P body → Every P (.childMore s u t w v opening call child ret more body)

private theorem child_legal {s : X86Control.State} (safe : E1M1NoiseOpeningFrame.CallerSafe s.core)
    (entry : Entry .lines s) (call : (dispatch s).pc=0x26f60) : Entry .sector (dispatch s) := by
  rcases dispatch_child s.core safe call with same|⟨_,one⟩
  · simpa only [Entry,same] using entry
  · exact Or.inr one

/-- Entry count validity propagates through the actual register operations.
The induction does not read SectorSafe.count from any node; CheckedTrace's
other existing guards are still used by the saved-frame proof. This does not
construct a trace or remove those guards from CheckedTrace's definition. -/
theorem all_entries {table stack phase s t w n} (a : Allocation table stack)
    (h : CheckedTrace (layout table) phase s t w n) (reserve : Reserve stack phase n s)
    (entry : Entry phase s) : Every Entry h.trace := by
  induction h with
  | sectorDone s done safe => exact .sectorDone (done:=done) entry
  | sectorMore s t w n more safe body ih =>
    have charge := sector_more_charge s.core more
    have parent : Reserve stack .sector (n+1) s := by simpa only [charge] using reserve
    apply Every.sectorMore (more:=more) entry (ih parent.start ?_)
    simpa only [Entry,start_count] using entry
  | lineDone s opening skip done safe => exact .lineDone (opening:=opening) (skip:=skip) (done:=done) entry
  | lineMore s t w n opening skip more safe body ih =>
    have sp : (advance (dispatch s)).core.regs 4=s.core.regs 4 := by
      rw [advance_sp,dispatch,dispatch_sp]
      exact if_neg (by change (dispatch s).pc≠0x26f60; omega)
    have next : Reserve stack .lines n (advance (dispatch s)) := by
      simpa only [Reserve,sp] using reserve
    apply Every.lineMore (opening:=opening) (skip:=skip) (more:=more) entry (ih next ?_)
    simpa only [Entry,advance_count,dispatch,dispatch_count s.core
      (E1M1NoiseOpeningFrame.allocation_safe a reserve.room)] using entry
  | childDone s u w n opening call safe child ret done ih =>
    exact .childDone (opening:=opening) (call:=call) (ret:=ret) (done:=done) entry (ih (reserve.child call)
      (child_legal (E1M1NoiseOpeningFrame.allocation_safe a reserve.room) entry call))
  | childMore s u t w v n m opening call safe child ret more body ci bi =>
    have pr := reserve.mono (Nat.le_add_right n m)
    have br : Reserve stack .lines m (advance u) := by
      simpa only [Reserve,advance_sp,child_stack child call] using reserve.mono (Nat.le_add_left m n)
    apply Every.childMore (opening:=opening) (call:=call) (ret:=ret) (more:=more) entry (ci (pr.child call)
      (child_legal (E1M1NoiseOpeningFrame.allocation_safe a reserve.room) entry call)) (bi br ?_)
    simpa only [Entry,resume_count a child pr call] using entry

/-- Add the count invariant to the existing joined frame/map/graph/fuel result.
A supplied finite checked trace and static/initial certificates remain inputs. -/
theorem sector_budget {table stack base edges regions s t w n}
    (g : E1M1NoiseGraphAllocation.Storage table stack base edges regions) (a : Allocation table stack)
    (h : CheckedTrace (layout table) .sector s t w n)
    (generation : Word) (xs : Ledger) (shape : addresses xs=layout table)
    (ledger : Represents generation s.core.memory xs)
    (low : stack.lo+56*table.length+20 ≤ (s.core.regs 4).toNat)
    (high : (s.core.regs 4).toNat+4 ≤ stack.hi) (bound : stack.hi≤2^32)
    (limit : Nat) (bounds : Bounded table limit) (map : MapRep table s.core.memory)
    (graph : E1M1NoiseGraph.GraphRep base edges s.core.memory) (entry : Entry .sector s) :
    Every Entry h.trace ∧ Restored s.core t ∧ MapRep table t.core.memory ∧
    E1M1NoiseGraph.GraphRep base edges t.core.memory ∧ eval (2*table.length*(limit+1)+1) .sector s=some t :=
  ⟨all_entries a h (sector_reserve h generation xs shape ledger low high bound) entry,
    g.sector_budget a h generation xs shape ledger low high bound limit bounds map graph⟩

end Doom.Proofs.E1M1NoiseCount
