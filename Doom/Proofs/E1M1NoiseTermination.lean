import Doom.Proofs.E1M1NoiseCount
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1NoiseTermination
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoisePreservation E1M1NoiseAccounting E1M1NoiseRecursive E1M1NoiseFootprint
open E1M1NoiseAllocation E1M1NoiseStack E1M1NoiseMap E1M1NoiseMapGuards E1M1NoiseLedger
open E1M1NoiseGraph E1M1NoiseGraphAllocation E1M1NoiseLineProgress

/-- Static storage and graph certificates, not a DOS startup theorem. -/
structure World (table : List SectorLines) (stack : Region) (base : Word)
    (edges : List Edge) (regions : List Region) (limit : Nat) : Prop where
  allocation : Allocation table stack
  storage : Storage table stack base edges regions
  bounds : Bounded table limit
  covered : Covered table edges
  closed : Closed table edges

def Position (table : List SectorLines) : Phase → X86Control.State → Prop
  | .sector,s => s.core.regs 0∈layout table
  | .lines,s => ∃ e∈table, Cursor e s.core

structure Ready (table : List SectorLines) (base : Word) (edges : List Edge)
    (generation : Word) (phase : Phase) (s : X86Control.State) (xs : Ledger) : Prop where
  shape : addresses xs=layout table
  ledger : Represents generation s.core.memory xs
  map : MapRep table s.core.memory
  graph : GraphRep base edges s.core.memory
  position : Position table phase s
  count : E1M1NoiseCount.Entry phase s

/-- Admission consumes ledger credit; scanning a line consumes the second
component. A child call has no line component, so even a pruned call decreases. -/
def rank (limit : Nat) (phase : Phase) (xs : Ledger) (s : X86Control.State) : Nat :=
  credit xs*(limit+1)+(match phase with | .sector => 0 | .lines => remaining s)+1

private theorem sector_pc (s : X86Control.State) : (sector s).pc=0x27011 ∨ (sector s).pc=0x26fa6 := by
  simp only [sector,E1M1NoiseAlert.sectorResult]; split
  · simp only [NoiseAlert.updated]; split <;> simp
  · rename_i no
    have ends : (NoiseAlert.gate (NoiseAlert.prepared s.core)).pc=0x26f83 ∨
        (NoiseAlert.gate (NoiseAlert.prepared s.core)).pc=0x27011 := by
      simp only [NoiseAlert.gate]; split
      · exact Or.inl rfl
      · split <;> simp
    exact Or.inl (ends.resolve_left no)

private theorem advance_pc (s : X86Control.State) : (advance s).pc=0x26fa8 ∨ (advance s).pc=0x27011 := by
  simp only [advance,NoiseTraversal.advanced]; split <;> simp

/-- A real recursive CALL writes the parent's continuation to the child's
incoming stack word. No return-address premise is supplied by the caller. -/
theorem call_word (s : X86Control.State) (call : (dispatch s).pc=0x26f60) :
    load32 (dispatch s).core.memory ((dispatch s).core.regs 4)=(0x27006#32) := by
  have raw (q : X86Memory.State) (h : (NoiseTraversal.blockResult q).pc=0x26f60) :
      load32 (NoiseTraversal.blockResult q).core.memory ((NoiseTraversal.blockResult q).core.regs 4)=(0x27006#32) := by
    simp only [NoiseTraversal.blockResult] at h ⊢
    split
    · simp [NoiseTraversal.recursiveCall,X86Routine.pushWord,put,write,load_store]
    · split <;> simp_all [NoiseTraversal.recursiveCall,X86Routine.pushWord,put,write,load_store]
  have line (q : X86Memory.State) (f : Option Flags) :
      (E1M1NoiseOpening.lineResult q f).pc=0x26fee ∨ (E1M1NoiseOpening.lineResult q f).pc=0x27006 := by
    simp only [E1M1NoiseOpening.lineResult]; split
    · simp only [E1M1NoiseOpening.neighbor]; split <;> exact Or.inl rfl
    · rename_i no
      simp only [NoiseTraversal.openingGate] at no ⊢
      split <;> simp_all
  by_cases two : (NoiseTraversal.lineGate s.core).pc=0x26fb4
  · simp only [dispatch,E1M1NoiseIteration.dispatched,if_pos two,E1M1NoiseOpening.blockResult] at call ⊢
    by_cases pass : (E1M1NoiseOpening.lineResult (NoiseTraversal.lineGate s.core).core (NoiseTraversal.lineGate s.core).flags).pc=0x26fee
    · simp only [if_pos pass] at call ⊢
      exact raw _ call
    · simp only [if_neg pass] at call
      have := line (NoiseTraversal.lineGate s.core).core (NoiseTraversal.lineGate s.core).flags
      omega
  · simp only [dispatch,E1M1NoiseIteration.dispatched,if_neg two] at call
    have := E1M1NoiseIteration.line_gate_pc s.core
    omega

private theorem reserve_low {stack phase n s} (h : Reserve stack phase n s) : 20≤(s.core.regs 4).toNat := by
  have := h.1
  cases phase <;> simp only [need] at this <;> omega

private theorem skipped_sp {s} (skip : (dispatch s).pc=0x27006) :
    (advance (dispatch s)).core.regs 4=s.core.regs 4 := by
  rw [advance_sp,dispatch,dispatch_sp]
  exact if_neg (by change (dispatch s).pc≠0x26f60; omega)

private theorem lines_rank {limit xs ys s t} (credit_le : credit ys≤credit xs)
    (progress : remaining t<remaining s) : rank limit .lines ys t<rank limit .lines xs s := by
  have mul := Nat.mul_le_mul_right (limit+1) credit_le
  simp only [rank]
  omega

/-- Construct the finite checked derivation by induction on visit credit and
remaining lines. No successful evaluation, child return, or finite trace is an
input. Existing trace theorems are applied only to children already constructed. -/
theorem construct_below {table stack base edges regions limit generation}
    (world : World table stack base edges regions limit) (budget : Nat)
    (phase : Phase) (s : X86Control.State) (xs : Ledger)
    (ready : Ready table base edges generation phase s xs)
    (reserve : Reserve stack phase (credit xs) s) (less : rank limit phase xs s<budget) :
    ∃ t w n, CheckedTrace (layout table) phase s t w n := by
  induction budget using Nat.strongRecOn generalizing phase s xs with
  | ind budget ih =>
    cases phase with
    | sector =>
      have safe := world.allocation.ledger_sector reserve.room ready.position ready.count
      rcases sector_pc s with done|more
      · exact ⟨_,_,_,.sectorDone s done safe⟩
      · obtain ⟨ys,shape,ledger,paid⟩ := E1M1NoiseLedger.sector_step _ generation s.core xs ready.shape ready.ledger safe
        rw [sector_more_charge s.core more] at paid
        obtain ⟨e,member,address⟩ := List.mem_map.mp ready.position
        have started := start_step member ready.map address.symm world.bounds
          (world.allocation.map_sector reserve.room ready.position) more
        have next : Ready table base edges generation .lines (startLines s) ys :=
          ⟨shape,ledger,started.1,ready.graph.sector_step
            (world.storage.protect_sector world.allocation reserve.room ready.position),
            ⟨e,member,started.2.1⟩,by simpa only [E1M1NoiseCount.Entry,E1M1NoiseCount.start_count] using ready.count⟩
        have space := (reserve.mono paid).start
        have decrease : rank limit .lines ys (startLines s)<rank limit .sector xs s := by
          have mul := Nat.mul_le_mul_right (limit+1) paid
          simp only [Nat.add_mul,Nat.one_mul] at mul
          have := started.2.2
          simp only [rank]
          omega
        obtain ⟨t,w,n,body⟩ := ih _ less .lines _ ys next space decrease
        exact ⟨t,_,_,.sectorMore s t w n more safe body⟩
    | lines =>
      obtain ⟨e,member,cursor⟩ := ready.position
      have small := (world.bounds e member).2
      have opening := E1M1NoiseOpeningFrame.opening_returns world.allocation reserve.room
      have safe := world.allocation.ledger_line reserve.room
      have ledger := E1M1NoiseLedger.line_step _ generation s.core xs ready.shape ready.ledger safe
      rcases E1M1NoiseIteration.dispatched_pc s.core with call|skip
      · have childEntry := world.storage.child_entry world.allocation reserve world.covered world.closed
          member ready.map cursor ready.graph ready.count call
        have childReady : Ready table base edges generation .sector (dispatch s) xs :=
          ⟨ready.shape,ledger,childEntry.2.2,childEntry.2.1,childEntry.1.member,childEntry.1.count⟩
        have active : 0<remaining s := by
          rw [cursor.remaining_eq (ready.map e member) small]
          have := cursor.live
          omega
        have decrease : rank limit .sector xs (dispatch s)<rank limit .lines xs s := by
          simp only [rank]; omega
        obtain ⟨u,w,n,child⟩ := ih _ less .sector _ xs childReady (reserve.child call) decrease
        obtain ⟨ys,shape,afterLedger,paid⟩ := child.accounting generation xs ready.shape ledger
        have credit_le : credit ys≤credit xs := by omega
        have cr := (reserve.mono (show n≤credit xs by omega)).child call
        obtain ⟨guards,_,below⟩ := checked_guards world.allocation child cr
        have frameSafe := world.allocation.frame_safe cr.room (reserve_low cr) below
        have restored := child.restores_sector frameSafe
        have ret : u.pc=0x27006 := by rw [restored.pc,call_word s call]; rfl
        rcases advance_pc u with more|done
        · have step := world.allocation.child_step reserve.room member ready.map cursor small child
            cr.room (reserve_low cr) below guards.protected more
          have afterGraph := world.storage.preserves_graph world.allocation child cr childReady.graph
          have next : Ready table base edges generation .lines (advance u) ys :=
            ⟨shape,afterLedger,step.1,afterGraph,⟨e,member,step.2.1⟩,by
              simpa only [E1M1NoiseCount.Entry,E1M1NoiseCount.resume_count world.allocation child
                (reserve.mono (show n≤credit xs by omega)) call] using ready.count⟩
          have space : Reserve stack .lines (credit ys) (advance u) := by
            simpa only [Reserve,advance_sp,child_stack child call] using reserve.mono credit_le
          have decrease := lines_rank (limit:=limit) credit_le (show remaining (advance u)<remaining s by have := step.2.2; omega)
          obtain ⟨t,v,m,body⟩ := ih _ less .lines _ ys next space decrease
          exact ⟨t,_,_,.childMore s u t w v n m opening call safe child ret more body⟩
        · exact ⟨_,_,_,.childDone s u w n opening call safe child ret done⟩
      · rcases advance_pc (dispatch s) with more|done
        · have step := world.allocation.skip_step reserve.room member ready.map cursor small more
          have next : Ready table base edges generation .lines (advance (dispatch s)) xs :=
            ⟨ready.shape,ledger,step.1,ready.graph.dispatch_step (world.storage.protect_line reserve.room),
              ⟨e,member,step.2.1⟩,by
                simpa only [E1M1NoiseCount.Entry,E1M1NoiseCount.advance_count,dispatch,
                  E1M1NoiseCount.dispatch_count s.core (E1M1NoiseOpeningFrame.allocation_safe world.allocation reserve.room)] using ready.count⟩
          have space : Reserve stack .lines (credit xs) (advance (dispatch s)) := by
            simpa only [Reserve,skipped_sp skip] using reserve
          have decrease := lines_rank (limit:=limit) (Nat.le_refl (credit xs))
            (show remaining (advance (dispatch s))<remaining s by have := step.2.2; omega)
          obtain ⟨t,w,n,body⟩ := ih _ less .lines _ xs next space decrease
          exact ⟨t,_,_,.lineMore s t w n opening skip more safe body⟩
        · exact ⟨_,_,_,.lineDone s opening skip done safe⟩

/-- Finite trace existence from entry relations and space, with no structural
fuel or prospective execution supplied. -/
theorem construct {table stack base edges regions limit generation phase s xs}
    (world : World table stack base edges regions limit)
    (ready : Ready table base edges generation phase s xs)
    (reserve : Reserve stack phase (credit xs) s) :
    ∃ t w n, CheckedTrace (layout table) phase s t w n :=
  construct_below world (rank limit phase xs s+1) phase s xs ready reserve (by omega)

/-- A map-sized entry reserve suffices without knowing a trace or admission
count. The credit bound follows directly from the finite ledger's shape. -/
theorem entry_reserve {table stack generation base edges s xs}
    (ready : Ready table base edges generation .sector s xs)
    (low : stack.lo+56*table.length+20≤(s.core.regs 4).toNat)
    (high : (s.core.regs 4).toNat+4≤stack.hi) (bound : stack.hi≤2^32) :
    Reserve stack .sector (credit xs) s := by
  have potential := E1M1NoiseVisits.potential_bound (xs.map Prod.snd)
  have length : xs.length=table.length := by
    have := congrArg List.length ready.shape
    simpa only [addresses,layout,List.length_map] using this
  change credit xs≤2*(xs.map Prod.snd).length at potential
  simp only [List.length_map,length] at potential
  refine ⟨?_,high,bound⟩
  simp only [need]
  omega

/-- No CheckedTrace premise: the original traversal completes within the
map-sized evaluator budget and restores its caller and static map/graph data.
Initial representation, allocation and graph closure are explicit assumptions. -/
theorem sector_total {table stack base edges regions limit generation s xs}
    (world : World table stack base edges regions limit)
    (ready : Ready table base edges generation .sector s xs)
    (low : stack.lo+56*table.length+20≤(s.core.regs 4).toNat)
    (high : (s.core.regs 4).toNat+4≤stack.hi) (bound : stack.hi≤2^32) :
    ∃ t, eval (2*table.length*(limit+1)+1) .sector s=some t ∧
      Restored s.core t ∧ MapRep table t.core.memory ∧ GraphRep base edges t.core.memory := by
  obtain ⟨t,w,n,trace⟩ := construct world ready (entry_reserve ready low high bound)
  obtain ⟨_,restored,map,graph,run⟩ := E1M1NoiseCount.sector_budget world.storage world.allocation trace
    generation xs ready.shape ready.ledger low high bound limit world.bounds ready.map ready.graph ready.count
  exact ⟨t,run,restored,map,graph⟩

/-- The constructed successful evaluator run is execution of the pinned
original instruction model, including the real recursive CALLs and RETs. -/
theorem sector_execution {table stack base edges regions limit generation s xs}
    (world : World table stack base edges regions limit)
    (ready : Ready table base edges generation .sector s xs)
    (low : stack.lo+56*table.length+20≤(s.core.regs 4).toNat)
    (high : (s.core.regs 4).toNat+4≤stack.hi) (bound : stack.hi≤2^32) (pc : s.pc=0x26f60) :
    ∃ t, Runs (E1M1NoiseRecursive.bound (2*table.length*(limit+1)+1)) s t ∧
      Restored s.core t ∧ MapRep table t.core.memory ∧ GraphRep base edges t.core.memory := by
  obtain ⟨t,run,rest⟩ := sector_total world ready low high bound
  exact ⟨t,E1M1NoiseRecursive.execution _ .sector s t pc run,rest⟩

end Doom.Proofs.E1M1NoiseTermination
