import Doom.Proofs.E1M1NoiseStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1NoiseOpeningFrame
open Verification X86 X86Memory X86Control BlockSummary E1M1NoiseLedger E1M1NoiseLineProgress

/-- Protect the helper's return word, sound-block count and selected line from
its global stores. Its own saves are separated by the x86 stack arithmetic. -/
def Safe (s : X86Memory.State) : Prop :=
  Protect [s.regs 4,s.regs 4-(8#32),s.regs 4-(12#32)] openingGlobals

theorem restored (s : X86Memory.State) (safe : Safe s) :
    (E1M1NoiseOpening.result s).core.regs 1=s.regs 1 ∧
    (E1M1NoiseOpening.result s).core.regs 2=s.regs 2 ∧
    (E1M1NoiseOpening.result s).pc=(load32 s.memory (s.regs 4)).toNat := by
  have keep (a : Word) (ha : a∈[s.regs 4,s.regs 4-(8#32),s.regs 4-(12#32)])
      (m : Memory) (v : Word) (g : Word) (hg : g∈openingGlobals) :=
    load_store_apart m g a v (safe a ha g hg)
  have k23 : Apart (s.regs 4-(8#32)) (s.regs 4-(12#32)) := DeathStack.slots_apart (s.regs 4) 2 3 (by decide)
  have k24 : Apart (s.regs 4-(8#32)) (s.regs 4-(16#32)) := DeathStack.slots_apart (s.regs 4) 2 4 (by decide)
  have k34 : Apart (s.regs 4-(12#32)) (s.regs 4-(16#32)) := DeathStack.slots_apart (s.regs 4) 3 4 (by decide)
  have k01 : Apart (s.regs 4) (s.regs 4-(4#32)) := by
    have h : Apart (s.regs 4-(0#32)) (s.regs 4-(4#32)) := DeathStack.slots_apart (s.regs 4) 0 1 (by decide)
    simpa using h
  have k02 : Apart (s.regs 4) (s.regs 4-(8#32)) := by
    have h : Apart (s.regs 4-(0#32)) (s.regs 4-(8#32)) := DeathStack.slots_apart (s.regs 4) 0 2 (by decide)
    simpa using h
  have k03 : Apart (s.regs 4) (s.regs 4-(12#32)) := by
    have h : Apart (s.regs 4-(0#32)) (s.regs 4-(12#32)) := DeathStack.slots_apart (s.regs 4) 0 3 (by decide)
    simpa using h
  have k04 : Apart (s.regs 4) (s.regs 4-(16#32)) := by
    have h : Apart (s.regs 4-(0#32)) (s.regs 4-(16#32)) := DeathStack.slots_apart (s.regs 4) 0 4 (by decide)
    simpa using h
  simp only [E1M1NoiseOpening.result]
  split <;> simp [NoiseOpening.closed,NoiseOpening.entry,NoiseOpening.prepared,NoiseOpening.saved,
    NoiseOpening.returned,NoiseOpening.range,NoiseOpening.floor,NoiseOpening.floorInputs,
    NoiseOpening.ceiling,NoiseOpening.ceilingInputs,PspriteLoop.popped,X86Routine.pushWord,put,write,
    ite_true,ite_false,BitVec.sub_sub,BitVec.sub_add_cancel]
  all_goals
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc] at k23 k24 k34 k01 k02 k03 k04 ⊢
    have keep0 (m : Memory) (v : Word) (g : Word) (hg : g∈openingGlobals) := keep (s.regs 4) (by simp) m v g hg
    have keep8 (m : Memory) (v : Word) (g : Word) (hg : g∈openingGlobals) := keep (s.regs 4-(8#32)) (by simp) m v g hg
    have keep12 (m : Memory) (v : Word) (g : Word) (hg : g∈openingGlobals) := keep (s.regs 4-(12#32)) (by simp) m v g hg
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc] at keep0 keep8 keep12
    simp [keep0,keep8,keep12,openingGlobals,load_store_apart _ _ _ _ k23,
      load_store_apart _ _ _ _ k24,load_store_apart _ _ _ _ k34,
      load_store_apart _ _ _ _ k01,load_store_apart _ _ _ _ k02,
      load_store_apart _ _ _ _ k03,load_store_apart _ _ _ _ k04,load_store]

def CallerSafe (s : X86Memory.State) : Prop :=
  Protect [s.regs 4-(4#32),s.regs 4-(12#32),s.regs 4-(16#32)] openingGlobals

theorem opened (s : X86Memory.State) (f : Option Flags) (safe : CallerSafe s) :
    (E1M1NoiseOpening.opened s f).core.regs 1=s.regs 1 ∧
    (E1M1NoiseOpening.opened s f).core.regs 2=s.regs 2 ∧
    (E1M1NoiseOpening.opened s f).pc=0x26fbb := by
  have h := restored (NoiseTraversal.openingCall s f).core (by
    simpa [Safe,CallerSafe,NoiseTraversal.openingCall,X86Routine.pushWord,put,write,BitVec.sub_sub] using safe)
  simpa [E1M1NoiseOpening.opened,NoiseTraversal.openingCall,X86Routine.pushWord,put,write,load_store] using h

theorem allocation_safe {table stack s} (a : E1M1NoiseAllocation.Allocation table stack)
    (room : E1M1NoiseAllocation.StackRoom stack s) : CallerSafe s := by
  intro b hb c hc
  apply E1M1NoiseAllocation.Region.apart (room b ?_) (E1M1NoiseAllocation.globals_contains hc) a.stackGlobals
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl <;> simp [E1M1NoiseFrame.slots]

/-- The finite traversal's opening-RET seam follows from allocation and room. -/
theorem opening_returns {table stack s} (a : E1M1NoiseAllocation.Allocation table stack)
    (room : E1M1NoiseAllocation.StackRoom stack s) : E1M1NoiseRecursive.OpeningReturns s := by
  intro _
  apply (opened _ _ ?_).2.2
  have safe := allocation_safe a room
  simpa [CallerSafe,NoiseTraversal.lineGate,NoiseTraversal.selected,put,write] using safe
end Doom.Proofs.E1M1NoiseOpeningFrame
