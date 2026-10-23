import Doom.Proofs.E1M1WeaponReadyReset
set_option linter.unusedSimpArgs false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Doom.Verification.ReadyResetFixture
open Doom Doom.Proofs X86 X86Memory X86Control

def p : Word := 0x600101
def obj : Word := 0x600501
def slot : Word := p+244
def table : Word := 0x15a28+28*10
def memory (frame : Nat) : Memory :=
  ([(p,obj),(obj+100,BitVec.ofNat 32 (0x15a28+28*frame)),(p+112,1),(p+116,10),
    (p+32,100),(slot,table),(slot+12,38*65536),(0x12db4,10),
    (table+8,1),(table+12,0x2d2f0),(table+16,10),
    (0x16a74,28),(0x16a78,0),(0x16a7c,0xffffffff),(0x16a80,0),(0x16a84,0),
    (1,0x2d095),(5,0),(9,slot),(13,0x2dc95)] : List (Word × Word)).foldl
      (fun m pair => store32 m pair.1 pair.2) (fun _ => 0)
def initial (frame : Nat) : X86Memory.State :=
  ⟨fun r => if r=0 then p else if r=2 || r=3 then slot else if r=4 then 1 else 0,memory frame⟩
def raised (frame : Nat) := E1M1WeaponReady.raiseNext (initial frame)
def call (frame : Nat) := E1M1WeaponReadyReset.call (raised frame).core

macro "table_safe" : tactic => `(tactic| (
  intro a ha b hb
  simp only [DeathSetter.tableWords,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at ha
  simp only [DeathSetter.fields,PainSetter.fields,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
  rcases ha with rfl|rfl|rfl|rfl|rfl <;> rcases hb with (rfl|rfl|rfl|rfl)|(rfl|rfl) <;> (subst a; subst b; unfold BlockSummary.Apart; decide)))
macro "stack_safe" : tactic => `(tactic| (
  intro a ha b hb
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at ha
  simp only [DeathSetter.fields,PainSetter.fields,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
  rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl|rfl <;> (subst a; subst b; unfold BlockSummary.Apart; decide)))

theorem inputs154 : DeathSetter.SetterInputs E1M1WeaponReadyReset.entry (call 154).core 0x2d319 := by
  constructor
  · decide
  · constructor <;> decide
  · decide
  · table_safe
  · stack_safe
theorem inputs155 : DeathSetter.SetterInputs E1M1WeaponReadyReset.entry (call 155).core 0x2d319 := by
  constructor
  · decide
  · constructor <;> decide
  · decide
  · table_safe
  · stack_safe

theorem weapon_safe : ∀ b, b ∈ DeathSetter.writes (call 154).core →
    BlockSummary.Apart ((call 154).core.regs 1+112) b := by
  intro b hb
  simp only [DeathSetter.writes,DeathSetter.fields,PainSetter.fields,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
  rcases hb with (rfl|rfl|rfl|rfl)|(rfl|rfl) <;> unfold BlockSummary.Apart <;> decide

def afterReset := E1M1WeaponReadyReset.afterReset (raised 154).core
def final := (E1M1WeaponReady.raisedIdleReturn afterReset.core).getD ⟨initial 154,none,0⟩
theorem returns : E1M1WeaponReady.raisedIdleReturn afterReset.core=some final := by
  have good : (E1M1WeaponReady.raisedIdleReturn afterReset.core).isSome=true := by decide
  unfold final
  generalize E1M1WeaponReady.raisedIdleReturn afterReset.core=r at *
  cases r <;> simp_all
example : afterReset.pc=0x2d319 := by decide
example : DeathSetter.observeFields afterReset.core.memory obj=(0x16a74,0xffffffff,28,0) := by decide
example : final.pc=0x2dc95 ∧ final.core.regs 4=17 := by decide
example : ∃ n, n≤118 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponReadyReset.program [] n
    ⟨(raised 154).core,(raised 154).flags,0x2d2f0⟩ final :=
  E1M1WeaponReadyReset.nested_execution _ _ 1 (by decide) inputs154 (by decide) weapon_safe (by decide) (by decide) final returns
example : ∃ n, n≤164 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponReadyReset.program [] n
    ⟨initial 154,none,0x2d4d0⟩ final :=
  E1M1WeaponReadyReset.raise_reset_return _ _ 1 (by decide) (by decide) inputs154 (by decide) weapon_safe (by decide) (by decide) final returns
-- Changing the return word invalidates the callee contract.
example : ¬DeathSetter.SetterInputs E1M1WeaponReadyReset.entry
    {(call 154).core with memory := store32 (call 154).core.memory ((call 154).core.regs 4) 0x2d31a} 0x2d319 := by
  intro h
  have bad := h.returnAddress
  simp [BlockSummary.load_store] at bad
end Doom.Verification.ReadyResetFixture
