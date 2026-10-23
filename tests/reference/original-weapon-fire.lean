import Doom.Proofs.E1M1WeaponFire
set_option linter.unusedSimpArgs false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Doom.Verification.WeaponFireFixture
open Doom Doom.Proofs X86 X86Memory X86Control

def p : Word := 0x600101
def obj : Word := 0x600501
def memory (w : Nat) (ammo : Int32) : Memory :=
  ([(p,obj),(p+112,BitVec.ofNat 32 w),(p+116,10),(p+32,100),(p+15,1),(p+188,0),
    (p+156+(if w=2 then 4 else 0),ammo.toBitVec),(1,0x2d38d),
    (0x15b94+8,4),(0x15b94+12,0),(0x15b94+16,14),(0x15b94+20,0),(0x15b94+24,0)] : List (Word × Word)).foldl
      (fun m pair => store32 m pair.1 pair.2) E1M1WeaponFire.tableMemory
/-- Unaligned player/object and a stack crossing address zero. -/
def initial (w : Nat) (ammo : Int32) : X86Memory.State :=
  ⟨fun r => if r=0 || r=1 then p else if r=4 then 1 else 0,memory w ammo⟩
def call := E1M1WeaponFire.poseCall (initial 1 1)
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

theorem enough : E1M1WeaponFire.Enough (initial 1 1) := by decide
theorem inputs : DeathSetter.SetterInputs E1M1WeaponFire.entry call.core 0x2d42a := by
  constructor
  · decide
  · constructor <;> decide
  · decide
  · table_safe
  · stack_safe

def afterPose := E1M1WeaponFire.afterPose (initial 1 1)
def attack := WeaponFire.attackCall afterPose.core
def installed := E1M1PspriteSetter.setterResult attack.core
example : (E1M1WeaponFire.afterCheck (initial 1 0)).pc = 0x2d19f := by decide
example : (E1M1WeaponFire.afterCheck (initial 1 (-1))).pc = 0x2d19f := by decide
example : (E1M1WeaponFire.afterCheck (initial 0 0)).pc = 0x2d41a := by decide
example : (E1M1WeaponFire.afterCheck (initial 2 1)).pc = 0x2d41a := by decide
example : DeathSetter.observeFields afterPose.core.memory obj=(0x16b00,12,28,4) := by decide
example : attack.pc=0x2d040 ∧ attack.core.regs 3=13 ∧ attack.core.regs 4=0xfffffff1 := by decide
example : installed.pc=0x2d09a ∧ load32 installed.core.memory (p+244)=0x15b94 ∧
    load32 installed.core.memory (p+248)=4 := by decide
example : ∃ n, n≤95 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponFire.program [] n
    ⟨initial 1 1,none,0x2d410⟩ installed := E1M1WeaponFire.attack_state_execution _ _ enough inputs
example : WeaponAmmo.Inputs (WeaponFire.checkCall (initial 1 1) none).core 1 1 := by
  constructor <;> decide
-- An incorrect saved return address cannot satisfy the actor setter contract.
example : ¬DeathSetter.SetterInputs E1M1WeaponFire.entry
    {call.core with memory := store32 call.core.memory (call.core.regs 4) 0x2d42b} 0x2d42a := by
  intro h
  have bad := h.returnAddress
  simp [BlockSummary.load_store] at bad


def requested := WeaponReadyGate.result (initial 1 1)
def requestedPose := E1M1WeaponFire.poseCall requested.core
theorem requested_inputs : DeathSetter.SetterInputs E1M1WeaponFire.entry requestedPose.core 0x2d42a := by
  constructor
  · decide
  · constructor <;> decide
  · decide
  · table_safe
  · stack_safe
example : ∃ n, n≤111 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponFire.program [] n
    ⟨initial 1 1,none,0x2d333⟩
      (E1M1PspriteSetter.setterResult (WeaponFire.attackCall (E1M1WeaponFire.afterPose requested.core).core).core) :=
  E1M1WeaponFire.ready_fire_execution _ _ (by decide) (by decide) requested_inputs
end Doom.Verification.WeaponFireFixture
