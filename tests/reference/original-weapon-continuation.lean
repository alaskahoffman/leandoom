import Doom.Proofs.E1M1WeaponContinuation
set_option linter.unusedSimpArgs false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Doom.Verification.WeaponContinuationFixture
open Doom Doom.Proofs X86 X86Memory X86Control

def p : Word := 0x600101
def obj : Word := 0x600501
def tables (a : Word) : BitVec 8 :=
  if (0x15ab4≤a.toNat ∧ a.toNat<0x15ad0) ∨ (0x15b94≤a.toNat ∧ a.toNat<0x15bb0) ∨
    (0x15c74≤a.toNat ∧ a.toNat<0x15c90) then E1M1WeaponContinuation.stateMemory a else E1M1WeaponFire.tableMemory a

def memory (w : Nat) (sh bu : Int32) (owned : Bool) : Memory :=
  ([(p,obj),(p+112,BitVec.ofNat 32 w),(p+116,10),(p+128,if owned then 1 else 0),
    (p+160,sh.toBitVec),(p+156,bu.toBitVec),(1,0x2d38d)] : List (Word × Word)).foldl
      (fun m pair => store32 m pair.1 pair.2) tables
/-- Unaligned objects and a stack crossing address zero. -/
def initial (w : Nat) (sh bu : Int32) (owned : Bool) : X86Memory.State :=
  ⟨fun r => if r=0 then p else if r=4 then 1 else 0,memory w sh bu owned⟩
def ready (w : Nat) := initial w 1 1 true
def call (w : Nat) := E1M1WeaponFire.poseCall (ready w)
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

macro "pose_inputs" : tactic => `(tactic| (
  constructor
  · decide
  · constructor <;> decide
  · decide
  · table_safe
  · stack_safe))

theorem actor_inputs (w : Fin 3) : DeathSetter.SetterInputs E1M1WeaponFire.entry (call w.val).core 0x2d42a := by
  have cases : w=0 ∨ w=1 ∨ w=2 := by omega
  rcases cases with rfl | rfl | rfl <;> pose_inputs

theorem return_inputs (w : Fin 3) : E1M1WeaponContinuation.AttackReturns (ready w.val) := by
  have cases : w=0 ∨ w=1 ∨ w=2 := by omega
  rcases cases with rfl | rfl | rfl <;> (constructor <;> decide)

theorem enough (w : Fin 3) : E1M1WeaponFire.Enough (ready w.val) := by
  have cases : w=0 ∨ w=1 ∨ w=2 := by omega
  rcases cases with rfl | rfl | rfl <;> decide

example (w : Fin 3) : ∃ n, n≤109 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponContinuation.program [] n
    ⟨ready w.val,none,0x2d410⟩
      (WeaponFire.noiseCall (E1M1WeaponContinuation.attackReturn (ready w.val)).core (E1M1WeaponContinuation.attackReturn (ready w.val)).flags) :=
  E1M1WeaponContinuation.noise_execution _ _ (enough w) (actor_inputs w) (return_inputs w)
example : (E1M1WeaponContinuation.attackReturn (ready 2)).pc=0x2d446 ∧
    load32 (E1M1WeaponContinuation.attackReturn (ready 2)).core.memory (p+248)=3 ∧
    (E1M1WeaponContinuation.attackReturn (ready 2)).core.regs 4=0xfffffff5 := by decide

def empty := initial 1 2 0 true
def checked := E1M1WeaponFire.afterCheck empty
theorem empty_inventory : WeaponFallback.Inventory checked.core := by constructor <;> decide
example : ∃ n, n≤62 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponContinuation.program [] n
    ⟨empty,none,0x2d410⟩ (WeaponFallback.result checked.core) :=
  E1M1WeaponContinuation.empty_execution _ _ (by decide) empty_inventory
example : WeaponFallback.field (WeaponFallback.result checked.core).core 116=2 := by decide
example : WeaponFallback.Inputs checked.core true 2 0 := by constructor <;> decide
example : (WeaponFallback.result checked.core).core.regs 3=11 := by decide
-- Nonzero and positive differ on corrupted negative counts; retain the invariant.
example : WeaponFallback.selected (initial 1 (-1) 0 true)=2 ∧
    (Weapon.fallbackWeapon true (-1) 0).val=0 := by decide
example : ¬WeaponFallback.Inputs (initial 1 (-1) 0 true) true (-1) 0 := by
  intro h
  have bad := h.shellsNonnegative
  contradiction
example : ¬WeaponFallback.Inventory (initial 1 0 0 false |>
    fun s => {s with memory := store32 s.memory (p+132) 1}) := by
  intro h
  have bad := h.chaingun
  have v : WeaponFallback.field (initial 1 0 0 false |>
      fun s => {s with memory := store32 s.memory (p+132) 1}) (132#32)=(1#32) := by decide
  rw [v] at bad
  contradiction
-- Saved ammo frame, real fire return, then the saved fire frame and its caller.
def rejection : X86Memory.State :=
  ⟨fun r => if r=4 then 1 else 0,
    ([(1,6),(5,2),(9,p),(13,3),(17,0x2d41a),(21,22),(25,11),(29,33),(33,0x2d38d)] : List (Word × Word)).foldl
      (fun m pair => store32 m pair.1 pair.2) (fun _ => 0)⟩
def rejected := WeaponFire.returned (WeaponFallback.returned rejection).core (some (logical32 0))
example : ∃ n, n≤12 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponContinuation.program [] n
    ⟨rejection,none,0x2d2aa⟩ rejected := E1M1WeaponContinuation.rejected_return_execution _ _ (by decide)
example : rejected.pc=0x2d38d ∧ rejected.core.regs 4=37 ∧ rejected.core.regs 0=0 ∧ rejected.core.regs 2=22 := by decide
end Doom.Verification.WeaponContinuationFixture
