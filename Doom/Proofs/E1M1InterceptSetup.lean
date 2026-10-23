import Doom.Proofs.OriginalInterceptSetup
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1InterceptSetup
open Verification X86 X86Memory X86Control BlockSummary
open OriginalInterceptSetup
attribute [local irreducible] load32 store32

def Safe (sp a : Word) : Prop := ∀ off∈[(4#32),8,12,16,20,24], Apart a (sp-off)
def result (s : X86Memory.State) (n : Nat) := ready (prepared (called s)) n

theorem memory (s : X86Memory.State) :
    (prepared (called s)).memory=
      store32 (store32 (store32 (store32 (store32 (store32 s.memory
        (s.regs 4-4) 0x2cb0b) (s.regs 4-8) (s.regs 3))
        (s.regs 4-12) (s.regs 1)) (s.regs 4-16) (s.regs 6))
        (s.regs 4-20) (s.regs 7)) (s.regs 4-24) (callback s) := by
  simp [prepared,saved,localFrame,push4,push3,push2,push1,called,X86Routine.pushWord,
    put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]

/-- All six handoff/prologue stores preserve a separated word. -/
theorem frame (s : X86Memory.State) (a : Word) (safe : Safe (s.regs 4) a) :
    load32 (prepared (called s)).memory a=load32 s.memory a := by
  rw [memory]
  rw [load_store_apart _ _ _ _ (safe 24 (by simp)),
      load_store_apart _ _ _ _ (safe 20 (by simp)),
      load_store_apart _ _ _ _ (safe 16 (by simp)),
      load_store_apart _ _ _ _ (safe 12 (by simp)),
      load_store_apart _ _ _ _ (safe 8 (by simp)),
      load_store_apart _ _ _ _ (safe 4 (by simp))]

theorem cursor_read (s : X86Memory.State) (safe : Safe (s.regs 4) 0x2c028) :
    cursor (called s)=load32 s.memory 0x2c028 := by
  unfold cursor
  have mem : (localFrame (called s)).memory=
      store32 (store32 (store32 (store32 (store32 s.memory
        (s.regs 4-4) 0x2cb0b) (s.regs 4-8) (s.regs 3))
        (s.regs 4-12) (s.regs 1)) (s.regs 4-16) (s.regs 6)) (s.regs 4-20) (s.regs 7) := by
    simp [localFrame,push4,push3,push2,push1,called,X86Routine.pushWord,
      put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rw [mem,load_store_apart _ _ _ _ (safe 20 (by simp)),
      load_store_apart _ _ _ _ (safe 16 (by simp)),
      load_store_apart _ _ _ _ (safe 12 (by simp)),
      load_store_apart _ _ _ _ (safe 8 (by simp)),
      load_store_apart _ _ _ _ (safe 4 (by simp))]

theorem fields (s : X86Memory.State) (n : Nat) (safe : Safe (s.regs 4) 0x2c028) :
    (result s n).core.regs 4=s.regs 4-24 ∧
    (result s n).core.regs 1=load32 s.memory 0x2c028 ∧
    (result s n).core.regs 7=65536 ∧
    (result s n).core.regs 6=BitVec.ofNat 32 n-1 ∧
    load32 (result s n).core.memory ((result s n).core.regs 4)=callback s ∧
    (result s n).pc=(if n=0 then 0x2c887 else 0x2c841) := by
  have cursor := cursor_read s safe
  simp [result,ready,counted,prepared,saved,localFrame,push4,push3,push2,push1,called,
    X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,load_store] at cursor ⊢
  all_goals exact cursor

/-- Original collection exit through count recovery and the first loop guard. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (bound : n≤128) (limit : load32 s.memory 0x2c028=E1M1MinimumScan.address n)
    (safe : Safe (s.regs 4) 0x2c028) :
    X86CodeMemory.Prefix FloorCaller.cm program [] 23 ⟨s,f,0x2cafd⟩ (result s n) := by
  have limit' : (prepared (called s)).regs 1=E1M1MinimumScan.address n := by
    change cursor (called s)=_
    rw [cursor_read s safe,limit]
  exact X86CodeMemory.lift_success (OriginalGroupBounds.prefix_join
    (OriginalGroupBounds.prefix_join (handoff_execution s f) (prologue_execution (called s) f))
    (count_execution (prepared (called s)) none n bound limit')) FloorCaller.cm

/-- The same separation protects all fields, not just fractions used by sorting. -/
theorem records (s : X86Memory.State) (n : Nat) (hits : Array Collision.Intercept)
    (resolve : Collision.Intercept → Word)
    (encoded : OriginalLineFinish.Encodes s.memory 0x2ba20 resolve hits)
    (safe : ∀ i<hits.size, ∀ off∈[(0#32),4,8],
      Safe (s.regs 4) (OriginalLineCollection.slot 0x2ba20 i off)) :
    OriginalLineFinish.Encodes (result s n).core.memory 0x2ba20 resolve hits := by
  intro i hi
  have before := encoded i hi
  change load32 (prepared (called s)).memory _=_ ∧ _ ∧ _
  rcases before with ⟨frac,line,object⟩
  refine ⟨?_,?_,?_⟩
  · rw [frame s _ (by simpa [OriginalLineCollection.slot] using safe i hi 0 (by simp))]; exact frac
  · exact (frame s _ (safe i hi 4 (by simp))).trans line
  · exact (frame s _ (safe i hi 8 (by simp))).trans object
end Doom.Proofs.E1M1InterceptSetup
