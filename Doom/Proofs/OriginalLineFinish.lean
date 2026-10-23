/-
Post-fraction PIT_AddLineIntercepts suffix from the pinned DOS shareware 1.9
executable; bytes and relocations: tests/reference/original-line-finish.json.
The machine theorem retains aliasing effects. The array bridge states the
separation/capacity obligations needed by the enclosing traversal explicitly.
-/
import Doom.Proofs.OriginalLineFraction
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalLineFinish
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0x89,0xc2,0x85,0xc0,0x7d,0xe,0xb8,0x1,0x0,0x0,0x0,0x83,0xc4,0x10,0x5d,0x5e,0x5a,0x59,0x5b,0xc3,0x83,0x3d,0x24,0xc0,0x2,0x0,0x0,0x74,0x18,0x3d,0x0,0x0,0x1,0x0,0x7d,0x11,0x83,0x79,0x32,0x0,0x75,0xb,0x31,0xc0,0x83,0xc4,0x10,0x5d,0x5e,0x5a,0x59,0x5b,0xc3,0x8b,0x15,0x28,0xc0,0x2,0x0,0x83,0xc2,0xc,0xc7,0x42,0xf8,0x1,0x0,0x0,0x0,0x89,0x42,0xf4,0x89,0x4a,0xfc,0xb8,0x1,0x0,0x0,0x0,0x89,0x15,0x28,0xc0,0x2,0x0,0x83,0xc4,0x10,0x5d,0x5e,0x5a,0x59,0x5b,0xc3]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c6bb≤pc ∧ pc<0x2c71a then X86Routine.decodeAt bytes (pc-0x2c6bb) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2c6bb => some (.control (.block (.legacy (.mov 2 0))),2)
  | 0x2c6bd => some (.control (.testWord 0 0),2)
  | 0x2c6bf => some (.jumpSigned 0 14,2)
  | 0x2c6c1 => some (.immediate 0 1,5)
  | 0x2c6cf => some (.control (.cmpImmediate ⟨none,none,0,0x2c024⟩ 0),7)
  | 0x2c6d6 => some (.control (.jumpZero true 24),2)
  | 0x2c6d8 => some (.compareRegister 0 65536,5)
  | 0x2c6dd => some (.jumpSigned 0 17,2)
  | 0x2c6df => some (.control (.cmpImmediate ⟨some 1,none,0,50⟩ 0),4)
  | 0x2c6e3 => some (.control (.jumpZero false 11),2)
  | 0x2c6e5 => some (.xorRegister 0 0,2)
  | 0x2c6f0 => some (.control (.block (.load 2 ⟨none,none,0,0x2c028⟩)),6)
  | 0x2c6f6 => some (.addImmediate 2 12,3)
  | 0x2c6f9 => some (.storeImmediate ⟨some 2,none,0,-8⟩ 1,7)
  | 0x2c700 => some (.control (.block (.store ⟨some 2,none,0,-12⟩ 0)),3)
  | 0x2c703 => some (.control (.block (.store ⟨some 2,none,0,-4⟩ 1)),3)
  | 0x2c706 => some (.immediate 0 1,5)
  | 0x2c70b => some (.control (.block (.store ⟨none,none,0,0x2c028⟩ 2)),6)
  | 0x2c6c6 => some (.addImmediate 4 16,3)
  | 0x2c6c9 => some (.pop 5,1)
  | 0x2c6ca => some (.pop 6,1)
  | 0x2c6cb => some (.pop 2,1)
  | 0x2c6cc => some (.pop 1,1)
  | 0x2c6cd => some (.pop 3,1)
  | 0x2c6ce => some (.ret,1)
  | 0x2c6e7 => some (.addImmediate 4 16,3)
  | 0x2c6ea => some (.pop 5,1)
  | 0x2c6eb => some (.pop 6,1)
  | 0x2c6ec => some (.pop 2,1)
  | 0x2c6ed => some (.pop 1,1)
  | 0x2c6ee => some (.pop 3,1)
  | 0x2c6ef => some (.ret,1)
  | 0x2c711 => some (.addImmediate 4 16,3)
  | 0x2c714 => some (.pop 5,1)
  | 0x2c715 => some (.pop 6,1)
  | 0x2c716 => some (.pop 2,1)
  | 0x2c717 => some (.pop 1,1)
  | 0x2c718 => some (.pop 3,1)
  | 0x2c719 => some (.ret,1)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

abbrev unwind := OriginalLineSecondPoint.unwind
theorem unwind_execution (s : X86Memory.State) (f : Option Flags) (pc : Nat)
    (atReturn : pc∈[0x2c6c6,0x2c6e7,0x2c711]) :
    X86Routine.Prefix program [] 7 ⟨s,f,pc⟩ (unwind s) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at atReturn
  rcases atReturn with rfl|rfl|rfl
  · have path : X86Routine.Prefix listed [] 7 ⟨s,f,0x2c6c6⟩ (unwind s) := by
      apply X86Routine.Prefix.step (middle := ⟨OriginalLineSecondPoint.unwind0 s,none,0x2c6c9⟩) (by simp) (by rfl) (by simp [X86Routine.execute,OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind0,OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind5,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨OriginalLineSecondPoint.unwind1 s,none,0x2c6ca⟩) (by simp) (by rfl) (by simp [X86Routine.execute,OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind0,OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind5,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨OriginalLineSecondPoint.unwind2 s,none,0x2c6cb⟩) (by simp) (by rfl) (by simp [X86Routine.execute,OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind0,OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind5,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨OriginalLineSecondPoint.unwind3 s,none,0x2c6cc⟩) (by simp) (by rfl) (by simp [X86Routine.execute,OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind0,OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind5,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨OriginalLineSecondPoint.unwind4 s,none,0x2c6cd⟩) (by simp) (by rfl) (by simp [X86Routine.execute,OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind0,OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind5,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨OriginalLineSecondPoint.unwind5 s,none,0x2c6ce⟩) (by simp) (by rfl) (by simp [X86Routine.execute,OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind0,OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind5,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := unwind s) (by simp) (by rfl) (by simp [X86Routine.execute,OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind0,OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind5,put,write,BitVec.add_assoc])
      exact .nil _
    exact path.transfer program [] decoded (by simp)
  · have path : X86Routine.Prefix listed [] 7 ⟨s,f,0x2c6e7⟩ (unwind s) := by
      apply X86Routine.Prefix.step (middle := ⟨OriginalLineSecondPoint.unwind0 s,none,0x2c6ea⟩) (by simp) (by rfl) (by simp [X86Routine.execute,OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind0,OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind5,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨OriginalLineSecondPoint.unwind1 s,none,0x2c6eb⟩) (by simp) (by rfl) (by simp [X86Routine.execute,OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind0,OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind5,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨OriginalLineSecondPoint.unwind2 s,none,0x2c6ec⟩) (by simp) (by rfl) (by simp [X86Routine.execute,OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind0,OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind5,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨OriginalLineSecondPoint.unwind3 s,none,0x2c6ed⟩) (by simp) (by rfl) (by simp [X86Routine.execute,OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind0,OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind5,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨OriginalLineSecondPoint.unwind4 s,none,0x2c6ee⟩) (by simp) (by rfl) (by simp [X86Routine.execute,OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind0,OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind5,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨OriginalLineSecondPoint.unwind5 s,none,0x2c6ef⟩) (by simp) (by rfl) (by simp [X86Routine.execute,OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind0,OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind5,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := unwind s) (by simp) (by rfl) (by simp [X86Routine.execute,OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind0,OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind5,put,write,BitVec.add_assoc])
      exact .nil _
    exact path.transfer program [] decoded (by simp)
  · have path : X86Routine.Prefix listed [] 7 ⟨s,f,0x2c711⟩ (unwind s) := by
      apply X86Routine.Prefix.step (middle := ⟨OriginalLineSecondPoint.unwind0 s,none,0x2c714⟩) (by simp) (by rfl) (by simp [X86Routine.execute,OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind0,OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind5,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨OriginalLineSecondPoint.unwind1 s,none,0x2c715⟩) (by simp) (by rfl) (by simp [X86Routine.execute,OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind0,OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind5,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨OriginalLineSecondPoint.unwind2 s,none,0x2c716⟩) (by simp) (by rfl) (by simp [X86Routine.execute,OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind0,OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind5,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨OriginalLineSecondPoint.unwind3 s,none,0x2c717⟩) (by simp) (by rfl) (by simp [X86Routine.execute,OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind0,OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind5,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨OriginalLineSecondPoint.unwind4 s,none,0x2c718⟩) (by simp) (by rfl) (by simp [X86Routine.execute,OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind0,OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind5,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := ⟨OriginalLineSecondPoint.unwind5 s,none,0x2c719⟩) (by simp) (by rfl) (by simp [X86Routine.execute,OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind0,OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind5,put,write,BitVec.add_assoc])
      apply X86Routine.Prefix.step (middle := unwind s) (by simp) (by rfl) (by simp [X86Routine.execute,OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind0,OriginalLineSecondPoint.unwind1,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind4,OriginalLineSecondPoint.unwind5,put,write,BitVec.add_assoc])
      exact .nil _
    exact path.transfer program [] decoded (by simp)
def ins1 (s : X86Memory.State) := put s 2 (load32 s.memory (0x2c028#32))
def ins2 (s : X86Memory.State) := put (ins1 s) 2 ((ins1 s).regs 2+(12#32))
def ins3 (s : X86Memory.State) := {(ins2 s) with memory:=store32 (ins2 s).memory ((ins2 s).regs 2-(8#32)) (1#32)}
def ins4 (s : X86Memory.State) := {(ins3 s) with memory:=store32 (ins3 s).memory ((ins3 s).regs 2-(12#32)) ((ins3 s).regs 0)}
def ins5 (s : X86Memory.State) := {(ins4 s) with memory:=store32 (ins4 s).memory ((ins4 s).regs 2-(4#32)) ((ins4 s).regs 1)}
def ins6 (s : X86Memory.State) := put (ins5 s) 0 1
def ins7 (s : X86Memory.State) := {(ins6 s) with memory:=store32 (ins6 s).memory (0x2c028#32) ((ins6 s).regs 2)}
def inserted := ins7

theorem insert_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 14 ⟨s,f,0x2c6f0⟩ (unwind (inserted s)) := by
  have head : X86Routine.Prefix listed [] 7 ⟨s,f,0x2c6f0⟩ ⟨inserted s,none,0x2c711⟩ := by
    apply X86Routine.Prefix.step (middle:=⟨ins1 s,f,0x2c6f6⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,ins1])
    apply X86Routine.Prefix.step (middle:=⟨ins2 s,none,0x2c6f9⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,ins1,ins2])
    apply X86Routine.Prefix.step (middle:=⟨ins3 s,none,0x2c700⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,ins1,ins2,ins3])
    apply X86Routine.Prefix.step (middle:=⟨ins4 s,none,0x2c703⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,ins1,ins2,ins3,ins4])
    apply X86Routine.Prefix.step (middle:=⟨ins5 s,none,0x2c706⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,ins1,ins2,ins3,ins4,ins5])
    apply X86Routine.Prefix.step (middle:=⟨ins6 s,none,0x2c70b⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,ins1,ins2,ins3,ins4,ins5,ins6])
    apply X86Routine.Prefix.step (middle:=⟨ins7 s,none,0x2c711⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,ins1,ins2,ins3,ins4,ins5,ins6,ins7])
    exact .nil _
  exact OriginalGroupBounds.prefix_join (head.transfer program [] decoded (by simp)) (unwind_execution _ _ _ (by simp))

def early (s : X86Memory.State) : Prop :=
  load32 s.memory (0x2c024#32)≠(0#32) ∧ (s.regs 0).toInt<65536 ∧ load32 s.memory (s.regs 1+(50#32))=(0#32)
instance (s : X86Memory.State) : Decidable (early s) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def stopped (s : X86Memory.State) := unwind (put s 0 0)
def accepted (s : X86Memory.State) := unwind (inserted s)
def selected (s : X86Memory.State) := if early s then stopped s else accepted s

theorem stopped_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 8 ⟨s,f,0x2c6e5⟩ (stopped s) := by
  have one : X86Routine.Prefix listed [] 1 ⟨s,f,0x2c6e5⟩ ⟨put s 0 0,some (logical32 0),0x2c6e7⟩ := by
    apply X86Routine.Prefix.step (middle:=⟨put s 0 0,some (logical32 0),0x2c6e7⟩) (by simp) (by rfl) (by simp [X86Routine.execute,logical32])
    exact .nil _
  exact OriginalGroupBounds.prefix_join (one.transfer program [] decoded (by simp)) (unwind_execution _ _ _ (by simp))

theorem selected_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤20, X86Routine.Prefix program [] n ⟨s,f,0x2c6cf⟩ (selected s) := by
  by_cases hg : load32 s.memory (0x2c024#32)=(0#32)
  · have head : X86Routine.Prefix listed [] 2 ⟨s,f,0x2c6cf⟩ ⟨s,some (compare32 (load32 s.memory (0x2c024#32)) 0),0x2c6f0⟩ := by
      apply X86Routine.Prefix.step (middle:=⟨s,some (compare32 (load32 s.memory (0x2c024#32)) 0),0x2c6d6⟩) (by simp) (by rfl) (by rfl)
      apply X86Routine.Prefix.step (middle:=⟨s,some (compare32 (load32 s.memory (0x2c024#32)) 0),0x2c6f0⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,cmp32_zero,PlayerHeight.cmp_ge_prop,hg])
      exact .nil _
    have eq : selected s=accepted s := by simp [selected,early,hg]
    refine ⟨16,by omega,?_⟩
    rw [eq]
    exact OriginalGroupBounds.prefix_join (head.transfer program [] decoded (by simp)) (insert_execution s _)
  · by_cases hf : 65536≤(s.regs 0).toInt
    · have head : X86Routine.Prefix listed [] 4 ⟨s,f,0x2c6cf⟩ ⟨s,some (compare32 (s.regs 0) 65536),0x2c6f0⟩ := by
        apply X86Routine.Prefix.step (middle:=⟨s,some (compare32 (load32 s.memory (0x2c024#32)) 0),0x2c6d6⟩) (by simp) (by rfl) (by rfl)
        apply X86Routine.Prefix.step (middle:=⟨s,some (compare32 (load32 s.memory (0x2c024#32)) 0),0x2c6d8⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,cmp32_zero,PlayerHeight.cmp_ge_prop,hg,hf,show ¬(s.regs 0).toInt<65536 by omega])
        apply X86Routine.Prefix.step (middle:=⟨s,some (compare32 (s.regs 0) 65536),0x2c6dd⟩) (by simp) (by rfl) (by rfl)
        apply X86Routine.Prefix.step (middle:=⟨s,some (compare32 (s.regs 0) 65536),0x2c6f0⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,cmp32_zero,PlayerHeight.cmp_ge_prop,hg,hf,show ¬(s.regs 0).toInt<65536 by omega])
        exact .nil _
      have eq : selected s=accepted s := by simp [selected,early,hg,hf,show ¬(s.regs 0).toInt<65536 by omega]
      refine ⟨18,by omega,?_⟩
      rw [eq]
      exact OriginalGroupBounds.prefix_join (head.transfer program [] decoded (by simp)) (insert_execution s _)
    · by_cases hb : load32 s.memory (s.regs 1+(50#32))=(0#32)
      · have head : X86Routine.Prefix listed [] 6 ⟨s,f,0x2c6cf⟩ ⟨s,some (compare32 (load32 s.memory (s.regs 1+(50#32))) 0),0x2c6e5⟩ := by
          apply X86Routine.Prefix.step (middle:=⟨s,some (compare32 (load32 s.memory (0x2c024#32)) 0),0x2c6d6⟩) (by simp) (by rfl) (by rfl)
          apply X86Routine.Prefix.step (middle:=⟨s,some (compare32 (load32 s.memory (0x2c024#32)) 0),0x2c6d8⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,cmp32_zero,PlayerHeight.cmp_ge_prop,hg,hf,hb,show (s.regs 0).toInt<65536 by omega])
          apply X86Routine.Prefix.step (middle:=⟨s,some (compare32 (s.regs 0) 65536),0x2c6dd⟩) (by simp) (by rfl) (by rfl)
          apply X86Routine.Prefix.step (middle:=⟨s,some (compare32 (s.regs 0) 65536),0x2c6df⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,cmp32_zero,PlayerHeight.cmp_ge_prop,hg,hf,hb,show (s.regs 0).toInt<65536 by omega])
          apply X86Routine.Prefix.step (middle:=⟨s,some (compare32 (load32 s.memory (s.regs 1+(50#32))) 0),0x2c6e3⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval])
          apply X86Routine.Prefix.step (middle:=⟨s,some (compare32 (load32 s.memory (s.regs 1+(50#32))) 0),0x2c6e5⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,cmp32_zero,PlayerHeight.cmp_ge_prop,hg,hf,hb,show (s.regs 0).toInt<65536 by omega])
          exact .nil _
        have eq : selected s=stopped s := by simp [selected,early,hg,hf,hb,show (s.regs 0).toInt<65536 by omega]
        refine ⟨14,by omega,?_⟩
        rw [eq]
        exact OriginalGroupBounds.prefix_join (head.transfer program [] decoded (by simp)) (stopped_execution s _)
      · have head : X86Routine.Prefix listed [] 6 ⟨s,f,0x2c6cf⟩ ⟨s,some (compare32 (load32 s.memory (s.regs 1+(50#32))) 0),0x2c6f0⟩ := by
          apply X86Routine.Prefix.step (middle:=⟨s,some (compare32 (load32 s.memory (0x2c024#32)) 0),0x2c6d6⟩) (by simp) (by rfl) (by rfl)
          apply X86Routine.Prefix.step (middle:=⟨s,some (compare32 (load32 s.memory (0x2c024#32)) 0),0x2c6d8⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,cmp32_zero,PlayerHeight.cmp_ge_prop,hg,hf,hb,show (s.regs 0).toInt<65536 by omega])
          apply X86Routine.Prefix.step (middle:=⟨s,some (compare32 (s.regs 0) 65536),0x2c6dd⟩) (by simp) (by rfl) (by rfl)
          apply X86Routine.Prefix.step (middle:=⟨s,some (compare32 (s.regs 0) 65536),0x2c6df⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,cmp32_zero,PlayerHeight.cmp_ge_prop,hg,hf,hb,show (s.regs 0).toInt<65536 by omega])
          apply X86Routine.Prefix.step (middle:=⟨s,some (compare32 (load32 s.memory (s.regs 1+(50#32))) 0),0x2c6e3⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval])
          apply X86Routine.Prefix.step (middle:=⟨s,some (compare32 (load32 s.memory (s.regs 1+(50#32))) 0),0x2c6f0⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,cmp32_zero,PlayerHeight.cmp_ge_prop,hg,hf,hb,show (s.regs 0).toInt<65536 by omega])
          exact .nil _
        have eq : selected s=accepted s := by simp [selected,early,hg,hf,hb,show (s.regs 0).toInt<65536 by omega]
        refine ⟨20,by omega,?_⟩
        rw [eq]
        exact OriginalGroupBounds.prefix_join (head.transfer program [] decoded (by simp)) (insert_execution s _)

def start (s : X86Memory.State) := put s 2 (s.regs 0)
def rejected (s : X86Memory.State) := unwind (put s 0 1)
def result (s : X86Memory.State) :=
  if (s.regs 0).toInt<0 then rejected (start s) else selected (start s)

theorem rejected_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 8 ⟨s,f,0x2c6c1⟩ (rejected s) := by
  have head : X86Routine.Prefix listed [] 1 ⟨s,f,0x2c6c1⟩ ⟨put s 0 1,f,0x2c6c6⟩ := by
    apply X86Routine.Prefix.step (middle:=⟨put s 0 1,f,0x2c6c6⟩) (by simp) (by rfl) (by rfl)
    exact .nil _
  exact OriginalGroupBounds.prefix_join (head.transfer program [] decoded (by simp)) (unwind_execution _ _ _ (by simp))

theorem execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤23, X86Routine.Prefix program [] n ⟨s,f,0x2c6bb⟩ (result s) := by
  have flags : logical32 (s.regs 0)=compare32 (s.regs 0) 0 := by simp [logical32,compare32,BitVec.ult_eq_decide]
  by_cases neg : (s.regs 0).toInt<0
  · have head : X86Routine.Prefix listed [] 3 ⟨s,f,0x2c6bb⟩ ⟨start s,some (logical32 (s.regs 0)),0x2c6c1⟩ := by
      apply X86Routine.Prefix.step (middle:=⟨start s,f,0x2c6bd⟩) (by simp) (by rfl) (by rfl)
      apply X86Routine.Prefix.step (middle:=⟨start s,some (logical32 (s.regs 0)),0x2c6bf⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,start,put,write])
      apply X86Routine.Prefix.step (middle:=⟨start s,some (logical32 (s.regs 0)),0x2c6c1⟩) (by simp) (by rfl) (by simp [X86Routine.execute,flags,PlayerHeight.cmp_ge_prop,show ¬0≤(s.regs 0).toInt by omega])
      exact .nil _
    exact ⟨11,by omega,by simpa only [result,if_pos neg] using OriginalGroupBounds.prefix_join (head.transfer program [] decoded (by simp)) (rejected_execution _ _)⟩
  · have head : X86Routine.Prefix listed [] 3 ⟨s,f,0x2c6bb⟩ ⟨start s,some (logical32 (s.regs 0)),0x2c6cf⟩ := by
      apply X86Routine.Prefix.step (middle:=⟨start s,f,0x2c6bd⟩) (by simp) (by rfl) (by rfl)
      apply X86Routine.Prefix.step (middle:=⟨start s,some (logical32 (s.regs 0)),0x2c6bf⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,start,put,write])
      apply X86Routine.Prefix.step (middle:=⟨start s,some (logical32 (s.regs 0)),0x2c6cf⟩) (by simp) (by rfl) (by simp [X86Routine.execute,flags,PlayerHeight.cmp_ge_prop,show 0≤(s.regs 0).toInt by omega])
      exact .nil _
    obtain ⟨n,hn,hp⟩ := selected_execution (start s) (some (logical32 (s.regs 0)))
    exact ⟨3+n,by omega,by simpa only [result,if_neg neg] using OriginalGroupBounds.prefix_join (head.transfer program [] decoded (by simp)) hp⟩

theorem unwind_value (s : X86Memory.State) : (unwind s).core.regs 0=s.regs 0 := by
  simp [OriginalLineSecondPoint.unwind,OriginalLineSecondPoint.unwind5,OriginalLineSecondPoint.unwind4,
    OriginalLineSecondPoint.unwind3,OriginalLineSecondPoint.unwind2,OriginalLineSecondPoint.unwind1,
    OriginalLineSecondPoint.unwind0,put,write]
theorem unwind_memory (s : X86Memory.State) : (unwind s).core.memory=s.memory := rfl
theorem unwind_sp (s : X86Memory.State) : (unwind s).core.regs 4=s.regs 4+(40#32) := by
  simp [OriginalLineSecondPoint.unwind,put,write]
theorem unwind_pc (s : X86Memory.State) : (unwind s).pc=(load32 s.memory (s.regs 4+(36#32))).toNat := rfl

def cursor (s : X86Memory.State) := load32 s.memory (0x2c028#32)
def written (s : X86Memory.State) :=
  store32 (store32 (store32 (store32 s.memory (cursor s+(4#32)) (1#32))
    (cursor s) (s.regs 0)) (cursor s+(8#32)) (s.regs 1)) (0x2c028#32) (cursor s+(12#32))

theorem inserted_memory (s : X86Memory.State) : (inserted s).memory=written s := by
  simp [inserted,ins1,ins2,ins3,ins4,ins5,ins6,ins7,written,cursor,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
theorem inserted_regs (s : X86Memory.State) :
    (inserted s).regs 0=(1#32) ∧ (inserted s).regs 4=s.regs 4 := by
  simp [inserted,ins1,ins2,ins3,ins4,ins5,ins6,ins7,put,write]
theorem early_start (s : X86Memory.State) : early (start s) ↔ early s := by
  simp [early,start,put,write]
theorem cursor_start (s : X86Memory.State) : cursor (start s)=cursor s := rfl
theorem written_start (s : X86Memory.State) : written (start s)=written s := by simp [written,cursor,start,put,write]

def inserts (s : X86Memory.State) : Prop := ¬(s.regs 0).toInt<0 ∧ ¬early s
instance (s : X86Memory.State) : Decidable (inserts s) := inferInstanceAs (Decidable (_ ∧ _))
theorem result_memory (s : X86Memory.State) :
    (result s).core.memory=if inserts s then written s else s.memory := by
  simp only [result,selected,early_start]
  by_cases hn : (s.regs 0).toInt<0 <;> by_cases he : early s <;>
    simp [rejected,stopped,accepted,hn,he,inserts,
      unwind_memory,inserted_memory,written_start,written,cursor,start,put,write]
theorem result_value (s : X86Memory.State) :
    (result s).core.regs 0=if ¬(s.regs 0).toInt<0 ∧ early s then (0#32) else (1#32) := by
  simp only [result,selected,early_start]
  by_cases hn : (s.regs 0).toInt<0 <;> by_cases he : early s <;>
    simp [rejected,stopped,accepted,hn,he,
      unwind_value,inserted_regs,put,write]
theorem result_sp (s : X86Memory.State) : (result s).core.regs 4=s.regs 4+(40#32) := by
  simp only [result,selected,early_start]
  by_cases hn : (s.regs 0).toInt<0 <;> by_cases he : early s <;>
    simp [rejected,stopped,accepted,hn,he,
      unwind_sp,inserted_regs,start,put,write]
theorem result_pc (s : X86Memory.State) :
    (result s).pc=(load32 (if inserts s then written s else s.memory) (s.regs 4+(36#32))).toNat := by
  simp only [result,selected,early_start]
  by_cases hn : (s.regs 0).toInt<0 <;> by_cases he : early s <;>
    simp [rejected,stopped,accepted,hn,he,inserts,
      unwind_pc,inserted_memory,written_start,written,cursor,inserted_regs,start,put,write]

theorem written_frame (s : X86Memory.State) (a : Word)
    (safe : ∀ w∈[cursor s,cursor s+(4#32),cursor s+(8#32),(0x2c028#32)], Apart a w) :
    load32 (written s) a=load32 s.memory a := by
  unfold written
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp))]
theorem frame (s : X86Memory.State) (a : Word)
    (safe : ∀ w∈[cursor s,cursor s+(4#32),cursor s+(8#32),(0x2c028#32)], Apart a w) :
    load32 (result s).core.memory a=load32 s.memory a := by
  rw [result_memory]; split
  · exact written_frame s a safe
  · rfl

theorem returned (s : X86Memory.State)
    (safe : ∀ w∈[cursor s,cursor s+(4#32),cursor s+(8#32),(0x2c028#32)], Apart (s.regs 4+(36#32)) w) :
    (result s).pc=(load32 s.memory (s.regs 4+(36#32))).toNat := by
  rw [result_pc]; split
  · rw [written_frame s _ safe]
  · rfl

theorem written_cursor (s : X86Memory.State) : load32 (written s) (0x2c028#32)=cursor s+(12#32) := by
  unfold written; rw [load_store]
theorem written_record (s : X86Memory.State)
    (safe : ∀ off∈[(0#32),4,8], Apart (cursor s+off) (0x2c028#32)) :
    load32 (written s) (cursor s)=s.regs 0 ∧
    load32 (written s) (cursor s+(4#32))=(1#32) ∧
    load32 (written s) (cursor s+(8#32))=s.regs 1 := by
  have apart (a b : Word) (h : Apart a b) := OriginalPathXStep.apart_translate (cursor s) a b h
  unfold written
  constructor
  · rw [load_store_apart _ _ _ _ (by simpa only [BitVec.add_zero] using safe (0#32) (by simp)),
      load_store_apart _ _ _ _ (by simpa only [BitVec.add_zero] using apart (0#32) (8#32) (by unfold Apart; decide)),load_store]
  constructor
  · rw [load_store_apart _ _ _ _ (safe (4#32) (by simp)),load_store_apart _ _ _ _ (apart (4#32) (8#32) (by unfold Apart; decide)),
      load_store_apart _ _ _ _ (by simpa only [BitVec.add_zero] using apart (4#32) (0#32) (by unfold Apart; decide)),load_store]
  · rw [load_store_apart _ _ _ _ (safe (8#32) (by simp)),load_store]

structure Inputs (s : X86Memory.State) (frac : Fixed) (line : Collision.Line) (flags : Nat) (p : Word) : Prop where
  fraction : s.regs 0=frac.raw.toBitVec
  pointer : s.regs 1=p
  active : load32 s.memory (0x2c024#32)≠(0#32) ↔ flags &&& 4≠0
  back : load32 s.memory (p+(50#32))=(0#32) ↔ line.back.isNone=true

theorem early_live (s : X86Memory.State) (frac : Fixed) (line : Collision.Line) (flags : Nat) (p : Word)
    (h : Inputs s frac line flags p) :
    early s ↔ (flags &&& 4 != 0 && frac.raw < 65536 && line.back.isNone)=true := by
  simp [early,h.fraction,h.pointer,h.active,h.back,Int32.toInt_toBitVec,Int32.lt_iff_toInt_lt,and_assoc]

theorem decision_live (s : X86Memory.State) (frac : Fixed) (line : Collision.Line) (flags : Nat) (p : Word)
    (h : Inputs s frac line flags p) :
    (result s).core.regs 0=(if frac.raw < 0 then (1#32)
      else if flags &&& 4 != 0 && frac.raw < 65536 && line.back.isNone then 0 else 1) := by
  rw [result_value]
  have neg : (s.regs 0).toInt<0 ↔ frac.raw<0 := by simp [h.fraction,Int32.toInt_toBitVec,Int32.lt_iff_toInt_lt]
  simp only [neg,early_live s frac line flags p h]
  by_cases hn : frac.raw<0 <;> simp [hn]

/-- The production side test and negative-fraction filter, given the fraction
already established by OriginalInterceptVector.live. -/
theorem line_intercept_live (trace : Collision.Divline) (line : Collision.Line) (frac : Fixed)
    (crossed : OriginalLineSecondPoint.firstSide trace line≠OriginalLineSecondPoint.lastSide trace line)
    (computed : Collision.interceptVector trace ⟨line.x,line.y,line.dx,line.dy⟩=.ok frac) :
    Collision.lineIntercept trace line=.ok (if frac.raw<0 then none else some frac) := by
  unfold Collision.lineIntercept
  unfold OriginalLineSecondPoint.firstSide OriginalLineSecondPoint.lastSide at crossed
  split at crossed <;> simp_all [computed] <;> rfl

/-- Ordered twelve-byte intercept records, with a caller-supplied mapping from
Lean IDs to original pointers. This does not assume an allocator or map image. -/
def RecordAt (memory : Memory) (address : Word) (hit : Collision.Intercept) (pointer : Word) : Prop :=
  load32 memory address=hit.frac.raw.toBitVec ∧
  load32 memory (address+(4#32))=(if hit.isLine then (1#32) else (0#32)) ∧
  load32 memory (address+(8#32))=pointer

def Encodes (memory : Memory) (base : Word) (resolve : Collision.Intercept → Word)
    (hits : Array Collision.Intercept) : Prop :=
  ∀ (i : Nat) (hi : i<hits.size),
    RecordAt memory (base+BitVec.ofNat 32 (12*i)) hits[i] (resolve hits[i])

/-- Appending preserves every earlier record and puts the new record last.
The separation conditions protect earlier records and the cursor global,
including when address arithmetic wraps. -/
theorem append_encoded (s : X86Memory.State) (base : Word)
    (resolve : Collision.Intercept → Word) (hits : Array Collision.Intercept) (hit : Collision.Intercept)
    (enabled : inserts s) (encoded : Encodes s.memory base resolve hits)
    (atEnd : cursor s=base+BitVec.ofNat 32 (12*hits.size))
    (fraction : s.regs 0=hit.frac.raw.toBitVec) (kind : hit.isLine=true)
    (pointer : s.regs 1=resolve hit)
    (newSafe : ∀ off∈[(0#32),4,8], Apart (cursor s+off) (0x2c028#32))
    (oldSafe : ∀ (i : Nat), i<hits.size → ∀ off∈[(0#32),4,8],
      ∀ w∈[cursor s,cursor s+(4#32),cursor s+(8#32),(0x2c028#32)],
        Apart (base+BitVec.ofNat 32 (12*i)+off) w) :
    Encodes (result s).core.memory base resolve (hits.push hit) := by
  rw [result_memory,if_pos enabled]
  intro i hi
  have bound : i≤hits.size := by simp only [Array.size_push] at hi; omega
  by_cases old : i<hits.size
  · rw [Array.getElem_push_lt old]
    have keep (off : Word) (ho : off∈[(0#32),4,8]) :=
      written_frame s (base+BitVec.ofNat 32 (12*i)+off) (oldSafe i old off ho)
    have previous := encoded i old
    unfold RecordAt at previous ⊢
    rw [show load32 (written s) (base+BitVec.ofNat 32 (12*i))=
        load32 s.memory (base+BitVec.ofNat 32 (12*i)) by simpa using keep 0 (by simp),
      keep (4#32) (by simp), keep (8#32) (by simp)]
    exact previous
  · have eq : i=hits.size := by omega
    subst i
    rw [Array.getElem_push_eq,←atEnd]
    have record := written_record s newSafe
    simpa only [RecordAt,fraction,pointer,kind,if_true] using record

/-- The actual production append operation has the same ordered result while
there is capacity. The original's overflow behavior remains outside this claim. -/
theorem append_live (r : Collision.PathResult) (hit : Collision.Intercept)
    (capacity : r.collected.size<128) :
    Collision.appendIntercept r hit=.ok {r with collected:=r.collected.push hit} := by
  simp [Collision.appendIntercept,show ¬r.collected.size≥128 by omega]

end Doom.Proofs.OriginalLineFinish
