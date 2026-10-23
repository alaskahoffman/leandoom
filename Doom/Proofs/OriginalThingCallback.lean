import Doom.Proofs.OriginalThingEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalThingCallback
open Verification X86 X86Memory X86Control BlockSummary
def thingCall : List UInt8 := [0x89,0xd0,0xff,0x14,0x24,0x85,0xc0,0x74,0xc,0x8b,0x52,0x2c,0x85,0xd2,0x75,0xf0]
def thingPrepare : List UInt8 := [0x53,0x51,0x52,0x56,0x57,0x55,0x83,0xec,0x18,0x89,0xc1]
def bytesProgram (call prepare : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c5d2≤pc ∧ pc<0x2c5e2 then X86Routine.decodeAt call (pc-0x2c5d2)
  else if 0x2c720≤pc ∧ pc<0x2c72b then X86Routine.decodeAt prepare (pc-0x2c720) else none
def program := bytesProgram thingCall thingPrepare
def listed : X86Routine.Program
  | 0x2c5d2 => some (.control (.block (.legacy (.mov 0 2))),2)
  | 0x2c5d4 => some (.callMemory ⟨some 4,none,0,0⟩,3)
  | 0x2c5d7 => some (.control (.testWord 0 0),2)
  | 0x2c5d9 => some (.control (.jumpZero true 12),2)
  | 0x2c5db => some (.control (.block (.legacy (.load 2 2 44))),3)
  | 0x2c5de => some (.control (.testWord 2 2),2)
  | 0x2c5e0 => some (.control (.jumpZero false (-16)),2)
  | 0x2c720 => some (.push 3,1)
  | 0x2c721 => some (.push 1,1)
  | 0x2c722 => some (.push 2,1)
  | 0x2c723 => some (.push 6,1)
  | 0x2c724 => some (.push 7,1)
  | 0x2c725 => some (.push 5,1)
  | 0x2c726 => some (.addImmediate 4 (-24),3)
  | 0x2c729 => some (.control (.block (.legacy (.mov 1 0))),2)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def argument (s : X86Memory.State) := put s 0 (s.regs 2)
def called (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord (argument s) 0x2c5d7,f,(load32 s.memory (s.regs 4)).toNat⟩
theorem call_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 2 ⟨s,f,0x2c5d2⟩ (called s f) := by
  have path : X86Routine.Prefix listed [] 2 ⟨s,f,0x2c5d2⟩ (called s f) := by
    apply X86Routine.Prefix.step (middle := ⟨argument s,f,0x2c5d4⟩) (by simp) (by rfl)
      (by simp [argument,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,blockPreservesFlags])
    apply X86Routine.Prefix.step (middle := called s f) (by simp) (by rfl)
      (by simp [called,argument,X86Routine.execute,X86Block.Address.eval,put,write])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

theorem call_observe (s : X86Memory.State) (f : Option Flags) :
    (called s f).core.regs 0=s.regs 2 ∧ (called s f).core.regs 2=s.regs 2 ∧
    (called s f).core.regs 4=s.regs 4-(4#32) ∧
    load32 (called s f).core.memory ((called s f).core.regs 4)=(0x2c5d7#32) ∧
    (called s f).pc=(load32 s.memory (s.regs 4)).toNat := by
  simp [called,argument,X86Routine.pushWord,put,write,load_store]

theorem call_frame (s : X86Memory.State) (f : Option Flags) (a : Word)
    (safe : Apart a (s.regs 4-(4#32))) :
    load32 (called s f).core.memory a=load32 s.memory a := by
  exact load_store_apart _ _ _ _ safe

def p1 (s : X86Memory.State) := X86Routine.pushWord s (s.regs 3)
def p2 (s : X86Memory.State) := X86Routine.pushWord (p1 s) (s.regs 1)
def p3 (s : X86Memory.State) := X86Routine.pushWord (p2 s) (s.regs 2)
def p4 (s : X86Memory.State) := X86Routine.pushWord (p3 s) (s.regs 6)
def p5 (s : X86Memory.State) := X86Routine.pushWord (p4 s) (s.regs 7)
def p6 (s : X86Memory.State) := X86Routine.pushWord (p5 s) (s.regs 5)
def p7 (s : X86Memory.State) := put (p6 s) 4 (s.regs 4-(48#32))
def prepared (s : X86Memory.State) := put (p7 s) 1 (s.regs 0)
theorem prepare_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 8 ⟨s,f,0x2c720⟩ ⟨prepared s,none,0x2c72b⟩ := by
  have path : X86Routine.Prefix listed [] 8 ⟨s,f,0x2c720⟩ ⟨prepared s,none,0x2c72b⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨p1 s,f,0x2c721⟩) (by simp) (by rfl) (by simp [prepared,p7,p6,p5,p4,p3,p2,p1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Routine.pushWord,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc])
    apply X86Routine.Prefix.step (middle := ⟨p2 s,f,0x2c722⟩) (by simp) (by rfl) (by simp [prepared,p7,p6,p5,p4,p3,p2,p1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Routine.pushWord,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc])
    apply X86Routine.Prefix.step (middle := ⟨p3 s,f,0x2c723⟩) (by simp) (by rfl) (by simp [prepared,p7,p6,p5,p4,p3,p2,p1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Routine.pushWord,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc])
    apply X86Routine.Prefix.step (middle := ⟨p4 s,f,0x2c724⟩) (by simp) (by rfl) (by simp [prepared,p7,p6,p5,p4,p3,p2,p1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Routine.pushWord,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc])
    apply X86Routine.Prefix.step (middle := ⟨p5 s,f,0x2c725⟩) (by simp) (by rfl) (by simp [prepared,p7,p6,p5,p4,p3,p2,p1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Routine.pushWord,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc])
    apply X86Routine.Prefix.step (middle := ⟨p6 s,f,0x2c726⟩) (by simp) (by rfl) (by simp [prepared,p7,p6,p5,p4,p3,p2,p1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Routine.pushWord,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc])
    apply X86Routine.Prefix.step (middle := ⟨p7 s,none,0x2c729⟩) (by simp) (by rfl) (by simp [prepared,p7,p6,p5,p4,p3,p2,p1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Routine.pushWord,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc])
    apply X86Routine.Prefix.step (middle := ⟨prepared s,none,0x2c72b⟩) (by simp) (by rfl) (by simp [prepared,p7,p6,p5,p4,p3,p2,p1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Routine.pushWord,blockPreservesFlags,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc])
    exact .nil _
  exact path.transfer program [] decoded (by simp)
def saved (s : X86Memory.State) : Memory :=
  store32 (store32 (store32 (store32 (store32 (store32 (s.memory) (s.regs 4-(4#32)) (s.regs 3)) (s.regs 4-(8#32)) (s.regs 1)) (s.regs 4-(12#32)) (s.regs 2)) (s.regs 4-(16#32)) (s.regs 6)) (s.regs 4-(20#32)) (s.regs 7)) (s.regs 4-(24#32)) (s.regs 5)
theorem prepare_observe (s : X86Memory.State) :
    (prepared s).regs 1=s.regs 0 ∧ (prepared s).regs 2=s.regs 2 ∧
    (prepared s).regs 4=s.regs 4-(48#32) ∧ (prepared s).memory=saved s := by
  simp [prepared,p7,p6,p5,p4,p3,p2,p1,saved,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem prepare_frame (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16,20,24], Apart a (s.regs 4-off)) :
    load32 (prepared s).memory a=load32 s.memory a := by
  rw [(prepare_observe s).2.2.2]
  unfold saved
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp))]

theorem slots_apart (sp a b : Word) (h : Apart (-a) (-b)) : Apart (sp-a) (sp-b) := by
  simpa only [BitVec.sub_eq_add_neg] using OriginalPathXStep.apart_translate sp (-a) (-b) h

theorem saved_cursor (s : X86Memory.State) :
    load32 (prepared s).memory (s.regs 4-(12#32))=s.regs 2 := by
  rw [(prepare_observe s).2.2.2]
  unfold saved
  rw [load_store_apart _ _ _ _ (slots_apart (s.regs 4) (12#32) (24#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (slots_apart (s.regs 4) (12#32) (20#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (slots_apart (s.regs 4) (12#32) (16#32) (by unfold Apart; decide))]
  exact load_store _ _ _
theorem saved_return (s : X86Memory.State) :
    load32 (prepared s).memory (s.regs 4)=load32 s.memory (s.regs 4) := by
  apply prepare_frame
  intro off ho
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at ho
  rcases ho with rfl|rfl|rfl|rfl|rfl|rfl <;>
    simpa using slots_apart (s.regs 4) (0#32) _ (by unfold Apart; decide)

/-- This reads the link in the state *after* the callback, not before it. -/
def next (s : X86Memory.State) := load32 s.memory (s.regs 2+(44#32))
def advanced (s : X86Memory.State) := put s 2 (next s)
def resumed (s : X86Memory.State) : X86Control.State :=
  if s.regs 0=(0#32) then ⟨s,some (logical32 (s.regs 0)),0x2c5e7⟩
  else ⟨advanced s,some (logical32 (next s)),if next s=(0#32) then 0x2c5e2 else 0x2c5d2⟩

theorem resume_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤5, X86Routine.Prefix program [] n ⟨s,f,0x2c5d7⟩ (resumed s) := by
  have path : ∃ n≤5, X86Routine.Prefix listed [] n ⟨s,f,0x2c5d7⟩ (resumed s) := by
    by_cases stop : s.regs 0=(0#32)
    · refine ⟨2,by omega,?_⟩
      apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c5d9⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute])
      apply X86Routine.Prefix.step (middle := resumed s) (by simp) (by rfl) (by simp [resumed,X86Routine.execute,X86Control.execute,logical32,stop])
      exact .nil _
    · refine ⟨5,by omega,?_⟩
      apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c5d9⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute])
      apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c5db⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,logical32,stop])
      apply X86Routine.Prefix.step (middle := ⟨advanced s,some (logical32 (s.regs 0)),0x2c5de⟩) (by simp) (by rfl) (by simp [advanced,next,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags])
      apply X86Routine.Prefix.step (middle := ⟨advanced s,some (logical32 (next s)),0x2c5e0⟩) (by simp) (by rfl) (by simp [advanced,X86Routine.execute,X86Control.execute,put,write])
      apply X86Routine.Prefix.step (middle := resumed s) (by simp) (by rfl) (by
        by_cases empty : next s=(0#32) <;> simp [resumed,X86Routine.execute,X86Control.execute,logical32,stop,empty])
      exact .nil _
  obtain ⟨n,hn,path⟩ := path
  exact ⟨n,hn,path.transfer program [] decoded (by simp)⟩

theorem resumed_observe (s : X86Memory.State) :
    (resumed s).core.memory=s.memory ∧ (resumed s).core.regs 4=s.regs 4 ∧
    (s.regs 0=(0#32) → (resumed s).pc=0x2c5e7 ∧ (resumed s).core.regs 2=s.regs 2) ∧
    (s.regs 0≠(0#32) → (resumed s).core.regs 2=load32 s.memory (s.regs 2+(44#32)) ∧
      (resumed s).pc=(if next s=(0#32) then 0x2c5e2 else 0x2c5d2)) := by
  by_cases stop : s.regs 0=(0#32) <;> simp [resumed,stop,advanced,put,write,next]
/-- The callback body begins here; no intersection decision is assumed. -/
def entered (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨prepared (called s f).core,none,0x2c72b⟩

theorem enter_execution (s : X86Memory.State) (f : Option Flags)
    (target : load32 s.memory (s.regs 4)=(0x2c720#32)) :
    X86Routine.Prefix program [] 10 ⟨s,f,0x2c5d2⟩ (entered s f) := by
  have a := call_execution s f
  have b := prepare_execution (called s f).core f
  have pc : (called s f).pc=0x2c720 := by simp [called,target]
  change X86Routine.Prefix _ _ _ ⟨(called s f).core,(called s f).flags,0x2c720⟩ _ at b
  rw [OriginalPathXStep.at_pc _ _ pc] at b
  exact OriginalGroupBounds.prefix_join a b

theorem enter_observe (s : X86Memory.State) (f : Option Flags) :
    (entered s f).core.regs 1=s.regs 2 ∧ (entered s f).core.regs 2=s.regs 2 ∧
    (entered s f).core.regs 4=s.regs 4-(52#32) ∧
    load32 (entered s f).core.memory (s.regs 4-(16#32))=s.regs 2 ∧
    load32 (entered s f).core.memory (s.regs 4-(4#32))=(0x2c5d7#32) := by
  have a := call_observe s f
  have b := prepare_observe (called s f).core
  have cursor := saved_cursor (called s f).core
  have ret := saved_return (called s f).core
  simp only [a.1,a.2.1,a.2.2.1] at b cursor ret
  refine ⟨b.1,b.2.1,?_,?_,?_⟩
  · simpa [entered,BitVec.sub_eq_add_neg,BitVec.add_assoc] using b.2.2.1
  · simpa [entered,BitVec.sub_eq_add_neg,BitVec.add_assoc] using cursor
  · exact ret.trans a.2.2.2.1

theorem enter_frame (s : X86Memory.State) (f : Option Flags) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16,20,24,28], Apart a (s.regs 4-off)) :
    load32 (entered s f).core.memory a=load32 s.memory a := by
  apply (prepare_frame (called s f).core a ?_).trans (call_frame s f a (safe 4 (by simp)))
  intro off ho
  rw [(call_observe s f).2.2.1]
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at ho
  rcases ho with rfl|rfl|rfl|rfl|rfl|rfl
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe (8#32) (by simp)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe (12#32) (by simp)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe (16#32) (by simp)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe (20#32) (by simp)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe (24#32) (by simp)
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe (28#32) (by simp)
end Doom.Proofs.OriginalThingCallback
