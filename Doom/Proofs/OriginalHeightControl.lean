import Doom.Proofs.OriginalHeightFrame

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
namespace Doom.Proofs.PlayerHeight
open Verification X86 X86Memory X86Control BlockSummary

@[simp] theorem control_step_64 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [82,130] (n+1) ⟨s,f,64⟩ =
      (X86Routine.execute (.testMemoryByte ⟨some 1,none,0,196⟩ 4) ⟨s,f,71⟩).bind (X86Routine.run program [82,130] n) := by rfl
@[simp] theorem control_step_71 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [82,130] (n+1) ⟨s,f,71⟩ =
      (X86Routine.execute (.control (.jumpZero false 9)) ⟨s,f,73⟩).bind (X86Routine.run program [82,130] n) := by rfl
@[simp] theorem control_step_73 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [82,130] (n+1) ⟨s,f,73⟩ =
      (X86Routine.execute (.control (.cmpImmediate ⟨none,none,0,184208⟩ 0)) ⟨s,f,80⟩).bind (X86Routine.run program [82,130] n) := by rfl
@[simp] theorem control_step_80 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [82,130] (n+1) ⟨s,f,80⟩ =
      (X86Routine.execute (.control (.jumpZero false 48)) ⟨s,f,82⟩).bind (X86Routine.run program [82,130] n) := by rfl
@[simp] theorem control_stop_64_82 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [82,130] n ⟨s,f,82⟩ = some ⟨s,f,82⟩ := by cases n <;> rfl
@[simp] theorem control_stop_64_130 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [82,130] n ⟨s,f,130⟩ = some ⟨s,f,130⟩ := by cases n <;> rfl
@[simp] theorem control_step_82 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [115] (n+1) ⟨s,f,82⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 1 0)))) ⟨s,f,84⟩).bind (X86Routine.run program [115] n) := by rfl
@[simp] theorem control_step_84 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [115] (n+1) ⟨s,f,84⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 0 20)))) ⟨s,f,87⟩).bind (X86Routine.run program [115] n) := by rfl
@[simp] theorem control_step_87 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [115] (n+1) ⟨s,f,87⟩ =
      (X86Routine.execute (.addImmediate 0 2686976) ⟨s,f,92⟩).bind (X86Routine.run program [115] n) := by rfl
@[simp] theorem control_step_92 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [115] (n+1) ⟨s,f,92⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 1,none,0,16⟩ 0))) ⟨s,f,95⟩).bind (X86Routine.run program [115] n) := by rfl
@[simp] theorem control_step_95 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [115] (n+1) ⟨s,f,95⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 1 0)))) ⟨s,f,97⟩).bind (X86Routine.run program [115] n) := by rfl
@[simp] theorem control_step_97 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [115] (n+1) ⟨s,f,97⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 0 60)))) ⟨s,f,100⟩).bind (X86Routine.run program [115] n) := by rfl
@[simp] theorem control_step_100 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [115] (n+1) ⟨s,f,100⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 5 1 16)))) ⟨s,f,103⟩).bind (X86Routine.run program [115] n) := by rfl
@[simp] theorem control_step_103 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [115] (n+1) ⟨s,f,103⟩ =
      (X86Routine.execute (.control (.block (.subEax 262144))) ⟨s,f,108⟩).bind (X86Routine.run program [115] n) := by rfl
@[simp] theorem control_step_108 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [115] (n+1) ⟨s,f,108⟩ =
      (X86Routine.execute (.compareRegisters 0 5) ⟨s,f,110⟩).bind (X86Routine.run program [115] n) := by rfl
@[simp] theorem control_step_110 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [115] (n+1) ⟨s,f,110⟩ =
      (X86Routine.execute (.jumpSigned 0 3) ⟨s,f,112⟩).bind (X86Routine.run program [115] n) := by rfl
@[simp] theorem control_step_112 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [115] (n+1) ⟨s,f,112⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 1,none,0,16⟩ 0))) ⟨s,f,115⟩).bind (X86Routine.run program [115] n) := by rfl
@[simp] theorem control_stop_82_115 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [115] n ⟨s,f,115⟩ = some ⟨s,f,115⟩ := by cases n <;> rfl
@[simp] theorem control_step_170 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [177,263] (n+1) ⟨s,f,170⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 5 1 4)))) ⟨s,f,173⟩).bind (X86Routine.run program [177,263] n) := by rfl
@[simp] theorem control_step_173 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [177,263] (n+1) ⟨s,f,173⟩ =
      (X86Routine.execute (.control (.testWord 5 5)) ⟨s,f,175⟩).bind (X86Routine.run program [177,263] n) := by rfl
@[simp] theorem control_step_175 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [177,263] (n+1) ⟨s,f,175⟩ =
      (X86Routine.execute (.control (.jumpZero false 86)) ⟨s,f,177⟩).bind (X86Routine.run program [177,263] n) := by rfl
@[simp] theorem control_stop_170_177 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [177,263] n ⟨s,f,177⟩ = some ⟨s,f,177⟩ := by cases n <;> rfl
@[simp] theorem control_stop_170_263 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run program [177,263] n ⟨s,f,263⟩ = some ⟨s,f,263⟩ := by cases n <;> rfl

def noMomentumWord (s : X86Memory.State) : Bool :=
  (s.memory (s.regs 1+(196#32)) &&& (4#8)) != (0#8)

def guardEnd (s : X86Memory.State) : X86Control.State :=
  if noMomentumWord s then ⟨s,some (logical8 (s.memory (s.regs 1+(196#32)) &&& 4)),82⟩
  else ⟨s,some (compare32 (load32 s.memory (184208#32)) 0),
    if load32 s.memory (184208#32) = (0#32) then 82 else 130⟩

theorem guard_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [82,130] 4 ⟨s,f,64⟩ = some (guardEnd s) := by
  by_cases hn : (s.memory (s.regs 1+(196#32)) &&& (4#8)) = (0#8) <;>
    by_cases hg : load32 s.memory (184208#32) = (0#32) <;>
    simp [guardEnd,noMomentumWord,X86Routine.execute,X86Control.execute,
      X86Block.Address.eval,logical8,compare32,hn,hg,BitVec.sub_zero]

def liveEnd (s : X86Memory.State) : X86Control.State :=
  let state := load32 s.memory (s.regs 1+(4#32))
  ⟨put s 5 state,some (logical32 state),if state = 0 then 177 else 263⟩

theorem live_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [177,263] 3 ⟨s,f,170⟩ = some (liveEnd s) := by
  by_cases h : load32 s.memory (s.regs 1+(4#32)) = (0#32) <;>
    simp [liveEnd,X86Routine.execute,X86Control.execute,X86Block.execute,
      X86Memory.execute,blockPreservesFlags,put,write,logical32,h]

/-- The latter part of the early clamp, after its first view-Z store. -/
theorem early_tail_execution (s : X86Memory.State) (f : Option Flags) :
    (X86Routine.run program [115] 7 ⟨s,f,95⟩).map (fun t => (t.pc,t.core.regs 1,t.core.regs 4)) =
      some (115,s.regs 1,s.regs 4) := by
  by_cases h : (load32 s.memory (s.regs 1+(16#32))).toInt ≤
      (load32 s.memory (viewObject s+(60#32))-(262144#32)).toInt <;>
    simp only [viewObject] at h <;>
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
      X86Block.Address.eval,put,write,eax,blockPreservesFlags,cmp_ge_prop,h,
      -BitVec.toInt_sub]

theorem early_tail_frame (s : X86Memory.State) (f : Option Flags)
    (a : Word) (apart : Apart a (s.regs 1+(16#32))) :
    (X86Routine.run program [115] 7 ⟨s,f,95⟩).map (fun t => load32 t.core.memory a) =
      some (load32 s.memory a) := by
  have untouched (m : Memory) (v : Word) : load32 (store32 m (s.regs 1+(16#32)) v) a = load32 m a :=
    load_store_apart _ _ _ _ apart
  by_cases h : (load32 s.memory (s.regs 1+(16#32))).toInt ≤
      (load32 s.memory (viewObject s+(60#32))-(262144#32)).toInt <;>
    simp only [viewObject] at h <;>
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
      X86Block.Address.eval,put,write,eax,blockPreservesFlags,untouched,cmp_ge_prop,h,
      -BitVec.toInt_sub]

/-- Includes the earlier clamp's execution, even though its result is overwritten. -/
theorem early_execution (s : X86Memory.State) (f : Option Flags) :
    (X86Routine.run program [115] 11 ⟨s,f,82⟩).map (fun t => (t.pc,t.core.regs 1,t.core.regs 4)) =
      some (115,s.regs 1,s.regs 4) := by
  simp only [control_step_82,control_step_84,control_step_87,control_step_92,
    X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
    blockPreservesFlags,Option.bind_some,put,write,↓reduceIte]
  rw [early_tail_execution]
  rfl

theorem early_frame (s : X86Memory.State) (f : Option Flags)
    (a : Word) (apart : Apart a (s.regs 1+(16#32))) :
    (X86Routine.run program [115] 11 ⟨s,f,82⟩).map (fun t => load32 t.core.memory a) =
      some (load32 s.memory a) := by
  simp only [control_step_82,control_step_84,control_step_87,control_step_92,
    X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
    blockPreservesFlags,Option.bind_some,put,write,↓reduceIte]
  rw [early_tail_frame _ _ a (by exact apart)]
  simp [X86Block.Address.eval,write,load_store_apart _ _ _ _ apart]

theorem airborne_frame (s : X86Memory.State) (f : Option Flags)
    (a : Word) (apart : Apart a (s.regs 1+(16#32))) :
    (X86Routine.run program [295] 6 ⟨s,f,115⟩).map (fun t => load32 t.core.memory a) =
      some (load32 s.memory a) := by
  have untouched (m : Memory) (v : Word) : load32 (store32 m (s.regs 1+(16#32)) v) a = load32 m a :=
    load_store_apart _ _ _ _ apart
  simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
    X86.execute,X86Block.Address.eval,put,write,eax,blockPreservesFlags,untouched]

end Doom.Proofs.PlayerHeight
