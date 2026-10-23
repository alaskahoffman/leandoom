import Doom.Proofs.OriginalGroupOutput
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalGroupCount
open Verification X86 X86Memory X86Control BlockSummary
def countBytes : List UInt8 := [0xa1,0x20,0xc1,0x2,0x0,0x8b,0x3d,0x34,0xc1,0x2,0x0,0x31,0xd2,0x31,0xf6,0x85,0xff,0x7e,0x29,0x8b,0x58,0x2e,0xff,0x43,0x4e,0x8b,0x78,0x32,0x42,0x85,0xff,0x74,0xd,0x3b,0x78,0x2e,0x74,0x8,0x8b,0x4f,0x4e,0x41,0x42,0x89,0x4f,0x4e,0x8b,0x2d,0x34,0xc1,0x2,0x0,0x46,0x83,0xc0,0x3e,0x39,0xee,0x7c,0xd7,0x8d,0x4,0x95,0x0,0x0,0x0,0x0,0x31,0xdb,0xba,0x32,0x0,0x0,0x0]
def bytesProgram (code : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2e5ef≤pc ∧ pc<0x2e639 then X86Routine.decodeAt code (pc-0x2e5ef) else none
def program := bytesProgram countBytes
def listed : X86Routine.Program
  | 0x2e5ef => some (.control (.block (.load 0 ⟨none,none,0,0x2c120⟩)),5)
  | 0x2e5f4 => some (.control (.block (.load 7 ⟨none,none,0,0x2c134⟩)),6)
  | 0x2e5fa => some (.xorRegister 2 2,2)
  | 0x2e5fc => some (.xorRegister 6 6,2)
  | 0x2e5fe => some (.control (.testWord 7 7),2)
  | 0x2e600 => some (.jumpSigned 1 41,2)
  | 0x2e602 => some (.control (.block (.legacy (.load 3 0 46))),3)
  | 0x2e605 => some (.incrementMemory ⟨some 3,none,0,78⟩,3)
  | 0x2e608 => some (.control (.block (.legacy (.load 7 0 50))),3)
  | 0x2e60b => some (.addImmediate 2 1,1)
  | 0x2e60c => some (.control (.testWord 7 7),2)
  | 0x2e60e => some (.control (.jumpZero true 13),2)
  | 0x2e610 => some (.control (.cmpMemory 7 ⟨some 0,none,0,46⟩),3)
  | 0x2e613 => some (.control (.jumpZero true 8),2)
  | 0x2e615 => some (.control (.block (.legacy (.load 1 7 78))),3)
  | 0x2e618 => some (.addImmediate 1 1,1)
  | 0x2e619 => some (.addImmediate 2 1,1)
  | 0x2e61a => some (.control (.block (.store ⟨some 7,none,0,78⟩ 1)),3)
  | 0x2e61d => some (.control (.block (.load 5 ⟨none,none,0,0x2c134⟩)),6)
  | 0x2e623 => some (.addImmediate 6 1,1)
  | 0x2e624 => some (.addImmediate 0 62,3)
  | 0x2e627 => some (.compareRegisters 6 5,2)
  | 0x2e629 => some (.jumpSigned 3 (-41),2)
  | 0x2e62b => some (.control (.block (.lea 0 ⟨none,some 2,2,0⟩)),7)
  | 0x2e632 => some (.xorRegister 3 3,2)
  | 0x2e634 => some (.immediate 2 50,5)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def front (s : X86Memory.State) := load32 s.memory (s.regs 0+46)
def frontMemory (s : X86Memory.State) :=
  store32 s.memory (front s+78) (load32 s.memory (front s+78)+1)
def back (s : X86Memory.State) := load32 (frontMemory s) (s.regs 0+50)
/-- The front pointer is re-read after the first counter write. -/
def again (s : X86Memory.State) := load32 (frontMemory s) (s.regs 0+46)
def second (s : X86Memory.State) : Bool := back s != 0 && back s != again s
def counted (s : X86Memory.State) : X86Memory.State :=
  let t := put (put (put s 3 (front s)) 7 (back s)) 2 (s.regs 2+1)
  if second s then
    {put (put t 1 (load32 (frontMemory s) (back s+78)+1)) 2 (s.regs 2+1+1) with
      memory := store32 (frontMemory s) (back s+78) (load32 (frontMemory s) (back s+78)+1)}
  else {t with memory := frontMemory s}
def advanced (s : X86Memory.State) : X86Control.State :=
  ⟨put (put (put s 5 (load32 s.memory 0x2c134)) 6 (s.regs 6+1)) 0 (s.regs 0+62),
    some (compare32 (s.regs 6+1) (load32 s.memory 0x2c134)),
    if (s.regs 6+1).toInt<(load32 s.memory 0x2c134).toInt then 0x2e602 else 0x2e62b⟩
def result (s : X86Memory.State) := advanced (counted s)
def entry (s : X86Memory.State) : X86Control.State :=
  ⟨put (put (put (put s 0 (load32 s.memory 0x2c120)) 7 (load32 s.memory 0x2c134)) 2 0) 6 0,
    some (logical32 (load32 s.memory 0x2c134)),
    if (load32 s.memory 0x2c134).toInt≤0 then 0x2e62b else 0x2e602⟩
def allocation (s : X86Memory.State) : X86Control.State :=
  ⟨put (put (put s 0 (s.regs 2 <<< 2)) 3 0) 2 50,some {(logical32 0) with carry := some false},0x2e639⟩
@[local simp] private theorem step_2e5ef (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e602,0x2e62b] (n+1) ⟨s,f,0x2e5ef⟩ =
      (X86Routine.execute (.control (.block (.load 0 ⟨none,none,0,0x2c120⟩))) ⟨s,f,0x2e5f4⟩).bind (X86Routine.run listed [0x2e602,0x2e62b] n) := by rfl
@[local simp] private theorem step_2e5f4 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e602,0x2e62b] (n+1) ⟨s,f,0x2e5f4⟩ =
      (X86Routine.execute (.control (.block (.load 7 ⟨none,none,0,0x2c134⟩))) ⟨s,f,0x2e5fa⟩).bind (X86Routine.run listed [0x2e602,0x2e62b] n) := by rfl
@[local simp] private theorem step_2e5fa (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e602,0x2e62b] (n+1) ⟨s,f,0x2e5fa⟩ =
      (X86Routine.execute (.xorRegister 2 2) ⟨s,f,0x2e5fc⟩).bind (X86Routine.run listed [0x2e602,0x2e62b] n) := by rfl
@[local simp] private theorem step_2e5fc (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e602,0x2e62b] (n+1) ⟨s,f,0x2e5fc⟩ =
      (X86Routine.execute (.xorRegister 6 6) ⟨s,f,0x2e5fe⟩).bind (X86Routine.run listed [0x2e602,0x2e62b] n) := by rfl
@[local simp] private theorem step_2e5fe (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e602,0x2e62b] (n+1) ⟨s,f,0x2e5fe⟩ =
      (X86Routine.execute (.control (.testWord 7 7)) ⟨s,f,0x2e600⟩).bind (X86Routine.run listed [0x2e602,0x2e62b] n) := by rfl
@[local simp] private theorem step_2e600 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e602,0x2e62b] (n+1) ⟨s,f,0x2e600⟩ =
      (X86Routine.execute (.jumpSigned 1 41) ⟨s,f,0x2e602⟩).bind (X86Routine.run listed [0x2e602,0x2e62b] n) := by rfl
@[local simp] private theorem step_2e602 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e629] (n+1) ⟨s,f,0x2e602⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 3 0 46)))) ⟨s,f,0x2e605⟩).bind (X86Routine.run listed [0x2e629] n) := by rfl
@[local simp] private theorem step_2e605 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e629] (n+1) ⟨s,f,0x2e605⟩ =
      (X86Routine.execute (.incrementMemory ⟨some 3,none,0,78⟩) ⟨s,f,0x2e608⟩).bind (X86Routine.run listed [0x2e629] n) := by rfl
@[local simp] private theorem step_2e608 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e629] (n+1) ⟨s,f,0x2e608⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 7 0 50)))) ⟨s,f,0x2e60b⟩).bind (X86Routine.run listed [0x2e629] n) := by rfl
@[local simp] private theorem step_2e60b (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e629] (n+1) ⟨s,f,0x2e60b⟩ =
      (X86Routine.execute (.addImmediate 2 1) ⟨s,f,0x2e60c⟩).bind (X86Routine.run listed [0x2e629] n) := by rfl
@[local simp] private theorem step_2e60c (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e629] (n+1) ⟨s,f,0x2e60c⟩ =
      (X86Routine.execute (.control (.testWord 7 7)) ⟨s,f,0x2e60e⟩).bind (X86Routine.run listed [0x2e629] n) := by rfl
@[local simp] private theorem step_2e60e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e629] (n+1) ⟨s,f,0x2e60e⟩ =
      (X86Routine.execute (.control (.jumpZero true 13)) ⟨s,f,0x2e610⟩).bind (X86Routine.run listed [0x2e629] n) := by rfl
@[local simp] private theorem step_2e610 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e629] (n+1) ⟨s,f,0x2e610⟩ =
      (X86Routine.execute (.control (.cmpMemory 7 ⟨some 0,none,0,46⟩)) ⟨s,f,0x2e613⟩).bind (X86Routine.run listed [0x2e629] n) := by rfl
@[local simp] private theorem step_2e613 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e629] (n+1) ⟨s,f,0x2e613⟩ =
      (X86Routine.execute (.control (.jumpZero true 8)) ⟨s,f,0x2e615⟩).bind (X86Routine.run listed [0x2e629] n) := by rfl
@[local simp] private theorem step_2e615 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e629] (n+1) ⟨s,f,0x2e615⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 1 7 78)))) ⟨s,f,0x2e618⟩).bind (X86Routine.run listed [0x2e629] n) := by rfl
@[local simp] private theorem step_2e618 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e629] (n+1) ⟨s,f,0x2e618⟩ =
      (X86Routine.execute (.addImmediate 1 1) ⟨s,f,0x2e619⟩).bind (X86Routine.run listed [0x2e629] n) := by rfl
@[local simp] private theorem step_2e619 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e629] (n+1) ⟨s,f,0x2e619⟩ =
      (X86Routine.execute (.addImmediate 2 1) ⟨s,f,0x2e61a⟩).bind (X86Routine.run listed [0x2e629] n) := by rfl
@[local simp] private theorem step_2e61a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e629] (n+1) ⟨s,f,0x2e61a⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 7,none,0,78⟩ 1))) ⟨s,f,0x2e61d⟩).bind (X86Routine.run listed [0x2e629] n) := by rfl
@[local simp] private theorem step_2e61d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e629] (n+1) ⟨s,f,0x2e61d⟩ =
      (X86Routine.execute (.control (.block (.load 5 ⟨none,none,0,0x2c134⟩))) ⟨s,f,0x2e623⟩).bind (X86Routine.run listed [0x2e629] n) := by rfl
@[local simp] private theorem step_2e623 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e629] (n+1) ⟨s,f,0x2e623⟩ =
      (X86Routine.execute (.addImmediate 6 1) ⟨s,f,0x2e624⟩).bind (X86Routine.run listed [0x2e629] n) := by rfl
@[local simp] private theorem step_2e624 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e629] (n+1) ⟨s,f,0x2e624⟩ =
      (X86Routine.execute (.addImmediate 0 62) ⟨s,f,0x2e627⟩).bind (X86Routine.run listed [0x2e629] n) := by rfl
@[local simp] private theorem step_2e627 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e629] (n+1) ⟨s,f,0x2e627⟩ =
      (X86Routine.execute (.compareRegisters 6 5) ⟨s,f,0x2e629⟩).bind (X86Routine.run listed [0x2e629] n) := by rfl
@[local simp] private theorem step_2e62b (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e639] (n+1) ⟨s,f,0x2e62b⟩ =
      (X86Routine.execute (.control (.block (.lea 0 ⟨none,some 2,2,0⟩))) ⟨s,f,0x2e632⟩).bind (X86Routine.run listed [0x2e639] n) := by rfl
@[local simp] private theorem step_2e632 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e639] (n+1) ⟨s,f,0x2e632⟩ =
      (X86Routine.execute (.xorRegister 3 3) ⟨s,f,0x2e634⟩).bind (X86Routine.run listed [0x2e639] n) := by rfl
@[local simp] private theorem step_2e634 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e639] (n+1) ⟨s,f,0x2e634⟩ =
      (X86Routine.execute (.immediate 2 50) ⟨s,f,0x2e639⟩).bind (X86Routine.run listed [0x2e639] n) := by rfl

@[local simp] private theorem stop_entry (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e602,0x2e62b] n ⟨s,f,0x2e602⟩=some ⟨s,f,0x2e602⟩ := by cases n <;> rfl
@[local simp] private theorem stop_empty (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e602,0x2e62b] n ⟨s,f,0x2e62b⟩=some ⟨s,f,0x2e62b⟩ := by cases n <;> rfl
@[local simp] private theorem stop_body (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e629] n ⟨s,f,0x2e629⟩=some ⟨s,f,0x2e629⟩ := by cases n <;> rfl
@[local simp] private theorem stop_allocation (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e639] n ⟨s,f,0x2e639⟩=some ⟨s,f,0x2e639⟩ := by cases n <;> rfl

theorem entry_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e602,0x2e62b] 6 ⟨s,f,0x2e5ef⟩=some (entry s) := by
  have run : X86Routine.run listed [0x2e602,0x2e62b] 6 ⟨s,f,0x2e5ef⟩=some (entry s) := by
    by_cases h : (load32 s.memory (0x2c134#32)).toInt≤0
    all_goals simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,entry,PlayerHeight.logical_le,
      put,write,-BitVec.toInt_add]
    all_goals
      have negative : ¬(load32 s.memory (0x2c134#32)).toInt≤0 := by omega
      simp [negative]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

/-- Stop just before the loop branch, so the backedge cannot be mistaken for
an exit at entry. This summary retains even overlapping-pointer read order. -/
theorem body_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e629] 16 ⟨s,f,0x2e602⟩=some {result s with pc:=0x2e629} := by
  have run : X86Routine.run listed [0x2e629] 16 ⟨s,f,0x2e602⟩=some {result s with pc:=0x2e629} := by
    by_cases zero : back s=(0#32) <;> by_cases same : back s=again s
    all_goals simp [back,again,frontMemory,front] at zero same
    all_goals try rw [same] at zero
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,result,advanced,counted,second,
      frontMemory,front,back,again,cmp32_zero,put,write,BitVec.add_assoc,zero,same,-BitVec.toInt_add]
    all_goals
      funext r
      by_cases h1 : r=1 <;> by_cases h2 : r=2 <;> simp [write,h1,h2,BitVec.add_assoc]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem branch_execution (s : X86Memory.State) :
    X86Routine.execute (.jumpSigned 3 (-41)) {result s with pc:=0x2e62b}=some (result s) := by
  have opposite (a b : Word) : (b.toInt≤a.toInt) ↔ ¬a.toInt<b.toInt := by omega
  by_cases less : ((counted s).regs 6+(1#32)).toInt<(load32 (counted s).memory (0x2c134#32)).toInt
  all_goals simp [X86Routine.execute,result,advanced,PlayerHeight.cmp_ge_prop,opposite,less,-BitVec.toInt_add]

/-- One complete counting iteration, including its conditional backedge. -/
theorem iteration_path (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤17 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2e602⟩ (result s) := by
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path (body_execution s f)
  have path := path.transfer program [] (fun _ _ => rfl) (by simp)
  have tail : X86Routine.Prefix program [] 1 {result s with pc:=0x2e629} (result s) :=
    .step (op:=.jumpSigned 3 (-41)) (length:=2) (by simp) (by change program 0x2e629 = _; decide) (branch_execution s) (.nil _)
  exact ⟨n+1,by omega,OriginalGroupBounds.prefix_join path tail⟩

theorem allocation_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e639] 3 ⟨s,f,0x2e62b⟩=some (allocation s) := by
  have run : X86Routine.run listed [0x2e639] 3 ⟨s,f,0x2e62b⟩=some (allocation s) := by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,allocation,put,write]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]



/-- Only the front count and, conditionally, the distinct back count are written. -/
def Protected (a : Word) (s : X86Memory.State) : Prop :=
  Apart a (front s+78) ∧ (second s=true → Apart a (back s+78))

theorem frame (s : X86Memory.State) (a : Word) (safe : Protected a s) :
    load32 (result s).core.memory a=load32 s.memory a := by
  by_cases h : second s=true
  · simp only [result,advanced,counted,h,ite_true,put]
    rw [load_store_apart _ _ _ _ (safe.2 h)]
    exact load_store_apart _ _ _ _ safe.1
  · simp only [result,advanced,counted,h,ite_false,put]
    exact load_store_apart _ _ _ _ safe.1

theorem progress (s : X86Memory.State) :
    (result s).core.regs 0=s.regs 0+62 ∧
    (result s).core.regs 6=s.regs 6+1 ∧
    (result s).core.regs 4=s.regs 4 ∧
    (result s).core.regs 2=s.regs 2+1+(if second s then 1 else 0) := by
  by_cases h : second s=true <;> simp [result,advanced,counted,h,put,write,BitVec.add_assoc]

/-- Storage separation turns the ordered machine reads into the cached fields. -/
theorem stable_pointers (s : X86Memory.State)
    (hf : Apart (s.regs 0+46) (front s+78))
    (hb : Apart (s.regs 0+50) (front s+78)) :
    again s=front s ∧ back s=load32 s.memory (s.regs 0+50) := by
  constructor
  · exact load_store_apart _ _ _ _ hf
  · exact load_store_apart _ _ _ _ hb

theorem distinct_rule (s : X86Memory.State)
    (hf : Apart (s.regs 0+46) (front s+78))
    (hb : Apart (s.regs 0+50) (front s+78)) :
    second s=(load32 s.memory (s.regs 0+50) != 0 &&
      load32 s.memory (s.regs 0+50) != front s) := by
  simp [second,(stable_pointers s hf hb).1,(stable_pointers s hf hb).2]

theorem front_count (s : X86Memory.State)
    (safe : second s=true → Apart (front s+78) (back s+78)) :
    load32 (result s).core.memory (front s+78)=load32 s.memory (front s+78)+1 := by
  by_cases h : second s=true
  · simp only [result,advanced,counted,h,ite_true,put]
    rw [load_store_apart _ _ _ _ (safe h)]
    exact load_store _ _ _
  · simp only [result,advanced,counted,h,ite_false,put]
    exact load_store _ _ _

theorem back_count (s : X86Memory.State) (yes : second s=true)
    (safe : Apart (back s+78) (front s+78)) :
    load32 (result s).core.memory (back s+78)=load32 s.memory (back s+78)+1 := by
  simp only [result,advanced,counted,yes,ite_true,put]
  rw [load_store]
  exact congrArg (fun v : Word => v+1) (load_store_apart _ _ _ _ safe)

/-- One iteration implements exactly the grouping scan's membership predicate:
each non-null sector gains one reference iff this line belongs to it. -/
theorem sector_count (s : X86Memory.State) (q : Word) (nonzero : q≠(0#32))
    (hf : Apart (s.regs 0+46) (front s+78))
    (hb : Apart (s.regs 0+50) (front s+78))
    (fromFront : q≠front s → Apart (q+78) (front s+78))
    (fromBack : q≠back s → Apart (q+78) (back s+78)) :
    load32 (result s).core.memory (q+78)=load32 s.memory (q+78)+
      (if OriginalGroupLines.accepts q (front s) (load32 s.memory (s.regs 0+50)) then 1 else 0) := by
  obtain ⟨againFront,backInitial⟩ := stable_pointers s hf hb
  rw [←backInitial]
  by_cases frontEq : q=front s
  · have safe : second s=true → Apart (front s+78) (back s+78) := by
      intro yes
      have both : back s≠0 ∧ back s≠front s := by simpa [second,againFront] using yes
      have different := both.2
      rw [←frontEq]
      exact fromBack (by intro eq; exact different (eq.symm.trans frontEq))
    simpa [OriginalGroupLines.accepts,frontEq] using front_count s safe
  · by_cases backEq : q=back s
    · have yes : second s=true := by simp [second,againFront,←backEq,nonzero,frontEq]
      have value := back_count s yes (by rw [←backEq]; exact fromFront frontEq)
      simpa [OriginalGroupLines.accepts,←backInitial,←backEq,frontEq] using value
    · have value := frame s (q+78) ⟨fromFront frontEq,fun _ => fromBack backEq⟩
      simpa [OriginalGroupLines.accepts,←backInitial,frontEq,backEq] using value

theorem inputs_preserved (s : X86Memory.State) (es : List OriginalGroupOutput.Line)
    (before : OriginalGroupOutput.Inputs es s.memory)
    (safe : ∀ e∈es, Protected (e.address+46) s ∧ Protected (e.address+50) s) :
    OriginalGroupOutput.Inputs es (result s).core.memory := by
  intro e member
  exact ⟨(frame s _ (safe e member).1).trans (before e member).1,
    (frame s _ (safe e member).2).trans (before e member).2⟩

end Doom.Proofs.OriginalGroupCount
