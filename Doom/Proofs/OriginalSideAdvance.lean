import Doom.Proofs.E1M1AimSideEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalSideAdvance
open Verification X86 X86Memory X86Control BlockSummary
def latchBytes : List UInt8 := [0xa1,0x1c,0xc1,0x2,0x0,0x83,0xc6,0x1e,0x39,0xc5,0x7c,0x8d]
def offsetsBytes : List UInt8 := [0xf,0xbf,0x3,0xc1,0xe0,0x10,0x89,0x2,0xf,0xbf,0x43,0x2,0xc1,0xe0,0x10,0x89,0x42,0x4,0x89,0xc8]
def bytesProgram (publish link latch offsets : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2e4d1≤pc ∧ pc<0x2e4dd then X86Routine.decodeAt latch (pc-0x2e4d1)
  else if 0x2e46a≤pc ∧ pc<0x2e47e then X86Routine.decodeAt offsets (pc-0x2e46a)
  else OriginalSideLoader.bytesProgram publish link pc
def program := bytesProgram OriginalSideLoader.publishBytes OriginalSideLoader.linkBytes latchBytes offsetsBytes
def listed : X86Routine.Program
  | 0x2e4d1 => some (.control (.block (.load 0 ⟨none,none,0,0x2c11c⟩)),5)
  | 0x2e4d6 => some (.addImmediate 6 30,3)
  | 0x2e4d9 => some (.compareRegisters 5 0,2)
  | 0x2e4db => some (.jumpSigned 3 (-115),2)
  | 0x2e46a => some (.control (.block (.legacy (.movsx16 0 3 0))),3)
  | 0x2e46d => some (.control (.block (.legacy (.shl 0 16))),3)
  | 0x2e470 => some (.control (.block (.store ⟨some 2,none,0,0⟩ 0)),2)
  | 0x2e472 => some (.control (.block (.legacy (.movsx16 0 3 2))),4)
  | 0x2e476 => some (.control (.block (.legacy (.shl 0 16))),3)
  | 0x2e479 => some (.control (.block (.store ⟨some 2,none,0,4⟩ 0)),3)
  | 0x2e47c => some (.control (.block (.legacy (.mov 0 1))),2)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def advanced (s : X86Memory.State) : X86Control.State :=
  ⟨put (put s 0 (load32 s.memory 0x2c11c)) 6 (s.regs 6+30),
    some (compare32 (s.regs 5) (load32 s.memory 0x2c11c)),
    if (s.regs 5).toInt<(load32 s.memory 0x2c11c).toInt then 0x2e46a else 0x2e4dd⟩
/-- The second offset is read after the first store, retaining alias behavior. -/
def first (s : X86Memory.State) : Word := (load16 s.memory (s.regs 3)).signExtend 32 <<< 16
def firstMemory (s : X86Memory.State) : Memory := store32 s.memory (s.regs 2) (first s)
def second (s : X86Memory.State) : Word := (load16 (firstMemory s) (s.regs 3+2)).signExtend 32 <<< 16
def prepared (s : X86Memory.State) : X86Control.State :=
  ⟨{put s 0 (s.regs 1) with memory:=store32 (firstMemory s) (s.regs 2+4) (second s)},none,0x2e47e⟩
def result (s : X86Memory.State) := advanced (OriginalSideLoader.linked s).core
@[local simp] private theorem step_2e4d1 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e46a,0x2e4dd] (n+1) ⟨s,f,0x2e4d1⟩ =
      (X86Routine.execute (.control (.block (.load 0 ⟨none,none,0,0x2c11c⟩))) ⟨s,f,0x2e4d6⟩).bind (X86Routine.run listed [0x2e46a,0x2e4dd] n) := by rfl
@[local simp] private theorem step_2e4d6 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e46a,0x2e4dd] (n+1) ⟨s,f,0x2e4d6⟩ =
      (X86Routine.execute (.addImmediate 6 30) ⟨s,f,0x2e4d9⟩).bind (X86Routine.run listed [0x2e46a,0x2e4dd] n) := by rfl
@[local simp] private theorem step_2e4d9 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e46a,0x2e4dd] (n+1) ⟨s,f,0x2e4d9⟩ =
      (X86Routine.execute (.compareRegisters 5 0) ⟨s,f,0x2e4db⟩).bind (X86Routine.run listed [0x2e46a,0x2e4dd] n) := by rfl
@[local simp] private theorem step_2e4db (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e46a,0x2e4dd] (n+1) ⟨s,f,0x2e4db⟩ =
      (X86Routine.execute (.jumpSigned 3 (-115)) ⟨s,f,0x2e4dd⟩).bind (X86Routine.run listed [0x2e46a,0x2e4dd] n) := by rfl
@[local simp] private theorem stop_2e46a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e46a,0x2e4dd] n ⟨s,f,0x2e46a⟩=some ⟨s,f,0x2e46a⟩ := by cases n <;> rfl
@[local simp] private theorem stop_2e4dd (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e46a,0x2e4dd] n ⟨s,f,0x2e4dd⟩=some ⟨s,f,0x2e4dd⟩ := by cases n <;> rfl
@[local simp] private theorem step_2e46a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e47e] (n+1) ⟨s,f,0x2e46a⟩ =
      (X86Routine.execute (.control (.block (.legacy (.movsx16 0 3 0)))) ⟨s,f,0x2e46d⟩).bind (X86Routine.run listed [0x2e47e] n) := by rfl
@[local simp] private theorem step_2e46d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e47e] (n+1) ⟨s,f,0x2e46d⟩ =
      (X86Routine.execute (.control (.block (.legacy (.shl 0 16)))) ⟨s,f,0x2e470⟩).bind (X86Routine.run listed [0x2e47e] n) := by rfl
@[local simp] private theorem step_2e470 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e47e] (n+1) ⟨s,f,0x2e470⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 2,none,0,0⟩ 0))) ⟨s,f,0x2e472⟩).bind (X86Routine.run listed [0x2e47e] n) := by rfl
@[local simp] private theorem step_2e472 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e47e] (n+1) ⟨s,f,0x2e472⟩ =
      (X86Routine.execute (.control (.block (.legacy (.movsx16 0 3 2)))) ⟨s,f,0x2e476⟩).bind (X86Routine.run listed [0x2e47e] n) := by rfl
@[local simp] private theorem step_2e476 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e47e] (n+1) ⟨s,f,0x2e476⟩ =
      (X86Routine.execute (.control (.block (.legacy (.shl 0 16)))) ⟨s,f,0x2e479⟩).bind (X86Routine.run listed [0x2e47e] n) := by rfl
@[local simp] private theorem step_2e479 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e47e] (n+1) ⟨s,f,0x2e479⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 2,none,0,4⟩ 0))) ⟨s,f,0x2e47c⟩).bind (X86Routine.run listed [0x2e47e] n) := by rfl
@[local simp] private theorem step_2e47c (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e47e] (n+1) ⟨s,f,0x2e47c⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 0 1)))) ⟨s,f,0x2e47e⟩).bind (X86Routine.run listed [0x2e47e] n) := by rfl
@[local simp] private theorem stop_2e47e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e47e] n ⟨s,f,0x2e47e⟩=some ⟨s,f,0x2e47e⟩ := by cases n <;> rfl
theorem latch_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e46a,0x2e4dd] 4 ⟨s,f,0x2e4d1⟩=some (advanced s) := by
  have run : X86Routine.run listed [0x2e46a,0x2e4dd] 4 ⟨s,f,0x2e4d1⟩=some (advanced s) := by
    have opposite : (load32 s.memory (0x2c11c#32)).toInt≤(s.regs 5).toInt ↔
        ¬(s.regs 5).toInt<(load32 s.memory (0x2c11c#32)).toInt := by omega
    by_cases less : (s.regs 5).toInt<(load32 s.memory (0x2c11c#32)).toInt
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,advanced,
      PlayerHeight.cmp_ge_prop,opposite,less,put,write,BitVec.add_assoc,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem offsets_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e47e] 7 ⟨s,f,0x2e46a⟩=some (prepared s) := by
  have run : X86Routine.run listed [0x2e47e] 7 ⟨s,f,0x2e46a⟩=some (prepared s) := by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,prepared,firstMemory,first,second,
      put,write,BitVec.add_assoc,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem original_agrees (pc : Nat) (h : OriginalSideLoader.program pc≠none) :
    program pc=OriginalSideLoader.program pc := by
  have within : (0x2e415≤pc ∧ pc<0x2e41c) ∨ (0x2e4af≤pc ∧ pc<0x2e4d1) := by
    by_cases yes : (0x2e415≤pc ∧ pc<0x2e41c) ∨ (0x2e4af≤pc ∧ pc<0x2e4d1)
    · exact yes
    have a : ¬(0x2e415≤pc ∧ pc<0x2e41c) := by omega
    have b : ¬(0x2e4af≤pc ∧ pc<0x2e4d1) := by omega
    simp [OriginalSideLoader.program,OriginalSideLoader.bytesProgram,a,b] at h
  simp [program,bytesProgram,show ¬(0x2e4d1≤pc ∧ pc<0x2e4dd) from by omega,
    show ¬(0x2e46a≤pc ∧ pc<0x2e47e) from by omega,OriginalSideLoader.program]

theorem linked_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e46a,0x2e4dd] 15 ⟨s,f,0x2e4af⟩=some (result s) := by
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path (OriginalSideLoader.link_execution s f)
  have active (pc : Nat) (h : OriginalSideLoader.program pc≠none) : pc∉[0x2e46a,0x2e4dd] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    constructor <;> intro eq <;> subst pc <;> exact h (by decide)
  have path := path.transfer program [0x2e46a,0x2e4dd] original_agrees active
  exact path.finish (latch_execution (OriginalSideLoader.linked s).core (OriginalSideLoader.linked s).flags) 15 (by omega)

theorem continued_execution (s : X86Memory.State) (f : Option Flags)
    (next : (result s).pc=0x2e46a) :
    X86Routine.run program [0x2e47e,0x2e4dd] 22 ⟨s,f,0x2e4af⟩=
      some (prepared (result s).core) := by
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path (linked_execution s f)
  have active (pc : Nat) (h : program pc≠none) : pc∉[0x2e47e,0x2e4dd] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    constructor <;> intro eq <;> subst pc <;> exact h (by decide)
  have path := path.transfer program [0x2e47e,0x2e4dd] (fun _ _ => rfl) active
  have tail := offsets_execution (result s).core (result s).flags
  obtain ⟨k,hk,tailpath,last⟩ := X86Routine.run_path tail
  have tailpath := tailpath.transfer program [0x2e47e,0x2e4dd] (fun _ _ => rfl) active
  have seam : (⟨(result s).core,(result s).flags,0x2e46a⟩ : X86Control.State)=result s := by rw [←next]
  rw [seam] at tailpath
  have stop : X86Routine.run program [0x2e47e,0x2e4dd] 0 (prepared (result s).core)=some (prepared (result s).core) := by rfl
  exact path.finish (tailpath.finish stop 7 (by omega)) 22 (by omega)

theorem memory (s : X86Memory.State) : (result s).core.memory=(OriginalSideLoader.linked s).core.memory := by rfl

theorem offsets_frame (s : X86Memory.State) (a : Word)
    (firstSafe : Apart a (s.regs 2)) (secondSafe : Apart a (s.regs 2+4)) :
    load32 (prepared s).core.memory a=load32 s.memory a := by
  change load32 (store32 (store32 s.memory (s.regs 2) (first s)) (s.regs 2+4) (second s)) a=_
  rw [load_store_apart _ _ _ _ secondSafe,load_store_apart _ _ _ _ firstSafe]

end Doom.Proofs.OriginalSideAdvance
