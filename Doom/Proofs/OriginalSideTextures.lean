import Doom.Proofs.E1M1AimSideAdvance
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalSideTextures
open Verification X86 X86Memory X86Control BlockSummary
def texturesBytes : List UInt8 := [0xe8,0xcd,0x62,0x0,0x0,0x89,0x4,0x24,0x8b,0x4,0x24,0x66,0x89,0x42,0x8,0x89,0xf8,0xe8,0xbc,0x62,0x0,0x0,0x89,0x4,0x24,0x8b,0x4,0x24,0x66,0x89,0x42,0xa,0x89,0xf0,0xe8,0xab,0x62,0x0,0x0,0x89,0x4,0x24,0x8b,0x4,0x24,0x66,0x89,0x42,0xc]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2e47e≤pc ∧ pc<0x2e4af then X86Routine.decodeAt bytes (pc-0x2e47e) else none
def program := bytesProgram texturesBytes
def listed : X86Routine.Program
  | 0x2e47e => some (.call 25293,5)
  | 0x2e483 => some (.control (.block (.store ⟨some 4,none,0,0⟩ 0)),3)
  | 0x2e486 => some (.control (.block (.load 0 ⟨some 4,none,0,0⟩)),3)
  | 0x2e489 => some (.storeHalf ⟨some 2,none,0,8⟩ 0,4)
  | 0x2e48d => some (.control (.block (.legacy (.mov 0 7))),2)
  | 0x2e48f => some (.call 25276,5)
  | 0x2e494 => some (.control (.block (.store ⟨some 4,none,0,0⟩ 0)),3)
  | 0x2e497 => some (.control (.block (.load 0 ⟨some 4,none,0,0⟩)),3)
  | 0x2e49a => some (.storeHalf ⟨some 2,none,0,10⟩ 0,4)
  | 0x2e49e => some (.control (.block (.legacy (.mov 0 6))),2)
  | 0x2e4a0 => some (.call 25259,5)
  | 0x2e4a5 => some (.control (.block (.store ⟨some 4,none,0,0⟩ 0)),3)
  | 0x2e4a8 => some (.control (.block (.load 0 ⟨some 4,none,0,0⟩)),3)
  | 0x2e4ab => some (.storeHalf ⟨some 2,none,0,12⟩ 0,4)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

/-- Exact caller writes: full EAX to scratch, then low AX to the side field. -/
def stored (s : X86Memory.State) (off : Word) : X86Memory.State :=
  {s with memory:=(X86Routine.store16 (store32 s.memory (s.regs 4) (s.regs 0))
    (s.regs 2+off) ((s.regs 0).extractLsb' 0 16))}
def firstCall (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord s 0x2e483,f,0x34750⟩
def secondCall (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord (put (stored s 8) 0 (s.regs 7)) 0x2e494,f,0x34750⟩
def thirdCall (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord (put (stored s 10) 0 (s.regs 6)) 0x2e4a5,f,0x34750⟩
def finished (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨stored s 12,f,0x2e4af⟩
private theorem one_step (p : X86Routine.Program) (exits : List Nat) (n : Nat)
    (s : X86Control.State) (op : X86Routine.Op) (len : Nat)
    (active : s.pc∉exits) (decode : p s.pc=some (op,len)) :
    X86Routine.run p exits (n+1) s=
      (X86Routine.execute op {s with pc:=s.pc+len}).bind (X86Routine.run p exits n) := by
  rw [X86Routine.run,if_neg active,decode]
  rfl
@[local simp] private theorem step_2e47e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x34750] (n+1) ⟨s,f,0x2e47e⟩ =
      (X86Routine.execute (.call 25293) ⟨s,f,0x2e483⟩).bind (X86Routine.run listed [0x34750] n) := by
  exact @one_step listed [0x34750] n ⟨s,f,0x2e47e⟩ (.call 25293) 5
    (by change (0x2e47e : Nat)∉[0x34750]; decide)
    (show listed 0x2e47e=some (.call 25293,5) from by decide)
@[local simp] private theorem step_2e483 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x34750] (n+1) ⟨s,f,0x2e483⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 4,none,0,0⟩ 0))) ⟨s,f,0x2e486⟩).bind (X86Routine.run listed [0x34750] n) := by rfl
@[local simp] private theorem step_2e486 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x34750] (n+1) ⟨s,f,0x2e486⟩ =
      (X86Routine.execute (.control (.block (.load 0 ⟨some 4,none,0,0⟩))) ⟨s,f,0x2e489⟩).bind (X86Routine.run listed [0x34750] n) := by rfl
@[local simp] private theorem step_2e489 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x34750] (n+1) ⟨s,f,0x2e489⟩ =
      (X86Routine.execute (.storeHalf ⟨some 2,none,0,8⟩ 0) ⟨s,f,0x2e48d⟩).bind (X86Routine.run listed [0x34750] n) := by rfl
@[local simp] private theorem step_2e48d (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x34750] (n+1) ⟨s,f,0x2e48d⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 0 7)))) ⟨s,f,0x2e48f⟩).bind (X86Routine.run listed [0x34750] n) := by rfl
@[local simp] private theorem step_2e48f (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x34750] (n+1) ⟨s,f,0x2e48f⟩ =
      (X86Routine.execute (.call 25276) ⟨s,f,0x2e494⟩).bind (X86Routine.run listed [0x34750] n) := by
  exact @one_step listed [0x34750] n ⟨s,f,0x2e48f⟩ (.call 25276) 5
    (by change (0x2e48f : Nat)∉[0x34750]; decide)
    (show listed 0x2e48f=some (.call 25276,5) from by decide)
@[local simp] private theorem step_2e494 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x34750] (n+1) ⟨s,f,0x2e494⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 4,none,0,0⟩ 0))) ⟨s,f,0x2e497⟩).bind (X86Routine.run listed [0x34750] n) := by rfl
@[local simp] private theorem step_2e497 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x34750] (n+1) ⟨s,f,0x2e497⟩ =
      (X86Routine.execute (.control (.block (.load 0 ⟨some 4,none,0,0⟩))) ⟨s,f,0x2e49a⟩).bind (X86Routine.run listed [0x34750] n) := by rfl
@[local simp] private theorem step_2e49a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x34750] (n+1) ⟨s,f,0x2e49a⟩ =
      (X86Routine.execute (.storeHalf ⟨some 2,none,0,10⟩ 0) ⟨s,f,0x2e49e⟩).bind (X86Routine.run listed [0x34750] n) := by rfl
@[local simp] private theorem step_2e49e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x34750] (n+1) ⟨s,f,0x2e49e⟩ =
      (X86Routine.execute (.control (.block (.legacy (.mov 0 6)))) ⟨s,f,0x2e4a0⟩).bind (X86Routine.run listed [0x34750] n) := by rfl
@[local simp] private theorem step_2e4a0 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x34750] (n+1) ⟨s,f,0x2e4a0⟩ =
      (X86Routine.execute (.call 25259) ⟨s,f,0x2e4a5⟩).bind (X86Routine.run listed [0x34750] n) := by
  exact @one_step listed [0x34750] n ⟨s,f,0x2e4a0⟩ (.call 25259) 5
    (by change (0x2e4a0 : Nat)∉[0x34750]; decide)
    (show listed 0x2e4a0=some (.call 25259,5) from by decide)
@[local simp] private theorem step_2e4a5 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e4af] (n+1) ⟨s,f,0x2e4a5⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 4,none,0,0⟩ 0))) ⟨s,f,0x2e4a8⟩).bind (X86Routine.run listed [0x2e4af] n) := by rfl
@[local simp] private theorem step_2e4a8 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e4af] (n+1) ⟨s,f,0x2e4a8⟩ =
      (X86Routine.execute (.control (.block (.load 0 ⟨some 4,none,0,0⟩))) ⟨s,f,0x2e4ab⟩).bind (X86Routine.run listed [0x2e4af] n) := by rfl
@[local simp] private theorem step_2e4ab (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e4af] (n+1) ⟨s,f,0x2e4ab⟩ =
      (X86Routine.execute (.storeHalf ⟨some 2,none,0,12⟩ 0) ⟨s,f,0x2e4af⟩).bind (X86Routine.run listed [0x2e4af] n) := by rfl
@[local simp] private theorem stop_34750 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x34750] n ⟨s,f,0x34750⟩=some ⟨s,f,0x34750⟩ := by cases n <;> rfl
@[local simp] private theorem stop_2e4af (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e4af] n ⟨s,f,0x2e4af⟩=some ⟨s,f,0x2e4af⟩ := by cases n <;> rfl
theorem first_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x34750] 1 ⟨s,f,0x2e47e⟩=some (firstCall s f) := by
  have run : X86Routine.run listed [0x34750] 1 ⟨s,f,0x2e47e⟩=some (firstCall s f) := by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,firstCall,secondCall,thirdCall,finished,stored,
      X86Routine.pushWord,put,write,load_store,BitVec.add_assoc,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem second_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x34750] 5 ⟨s,f,0x2e483⟩=some (secondCall s f) := by
  have run : X86Routine.run listed [0x34750] 5 ⟨s,f,0x2e483⟩=some (secondCall s f) := by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,firstCall,secondCall,thirdCall,finished,stored,
      X86Routine.pushWord,put,write,load_store,BitVec.add_assoc,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem third_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x34750] 5 ⟨s,f,0x2e494⟩=some (thirdCall s f) := by
  have run : X86Routine.run listed [0x34750] 5 ⟨s,f,0x2e494⟩=some (thirdCall s f) := by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,firstCall,secondCall,thirdCall,finished,stored,
      X86Routine.pushWord,put,write,load_store,BitVec.add_assoc,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem finish_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e4af] 3 ⟨s,f,0x2e4a5⟩=some (finished s f) := by
  have run : X86Routine.run listed [0x2e4af] 3 ⟨s,f,0x2e4a5⟩=some (finished s f) := by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,firstCall,secondCall,thirdCall,finished,stored,
      X86Routine.pushWord,put,write,load_store,BitVec.add_assoc,-BitVec.toInt_add]
    funext r
    by_cases h : r=0 <;> simp [write,h]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem return_addresses (s : X86Memory.State) (f : Option Flags) :
    load32 (firstCall s f).core.memory ((firstCall s f).core.regs 4)=0x2e483 ∧
    load32 (secondCall s f).core.memory ((secondCall s f).core.regs 4)=0x2e494 ∧
    load32 (thirdCall s f).core.memory ((thirdCall s f).core.regs 4)=0x2e4a5 := by
  simp [firstCall,secondCall,thirdCall,X86Routine.pushWord,stored,put,write,load_store]

theorem arguments (s : X86Memory.State) (f : Option Flags) :
    (firstCall s f).core.regs 0=s.regs 0 ∧ (secondCall s f).core.regs 0=s.regs 7 ∧
    (thirdCall s f).core.regs 0=s.regs 6 ∧
    (firstCall s f).core.regs 4=s.regs 4-4 ∧ (secondCall s f).core.regs 4=s.regs 4-4 ∧
    (thirdCall s f).core.regs 4=s.regs 4-4 := by
  simp [firstCall,secondCall,thirdCall,X86Routine.pushWord,stored,put,write]

theorem stored_value (s : X86Memory.State) (off : Word) :
    load16 (stored s off).memory (s.regs 2+off)=(s.regs 0).extractLsb' 0 16 := by
  exact HalfMemory.readback _ _ _

theorem stored_frame (s : X86Memory.State) (off a : Word)
    (scratch : Apart a (s.regs 4)) (field : HalfMemory.Separate 4 2 a (s.regs 2+off)) :
    load32 (stored s off).memory a=load32 s.memory a := by
  change load32 (X86Routine.store16 (store32 s.memory (s.regs 4) (s.regs 0))
    (s.regs 2+off) ((s.regs 0).extractLsb' 0 16)) a=_
  rw [HalfMemory.word_frame _ _ _ _ field,load_store_apart _ _ _ _ scratch]

theorem first_frame (s : X86Memory.State) (f : Option Flags) (a : Word)
    (stack : Apart a (s.regs 4-4)) : load32 (firstCall s f).core.memory a=load32 s.memory a := by
  exact load_store_apart _ _ _ _ stack

theorem second_frame (s : X86Memory.State) (f : Option Flags) (a : Word)
    (scratch : Apart a (s.regs 4)) (field : HalfMemory.Separate 4 2 a (s.regs 2+8))
    (stack : Apart a (s.regs 4-4)) : load32 (secondCall s f).core.memory a=load32 s.memory a := by
  change load32 (store32 (stored s 8).memory (s.regs 4-4) 0x2e494) a=_
  rw [load_store_apart _ _ _ _ stack,stored_frame s 8 a scratch field]

theorem third_frame (s : X86Memory.State) (f : Option Flags) (a : Word)
    (scratch : Apart a (s.regs 4)) (field : HalfMemory.Separate 4 2 a (s.regs 2+10))
    (stack : Apart a (s.regs 4-4)) : load32 (thirdCall s f).core.memory a=load32 s.memory a := by
  change load32 (store32 (stored s 10).memory (s.regs 4-4) 0x2e4a5) a=_
  rw [load_store_apart _ _ _ _ stack,stored_frame s 10 a scratch field]

end Doom.Proofs.OriginalSideTextures
