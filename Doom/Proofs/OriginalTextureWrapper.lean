import Doom.Proofs.E1M1AimSideTextures
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalTextureWrapper
open Verification X86 X86Memory X86Control BlockSummary
def wrapperBytes : List UInt8 := [0x53,0x52,0x89,0xc2,0xe8,0x97,0xff,0xff,0xff,0x89,0xc3,0x83,0xf8,0xff,0x75,0xe,0x52,0x68,0xb0,0x34,0x2,0x0,0xe8,0xa5,0x63,0xfe,0xff,0x83,0xc4,0x8,0x89,0xd8,0x5a,0x5b,0xc3]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x34750≤pc ∧ pc<0x34773 then X86Routine.decodeAt bytes (pc-0x34750) else none
def program := bytesProgram wrapperBytes
def listed : X86Routine.Program
  | 0x34750 => some (.push 3,1)
  | 0x34751 => some (.push 2,1)
  | 0x34752 => some (.control (.block (.legacy (.mov 2 0))),2)
  | 0x34754 => some (.call (-105),5)
  | 0x34759 => some (.control (.block (.legacy (.mov 3 0))),2)
  | 0x3475b => some (.compareRegister 0 0xffffffff,3)
  | 0x3475e => some (.control (.jumpZero false 14),2)
  | 0x3476e => some (.control (.block (.legacy (.mov 0 3))),2)
  | 0x34770 => some (.pop 2,1)
  | 0x34771 => some (.pop 3,1)
  | 0x34772 => some (.ret,1)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def saved (s : X86Memory.State) := X86Routine.pushWord (X86Routine.pushWord s (s.regs 3)) (s.regs 2)
def search (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord (put (saved s) 2 (s.regs 0)) 0x34759,f,0x346f0⟩
def choice (s : X86Memory.State) : X86Control.State :=
  ⟨put s 3 (s.regs 0),some (compare32 (s.regs 0) 0xffffffff),
    if s.regs 0=(0xffffffff#32) then 0x34760 else 0x3476e⟩
def restored (s : X86Memory.State) :=
  put (put (put (put s 0 (s.regs 3)) 2 (load32 s.memory (s.regs 4)))
    3 (load32 s.memory (s.regs 4+4))) 4 (s.regs 4+12)
def result (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨restored s,f,(load32 s.memory (s.regs 4+8)).toNat⟩
private theorem one_step (p : X86Routine.Program) (exits : List Nat) (n : Nat)
    (s : X86Control.State) (op : X86Routine.Op) (len : Nat)
    (active : s.pc∉exits) (decode : p s.pc=some (op,len)) :
    X86Routine.run p exits (n+1) s=
      (X86Routine.execute op {s with pc:=s.pc+len}).bind (X86Routine.run p exits n) := by
  rw [X86Routine.run,if_neg active,decode]
  rfl
@[local simp] private theorem step_34750 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x34750∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x34750⟩=
      (X86Routine.execute (.push 3) ⟨s,f,0x34751⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x34750⟩ (.push 3) 1 h (by rfl)
@[local simp] private theorem step_34751 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x34751∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x34751⟩=
      (X86Routine.execute (.push 2) ⟨s,f,0x34752⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x34751⟩ (.push 2) 1 h (by rfl)
@[local simp] private theorem step_34752 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x34752∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x34752⟩=
      (X86Routine.execute (.control (.block (.legacy (.mov 2 0)))) ⟨s,f,0x34754⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x34752⟩ (.control (.block (.legacy (.mov 2 0)))) 2 h (by rfl)
@[local simp] private theorem step_34754 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x34754∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x34754⟩=
      (X86Routine.execute (.call (-105)) ⟨s,f,0x34759⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x34754⟩ (.call (-105)) 5 h (by rfl)
@[local simp] private theorem step_34759 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x34759∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x34759⟩=
      (X86Routine.execute (.control (.block (.legacy (.mov 3 0)))) ⟨s,f,0x3475b⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x34759⟩ (.control (.block (.legacy (.mov 3 0)))) 2 h (by rfl)
@[local simp] private theorem step_3475b (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x3475b∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x3475b⟩=
      (X86Routine.execute (.compareRegister 0 0xffffffff) ⟨s,f,0x3475e⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x3475b⟩ (.compareRegister 0 0xffffffff) 3 h (by rfl)
@[local simp] private theorem step_3475e (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x3475e∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x3475e⟩=
      (X86Routine.execute (.control (.jumpZero false 14)) ⟨s,f,0x34760⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x3475e⟩ (.control (.jumpZero false 14)) 2 h (by rfl)
@[local simp] private theorem step_3476e (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x3476e∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x3476e⟩=
      (X86Routine.execute (.control (.block (.legacy (.mov 0 3)))) ⟨s,f,0x34770⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x3476e⟩ (.control (.block (.legacy (.mov 0 3)))) 2 h (by rfl)
@[local simp] private theorem step_34770 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x34770∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x34770⟩=
      (X86Routine.execute (.pop 2) ⟨s,f,0x34771⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x34770⟩ (.pop 2) 1 h (by rfl)
@[local simp] private theorem step_34771 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x34771∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x34771⟩=
      (X86Routine.execute (.pop 3) ⟨s,f,0x34772⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x34771⟩ (.pop 3) 1 h (by rfl)
@[local simp] private theorem step_34772 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x34772∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x34772⟩=
      (X86Routine.execute (.ret) ⟨s,f,0x34773⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x34772⟩ (.ret) 1 h (by rfl)
@[local simp] private theorem stopped (s : X86Memory.State) (f : Option Flags)
    (n pc : Nat) (exits : List Nat) (h : pc∈exits) :
    X86Routine.run listed exits n ⟨s,f,pc⟩=some ⟨s,f,pc⟩ := by
  cases n <;> simp [X86Routine.run,h]

theorem entry_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x346f0] 4 ⟨s,f,0x34750⟩=some (search s f) := by
  have run : X86Routine.run listed [0x346f0] 4 ⟨s,f,0x34750⟩=some (search s f) := by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86.execute,blockPreservesFlags,search,saved,X86Routine.pushWord,put,write]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem gate_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x34760,0x3476e] 3 ⟨s,f,0x34759⟩=some (choice s) := by
  have run : X86Routine.run listed [0x34760,0x3476e] 3 ⟨s,f,0x34759⟩=some (choice s) := by
    by_cases h : s.regs 0=(0xffffffff#32)
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86.execute,blockPreservesFlags,choice,cmp32_zero,h,put,write]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem return_execution (s : X86Memory.State) (f : Option Flags) (dest : Word)
    (outside : dest.toNat<0x3476e ∨ 0x34773≤dest.toNat)
    (ret : load32 s.memory (s.regs 4+8)=dest) :
    X86Routine.run program [dest.toNat] 4 ⟨s,f,0x3476e⟩=some (result s f) := by
  change load32 s.memory (s.regs 4+(8#32))=dest at ret
  have h0 : dest.toNat≠0x3476e := by omega
  have h1 : dest.toNat≠0x34770 := by omega
  have h2 : dest.toNat≠0x34771 := by omega
  have h3 : dest.toNat≠0x34772 := by omega
  have run : X86Routine.run listed [dest.toNat] 4 ⟨s,f,0x3476e⟩=some (result s f) := by
    simp [h0,h1,h2,h3,Ne.symm h0,Ne.symm h1,Ne.symm h2,Ne.symm h3,
      X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86.execute,blockPreservesFlags,result,restored,put,write,BitVec.add_assoc,ret]
    funext r
    by_cases h : r=4 <;> simp [write,h]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem entry_arguments (s : X86Memory.State) (f : Option Flags) :
    (search s f).core.regs 0=s.regs 0 ∧ (search s f).core.regs 2=s.regs 0 ∧
    (search s f).core.regs 4=s.regs 4-12 ∧
    load32 (search s f).core.memory ((search s f).core.regs 4)=0x34759 := by
  simp [search,saved,X86Routine.pushWord,put,write,load_store,BitVec.sub_sub]

theorem entry_frame (s : X86Memory.State) (f : Option Flags) (a : Word)
    (ebx : Apart a (s.regs 4-4)) (edx : Apart a (s.regs 4-8))
    (call : Apart a (s.regs 4-12)) :
    load32 (search s f).core.memory a=load32 s.memory a := by
  change load32 (store32 (store32 (store32 s.memory (s.regs 4-4) (s.regs 3))
    (s.regs 4-4-4) (s.regs 2)) (s.regs 4-4-4-4) 0x34759) a=_
  have h8 : s.regs 4-4-4=s.regs 4-8 := by simp [BitVec.sub_sub]
  have h12 : s.regs 4-4-4-4=s.regs 4-12 := by simp [BitVec.sub_sub]
  rw [h12,h8,load_store_apart _ _ _ _ call,load_store_apart _ _ _ _ edx,
    load_store_apart _ _ _ _ ebx]

theorem return_memory (s : X86Memory.State) (f : Option Flags) :
    (result s f).core.memory=s.memory := by rfl

theorem return_registers (s : X86Memory.State) (f : Option Flags) :
    (result s f).core.regs 0=s.regs 3 ∧
    (result s f).core.regs 2=load32 s.memory (s.regs 4) ∧
    (result s f).core.regs 3=load32 s.memory (s.regs 4+4) ∧
    (result s f).core.regs 4=s.regs 4+12 ∧
    (∀ r, r≠0 → r≠2 → r≠3 → r≠4 → (result s f).core.regs r=s.regs r) := by
  simp [result,restored,put,write]
  intro r h0 h2 h3 h4
  simp [h0,h2,h3,h4]
theorem saved_slots (s : X86Memory.State) (f : Option Flags) :
  load32 (search s f).core.memory (s.regs 4-8)=s.regs 2 ∧
  load32 (search s f).core.memory (s.regs 4-4)=s.regs 3 ∧
  load32 (search s f).core.memory (s.regs 4)=load32 s.memory (s.regs 4) := by
  have sep (a b : Fin 8) (h : a≠b) := PlayerHeight.slots_apart (s.regs 4-12) a b h
  have h10 : Apart (s.regs 4-8) (s.regs 4-12) := by
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using sep 1 0 (by decide)
  have h20 : Apart (s.regs 4-4) (s.regs 4-12) := by
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using sep 2 0 (by decide)
  have h21 : Apart (s.regs 4-4) (s.regs 4-8) := by
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using sep 2 1 (by decide)
  have h30 : Apart (s.regs 4) (s.regs 4-12) := by
    have h := sep 3 0 (by decide)
    change Apart (s.regs 4-12+12) (s.regs 4-12+0) at h
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h
  have h31 : Apart (s.regs 4) (s.regs 4-8) := by
    have h := sep 3 1 (by decide)
    change Apart (s.regs 4-12+12) (s.regs 4-12+4) at h
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h
  have h32 : Apart (s.regs 4) (s.regs 4-4) := by
    have h := sep 3 2 (by decide)
    change Apart (s.regs 4-12+12) (s.regs 4-12+8) at h
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h
  have mem : (search s f).core.memory=
      store32 (store32 (store32 s.memory (s.regs 4-4) (s.regs 3))
        (s.regs 4-8) (s.regs 2)) (s.regs 4-12) 0x34759 := by
    simp [search,saved,X86Routine.pushWord,
      put,write,BitVec.sub_sub]
  rw [mem]
  simp only [load_store_apart _ _ _ _ h10,load_store_apart _ _ _ _ h20,
    load_store_apart _ _ _ _ h21,load_store_apart _ _ _ _ h30,
    load_store_apart _ _ _ _ h31,load_store_apart _ _ _ _ h32,load_store,and_self]

end Doom.Proofs.OriginalTextureWrapper
