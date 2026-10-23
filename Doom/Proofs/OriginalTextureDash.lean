import Doom.Proofs.E1M1AimTextureWrapper
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalTextureDash
open Verification X86 X86Memory X86Control BlockSummary
def entryBytes : List UInt8 := [0x53,0x51,0x52,0x56,0x57,0x89,0xc7,0x80,0x38,0x2d,0x75,0x4,0x31,0xc0,0xeb,0x41]
def restoreBytes : List UInt8 := [0x5f,0x5e,0x5a,0x59,0x5b,0xc3]
def bytesProgram (entry restore : List UInt8) : X86Routine.Program := fun pc =>
  if 0x346f0≤pc ∧ pc<0x34700 then X86Routine.decodeAt entry (pc-0x346f0)
  else if 0x34741≤pc ∧ pc<0x34747 then X86Routine.decodeAt restore (pc-0x34741) else none
def program := bytesProgram entryBytes restoreBytes
def listed : X86Routine.Program
  | 0x346f0 => some (.push 3,1)
  | 0x346f1 => some (.push 1,1)
  | 0x346f2 => some (.push 2,1)
  | 0x346f3 => some (.push 6,1)
  | 0x346f4 => some (.push 7,1)
  | 0x346f5 => some (.control (.block (.legacy (.mov 7 0))),2)
  | 0x346f7 => some (.compareByte ⟨some 0,none,0,0⟩ 0x2d,3)
  | 0x346fa => some (.control (.jumpZero false 4),2)
  | 0x346fc => some (.xorRegister 0 0,2)
  | 0x346fe => some (.jump 65,2)
  | 0x34741 => some (.pop 7,1)
  | 0x34742 => some (.pop 6,1)
  | 0x34743 => some (.pop 2,1)
  | 0x34744 => some (.pop 1,1)
  | 0x34745 => some (.pop 3,1)
  | 0x34746 => some (.ret,1)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def stackMemory (s : X86Memory.State) : Memory :=
  store32 (store32 (store32 (store32 (store32 s.memory (s.regs 4-4) (s.regs 3))
    (s.regs 4-8) (s.regs 1)) (s.regs 4-12) (s.regs 2))
    (s.regs 4-16) (s.regs 6)) (s.regs 4-20) (s.regs 7)
def prepared (s : X86Memory.State) : X86Memory.State :=
  {put (put s 4 (s.regs 4-20)) 7 (s.regs 0) with memory:=stackMemory s}
/-- The byte is read after the five pushes, retaining alias behavior. -/
def nameByte (s : X86Memory.State) := stackMemory s (s.regs 0)
def gate (s : X86Memory.State) : X86Control.State :=
  ⟨prepared s,some (X86Routine.compare8 (nameByte s) 0x2d),
    if nameByte s=(0x2d#8) then 0x346fc else 0x34700⟩
def zeroed (s : X86Memory.State) : X86Control.State :=
  ⟨put s 0 0,some (logical32 0),0x34741⟩
def restored (s : X86Memory.State) :=
  put (put (put (put (put (put s 7 (load32 s.memory (s.regs 4)))
    6 (load32 s.memory (s.regs 4+4))) 2 (load32 s.memory (s.regs 4+8)))
    1 (load32 s.memory (s.regs 4+12))) 3 (load32 s.memory (s.regs 4+16))) 4 (s.regs 4+24)
def result (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨restored s,f,(load32 s.memory (s.regs 4+20)).toNat⟩
@[local simp] private theorem step_346f0 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x346f0∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x346f0⟩=
      (X86Routine.execute (.push 3) ⟨s,f,0x346f1⟩).bind (X86Routine.run listed exits n) := by
  rw [X86Routine.run,if_neg h]
  rfl
@[local simp] private theorem step_346f1 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x346f1∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x346f1⟩=
      (X86Routine.execute (.push 1) ⟨s,f,0x346f2⟩).bind (X86Routine.run listed exits n) := by
  rw [X86Routine.run,if_neg h]
  rfl
@[local simp] private theorem step_346f2 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x346f2∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x346f2⟩=
      (X86Routine.execute (.push 2) ⟨s,f,0x346f3⟩).bind (X86Routine.run listed exits n) := by
  rw [X86Routine.run,if_neg h]
  rfl
@[local simp] private theorem step_346f3 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x346f3∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x346f3⟩=
      (X86Routine.execute (.push 6) ⟨s,f,0x346f4⟩).bind (X86Routine.run listed exits n) := by
  rw [X86Routine.run,if_neg h]
  rfl
@[local simp] private theorem step_346f4 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x346f4∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x346f4⟩=
      (X86Routine.execute (.push 7) ⟨s,f,0x346f5⟩).bind (X86Routine.run listed exits n) := by
  rw [X86Routine.run,if_neg h]
  rfl
@[local simp] private theorem step_346f5 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x346f5∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x346f5⟩=
      (X86Routine.execute (.control (.block (.legacy (.mov 7 0)))) ⟨s,f,0x346f7⟩).bind (X86Routine.run listed exits n) := by
  rw [X86Routine.run,if_neg h]
  rfl
@[local simp] private theorem step_346f7 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x346f7∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x346f7⟩=
      (X86Routine.execute (.compareByte ⟨some 0,none,0,0⟩ 0x2d) ⟨s,f,0x346fa⟩).bind (X86Routine.run listed exits n) := by
  rw [X86Routine.run,if_neg h]
  rfl
@[local simp] private theorem step_346fa (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x346fa∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x346fa⟩=
      (X86Routine.execute (.control (.jumpZero false 4)) ⟨s,f,0x346fc⟩).bind (X86Routine.run listed exits n) := by
  rw [X86Routine.run,if_neg h]
  rfl
@[local simp] private theorem step_346fc (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x346fc∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x346fc⟩=
      (X86Routine.execute (.xorRegister 0 0) ⟨s,f,0x346fe⟩).bind (X86Routine.run listed exits n) := by
  rw [X86Routine.run,if_neg h]
  rfl
@[local simp] private theorem step_346fe (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x346fe∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x346fe⟩=
      (X86Routine.execute (.jump 65) ⟨s,f,0x34700⟩).bind (X86Routine.run listed exits n) := by
  rw [X86Routine.run,if_neg h]
  rfl
@[local simp] private theorem step_34741 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x34741∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x34741⟩=
      (X86Routine.execute (.pop 7) ⟨s,f,0x34742⟩).bind (X86Routine.run listed exits n) := by
  rw [X86Routine.run,if_neg h]
  rfl
@[local simp] private theorem step_34742 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x34742∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x34742⟩=
      (X86Routine.execute (.pop 6) ⟨s,f,0x34743⟩).bind (X86Routine.run listed exits n) := by
  rw [X86Routine.run,if_neg h]
  rfl
@[local simp] private theorem step_34743 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x34743∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x34743⟩=
      (X86Routine.execute (.pop 2) ⟨s,f,0x34744⟩).bind (X86Routine.run listed exits n) := by
  rw [X86Routine.run,if_neg h]
  rfl
@[local simp] private theorem step_34744 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x34744∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x34744⟩=
      (X86Routine.execute (.pop 1) ⟨s,f,0x34745⟩).bind (X86Routine.run listed exits n) := by
  rw [X86Routine.run,if_neg h]
  rfl
@[local simp] private theorem step_34745 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x34745∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x34745⟩=
      (X86Routine.execute (.pop 3) ⟨s,f,0x34746⟩).bind (X86Routine.run listed exits n) := by
  rw [X86Routine.run,if_neg h]
  rfl
@[local simp] private theorem step_34746 (s : X86Memory.State) (f : Option Flags)
    (n : Nat) (exits : List Nat) (h : 0x34746∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x34746⟩=
      (X86Routine.execute (.ret) ⟨s,f,0x34747⟩).bind (X86Routine.run listed exits n) := by
  rw [X86Routine.run,if_neg h]
  rfl
@[local simp] private theorem stopped (s : X86Memory.State) (f : Option Flags)
    (n pc : Nat) (exits : List Nat) (h : pc∈exits) :
    X86Routine.run listed exits n ⟨s,f,pc⟩=some ⟨s,f,pc⟩ := by
  cases n <;> simp [X86Routine.run,h]

theorem entry_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x346fc,0x34700] 8 ⟨s,f,0x346f0⟩=some (gate s) := by
  have run : X86Routine.run listed [0x346fc,0x34700] 8 ⟨s,f,0x346f0⟩=some (gate s) := by
    have cmp (b : BitVec 8) : (X86Routine.compare8 b (0x2d#8)).zero=(b == (0x2d#8)) := by
      have h : ∀ b : BitVec 8, (X86Routine.compare8 b (0x2d#8)).zero=(b == (0x2d#8)) := by decide +kernel
      exact h b
    by_cases h : nameByte s=(0x2d#8)
    all_goals simp [nameByte,stackMemory] at h
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,gate,prepared,nameByte,
      X86Routine.pushWord,put,write,BitVec.sub_sub,stackMemory,cmp,h]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem zero_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x34741] 2 ⟨s,f,0x346fc⟩=some (zeroed s) := by
  have run : X86Routine.run listed [0x34741] 2 ⟨s,f,0x346fc⟩=some (zeroed s) := by
    simp [X86Routine.execute,zeroed,logical32]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem return_execution (s : X86Memory.State) (f : Option Flags) (dest : Word)
    (outside : dest.toNat<0x34741 ∨ 0x34747≤dest.toNat)
    (ret : load32 s.memory (s.regs 4+20)=dest) :
    X86Routine.run program [dest.toNat] 6 ⟨s,f,0x34741⟩=some (result s f) := by
  change load32 s.memory (s.regs 4+(20#32))=dest at ret
  have h0 : dest.toNat≠0x34741 := by omega
  have h1 : dest.toNat≠0x34742 := by omega
  have h2 : dest.toNat≠0x34743 := by omega
  have h3 : dest.toNat≠0x34744 := by omega
  have h4 : dest.toNat≠0x34745 := by omega
  have h5 : dest.toNat≠0x34746 := by omega
  have run : X86Routine.run listed [dest.toNat] 6 ⟨s,f,0x34741⟩=some (result s f) := by
    simp [h0,Ne.symm h0,h1,Ne.symm h1,h2,Ne.symm h2,h3,Ne.symm h3,h4,Ne.symm h4,h5,Ne.symm h5,
      X86Routine.execute,result,restored,put,write,BitVec.add_assoc,ret]
    funext r
    by_cases h : r=4 <;> simp [write,h]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem stack_frame (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(4#32),8,12,16,20], Apart a (s.regs 4-off)) :
    load32 (stackMemory s) a=load32 s.memory a := by
  simp only [stackMemory,load_store_apart _ _ _ _ (safe 20 (by simp)),
    load_store_apart _ _ _ _ (safe 16 (by simp)),load_store_apart _ _ _ _ (safe 12 (by simp)),
    load_store_apart _ _ _ _ (safe 8 (by simp)),load_store_apart _ _ _ _ (safe 4 (by simp))]

/-- Return executes only reads and register updates. -/
theorem return_memory (s : X86Memory.State) (f : Option Flags) :
    (result s f).core.memory=s.memory := by rfl


/-- Words above the five saved registers survive all pushes, even across wraparound. -/
theorem stack_above (s : X86Memory.State) (off : Word) (member : off∈[(0#32),4,8,12]) :
    load32 (stackMemory s) (s.regs 4+off)=load32 s.memory (s.regs 4+off) := by
  apply stack_frame
  intro k hk
  have h : Apart off (0-k) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member hk
    rcases member with rfl|rfl|rfl|rfl
    all_goals rcases hk with rfl|rfl|rfl|rfl|rfl
    all_goals unfold Apart; decide
  have h := HalfMemory.translate (s.regs 4) off (0-k) 4 4 h
  change Apart (s.regs 4+off) (s.regs 4+(0-k)) at h
  simpa [BitVec.sub_eq_add_neg] using h

theorem saved_slots (s : X86Memory.State) :
    load32 (stackMemory s) (s.regs 4-20)=s.regs 7 ∧
    load32 (stackMemory s) (s.regs 4-16)=s.regs 6 ∧
    load32 (stackMemory s) (s.regs 4-12)=s.regs 2 ∧
    load32 (stackMemory s) (s.regs 4-8)=s.regs 1 ∧
    load32 (stackMemory s) (s.regs 4-4)=s.regs 3 := by
  have h10 : Apart (s.regs 4-16) (s.regs 4-20) := by
    have h := PlayerHeight.slots_apart (s.regs 4-20) 1 0 (by decide)
    change Apart (s.regs 4-20+4) (s.regs 4-20+0) at h
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h
  have h20 : Apart (s.regs 4-12) (s.regs 4-20) := by
    have h := PlayerHeight.slots_apart (s.regs 4-20) 2 0 (by decide)
    change Apart (s.regs 4-20+8) (s.regs 4-20+0) at h
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h
  have h21 : Apart (s.regs 4-12) (s.regs 4-16) := by
    have h := PlayerHeight.slots_apart (s.regs 4-20) 2 1 (by decide)
    change Apart (s.regs 4-20+8) (s.regs 4-20+4) at h
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h
  have h30 : Apart (s.regs 4-8) (s.regs 4-20) := by
    have h := PlayerHeight.slots_apart (s.regs 4-20) 3 0 (by decide)
    change Apart (s.regs 4-20+12) (s.regs 4-20+0) at h
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h
  have h31 : Apart (s.regs 4-8) (s.regs 4-16) := by
    have h := PlayerHeight.slots_apart (s.regs 4-20) 3 1 (by decide)
    change Apart (s.regs 4-20+12) (s.regs 4-20+4) at h
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h
  have h32 : Apart (s.regs 4-8) (s.regs 4-12) := by
    have h := PlayerHeight.slots_apart (s.regs 4-20) 3 2 (by decide)
    change Apart (s.regs 4-20+12) (s.regs 4-20+8) at h
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h
  have h40 : Apart (s.regs 4-4) (s.regs 4-20) := by
    have h := PlayerHeight.slots_apart (s.regs 4-20) 4 0 (by decide)
    change Apart (s.regs 4-20+16) (s.regs 4-20+0) at h
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h
  have h41 : Apart (s.regs 4-4) (s.regs 4-16) := by
    have h := PlayerHeight.slots_apart (s.regs 4-20) 4 1 (by decide)
    change Apart (s.regs 4-20+16) (s.regs 4-20+4) at h
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h
  have h42 : Apart (s.regs 4-4) (s.regs 4-12) := by
    have h := PlayerHeight.slots_apart (s.regs 4-20) 4 2 (by decide)
    change Apart (s.regs 4-20+16) (s.regs 4-20+8) at h
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h
  have h43 : Apart (s.regs 4-4) (s.regs 4-8) := by
    have h := PlayerHeight.slots_apart (s.regs 4-20) 4 3 (by decide)
    change Apart (s.regs 4-20+16) (s.regs 4-20+12) at h
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h
  simp only [stackMemory,load_store_apart _ _ _ _ h10,load_store_apart _ _ _ _ h20,load_store_apart _ _ _ _ h21,load_store_apart _ _ _ _ h30,load_store_apart _ _ _ _ h31,load_store_apart _ _ _ _ h32,load_store_apart _ _ _ _ h40,load_store_apart _ _ _ _ h41,load_store_apart _ _ _ _ h42,load_store_apart _ _ _ _ h43,load_store,and_self]

def returned (s : X86Memory.State) : X86Control.State :=
  ⟨{put (put s 0 0) 4 (s.regs 4+4) with memory:=stackMemory s},
    some (logical32 0),(load32 s.memory (s.regs 4)).toNat⟩

theorem restored_prepared (s : X86Memory.State) :
    result (zeroed (prepared s)).core (zeroed (prepared s)).flags=returned s := by
  obtain ⟨a,b,c,d,e⟩ := saved_slots s
  have ret := stack_above s 0 (by simp)
  simp [result,restored,zeroed,prepared,returned,put,write,
    BitVec.sub_eq_add_neg,BitVec.add_assoc] at a b c d e ret ⊢
  simp [a,b,c,d,e,ret]
  funext r
  by_cases r0 : r=0 <;> by_cases r4 : r=4 <;> by_cases r3 : r=3 <;>
    by_cases r1 : r=1 <;> by_cases r2 : r=2 <;> by_cases r6 : r=6 <;>
    by_cases r7 : r=7 <;> simp_all [write]
end Doom.Proofs.OriginalTextureDash
