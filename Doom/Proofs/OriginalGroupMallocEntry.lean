import Doom.Proofs.OriginalGroupSelected
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalGroupMallocEntry
open Verification X86 X86Memory X86Control BlockSummary
def callBytes : List UInt8 := [0xe8,0x52,0xb0,0x0,0x0]
def entryBytes : List UInt8 := [0x51,0x56,0x57,0x55,0x89,0xc1,0x89,0xd5,0x89,0xdf,0x8b,0x1d,0xe0,0x4f,0x7,0x0,0x8b,0x5b,0x1c,0x8d,0x48,0x3,0x8b,0x43,0x14,0x80,0xe1,0xfc,0x8b,0x50,0x4,0x83,0xc1,0x18,0x85,0xd2,0x75,0x2,0x89,0xc3,0x89,0xda,0x8b,0x73,0x14,0x39,0xf2,0x75,0xe,0x51,0x68,0x28,0x3b,0x2,0x0,0xe8,0x44,0x14,0xfe,0xff,0x83,0xc4,0x8,0x83,0x7a,0x4,0x0,0x74,0x20,0x83,0x7a,0x8,0x64,0x7d,0x7,0x8b,0x52,0x10,0x89,0xd3,0xeb,0x16,0x8d,0x42,0x18,0x8b,0x5b,0x14,0xe8,0x13,0xff,0xff,0xff,0x8b,0x5b,0x10,0x8b,0x53,0x10,0xeb,0x3,0x8b,0x52,0x10]
def bytesProgram (call entry : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2e639≤pc ∧ pc<0x2e63e then X86Routine.decodeAt call (pc-0x2e639)
  else if 0x39690≤pc ∧ pc<0x396f8 then X86Routine.decodeAt entry (pc-0x39690) else none
def program := bytesProgram callBytes entryBytes
def listed : X86Routine.Program
  | 0x2e639 => some (.call (45138),5)
  | 0x39690 => some (.push 1,1)
  | 0x39691 => some (.push 6,1)
  | 0x39692 => some (.push 7,1)
  | 0x39693 => some (.push 5,1)
  | 0x39694 => some (.control (.block (.legacy (.mov 1 0))),2)
  | 0x39696 => some (.control (.block (.legacy (.mov 5 2))),2)
  | 0x39698 => some (.control (.block (.legacy (.mov 7 3))),2)
  | 0x3969a => some (.control (.block (.load 3 ⟨none,none,0,0x74fe0⟩)),6)
  | 0x396a0 => some (.control (.block (.legacy (.load 3 3 28))),3)
  | 0x396a3 => some (.control (.block (.legacy (.lea 1 0 3))),3)
  | 0x396a6 => some (.control (.block (.legacy (.load 0 3 20))),3)
  | 0x396a9 => some (.andByteImmediate 1 0xfc,3)
  | 0x396ac => some (.control (.block (.legacy (.load 2 0 4))),3)
  | 0x396af => some (.addImmediate 1 24,3)
  | 0x396b2 => some (.control (.testWord 2 2),2)
  | 0x396b4 => some (.control (.jumpZero false 2),2)
  | 0x396b6 => some (.control (.block (.legacy (.mov 3 0))),2)
  | 0x396b8 => some (.control (.block (.legacy (.mov 2 3))),2)
  | 0x396ba => some (.control (.block (.legacy (.load 6 3 20))),3)
  | 0x396bd => some (.compareRegisters 2 6,2)
  | 0x396bf => some (.control (.jumpZero false 14),2)
  | 0x396cf => some (.control (.cmpImmediate ⟨some 2,none,0,4⟩ 0),4)
  | 0x396d3 => some (.control (.jumpZero true 32),2)
  | 0x396f5 => some (.control (.block (.legacy (.load 2 2 16))),3)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def called (s : X86Memory.State) := X86Routine.pushWord s 0x2e63e
def saved (s : X86Memory.State) :=
  X86Routine.pushWord (X86Routine.pushWord (X86Routine.pushWord (X86Routine.pushWord s (s.regs 1))
    (s.regs 6)) (s.regs 7)) (s.regs 5)
def rounded (n : Word) := ((n+3) &&& 0xfffffffc)+24
theorem byte_mask (x : Word) : (x &&& 0xffffff00) ||| ((x.extractLsb' 0 8 &&& 0xfc).zeroExtend 32) = x &&& 0xfffffffc := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
@[local simp] theorem byte_mask_normal (x : Word) :
    (x &&& 0xffffff00) ||| (BitVec.setWidth 32 (x.extractLsb' 0 8) &&& 0xfc)=x &&& 0xfffffffc := by
  simpa using byte_mask x
def rover (s : X86Memory.State) := load32 s.memory (load32 s.memory 0x74fe0+28)
def previous (s : X86Memory.State) := load32 s.memory (rover s+20)
def owner (s : X86Memory.State) := load32 s.memory (previous s+4)
def base (s : X86Memory.State) := if owner s=0 then previous s else rover s
def prepared (s : X86Memory.State) : X86Control.State :=
  ⟨put (put (put (put (put (put (put s 5 (s.regs 2)) 7 (s.regs 3)) 1 (rounded (s.regs 0)))
    0 (previous s)) 3 (base s)) 2 (base s)) 6 (load32 s.memory (base s+20)),
    some (logical32 (owner s)),0x396bd⟩
def result (s : X86Memory.State) := prepared (saved s)
def firstFree (s : X86Memory.State) : X86Control.State :=
  ⟨put s 2 (load32 s.memory (s.regs 2+16)),some (compare32 (load32 s.memory (s.regs 2+4)) 0),0x396f8⟩
private theorem one_step (p : X86Routine.Program) (exits : List Nat) (n : Nat)
    (s : X86Control.State) (op : X86Routine.Op) (len : Nat)
    (active : s.pc∉exits) (decode : p s.pc=some (op,len)) :
    X86Routine.run p exits (n+1) s=
      (X86Routine.execute op {s with pc:=s.pc+len}).bind (X86Routine.run p exits n) := by
  rw [X86Routine.run,if_neg active,decode]
  rfl
@[local simp] private theorem step_2e639 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39690] (n+1) ⟨s,f,0x2e639⟩=
      (X86Routine.execute (.call (45138)) ⟨s,f,0x2e63e⟩).bind (X86Routine.run listed [0x39690] n) := by
  exact @one_step listed [0x39690] n ⟨s,f,0x2e639⟩ (.call 45138) 5
    (by change (0x2e639 : Nat)∉[0x39690]; decide)
    (show listed 0x2e639=some (.call 45138,5) from by decide)
@[local simp] private theorem stop_39690 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39690] n ⟨s,f,0x39690⟩=some ⟨s,f,0x39690⟩ := by cases n <;> rfl
@[local simp] private theorem step_39690 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39694] (n+1) ⟨s,f,0x39690⟩=
      (X86Routine.execute (.push 1) ⟨s,f,0x39691⟩).bind (X86Routine.run listed [0x39694] n) := by rfl
@[local simp] private theorem step_39691 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39694] (n+1) ⟨s,f,0x39691⟩=
      (X86Routine.execute (.push 6) ⟨s,f,0x39692⟩).bind (X86Routine.run listed [0x39694] n) := by rfl
@[local simp] private theorem step_39692 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39694] (n+1) ⟨s,f,0x39692⟩=
      (X86Routine.execute (.push 7) ⟨s,f,0x39693⟩).bind (X86Routine.run listed [0x39694] n) := by rfl
@[local simp] private theorem step_39693 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39694] (n+1) ⟨s,f,0x39693⟩=
      (X86Routine.execute (.push 5) ⟨s,f,0x39694⟩).bind (X86Routine.run listed [0x39694] n) := by rfl
@[local simp] private theorem stop_39694 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x39694] n ⟨s,f,0x39694⟩=some ⟨s,f,0x39694⟩ := by cases n <;> rfl
@[local simp] private theorem step_39694 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd] (n+1) ⟨s,f,0x39694⟩=
      (X86Routine.execute (.control (.block (.legacy (.mov 1 0)))) ⟨s,f,0x39696⟩).bind (X86Routine.run listed [0x396bd] n) := by rfl
@[local simp] private theorem step_39696 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd] (n+1) ⟨s,f,0x39696⟩=
      (X86Routine.execute (.control (.block (.legacy (.mov 5 2)))) ⟨s,f,0x39698⟩).bind (X86Routine.run listed [0x396bd] n) := by rfl
@[local simp] private theorem step_39698 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd] (n+1) ⟨s,f,0x39698⟩=
      (X86Routine.execute (.control (.block (.legacy (.mov 7 3)))) ⟨s,f,0x3969a⟩).bind (X86Routine.run listed [0x396bd] n) := by rfl
@[local simp] private theorem step_3969a (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd] (n+1) ⟨s,f,0x3969a⟩=
      (X86Routine.execute (.control (.block (.load 3 ⟨none,none,0,0x74fe0⟩))) ⟨s,f,0x396a0⟩).bind (X86Routine.run listed [0x396bd] n) := by rfl
@[local simp] private theorem step_396a0 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd] (n+1) ⟨s,f,0x396a0⟩=
      (X86Routine.execute (.control (.block (.legacy (.load 3 3 28)))) ⟨s,f,0x396a3⟩).bind (X86Routine.run listed [0x396bd] n) := by rfl
@[local simp] private theorem step_396a3 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd] (n+1) ⟨s,f,0x396a3⟩=
      (X86Routine.execute (.control (.block (.legacy (.lea 1 0 3)))) ⟨s,f,0x396a6⟩).bind (X86Routine.run listed [0x396bd] n) := by rfl
@[local simp] private theorem step_396a6 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd] (n+1) ⟨s,f,0x396a6⟩=
      (X86Routine.execute (.control (.block (.legacy (.load 0 3 20)))) ⟨s,f,0x396a9⟩).bind (X86Routine.run listed [0x396bd] n) := by rfl
@[local simp] private theorem step_396a9 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd] (n+1) ⟨s,f,0x396a9⟩=
      (X86Routine.execute (.andByteImmediate 1 0xfc) ⟨s,f,0x396ac⟩).bind (X86Routine.run listed [0x396bd] n) := by rfl
@[local simp] private theorem step_396ac (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd] (n+1) ⟨s,f,0x396ac⟩=
      (X86Routine.execute (.control (.block (.legacy (.load 2 0 4)))) ⟨s,f,0x396af⟩).bind (X86Routine.run listed [0x396bd] n) := by rfl
@[local simp] private theorem step_396af (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd] (n+1) ⟨s,f,0x396af⟩=
      (X86Routine.execute (.addImmediate 1 24) ⟨s,f,0x396b2⟩).bind (X86Routine.run listed [0x396bd] n) := by rfl
@[local simp] private theorem step_396b2 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd] (n+1) ⟨s,f,0x396b2⟩=
      (X86Routine.execute (.control (.testWord 2 2)) ⟨s,f,0x396b4⟩).bind (X86Routine.run listed [0x396bd] n) := by rfl
@[local simp] private theorem step_396b4 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd] (n+1) ⟨s,f,0x396b4⟩=
      (X86Routine.execute (.control (.jumpZero false 2)) ⟨s,f,0x396b6⟩).bind (X86Routine.run listed [0x396bd] n) := by rfl
@[local simp] private theorem step_396b6 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd] (n+1) ⟨s,f,0x396b6⟩=
      (X86Routine.execute (.control (.block (.legacy (.mov 3 0)))) ⟨s,f,0x396b8⟩).bind (X86Routine.run listed [0x396bd] n) := by rfl
@[local simp] private theorem step_396b8 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd] (n+1) ⟨s,f,0x396b8⟩=
      (X86Routine.execute (.control (.block (.legacy (.mov 2 3)))) ⟨s,f,0x396ba⟩).bind (X86Routine.run listed [0x396bd] n) := by rfl
@[local simp] private theorem step_396ba (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd] (n+1) ⟨s,f,0x396ba⟩=
      (X86Routine.execute (.control (.block (.legacy (.load 6 3 20)))) ⟨s,f,0x396bd⟩).bind (X86Routine.run listed [0x396bd] n) := by rfl
@[local simp] private theorem stop_396bd (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396bd] n ⟨s,f,0x396bd⟩=some ⟨s,f,0x396bd⟩ := by cases n <;> rfl
@[local simp] private theorem step_396bd (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396f8] (n+1) ⟨s,f,0x396bd⟩=
      (X86Routine.execute (.compareRegisters 2 6) ⟨s,f,0x396bf⟩).bind (X86Routine.run listed [0x396f8] n) := by rfl
@[local simp] private theorem step_396bf (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396f8] (n+1) ⟨s,f,0x396bf⟩=
      (X86Routine.execute (.control (.jumpZero false 14)) ⟨s,f,0x396c1⟩).bind (X86Routine.run listed [0x396f8] n) := by rfl
@[local simp] private theorem step_396cf (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396f8] (n+1) ⟨s,f,0x396cf⟩=
      (X86Routine.execute (.control (.cmpImmediate ⟨some 2,none,0,4⟩ 0)) ⟨s,f,0x396d3⟩).bind (X86Routine.run listed [0x396f8] n) := by rfl
@[local simp] private theorem step_396d3 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396f8] (n+1) ⟨s,f,0x396d3⟩=
      (X86Routine.execute (.control (.jumpZero true 32)) ⟨s,f,0x396d5⟩).bind (X86Routine.run listed [0x396f8] n) := by rfl
@[local simp] private theorem step_396f5 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396f8] (n+1) ⟨s,f,0x396f5⟩=
      (X86Routine.execute (.control (.block (.legacy (.load 2 2 16)))) ⟨s,f,0x396f8⟩).bind (X86Routine.run listed [0x396f8] n) := by rfl
@[local simp] private theorem stop_396f8 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x396f8] n ⟨s,f,0x396f8⟩=some ⟨s,f,0x396f8⟩ := by cases n <;> rfl
theorem call_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x39690] 1 ⟨s,f,0x2e639⟩=some ⟨called s,f,0x39690⟩ := by
  have run : X86Routine.run listed [0x39690] 1 ⟨s,f,0x2e639⟩=some ⟨called s,f,0x39690⟩ := by
    simp [X86Routine.execute,called]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]
theorem save_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x39694] 4 ⟨s,f,0x39690⟩=some ⟨saved s,f,0x39694⟩ := by
  have run : X86Routine.run listed [0x39694] 4 ⟨s,f,0x39690⟩=some ⟨saved s,f,0x39694⟩ := by
    simp [X86Routine.execute,saved,X86Routine.pushWord,put,write]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]
theorem prepare_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x396bd] 15 ⟨s,f,0x39694⟩=some (prepared s) := by
  have run : X86Routine.run listed [0x396bd] 15 ⟨s,f,0x39694⟩=some (prepared s) := by
    by_cases free : load32 s.memory (load32 s.memory (load32 s.memory (load32 s.memory (0x74fe0#32)+(28#32))+(20#32))+(4#32))=(0#32)
    all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,putByte,readByte,byteReg,
      prepared,rounded,base,owner,previous,rover,put,write,byte_mask,free,-BitVec.toInt_add]
    all_goals funext r
    all_goals by_cases h0 : r=0 <;> by_cases h1 : r=1 <;> by_cases h2 : r=2 <;>
      by_cases h3 : r=3 <;> simp [write,h0,h1,h2,h3]
    all_goals exact byte_mask_normal (s.regs 0+(3#32))
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem free_execution (s : X86Memory.State) (f : Option Flags)
    (more : s.regs 2≠s.regs 6) (free : load32 s.memory (s.regs 2+(4#32))=(0#32)) :
    X86Routine.run program [0x396f8] 5 ⟨s,f,0x396bd⟩=some (firstFree s) := by
  have run : X86Routine.run listed [0x396f8] 5 ⟨s,f,0x396bd⟩=some (firstFree s) := by
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,firstFree,cmp32_zero,put,write,more,free]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

/-- The save frame is the only memory effect of the prologue. -/
theorem prepared_memory (s : X86Memory.State) : (prepared s).core.memory=s.memory := rfl
theorem saved_register (s : X86Memory.State) (r : Reg) (h : r≠4) : (saved s).regs r=s.regs r := by
  simp [saved,X86Routine.pushWord,write,h]
theorem saved_stack (s : X86Memory.State) : (saved s).regs 4=s.regs 4-16 := by
  simp [saved,X86Routine.pushWord,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]

def SafeWord (a : Word) (s : X86Memory.State) : Prop :=
  ∀ b∈[s.regs 4-4,s.regs 4-8,s.regs 4-12,s.regs 4-16], Apart a b

theorem saved_frame (s : X86Memory.State) (a : Word) (safe : SafeWord a s) :
    load32 (saved s).memory a=load32 s.memory a := by
  simp only [SafeWord,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true] at safe
  simp only [saved,X86Routine.pushWord,write,↓reduceIte]
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc] at safe ⊢
  rw [load_store_apart _ _ _ _ safe.2.2.2,load_store_apart _ _ _ _ safe.2.2.1,
    load_store_apart _ _ _ _ safe.2.1,load_store_apart _ _ _ _ safe.1]

theorem request_e1m1 : rounded 2568=2592 := by decide +kernel
end Doom.Proofs.OriginalGroupMallocEntry
