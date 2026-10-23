import Doom.Proofs.E1M1AimSideStack
import Doom.Proofs.HeapWrites
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalSideCleanup
open Verification X86 X86Memory X86Control BlockSummary
/-- The real cleanup and Z_Free bytes. The initial selected theorem below covers
an owned block with both adjacent blocks occupied; it does not assume a callee
execution, and does not claim this branch is reached by DOS startup. -/
def cleanupBytes : List UInt8 := [0x8b,0x44,0x24,0x4,0xe8,0x1a,0xb1,0x0,0x0,0x83,0xc4,0x8,0x5d,0x5f,0x5e,0x5a,0x59,0x5b,0xc3]
def freeBytes : List UInt8 := [0x53,0x51,0x52,0x8d,0x50,0xe8,0x81,0x7a,0xc,0x11,0x4a,0x1d,0x0,0x74,0xd,0x68,0x0,0x3b,0x2,0x0,0xe8,0xf7,0x14,0xfe,0xff,0x83,0xc4,0x4,0x8b,0x4a,0x4,0x81,0xf9,0x0,0x1,0x0,0x0,0x76,0x6,0xc7,0x1,0x0,0x0,0x0,0x0,0xc7,0x42,0x4,0x0,0x0,0x0,0x0,0xc7,0x42,0x8,0x0,0x0,0x0,0x0,0x8b,0x42,0x14,0xc7,0x42,0xc,0x0,0x0,0x0,0x0,0x83,0x78,0x4,0x0,0x75,0x1d,0x8b,0x1a,0x1,0x18,0x8b,0x5a,0x10,0x89,0x58,0x10,0x89,0x43,0x14,0x8b,0x1d,0xe0,0x4f,0x7,0x0,0x3b,0x53,0x1c,0x75,0x3,0x89,0x43,0x1c,0x89,0xc2,0x8b,0x42,0x10,0x83,0x78,0x4,0x0,0x75,0x1b,0x8b,0x18,0x1,0x1a,0x8b,0x58,0x10,0x89,0x5a,0x10,0x89,0x53,0x14,0x8b,0x1d,0xe0,0x4f,0x7,0x0,0x3b,0x43,0x1c,0x75,0x3,0x89,0x53,0x1c,0x5a,0x59,0x5b,0xc3]
def bytesProgram (cleanup free : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2e4dd≤pc ∧ pc<0x2e4f0 then X86Routine.decodeAt cleanup (pc-0x2e4dd)
  else if 0x39600≤pc ∧ pc<0x39690 then X86Routine.decodeAt free (pc-0x39600) else none
def program := bytesProgram cleanupBytes freeBytes
def listed : X86Routine.Program
  | 0x2e4dd => some (.control (.block (.load 0 ⟨some 4,none,0,4⟩)),4)
  | 0x2e4e1 => some (.call 45338,5)
  | 0x39600 => some (.push 3,1)
  | 0x39601 => some (.push 1,1)
  | 0x39602 => some (.push 2,1)
  | 0x39603 => some (.control (.block (.legacy (.lea 2 0 (-24)))),3)
  | 0x39606 => some (.control (.cmpImmediate ⟨some 2,none,0,12⟩ 0x1d4a11),7)
  | 0x3960d => some (.control (.jumpZero true 13),2)
  | 0x3961c => some (.control (.block (.legacy (.load 1 2 4))),3)
  | 0x3961f => some (.compareRegister 1 256,6)
  | 0x39625 => some (.jumpUnsigned 1 6,2)
  | 0x39627 => some (.storeImmediate ⟨some 1,none,0,0⟩ 0,6)
  | 0x3962d => some (.storeImmediate ⟨some 2,none,0,4⟩ 0,7)
  | 0x39634 => some (.storeImmediate ⟨some 2,none,0,8⟩ 0,7)
  | 0x3963b => some (.control (.block (.legacy (.load 0 2 20))),3)
  | 0x3963e => some (.storeImmediate ⟨some 2,none,0,12⟩ 0,7)
  | 0x39645 => some (.control (.cmpImmediate ⟨some 0,none,0,4⟩ 0),4)
  | 0x39649 => some (.control (.jumpZero false 29),2)
  | 0x39668 => some (.control (.block (.legacy (.load 0 2 16))),3)
  | 0x3966b => some (.control (.cmpImmediate ⟨some 0,none,0,4⟩ 0),4)
  | 0x3966f => some (.control (.jumpZero false 27),2)
  | 0x3968c => some (.pop 2,1)
  | 0x3968d => some (.pop 1,1)
  | 0x3968e => some (.pop 3,1)
  | 0x3968f => some (.ret,1)
  | 0x2e4e6 => some (.addImmediate 4 8,3)
  | 0x2e4e9 => some (.pop 5,1)
  | 0x2e4ea => some (.pop 7,1)
  | 0x2e4eb => some (.pop 6,1)
  | 0x2e4ec => some (.pop 2,1)
  | 0x2e4ed => some (.pop 1,1)
  | 0x2e4ee => some (.pop 3,1)
  | 0x2e4ef => some (.ret,1)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def raw (s : X86Memory.State) := load32 s.memory (s.regs 4+4)
def block (s : X86Memory.State) := raw s-24
def saved (s : X86Memory.State) :=
  X86Routine.pushWord (X86Routine.pushWord (X86Routine.pushWord
    (X86Routine.pushWord (put s 0 (raw s)) 0x2e4e6) (s.regs 3)) (s.regs 1)) (s.regs 2)
def owner (s : X86Memory.State) := load32 (saved s).memory (block s+4)
def firstMemory (s : X86Memory.State) :=
  store32 (store32 (store32 (saved s).memory (owner s) 0) (block s+4) 0) (block s+8) 0
def prev (s : X86Memory.State) := load32 (firstMemory s) (block s+20)
def cleared (s : X86Memory.State) := store32 (firstMemory s) (block s+12) 0
def next (s : X86Memory.State) := load32 (cleared s) (block s+16)
def writes (s : X86Memory.State) : List (Word × Word) :=
  [(owner s,0),(block s+4,0),(block s+8,0),(block s+12,0)]
structure Ready (s : X86Memory.State) : Prop where
  valid : load32 (saved s).memory (block s+12)=0x1d4a11
  owned : 256<(owner s).toNat
  prevBusy : load32 (cleared s) (prev s+4)≠0
  nextBusy : load32 (cleared s) (next s+4)≠0
  returnSafe : ∀ w∈writes s, Apart (s.regs 4-4) w.1

def popCore (r : Reg) (s : X86Memory.State) :=
  put (put s 4 (s.regs 4+4)) r (load32 s.memory (s.regs 4))
def opened (s : X86Memory.State) : X86Control.State :=
  ⟨put (saved s) 2 (block s),some (compare32 (load32 (saved s).memory (block s+12)) 0x1d4a11),0x3961c⟩
def ownedState (s : X86Memory.State) : X86Control.State :=
  let user := load32 s.memory (s.regs 2+4)
  ⟨{put s 1 user with memory:=store32 s.memory user 0},some (compare32 user 256),0x3962d⟩
def clearState (s : X86Memory.State) : X86Control.State :=
  let m := store32 (store32 s.memory (s.regs 2+4) 0) (s.regs 2+8) 0
  let p := load32 m (s.regs 2+20)
  let m := store32 m (s.regs 2+12) 0
  ⟨{put s 0 p with memory:=m},some (compare32 (load32 m (p+4)) 0),0x39668⟩
def nextState (s : X86Memory.State) : X86Control.State :=
  let p := load32 s.memory (s.regs 2+16)
  ⟨put s 0 p,some (compare32 (load32 s.memory (p+4)) 0),0x3968c⟩
def popped (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  let t := popCore 3 (popCore 1 (popCore 2 s))
  ⟨put t 4 (t.regs 4+4),f,(load32 t.memory (t.regs 4)).toNat⟩
def beforeReturn (s : X86Memory.State) := nextState (clearState (ownedState (opened s).core).core).core
def returned (s : X86Memory.State) := popped (beforeReturn s).core (beforeReturn s).flags
def restored (s : X86Memory.State) : X86Memory.State :=
  put (popCore 3 (popCore 1 (popCore 2 (popCore 6 (popCore 7 (popCore 5
    (put s 4 (s.regs 4+8)))))))) 4 (s.regs 4+36)
def tail (s : X86Memory.State) : X86Control.State :=
  ⟨restored s,none,(load32 s.memory (s.regs 4+32)).toNat⟩
def result (s : X86Memory.State) := tail (returned s).core

theorem return_slot (s : X86Memory.State) (h : Ready s) :
    load32 (cleared s) (s.regs 4-4)=0x2e4e6 := by
  have frame := HeapWrites.frame (writes s) (saved s).memory (s.regs 4-4) h.returnSafe
  have a : Apart (s.regs 4-4) (s.regs 4-8) := by
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using PlayerHeight.slots_apart (s.regs 4-8) 1 0 (by decide)
  have b : Apart (s.regs 4-4) (s.regs 4-12) := by
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using PlayerHeight.slots_apart (s.regs 4-12) 2 0 (by decide)
  have c : Apart (s.regs 4-4) (s.regs 4-16) := by
    have h := PlayerHeight.slots_apart (s.regs 4-16) 3 0 (by decide)
    change Apart ((s.regs 4-16)+12) ((s.regs 4-16)+0) at h
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h
  change load32 (cleared s) (s.regs 4-4)=load32 (saved s).memory (s.regs 4-4) at frame
  rw [frame]
  have mem : (saved s).memory=store32 (store32 (store32 (store32 s.memory (s.regs 4-4) 0x2e4e6) (s.regs 4-8) (s.regs 3)) (s.regs 4-12) (s.regs 1)) (s.regs 4-16) (s.regs 2) := by
    simp [saved,X86Routine.pushWord,put,write,BitVec.sub_sub]
  rw [mem,load_store_apart _ _ _ _ c,load_store_apart _ _ _ _ b,load_store_apart _ _ _ _ a,load_store]
private theorem one_step (p : X86Routine.Program) (exits : List Nat) (n : Nat)
    (s : X86Control.State) (op : X86Routine.Op) (len : Nat)
    (active : s.pc∉exits) (decode : p s.pc=some (op,len)) :
    X86Routine.run p exits (n+1) s=
      (X86Routine.execute op {s with pc:=s.pc+len}).bind (X86Routine.run p exits n) := by
  rw [X86Routine.run,if_neg active,decode]
  rfl
@[local simp] private theorem step_2e4dd (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x2e4dd∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x2e4dd⟩ =
      (X86Routine.execute (.control (.block (.load 0 ⟨some 4,none,0,4⟩))) ⟨s,f,0x2e4e1⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x2e4dd⟩ (.control (.block (.load 0 ⟨some 4,none,0,4⟩))) 4 active rfl
@[local simp] private theorem step_2e4e1 (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x2e4e1∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x2e4e1⟩ =
      (X86Routine.execute (.call 45338) ⟨s,f,0x2e4e6⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x2e4e1⟩ (.call 45338) 5 active rfl
@[local simp] private theorem step_39600 (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x39600∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x39600⟩ =
      (X86Routine.execute (.push 3) ⟨s,f,0x39601⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x39600⟩ (.push 3) 1 active rfl
@[local simp] private theorem step_39601 (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x39601∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x39601⟩ =
      (X86Routine.execute (.push 1) ⟨s,f,0x39602⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x39601⟩ (.push 1) 1 active rfl
@[local simp] private theorem step_39602 (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x39602∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x39602⟩ =
      (X86Routine.execute (.push 2) ⟨s,f,0x39603⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x39602⟩ (.push 2) 1 active rfl
@[local simp] private theorem step_39603 (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x39603∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x39603⟩ =
      (X86Routine.execute (.control (.block (.legacy (.lea 2 0 (-24))))) ⟨s,f,0x39606⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x39603⟩ (.control (.block (.legacy (.lea 2 0 (-24))))) 3 active rfl
@[local simp] private theorem step_39606 (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x39606∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x39606⟩ =
      (X86Routine.execute (.control (.cmpImmediate ⟨some 2,none,0,12⟩ 0x1d4a11)) ⟨s,f,0x3960d⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x39606⟩ (.control (.cmpImmediate ⟨some 2,none,0,12⟩ 0x1d4a11)) 7 active rfl
@[local simp] private theorem step_3960d (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x3960d∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x3960d⟩ =
      (X86Routine.execute (.control (.jumpZero true 13)) ⟨s,f,0x3960f⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x3960d⟩ (.control (.jumpZero true 13)) 2 active rfl
@[local simp] private theorem step_3961c (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x3961c∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x3961c⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 1 2 4)))) ⟨s,f,0x3961f⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x3961c⟩ (.control (.block (.legacy (.load 1 2 4)))) 3 active rfl
@[local simp] private theorem step_3961f (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x3961f∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x3961f⟩ =
      (X86Routine.execute (.compareRegister 1 256) ⟨s,f,0x39625⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x3961f⟩ (.compareRegister 1 256) 6 active rfl
@[local simp] private theorem step_39625 (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x39625∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x39625⟩ =
      (X86Routine.execute (.jumpUnsigned 1 6) ⟨s,f,0x39627⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x39625⟩ (.jumpUnsigned 1 6) 2 active rfl
@[local simp] private theorem step_39627 (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x39627∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x39627⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 1,none,0,0⟩ 0) ⟨s,f,0x3962d⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x39627⟩ (.storeImmediate ⟨some 1,none,0,0⟩ 0) 6 active rfl
@[local simp] private theorem step_3962d (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x3962d∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x3962d⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 2,none,0,4⟩ 0) ⟨s,f,0x39634⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x3962d⟩ (.storeImmediate ⟨some 2,none,0,4⟩ 0) 7 active rfl
@[local simp] private theorem step_39634 (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x39634∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x39634⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 2,none,0,8⟩ 0) ⟨s,f,0x3963b⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x39634⟩ (.storeImmediate ⟨some 2,none,0,8⟩ 0) 7 active rfl
@[local simp] private theorem step_3963b (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x3963b∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x3963b⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 2 20)))) ⟨s,f,0x3963e⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x3963b⟩ (.control (.block (.legacy (.load 0 2 20)))) 3 active rfl
@[local simp] private theorem step_3963e (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x3963e∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x3963e⟩ =
      (X86Routine.execute (.storeImmediate ⟨some 2,none,0,12⟩ 0) ⟨s,f,0x39645⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x3963e⟩ (.storeImmediate ⟨some 2,none,0,12⟩ 0) 7 active rfl
@[local simp] private theorem step_39645 (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x39645∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x39645⟩ =
      (X86Routine.execute (.control (.cmpImmediate ⟨some 0,none,0,4⟩ 0)) ⟨s,f,0x39649⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x39645⟩ (.control (.cmpImmediate ⟨some 0,none,0,4⟩ 0)) 4 active rfl
@[local simp] private theorem step_39649 (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x39649∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x39649⟩ =
      (X86Routine.execute (.control (.jumpZero false 29)) ⟨s,f,0x3964b⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x39649⟩ (.control (.jumpZero false 29)) 2 active rfl
@[local simp] private theorem step_39668 (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x39668∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x39668⟩ =
      (X86Routine.execute (.control (.block (.legacy (.load 0 2 16)))) ⟨s,f,0x3966b⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x39668⟩ (.control (.block (.legacy (.load 0 2 16)))) 3 active rfl
@[local simp] private theorem step_3966b (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x3966b∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x3966b⟩ =
      (X86Routine.execute (.control (.cmpImmediate ⟨some 0,none,0,4⟩ 0)) ⟨s,f,0x3966f⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x3966b⟩ (.control (.cmpImmediate ⟨some 0,none,0,4⟩ 0)) 4 active rfl
@[local simp] private theorem step_3966f (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x3966f∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x3966f⟩ =
      (X86Routine.execute (.control (.jumpZero false 27)) ⟨s,f,0x39671⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x3966f⟩ (.control (.jumpZero false 27)) 2 active rfl
@[local simp] private theorem step_3968c (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x3968c∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x3968c⟩ =
      (X86Routine.execute (.pop 2) ⟨s,f,0x3968d⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x3968c⟩ (.pop 2) 1 active rfl
@[local simp] private theorem step_3968d (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x3968d∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x3968d⟩ =
      (X86Routine.execute (.pop 1) ⟨s,f,0x3968e⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x3968d⟩ (.pop 1) 1 active rfl
@[local simp] private theorem step_3968e (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x3968e∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x3968e⟩ =
      (X86Routine.execute (.pop 3) ⟨s,f,0x3968f⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x3968e⟩ (.pop 3) 1 active rfl
@[local simp] private theorem step_3968f (s : X86Memory.State) (f : Option Flags) (n : Nat)
    (exits : List Nat) (active : 0x3968f∉exits) :
    X86Routine.run listed exits (n+1) ⟨s,f,0x3968f⟩ =
      (X86Routine.execute (.ret) ⟨s,f,0x39690⟩).bind (X86Routine.run listed exits n) := by
  exact @one_step listed exits n ⟨s,f,0x3968f⟩ (.ret) 1 active rfl
@[local simp] private theorem stopped (s : X86Memory.State) (f : Option Flags) (n pc : Nat)
    (exits : List Nat) (active : pc∈exits) :
    X86Routine.run listed exits n ⟨s,f,pc⟩=some ⟨s,f,pc⟩ := by cases n <;> simp [X86Routine.run,active]

private theorem append {p exits n m s t u} (a : X86Routine.Prefix p exits n s t)
    (b : X86Routine.Prefix p exits m t u) : X86Routine.Prefix p exits (n+m) s u := by
  induction a with
  | nil => simpa using b
  | step active dec exe rest ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using X86Routine.Prefix.step active dec exe (ih b)
private theorem lift {exits n s t} (run : X86Routine.run listed exits n s=some t) :
    ∃ k≤n, X86Routine.Prefix program [] k s t := by
  obtain ⟨k,hk,path,_⟩ := X86Routine.run_path run
  exact ⟨k,hk,path.transfer program [] decoded (by simp)⟩
@[local simp] private theorem compare_carry (a b : Word) : (compare32 a b).carry=some (a.ult b) := rfl

theorem open_execution (s : X86Memory.State) (f : Option Flags)
    (valid : load32 (saved s).memory (block s+12)=0x1d4a11) :
    ∃ k≤8, X86Routine.Prefix program [] k ⟨s,f,0x2e4dd⟩ (opened s) := by
  have path : X86Routine.Prefix listed [] 8 ⟨s,f,0x2e4dd⟩ (opened s) := by
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=⟨X86Routine.pushWord (put s 0 (raw s)) 0x2e4e6,f,0x39600⟩) (by simp) rfl (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,blockPreservesFlags,raw,put,write,X86Block.Address.eval]) ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=opened s) (by simp) rfl ?_ (.nil _)
    simp [saved,block,raw,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc] at valid
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,opened,saved,block,raw,
      X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,cmp32_zero,valid]
  exact ⟨8,by decide,path.transfer program [] decoded (by simp)⟩

theorem owner_execution (s : X86Memory.State) (f : Option Flags)
    (owned : 256<(load32 s.memory (s.regs 2+4)).toNat) :
    ∃ k≤4, X86Routine.Prefix program [] k ⟨s,f,0x3961c⟩ (ownedState s) := by
  have less : (load32 s.memory (s.regs 2+4)).ult (256#32)=false := by
    simp only [BitVec.ult,decide_eq_false_iff_not]; change ¬(load32 s.memory (s.regs 2+4)).toNat<256; omega
  have neq : load32 s.memory (s.regs 2+4)≠(256#32) := by intro eq; rw [eq] at owned; contradiction
  change (load32 s.memory (s.regs 2+(4#32))).ult (256#32)=false at less
  change load32 s.memory (s.regs 2+(4#32))≠(256#32) at neq
  apply lift (exits:=[0x3962d])
  simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
    X86Block.Address.eval,X86.execute,blockPreservesFlags,ownedState,put,write,
    cmp32_zero,compare_carry,less,neq]

theorem clear_execution (s : X86Memory.State) (f : Option Flags)
    (busy : load32 (clearState s).core.memory ((clearState s).core.regs 0+4)≠0) :
    ∃ k≤6, X86Routine.Prefix program [] k ⟨s,f,0x3962d⟩ (clearState s) := by
  apply lift (exits:=[0x39668])
  simp [clearState,put,write] at busy
  simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
    X86Block.Address.eval,X86.execute,blockPreservesFlags,clearState,put,write,cmp32_zero,busy]

theorem next_execution (s : X86Memory.State) (f : Option Flags)
    (busy : load32 s.memory (load32 s.memory (s.regs 2+16)+4)≠0) :
    ∃ k≤3, X86Routine.Prefix program [] k ⟨s,f,0x39668⟩ (nextState s) := by
  change load32 s.memory (load32 s.memory (s.regs 2+(16#32))+(4#32))≠(0#32) at busy
  apply lift (exits:=[0x3968c])
  simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
    X86Block.Address.eval,X86.execute,blockPreservesFlags,nextState,put,write,cmp32_zero,busy]

theorem pop_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 4 ⟨s,f,0x3968c⟩ (popped s f) := by
  have path : X86Routine.Prefix listed [] 4 ⟨s,f,0x3968c⟩ (popped s f) := by
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    exact .nil _
  exact path.transfer program [] decoded (by simp)

theorem return_properties (s : X86Memory.State) (h : Ready s) :
    (returned s).pc=0x2e4e6 ∧ (returned s).core.regs 4=s.regs 4 ∧
      (returned s).core.memory=cleared s := by
  have ret := return_slot s h
  simp [returned,beforeReturn,popped,popCore,nextState,clearState,ownedState,opened,saved,
    X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,
    cleared,firstMemory,block,owner,raw] at ret ⊢
  exact congrArg BitVec.toNat ret

theorem free_execution (s : X86Memory.State) (f : Option Flags) (h : Ready s) :
    ∃ k≤25, X86Routine.Prefix program [] k ⟨s,f,0x2e4dd⟩ (returned s) := by
  obtain ⟨a,ha,pa⟩ := open_execution s f h.valid
  obtain ⟨b,hb,pb⟩ := owner_execution (opened s).core (opened s).flags (by
    simpa [opened,put,write,owner] using h.owned)
  obtain ⟨c,hc,pc⟩ := clear_execution (ownedState (opened s).core).core (ownedState (opened s).core).flags (by
    simpa [clearState,ownedState,opened,cleared,firstMemory,prev,owner,put,write] using h.prevBusy)
  obtain ⟨d,hd,pd⟩ := next_execution (clearState (ownedState (opened s).core).core).core
    (clearState (ownedState (opened s).core).core).flags (by
      simpa [clearState,ownedState,opened,cleared,firstMemory,next,owner,put,write] using h.nextBusy)
  have pe := pop_execution (beforeReturn s).core (beforeReturn s).flags
  exact ⟨a+b+c+d+4,by omega,append (append (append (append pa pb) pc) pd) pe⟩

theorem tail_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 8 ⟨s,f,0x2e4e6⟩ (tail s) := by
  have path : X86Routine.Prefix listed [] 8 ⟨s,f,0x2e4e6⟩ (tail s) := by
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    simpa [tail,restored,popCore,X86Routine.execute,put,write,BitVec.add_assoc] using X86Routine.Prefix.nil (program:=listed) (exits:=[]) (tail s)
  exact path.transfer program [] decoded (by simp)

theorem execution (s : X86Memory.State) (f : Option Flags) (h : Ready s) :
    ∃ k≤40, X86Routine.Prefix program [] k ⟨s,f,0x2e4dd⟩ (result s) := by
  obtain ⟨n,hn,path⟩ := free_execution s f h
  have tailPath := tail_execution (returned s).core (returned s).flags
  have seam : (⟨(returned s).core,(returned s).flags,0x2e4e6⟩ : X86Control.State)=returned s := by
    rw [←(return_properties s h).1]
  rw [seam] at tailPath
  exact ⟨n+8,by omega,append path tailPath⟩
end Doom.Proofs.OriginalSideCleanup
