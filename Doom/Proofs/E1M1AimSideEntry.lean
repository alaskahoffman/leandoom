import Doom.Proofs.E1M1AimSideCleanup
import Doom.Verification.X86StartupRoutine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimSideEntry
open Verification X86 X86Memory X86Control BlockSummary
open X86StartupRoutine (Prefix)
/-! Starts at the actual P_LoadSideDefs entry, not a reached helper state.
The lump-directory image is an explicit boundary assumption; no heap allocation
or filesystem success is asserted by reaching the allocation request. -/
def entryBytes : List UInt8 := [0x53,0x51,0x52,0x56,0x57,0x55,0x83,0xec,0x8,0x89,0xc1,0xbb,0x1e,0x0,0x0,0x0,0x31,0xd2,0xe8,0xb9,0xa7,0x0,0x0,0xf7,0xf3,0xa3,0x1c,0xc1,0x2,0x0,0x8d,0x14,0xc5,0x0,0x0,0x0,0x0,0x31,0xdb,0x1,0xd0,0xba,0x32,0x0,0x0,0x0,0x1,0xc0,0xe8,0x7b,0xb2,0x0,0x0,0x89,0xc3,0xa3,0x18,0xc1,0x2,0x0,0xa1,0x1c,0xc1,0x2,0x0,0x8d,0x34,0xc5,0x0,0x0,0x0,0x0,0x1,0xc6,0x31,0xd2,0x1,0xf6,0x89,0xd8,0x89,0xf3,0xe8,0x39,0x1a,0x1,0x0,0xba,0x1,0x0,0x0,0x0,0x89,0xc8,0x31,0xed,0xe8,0xbb,0xa8,0x0,0x0]
def lengthBytes : List UInt8 := [0x52,0x89,0xc2,0x3b,0x5,0xa0,0x4f,0x7,0x0,0x7c,0xe,0x50,0x68,0xdc,0x39,0x2,0x0,0xe8,0x4a,0x1f,0xfe,0xff,0x83,0xc4,0x8,0x8d,0x4,0x95,0x0,0x0,0x0,0x0,0x1,0xc2,0xa1,0xa4,0x4f,0x7,0x0,0x8d,0x14,0x95,0x0,0x0,0x0,0x0,0x8b,0x44,0x2,0x10,0x5a,0xc3]
def bytesProgram (entry length : List UInt8) : X86StartupRoutine.Program := fun pc =>
  if 0x2e3e0≤pc ∧ pc<0x2e445 then X86StartupRoutine.decodeAt entry (pc-0x2e3e0)
  else if 0x38bb0≤pc ∧ pc<0x38be4 then X86StartupRoutine.decodeAt length (pc-0x38bb0)
  else none
def program := bytesProgram entryBytes lengthBytes
def listed : X86StartupRoutine.Program
  | 0x2e3e0 => some (.base (.base (.push 3)),1)
  | 0x2e3e1 => some (.base (.base (.push 1)),1)
  | 0x2e3e2 => some (.base (.base (.push 2)),1)
  | 0x2e3e3 => some (.base (.base (.push 6)),1)
  | 0x2e3e4 => some (.base (.base (.push 7)),1)
  | 0x2e3e5 => some (.base (.base (.push 5)),1)
  | 0x2e3e6 => some (.base (.base (.addImmediate 4 (-8))),3)
  | 0x2e3e9 => some (.base (.base (.control (.block (.legacy (.mov 1 0))))),2)
  | 0x2e3eb => some (.base (.base (.immediate 3 30)),5)
  | 0x2e3f0 => some (.base (.base (.xorRegister 2 2)),2)
  | 0x2e3f2 => some (.base (.base (.call 42937)),5)
  | 0x2e3f7 => some (.unsignedDivide 3,2)
  | 0x2e3f9 => some (.base (.base (.control (.storeEax 0x2c11c))),5)
  | 0x2e3fe => some (.base (.base (.control (.block (.lea 2 ⟨none,some 0,3,0⟩)))),7)
  | 0x2e405 => some (.base (.base (.xorRegister 3 3)),2)
  | 0x2e407 => some (.base (.base (.control (.block (.arithmetic (.add 0 2))))),2)
  | 0x2e409 => some (.base (.base (.immediate 2 50)),5)
  | 0x2e40e => some (.base (.base (.control (.block (.arithmetic (.add 0 0))))),2)
  | 0x2e410 => some (.base (.base (.call 45691)),5)
  | 0x38bb0 => some (.base (.base (.push 2)),1)
  | 0x38bb1 => some (.base (.base (.control (.block (.legacy (.mov 2 0))))),2)
  | 0x38bb3 => some (.base (.base (.control (.cmpMemory 0 ⟨none,none,0,0x74fa0⟩))),6)
  | 0x38bb9 => some (.base (.base (.jumpSigned 3 14)),2)
  | 0x38bc9 => some (.base (.base (.control (.block (.lea 0 ⟨none,some 2,2,0⟩)))),7)
  | 0x38bd0 => some (.base (.base (.control (.block (.arithmetic (.add 2 0))))),2)
  | 0x38bd2 => some (.base (.base (.control (.block (.load 0 ⟨none,none,0,0x74fa4⟩)))),5)
  | 0x38bd7 => some (.base (.base (.control (.block (.lea 2 ⟨none,some 2,2,0⟩)))),7)
  | 0x38bde => some (.base (.base (.control (.block (.load 0 ⟨some 2,some 0,0,16⟩)))),4)
  | 0x38be2 => some (.base (.base (.pop 2)),1)
  | 0x38be3 => some (.base (.base (.ret)),1)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def saves (s : X86Memory.State) : List (Word × Word) :=
  [(s.regs 4-4,s.regs 3),(s.regs 4-8,s.regs 1),(s.regs 4-12,s.regs 2),
   (s.regs 4-16,s.regs 6),(s.regs 4-20,s.regs 7),(s.regs 4-24,s.regs 5),
   (s.regs 4-36,0x2e3f7),(s.regs 4-40,0)]
def savedMemory (s : X86Memory.State) := HeapWrites.apply (saves s) s.memory
def called (s : X86Memory.State) : X86Memory.State :=
  let t := X86Routine.pushWord (X86Routine.pushWord (X86Routine.pushWord
    (X86Routine.pushWord (X86Routine.pushWord (X86Routine.pushWord s (s.regs 3))
      (s.regs 1)) (s.regs 2)) (s.regs 6)) (s.regs 7)) (s.regs 5)
  X86Routine.pushWord (put (put (put (put t 4 (t.regs 4-8)) 1 (s.regs 0)) 3 30) 2 0) 0x2e3f7
def lengthOpen (s : X86Memory.State) : X86Control.State :=
  ⟨put (X86Routine.pushWord (called s) 0) 2 9,some (compare32 9 1264),0x38bc9⟩
def measured (s : X86Memory.State) : X86Control.State :=
  ⟨put (put (put (X86Routine.pushWord (called s) 0) 4 ((X86Routine.pushWord (called s) 0).regs 4+8)) 0 19440) 2 0,
    none,0x2e3f7⟩
def request (s : X86Memory.State) : X86Control.State :=
  ⟨X86Routine.pushWord
    (put (put (put {(measured s).core with memory:=store32 (measured s).core.memory 0x2c11c 648}
      0 11664) 2 50) 3 0) 0x2e415,none,0x39690⟩
def Safe (s : X86Memory.State) (a : Word) : Prop := ∀ w∈saves s, Apart a w.1
structure Initial (s : X86Memory.State) (table : Word) : Prop where
  index : s.regs 0=9
  count : load32 s.memory 0x74fa0=1264
  tablePointer : load32 s.memory 0x74fa4=table
  length : load32 s.memory (180+table+16)=19440
  countSafe : Safe s 0x74fa0
  tableSafe : Safe s 0x74fa4
  lengthSafe : Safe s (180+table+16)
  countReturn : Apart 0x2c11c (s.regs 4-36)

theorem saved_memory (s : X86Memory.State) :
    (X86Routine.pushWord (called s) 0).memory=savedMemory s := by
  simp [called,savedMemory,saves,HeapWrites.apply,X86Routine.pushWord,put,write,
    BitVec.sub_eq_add_neg,BitVec.add_assoc]
theorem saved_frame (s : X86Memory.State) (a : Word) (h : Safe s a) :
    load32 (savedMemory s) a=load32 s.memory a := by
  exact HeapWrites.frame _ _ _ h

theorem call_execution (s : X86Memory.State) (f : Option Flags) :
    Prefix program [] 11 ⟨s,f,0x2e3e0⟩ ⟨called s,some ⟨true,false,false,some false⟩,0x38bb0⟩ := by
  have path : Prefix listed [] 11 ⟨s,f,0x2e3e0⟩ ⟨called s,some ⟨true,false,false,some false⟩,0x38bb0⟩ := by
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=⟨called s,some ⟨true,false,false,some false⟩,0x38bb0⟩) (by simp) rfl ?_ (.nil _)
    simp [X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,
      X86Control.execute,X86Block.execute,X86Memory.execute,blockPreservesFlags,
      called,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,logical32]
  exact path.transfer program [] decoded (by simp)

theorem length_open_execution (s : X86Memory.State) (table : Word) (h : Initial s table) :
    Prefix program [] 4 ⟨called s,some ⟨true,false,false,some false⟩,0x38bb0⟩ (lengthOpen s) := by
  have index : (called s).regs 0=9 := by
    simp [called,X86Routine.pushWord,put,write,h.index]
  have edx : (called s).regs 2=0 := by
    simp [called,X86Routine.pushWord,put,write]
  have count : load32 (X86Routine.pushWord (called s) 0).memory 0x74fa0=1264 := by
    rw [saved_memory]; exact (saved_frame s _ h.countSafe).trans h.count
  generalize hc : called s = c at index edx count ⊢
  have path : Prefix listed [] 4 ⟨c,some ⟨true,false,false,some false⟩,0x38bb0⟩ (lengthOpen s) := by
    refine .step (middle:=⟨X86Routine.pushWord c 0,some ⟨true,false,false,some false⟩,0x38bb1⟩) (by simp) rfl ?_ ?_
    · simp [X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,edx]
    refine .step (middle:=⟨put (X86Routine.pushWord c 0) 2 9,some ⟨true,false,false,some false⟩,0x38bb3⟩) (by simp) rfl ?_ ?_
    · simp [X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,
        X86Control.execute,X86Block.execute,X86Memory.execute,blockPreservesFlags,
        X86Routine.pushWord,put,write,index]
    refine .step (middle:=⟨put (X86Routine.pushWord c 0) 2 9,some (compare32 9 1264),0x38bb9⟩) (by simp) rfl ?_ ?_
    · change (some ⟨put (X86Routine.pushWord c 0) 2 9,
        some (compare32 ((X86Routine.pushWord c 0).regs 0) (load32 (X86Routine.pushWord c 0).memory 0x74fa0)),0x38bb9⟩ : Option X86Control.State)=_
      rw [count]; simp [X86Routine.pushWord,put,write,index]
    refine .step (middle:=lengthOpen s) (by simp) rfl ?_ (.nil _)
    rw [lengthOpen,hc]
    rfl
  exact path.transfer program [] decoded (by simp)

theorem length_execution (s : X86Memory.State) (table : Word) (h : Initial s table) :
    Prefix program [] 7 (lengthOpen s) (measured s) := by
  have tp := (saved_frame s _ h.tableSafe).trans h.tablePointer
  have len := (saved_frame s _ h.lengthSafe).trans h.length
  have ret : load32 (savedMemory s) (s.regs 4-36)=0x2e3f7 := by
    have sep : Apart (s.regs 4-36) (s.regs 4-40) := by
      simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using
        PlayerHeight.slots_apart (s.regs 4-40) 1 0 (by decide)
    change Apart (s.regs 4-(36#32)) (s.regs 4-(40#32)) at sep
    simp only [savedMemory,saves,HeapWrites.apply,List.foldl]
    exact (load_store_apart _ _ _ _ sep).trans (load_store _ _ _)
  have zero : load32 (savedMemory s) (s.regs 4-40)=0 := by
    exact load_store _ _ _
  have sp : (X86Routine.pushWord (called s) 0).regs 4=s.regs 4-40 := by
    simp [called,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rw [←saved_memory] at tp len ret zero
  rw [←sp] at zero
  have ret' : load32 (X86Routine.pushWord (called s) 0).memory
      ((X86Routine.pushWord (called s) 0).regs 4+4)=0x2e3f7 := by
    have addr : (X86Routine.pushWord (called s) 0).regs 4+4=s.regs 4-36 := by
      simp [called,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rw [addr]; exact ret
  unfold lengthOpen measured
  generalize hp : X86Routine.pushWord (called s) 0 = p at tp len zero ret' ⊢
  simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc] at tp len zero ret'
  have path : Prefix listed [] 7 ⟨put p 2 9,some (compare32 9 1264),0x38bc9⟩
      ⟨put (put (put p 4 (p.regs 4+8)) 0 19440) 2 0,none,0x2e3f7⟩ := by
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=⟨put (put (put p 4 (p.regs 4+8)) 0 19440) 2 0,none,0x2e3f7⟩) (by simp) rfl ?_ (.nil _)
    simp [X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,
      X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,
      X86.execute,blockPreservesFlags,put,write,tp,len,zero,ret',BitVec.add_assoc]
    funext r
    by_cases a : r=0 <;> by_cases b : r=2 <;> by_cases c : r=4 <;> simp [write,a,b,c]
  exact path.transfer program [] decoded (by simp)

theorem request_execution (s : X86Memory.State) :
    Prefix program [] 8 (measured s) (request s) := by
  have eax : (measured s).core.regs 0=19440 := rfl
  have edx : (measured s).core.regs 2=0 := rfl
  have ebx : (measured s).core.regs 3=30 := by simp [measured,called,X86Routine.pushWord,put,write]
  unfold request
  change Prefix program [] 8 ⟨(measured s).core,none,0x2e3f7⟩ _
  generalize hm : (measured s).core=m at eax edx ebx ⊢
  have path : Prefix listed [] 8 ⟨m,none,0x2e3f7⟩
      ⟨X86Routine.pushWord (put (put (put {m with memory:=store32 m.memory 0x2c11c 648}
        0 11664) 2 50) 3 0) 0x2e415,none,0x39690⟩ := by
    refine .step (middle:=⟨put (put m 0 648) 2 0,none,0x2e3f9⟩) (by simp) rfl ?_ ?_
    · simp [X86StartupRoutine.execute,eax,edx,ebx]
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=⟨X86Routine.pushWord (put (put (put {m with memory:=store32 m.memory 0x2c11c 648}
        0 11664) 2 50) 3 0) 0x2e415,none,0x39690⟩) (by simp) rfl ?_ (.nil _)
    simp [X86StartupRoutine.execute,X86ByteRoutine.execute,X86Routine.execute,
      X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,
      X86.execute,blockPreservesFlags,X86Routine.pushWord,put,write,X86.eax]
    funext r
    by_cases a : r=0 <;> by_cases b : r=2 <;> by_cases c : r=3 <;> by_cases d : r=4 <;> simp [write,a,b,c,d]
  exact path.transfer program [] decoded (by simp)

theorem execution (s : X86Memory.State) (f : Option Flags) (table : Word) (h : Initial s table) :
    Prefix program [] 30 ⟨s,f,0x2e3e0⟩ (request s) := by
  exact ((call_execution s f).trans (length_open_execution s table h)).trans
    ((length_execution s table h).trans (request_execution s))
theorem request_observations (s : X86Memory.State) (table : Word) (h : Initial s table) :
    (request s).pc=0x39690 ∧ (request s).core.regs 0=11664 ∧
    (request s).core.regs 2=50 ∧ (request s).core.regs 3=0 ∧
    load32 (request s).core.memory ((request s).core.regs 4)=0x2e415 ∧
    load32 (request s).core.memory 0x2c11c=648 := by
  have sep := h.countReturn
  simp only [BitVec.ofNat_eq_ofNat,BitVec.sub_eq_add_neg] at sep
  simp [request,measured,called,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc,
    load_store]
  exact (load_store_apart _ _ _ _ sep).trans (load_store _ _ _)
end Doom.Proofs.E1M1AimSideEntry
