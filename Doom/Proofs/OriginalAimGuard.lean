import Doom.Proofs.E1M1QueryCallback
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalAimGuard
open Verification X86 X86Memory X86Control BlockSummary
attribute [local irreducible] load32 store32
def guardCode : List UInt8 := [0x53,0x51,0x52,0x56,0x57,0x55,0x89,0xc2,0x83,0x78,0x4,0x0,0xf,0x84,0xa8,0x0,0x0,0x0,0x8b,0x48,0x8,0xf6,0x41,0x10,0x4,0xf,0x84,0x53,0x1,0x0,0x0]
def stopCode : List UInt8 := [0x31,0xc0,0x5d,0x5f,0x5e,0x5a,0x59,0x5b,0xc3]
def bytesProgram (head tail : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2b760≤pc ∧ pc<0x2b77f then X86Routine.decodeAt head (pc-0x2b760)
  else if 0x2b8d2≤pc ∧ pc<0x2b8db then X86Routine.decodeAt tail (pc-0x2b8d2) else none
def program := bytesProgram guardCode stopCode
def listed : X86Routine.Program
  | 0x2b760 => some (.push 3,1)
  | 0x2b761 => some (.push 1,1)
  | 0x2b762 => some (.push 2,1)
  | 0x2b763 => some (.push 6,1)
  | 0x2b764 => some (.push 7,1)
  | 0x2b765 => some (.push 5,1)
  | 0x2b766 => some (.control (.block (.legacy (.mov 2 0))),2)
  | 0x2b768 => some (.control (.cmpImmediate ⟨some 0,none,0,4⟩ 0),4)
  | 0x2b76c => some (.control (.jumpZero true 168),6)
  | 0x2b772 => some (.control (.block (.legacy (.load 1 0 8))),3)
  | 0x2b775 => some (.testMemoryByte ⟨some 1,none,0,16⟩ 4,4)
  | 0x2b779 => some (.control (.jumpZero true 339),6)
  | 0x2b8d2 => some (.xorRegister 0 0,2)
  | 0x2b8d4 => some (.pop 5,1)
  | 0x2b8d5 => some (.pop 7,1)
  | 0x2b8d6 => some (.pop 6,1)
  | 0x2b8d7 => some (.pop 2,1)
  | 0x2b8d8 => some (.pop 1,1)
  | 0x2b8d9 => some (.pop 3,1)
  | 0x2b8da => some (.ret,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide
def save1 (s : X86Memory.State) := X86Routine.pushWord s (s.regs 3)
def save2 (s : X86Memory.State) := X86Routine.pushWord (save1 s) (s.regs 1)
def save3 (s : X86Memory.State) := X86Routine.pushWord (save2 s) (s.regs 2)
def save4 (s : X86Memory.State) := X86Routine.pushWord (save3 s) (s.regs 6)
def save5 (s : X86Memory.State) := X86Routine.pushWord (save4 s) (s.regs 7)
def save6 (s : X86Memory.State) := X86Routine.pushWord (save5 s) (s.regs 5)
def saved := save6
def prepared (s : X86Memory.State) := put (saved s) 2 (s.regs 0)
def kind (s : X86Memory.State) := load32 (saved s).memory (s.regs 0+4)
def entry (s : X86Memory.State) : X86Control.State :=
  ⟨prepared s,some (compare32 (kind s) 0),if kind s=0 then 0x2b81a else 0x2b772⟩
def line (s : X86Memory.State) := load32 s.memory (s.regs 0+8)
def lineCore (s : X86Memory.State) := put s 1 (line s)
def bits (s : X86Memory.State) := s.memory (line s+16) &&& (4#8)
def lineGate (s : X86Memory.State) : X86Control.State :=
  ⟨lineCore s,some (logical8 (bits s)),if bits s=0 then 0x2b8d2 else 0x2b77f⟩
def pop (s : X86Memory.State) (r : Reg) :=
  put (put s 4 (s.regs 4+4)) r (load32 s.memory (s.regs 4))
def u0 (s : X86Memory.State) := put s 0 0
def u1 (s : X86Memory.State) := pop (u0 s) 5
def u2 (s : X86Memory.State) := pop (u1 s) 7
def u3 (s : X86Memory.State) := pop (u2 s) 6
def u4 (s : X86Memory.State) := pop (u3 s) 2
def u5 (s : X86Memory.State) := pop (u4 s) 1
def u6 (s : X86Memory.State) := pop (u5 s) 3
def stopped (s : X86Memory.State) : X86Control.State :=
  ⟨put (u6 s) 4 ((u6 s).regs 4+4),some (logical32 0),
    (load32 (u6 s).memory ((u6 s).regs 4)).toNat⟩

/-- Execute the original bytes without assumptions about interior memory. -/
theorem entry_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 9 ⟨s,f,0x2b760⟩ (entry s) := by
  have run : X86Routine.Prefix listed [] 9 ⟨s,f,0x2b760⟩ (entry s) := by
    apply X86Routine.Prefix.step (middle := ⟨save1 s,f,0x2b761⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,save1,save2,save3,save4,save5,save6,saved,prepared,kind,entry,line,lineCore,bits,lineGate,logical8,logical32,cmp32_zero,pop,u0,u1,u2,u3,u4,u5,u6,stopped,BitVec.add_assoc,BitVec.sub_eq_add_neg]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨save2 s,f,0x2b762⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,save1,save2,save3,save4,save5,save6,saved,prepared,kind,entry,line,lineCore,bits,lineGate,logical8,logical32,cmp32_zero,pop,u0,u1,u2,u3,u4,u5,u6,stopped,BitVec.add_assoc,BitVec.sub_eq_add_neg]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨save3 s,f,0x2b763⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,save1,save2,save3,save4,save5,save6,saved,prepared,kind,entry,line,lineCore,bits,lineGate,logical8,logical32,cmp32_zero,pop,u0,u1,u2,u3,u4,u5,u6,stopped,BitVec.add_assoc,BitVec.sub_eq_add_neg]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨save4 s,f,0x2b764⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,save1,save2,save3,save4,save5,save6,saved,prepared,kind,entry,line,lineCore,bits,lineGate,logical8,logical32,cmp32_zero,pop,u0,u1,u2,u3,u4,u5,u6,stopped,BitVec.add_assoc,BitVec.sub_eq_add_neg]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨save5 s,f,0x2b765⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,save1,save2,save3,save4,save5,save6,saved,prepared,kind,entry,line,lineCore,bits,lineGate,logical8,logical32,cmp32_zero,pop,u0,u1,u2,u3,u4,u5,u6,stopped,BitVec.add_assoc,BitVec.sub_eq_add_neg]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨save6 s,f,0x2b766⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,save1,save2,save3,save4,save5,save6,saved,prepared,kind,entry,line,lineCore,bits,lineGate,logical8,logical32,cmp32_zero,pop,u0,u1,u2,u3,u4,u5,u6,stopped,BitVec.add_assoc,BitVec.sub_eq_add_neg]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨prepared s,f,0x2b768⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,save1,save2,save3,save4,save5,save6,saved,prepared,kind,entry,line,lineCore,bits,lineGate,logical8,logical32,cmp32_zero,pop,u0,u1,u2,u3,u4,u5,u6,stopped,BitVec.add_assoc,BitVec.sub_eq_add_neg]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨prepared s,some (compare32 (kind s) 0),0x2b76c⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,save1,save2,save3,save4,save5,save6,saved,prepared,kind,entry,line,lineCore,bits,lineGate,logical8,logical32,cmp32_zero,pop,u0,u1,u2,u3,u4,u5,u6,stopped,BitVec.add_assoc,BitVec.sub_eq_add_neg]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := entry s) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,save1,save2,save3,save4,save5,save6,saved,prepared,kind,entry,line,lineCore,bits,lineGate,logical8,logical32,cmp32_zero,pop,u0,u1,u2,u3,u4,u5,u6,stopped,BitVec.add_assoc,BitVec.sub_eq_add_neg]
      all_goals split <;> simp_all)
    exact .nil _
  exact run.transfer program [] decoded (by simp)

/-- Execute the original bytes without assumptions about interior memory. -/
theorem line_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2b772⟩ (lineGate s) := by
  have run : X86Routine.Prefix listed [] 3 ⟨s,f,0x2b772⟩ (lineGate s) := by
    apply X86Routine.Prefix.step (middle := ⟨lineCore s,f,0x2b775⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,save1,save2,save3,save4,save5,save6,saved,prepared,kind,entry,line,lineCore,bits,lineGate,logical8,logical32,cmp32_zero,pop,u0,u1,u2,u3,u4,u5,u6,stopped,BitVec.add_assoc,BitVec.sub_eq_add_neg]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨lineCore s,some (logical8 (bits s)),0x2b779⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,save1,save2,save3,save4,save5,save6,saved,prepared,kind,entry,line,lineCore,bits,lineGate,logical8,logical32,cmp32_zero,pop,u0,u1,u2,u3,u4,u5,u6,stopped,BitVec.add_assoc,BitVec.sub_eq_add_neg]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := lineGate s) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,save1,save2,save3,save4,save5,save6,saved,prepared,kind,entry,line,lineCore,bits,lineGate,logical8,logical32,cmp32_zero,pop,u0,u1,u2,u3,u4,u5,u6,stopped,BitVec.add_assoc,BitVec.sub_eq_add_neg]
      all_goals split <;> simp_all)
    exact .nil _
  exact run.transfer program [] decoded (by simp)

/-- Execute the original bytes without assumptions about interior memory. -/
theorem stop_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 8 ⟨s,f,0x2b8d2⟩ (stopped s) := by
  have run : X86Routine.Prefix listed [] 8 ⟨s,f,0x2b8d2⟩ (stopped s) := by
    apply X86Routine.Prefix.step (middle := ⟨u0 s,some (logical32 0),0x2b8d4⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,save1,save2,save3,save4,save5,save6,saved,prepared,kind,entry,line,lineCore,bits,lineGate,logical8,logical32,cmp32_zero,pop,u0,u1,u2,u3,u4,u5,u6,stopped,BitVec.add_assoc,BitVec.sub_eq_add_neg]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨u1 s,some (logical32 0),0x2b8d5⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,save1,save2,save3,save4,save5,save6,saved,prepared,kind,entry,line,lineCore,bits,lineGate,logical8,logical32,cmp32_zero,pop,u0,u1,u2,u3,u4,u5,u6,stopped,BitVec.add_assoc,BitVec.sub_eq_add_neg]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨u2 s,some (logical32 0),0x2b8d6⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,save1,save2,save3,save4,save5,save6,saved,prepared,kind,entry,line,lineCore,bits,lineGate,logical8,logical32,cmp32_zero,pop,u0,u1,u2,u3,u4,u5,u6,stopped,BitVec.add_assoc,BitVec.sub_eq_add_neg]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨u3 s,some (logical32 0),0x2b8d7⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,save1,save2,save3,save4,save5,save6,saved,prepared,kind,entry,line,lineCore,bits,lineGate,logical8,logical32,cmp32_zero,pop,u0,u1,u2,u3,u4,u5,u6,stopped,BitVec.add_assoc,BitVec.sub_eq_add_neg]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨u4 s,some (logical32 0),0x2b8d8⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,save1,save2,save3,save4,save5,save6,saved,prepared,kind,entry,line,lineCore,bits,lineGate,logical8,logical32,cmp32_zero,pop,u0,u1,u2,u3,u4,u5,u6,stopped,BitVec.add_assoc,BitVec.sub_eq_add_neg]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨u5 s,some (logical32 0),0x2b8d9⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,save1,save2,save3,save4,save5,save6,saved,prepared,kind,entry,line,lineCore,bits,lineGate,logical8,logical32,cmp32_zero,pop,u0,u1,u2,u3,u4,u5,u6,stopped,BitVec.add_assoc,BitVec.sub_eq_add_neg]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := ⟨u6 s,some (logical32 0),0x2b8da⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,save1,save2,save3,save4,save5,save6,saved,prepared,kind,entry,line,lineCore,bits,lineGate,logical8,logical32,cmp32_zero,pop,u0,u1,u2,u3,u4,u5,u6,stopped,BitVec.add_assoc,BitVec.sub_eq_add_neg]
      all_goals split <;> simp_all)
    apply X86Routine.Prefix.step (middle := stopped s) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write,save1,save2,save3,save4,save5,save6,saved,prepared,kind,entry,line,lineCore,bits,lineGate,logical8,logical32,cmp32_zero,pop,u0,u1,u2,u3,u4,u5,u6,stopped,BitVec.add_assoc,BitVec.sub_eq_add_neg]
      all_goals split <;> simp_all)
    exact .nil _
  exact run.transfer program [] decoded (by simp)
end Doom.Proofs.OriginalAimGuard
