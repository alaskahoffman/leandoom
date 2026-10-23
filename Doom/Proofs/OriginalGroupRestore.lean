import Doom.Proofs.OriginalGroupRemainder
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
namespace Doom.Proofs.OriginalGroupRestore
open Verification X86 X86Memory X86Control BlockSummary
abbrev program := OriginalGroupAllocation.program
def listed : X86Routine.Program
  | 0x39771 => some (.pop 5,1)
  | 0x39772 => some (.pop 7,1)
  | 0x39773 => some (.pop 6,1)
  | 0x39774 => some (.pop 1,1)
  | 0x39775 => some (.ret,1)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def restored (s : X86Memory.State) :=
  put (put (put (put (put s 5 (load32 s.memory (s.regs 4)))
    7 (load32 s.memory (s.regs 4+4))) 6 (load32 s.memory (s.regs 4+8)))
    1 (load32 s.memory (s.regs 4+12))) 4 (s.regs 4+20)
def result (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨restored s,f,(load32 s.memory (s.regs 4+16)).toNat⟩
@[local simp] private theorem step_39771 (s : X86Memory.State) (f : Option Flags)
    (n dest : Nat) (h : dest≠0x39771) :
    X86Routine.run listed [dest] (n+1) ⟨s,f,0x39771⟩=
      (X86Routine.execute (.pop 5) ⟨s,f,0x39772⟩).bind (X86Routine.run listed [dest] n) := by
  rw [X86Routine.run,if_neg (by simpa using Ne.symm h)]
  rfl
@[local simp] private theorem step_39772 (s : X86Memory.State) (f : Option Flags)
    (n dest : Nat) (h : dest≠0x39772) :
    X86Routine.run listed [dest] (n+1) ⟨s,f,0x39772⟩=
      (X86Routine.execute (.pop 7) ⟨s,f,0x39773⟩).bind (X86Routine.run listed [dest] n) := by
  rw [X86Routine.run,if_neg (by simpa using Ne.symm h)]
  rfl
@[local simp] private theorem step_39773 (s : X86Memory.State) (f : Option Flags)
    (n dest : Nat) (h : dest≠0x39773) :
    X86Routine.run listed [dest] (n+1) ⟨s,f,0x39773⟩=
      (X86Routine.execute (.pop 6) ⟨s,f,0x39774⟩).bind (X86Routine.run listed [dest] n) := by
  rw [X86Routine.run,if_neg (by simpa using Ne.symm h)]
  rfl
@[local simp] private theorem step_39774 (s : X86Memory.State) (f : Option Flags)
    (n dest : Nat) (h : dest≠0x39774) :
    X86Routine.run listed [dest] (n+1) ⟨s,f,0x39774⟩=
      (X86Routine.execute (.pop 1) ⟨s,f,0x39775⟩).bind (X86Routine.run listed [dest] n) := by
  rw [X86Routine.run,if_neg (by simpa using Ne.symm h)]
  rfl
@[local simp] private theorem step_39775 (s : X86Memory.State) (f : Option Flags)
    (n dest : Nat) (h : dest≠0x39775) :
    X86Routine.run listed [dest] (n+1) ⟨s,f,0x39775⟩=
      (X86Routine.execute (.ret) ⟨s,f,0x39776⟩).bind (X86Routine.run listed [dest] n) := by
  rw [X86Routine.run,if_neg (by simpa using Ne.symm h)]
  rfl
@[local simp] private theorem stopped (s : X86Memory.State) (f : Option Flags) (n dest : Nat) :
    X86Routine.run listed [dest] n ⟨s,f,dest⟩=some ⟨s,f,dest⟩ := by
  cases n <;> simp [X86Routine.run]

/-- Five instructions, with all stack reads made from the incoming memory.
The destination is excluded from the epilogue so it cannot stop prematurely. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (dest : Word)
    (outside : dest.toNat<0x39771 ∨ 0x39776≤dest.toNat)
    (ret : load32 s.memory (s.regs 4+16)=dest) :
    X86Routine.run program [dest.toNat] 5 ⟨s,f,0x39771⟩=some (result s f) := by
  change load32 s.memory (s.regs 4+(16#32))=dest at ret
  have h0 : dest.toNat≠0x39771 := by omega
  have h1 : dest.toNat≠0x39772 := by omega
  have h2 : dest.toNat≠0x39773 := by omega
  have h3 : dest.toNat≠0x39774 := by omega
  have h4 : dest.toNat≠0x39775 := by omega
  have run : X86Routine.run listed [dest.toNat] 5 ⟨s,f,0x39771⟩=some (result s f) := by
    simp [h0,h1,h2,h3,h4,X86Routine.execute,result,restored,put,write,BitVec.add_assoc,ret]
    funext r
    by_cases h : r=4 <;> simp [write,h]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

theorem memory (s : X86Memory.State) (f : Option Flags) : (result s f).core.memory=s.memory := rfl

theorem registers (s : X86Memory.State) (f : Option Flags) :
    (result s f).core.regs 4=s.regs 4+20 ∧
    (result s f).core.regs 5=load32 s.memory (s.regs 4) ∧
    (result s f).core.regs 7=load32 s.memory (s.regs 4+4) ∧
    (result s f).core.regs 6=load32 s.memory (s.regs 4+8) ∧
    (result s f).core.regs 1=load32 s.memory (s.regs 4+12) ∧
    (result s f).core.regs 0=s.regs 0 := by simp [result,restored,put,write]
end Doom.Proofs.OriginalGroupRestore
