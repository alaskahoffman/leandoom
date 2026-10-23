import Doom.Proofs.E1M1AimCeilingEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalAimWindow
open Verification X86 X86Memory X86Control BlockSummary
attribute [local irreducible] load32 store32
def code : List UInt8 := [0xa1,0xe8,0xc1,0x2,0x0,0x3b,0x5,0xe4,0xc1,0x2,0x0,0xf,0x8f,0x8c,0x0,0x0,0x0,0x31,0xc0,0x5d,0x5f,0x5e,0x5a,0x59,0x5b,0xc3]
def continueCode : List UInt8 := [0xb8,0x1,0x0,0x0,0x0,0x5d,0x5f,0x5e,0x5a,0x59,0x5b,0xc3]
def bytesProgram (head tail : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2b800≤pc ∧ pc<0x2b81a then X86Routine.decodeAt head (pc-0x2b800)
  else if 0x2b89d≤pc ∧ pc<0x2b8a9 then X86Routine.decodeAt tail (pc-0x2b89d) else none
def program := bytesProgram code continueCode
def listed : X86Routine.Program
  | 0x2b800 => some (.control (.block (.load 0 ⟨none,none,0,0x2c1e8⟩)),5)
  | 0x2b805 => some (.control (.cmpMemory 0 ⟨none,none,0,0x2c1e4⟩),6)
  | 0x2b80b => some (.jumpSigned 2 140,6)
  | 0x2b811 => some (.xorRegister 0 0,2)
  | 0x2b813 => some (.pop 5,1)
  | 0x2b814 => some (.pop 7,1)
  | 0x2b815 => some (.pop 6,1)
  | 0x2b816 => some (.pop 2,1)
  | 0x2b817 => some (.pop 1,1)
  | 0x2b818 => some (.pop 3,1)
  | 0x2b819 => some (.ret,1)
  | 0x2b89d => some (.immediate 0 1,5)
  | 0x2b8a2 => some (.pop 5,1)
  | 0x2b8a3 => some (.pop 7,1)
  | 0x2b8a4 => some (.pop 6,1)
  | 0x2b8a5 => some (.pop 2,1)
  | 0x2b8a6 => some (.pop 1,1)
  | 0x2b8a7 => some (.pop 3,1)
  | 0x2b8a8 => some (.ret,1)
  | _ => none

/-- Decode near JG with an arbitrary signed displacement and trailing bytes. -/
theorem decode_jg (a b c d : UInt8) (tail : List UInt8) :
    X86Routine.decode ([0x0f,0x8f,a,b,c,d]++tail)=
      some (.jumpSigned 2 (((d.toBitVec ++ c.toBitVec) ++ (b.toBitVec ++ a.toBitVec)).toInt),tail) := by
  rfl

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def lower (s : X86Memory.State) := load32 s.memory (0x2c1e4#32)
def upper (s : X86Memory.State) := load32 s.memory (0x2c1e8#32)
def loaded (s : X86Memory.State) := put s 0 (upper s)
def gate (s : X86Memory.State) : X86Control.State :=
  ⟨loaded s,some (compare32 (upper s) (lower s)),
    if (lower s).toInt<(upper s).toInt then 0x2b89d else 0x2b811⟩
def v0 (s : X86Memory.State) (v : Word) := put s 0 v
def v1 (s : X86Memory.State) (v : Word) := OriginalAimGuard.pop (v0 s v) 5
def v2 (s : X86Memory.State) (v : Word) := OriginalAimGuard.pop (v1 s v) 7
def v3 (s : X86Memory.State) (v : Word) := OriginalAimGuard.pop (v2 s v) 6
def v4 (s : X86Memory.State) (v : Word) := OriginalAimGuard.pop (v3 s v) 2
def v5 (s : X86Memory.State) (v : Word) := OriginalAimGuard.pop (v4 s v) 1
def v6 (s : X86Memory.State) (v : Word) := OriginalAimGuard.pop (v5 s v) 3
def returned (s : X86Memory.State) (v : Word) (f : Option Flags) : X86Control.State :=
  ⟨put (v6 s v) 4 ((v6 s v).regs 4+4),f,(load32 (v6 s v).memory ((v6 s v).regs 4)).toNat⟩
def result (s : X86Memory.State) : X86Control.State :=
  if (lower s).toInt<(upper s).toInt then returned (loaded s) 1 (gate s).flags
  else returned (loaded s) 0 (some (logical32 0))

theorem gate_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2b800⟩ (gate s) := by
  have run : X86Routine.Prefix listed [] 3 ⟨s,f,0x2b800⟩ (gate s) := by
    apply X86Routine.Prefix.step (middle := ⟨loaded s,f,0x2b805⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,loaded,lower,upper,gate,v0,v1,v2,v3,v4,v5,v6,returned,OriginalAimGuard.pop,cmp32_signed_le,BitVec.add_assoc]
      all_goals split <;> simp_all <;> omega)
    apply X86Routine.Prefix.step (middle := ⟨loaded s,some (compare32 (upper s) (lower s)),0x2b80b⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,loaded,lower,upper,gate,v0,v1,v2,v3,v4,v5,v6,returned,OriginalAimGuard.pop,cmp32_signed_le,BitVec.add_assoc]
      all_goals split <;> simp_all <;> omega)
    apply X86Routine.Prefix.step (middle := gate s) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,loaded,lower,upper,gate,v0,v1,v2,v3,v4,v5,v6,returned,OriginalAimGuard.pop,cmp32_signed_le,BitVec.add_assoc]
      all_goals split <;> simp_all <;> omega)
    exact .nil _
  exact run.transfer program [] decoded (by simp)

theorem stop_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 8 ⟨s,f,0x2b811⟩ (returned s 0 (some (logical32 0))) := by
  have run : X86Routine.Prefix listed [] 8 ⟨s,f,0x2b811⟩ (returned s 0 (some (logical32 0))) := by
    apply X86Routine.Prefix.step (middle := ⟨v0 s 0,some (logical32 0),0x2b813⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,loaded,lower,upper,gate,v0,v1,v2,v3,v4,v5,v6,returned,OriginalAimGuard.pop,cmp32_signed_le,BitVec.add_assoc,logical32])
    apply X86Routine.Prefix.step (middle := ⟨v1 s 0,some (logical32 0),0x2b814⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,loaded,lower,upper,gate,v0,v1,v2,v3,v4,v5,v6,returned,OriginalAimGuard.pop,cmp32_signed_le,BitVec.add_assoc,logical32])
    apply X86Routine.Prefix.step (middle := ⟨v2 s 0,some (logical32 0),0x2b815⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,loaded,lower,upper,gate,v0,v1,v2,v3,v4,v5,v6,returned,OriginalAimGuard.pop,cmp32_signed_le,BitVec.add_assoc,logical32])
    apply X86Routine.Prefix.step (middle := ⟨v3 s 0,some (logical32 0),0x2b816⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,loaded,lower,upper,gate,v0,v1,v2,v3,v4,v5,v6,returned,OriginalAimGuard.pop,cmp32_signed_le,BitVec.add_assoc,logical32])
    apply X86Routine.Prefix.step (middle := ⟨v4 s 0,some (logical32 0),0x2b817⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,loaded,lower,upper,gate,v0,v1,v2,v3,v4,v5,v6,returned,OriginalAimGuard.pop,cmp32_signed_le,BitVec.add_assoc,logical32])
    apply X86Routine.Prefix.step (middle := ⟨v5 s 0,some (logical32 0),0x2b818⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,loaded,lower,upper,gate,v0,v1,v2,v3,v4,v5,v6,returned,OriginalAimGuard.pop,cmp32_signed_le,BitVec.add_assoc,logical32])
    apply X86Routine.Prefix.step (middle := ⟨v6 s 0,some (logical32 0),0x2b819⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,loaded,lower,upper,gate,v0,v1,v2,v3,v4,v5,v6,returned,OriginalAimGuard.pop,cmp32_signed_le,BitVec.add_assoc,logical32])
    apply X86Routine.Prefix.step (middle := returned s 0 (some (logical32 0))) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,loaded,lower,upper,gate,v0,v1,v2,v3,v4,v5,v6,returned,OriginalAimGuard.pop,cmp32_signed_le,BitVec.add_assoc])
    exact .nil _
  exact run.transfer program [] decoded (by simp)

theorem continue_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 8 ⟨s,f,0x2b89d⟩ (returned s 1 (f)) := by
  have run : X86Routine.Prefix listed [] 8 ⟨s,f,0x2b89d⟩ (returned s 1 (f)) := by
    apply X86Routine.Prefix.step (middle := ⟨v0 s 1,f,0x2b8a2⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,loaded,lower,upper,gate,v0,v1,v2,v3,v4,v5,v6,returned,OriginalAimGuard.pop,cmp32_signed_le,BitVec.add_assoc,logical32])
    apply X86Routine.Prefix.step (middle := ⟨v1 s 1,f,0x2b8a3⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,loaded,lower,upper,gate,v0,v1,v2,v3,v4,v5,v6,returned,OriginalAimGuard.pop,cmp32_signed_le,BitVec.add_assoc,logical32])
    apply X86Routine.Prefix.step (middle := ⟨v2 s 1,f,0x2b8a4⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,loaded,lower,upper,gate,v0,v1,v2,v3,v4,v5,v6,returned,OriginalAimGuard.pop,cmp32_signed_le,BitVec.add_assoc,logical32])
    apply X86Routine.Prefix.step (middle := ⟨v3 s 1,f,0x2b8a5⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,loaded,lower,upper,gate,v0,v1,v2,v3,v4,v5,v6,returned,OriginalAimGuard.pop,cmp32_signed_le,BitVec.add_assoc,logical32])
    apply X86Routine.Prefix.step (middle := ⟨v4 s 1,f,0x2b8a6⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,loaded,lower,upper,gate,v0,v1,v2,v3,v4,v5,v6,returned,OriginalAimGuard.pop,cmp32_signed_le,BitVec.add_assoc,logical32])
    apply X86Routine.Prefix.step (middle := ⟨v5 s 1,f,0x2b8a7⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,loaded,lower,upper,gate,v0,v1,v2,v3,v4,v5,v6,returned,OriginalAimGuard.pop,cmp32_signed_le,BitVec.add_assoc,logical32])
    apply X86Routine.Prefix.step (middle := ⟨v6 s 1,f,0x2b8a8⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,loaded,lower,upper,gate,v0,v1,v2,v3,v4,v5,v6,returned,OriginalAimGuard.pop,cmp32_signed_le,BitVec.add_assoc,logical32])
    apply X86Routine.Prefix.step (middle := returned s 1 (f)) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,loaded,lower,upper,gate,v0,v1,v2,v3,v4,v5,v6,returned,OriginalAimGuard.pop,cmp32_signed_le,BitVec.add_assoc])
    exact .nil _
  exact run.transfer program [] decoded (by simp)

theorem execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 11 ⟨s,f,0x2b800⟩ (result s) := by
  have p := gate_execution s f
  by_cases live : (lower s).toInt<(upper s).toInt
  · have pc : (gate s).pc=0x2b89d := by simp [gate,live]
    have q := continue_execution (gate s).core (gate s).flags
    rw [OriginalPathXStep.at_pc _ _ pc] at q
    simpa only [result,if_pos live,gate] using OriginalGroupBounds.prefix_join p q
  · have pc : (gate s).pc=0x2b811 := by simp [gate,live]
    have q := stop_execution (gate s).core (gate s).flags
    rw [OriginalPathXStep.at_pc _ _ pc] at q
    simpa only [result,if_neg live,gate] using OriginalGroupBounds.prefix_join p q

theorem returned_fields (s : X86Memory.State) (v : Word) (f : Option Flags) :
    (returned s v f).core.regs 0=v ∧ (returned s v f).core.regs 4=s.regs 4+(28#32) ∧
    (returned s v f).core.memory=s.memory ∧ (returned s v f).pc=(load32 s.memory (s.regs 4+(24#32))).toNat ∧
    (returned s v f).core.regs 5=load32 s.memory (s.regs 4) ∧
    (returned s v f).core.regs 7=load32 s.memory (s.regs 4+(4#32)) ∧
    (returned s v f).core.regs 6=load32 s.memory (s.regs 4+(8#32)) ∧
    (returned s v f).core.regs 2=load32 s.memory (s.regs 4+(12#32)) ∧
    (returned s v f).core.regs 1=load32 s.memory (s.regs 4+(16#32)) ∧
    (returned s v f).core.regs 3=load32 s.memory (s.regs 4+(20#32)) := by
  simp [returned,v0,v1,v2,v3,v4,v5,v6,OriginalAimGuard.pop,put,write,BitVec.add_assoc]

theorem result_fields (s : X86Memory.State) :
    (result s).core.regs 0=(if (lower s).toInt<(upper s).toInt then 1 else 0) ∧
    (result s).core.regs 4=s.regs 4+(28#32) ∧ (result s).core.memory=s.memory ∧
    (result s).pc=(load32 s.memory (s.regs 4+(24#32))).toNat := by
  unfold result
  split
  · rename_i live
    have r := returned_fields (loaded s) 1 (gate s).flags
    simpa [loaded,put,write,live] using And.intro r.1 (And.intro r.2.1 (And.intro r.2.2.1 r.2.2.2.1))
  · rename_i closed
    have r := returned_fields (loaded s) 0 (some (logical32 0))
    simpa [loaded,put,write,closed] using And.intro r.1 (And.intro r.2.1 (And.intro r.2.2.1 r.2.2.2.1))
theorem result_saved_regs (s : X86Memory.State) :
    (result s).core.regs 5=load32 s.memory (s.regs 4) ∧
    (result s).core.regs 7=load32 s.memory (s.regs 4+(4#32)) ∧
    (result s).core.regs 6=load32 s.memory (s.regs 4+(8#32)) ∧
    (result s).core.regs 2=load32 s.memory (s.regs 4+(12#32)) ∧
    (result s).core.regs 1=load32 s.memory (s.regs 4+(16#32)) ∧
    (result s).core.regs 3=load32 s.memory (s.regs 4+(20#32)) := by
  unfold result
  split
  · simpa [loaded,put,write] using (returned_fields (loaded s) 1 (gate s).flags).2.2.2.2
  · simpa [loaded,put,write] using (returned_fields (loaded s) 0 (some (logical32 0))).2.2.2.2
end Doom.Proofs.OriginalAimWindow
