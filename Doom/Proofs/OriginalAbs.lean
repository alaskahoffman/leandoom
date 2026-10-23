import Doom.Proofs.OriginalDivMemory
import Doom.Path
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalAbs
open Verification X86 X86Memory X86Control BlockSummary

def code : List UInt8 := [0x85,0xc0,0x7d,0x02,0xf7,0xd8,0xc3]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x418d8≤pc ∧ pc<0x418df then X86Routine.decodeAt bytes (pc-0x418d8) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x418d8 => some (.control (.testWord 0 0),2)
  | 0x418da => some (.jumpSigned 0 2,2)
  | 0x418dc => some (.negateRegister 0,2)
  | 0x418de => some (.ret,1)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def value (w : Word) : Word := if w.toInt<0 then -w else w
def result (s : X86Memory.State) : X86Control.State :=
  ⟨put (if (s.regs 0).toInt<0 then put s 0 (-s.regs 0) else s) 4 (s.regs 4+4),
    if (s.regs 0).toInt<0 then none else some (logical32 (s.regs 0)),
    (load32 s.memory (s.regs 4)).toNat⟩
theorem logical_ge (w : Word) :
    ((logical32 w).sign == (logical32 w).overflow)=decide (0≤w.toInt) := by
  have eq : logical32 w=compare32 w 0 := by simp [logical32,compare32,BitVec.ult_eq_decide]
  rw [eq,PlayerHeight.cmp_ge]
  rfl

theorem logical_ge_prop (w : Word) :
    (logical32 w).sign=(logical32 w).overflow ↔ 0≤w.toInt := by
  have h := congrArg (fun b => b=true) (logical_ge w)
  exact Iff.of_eq (by simpa only [beq_iff_eq,decide_eq_true_eq] using h)

theorem execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤4 ∧ X86Routine.Prefix program [] n ⟨s,f,0x418d8⟩ (result s) := by
  have start : X86Routine.Prefix listed [] 1 ⟨s,f,0x418d8⟩ ⟨s,some (logical32 (s.regs 0)),0x418da⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x418da⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute])
    exact .nil _
  by_cases h : (s.regs 0).toInt<0
  · have path : X86Routine.Prefix listed [] 3 ⟨s,some (logical32 (s.regs 0)),0x418da⟩ (result s) := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x418dc⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,logical_ge,logical_ge_prop,show ¬0≤(s.regs 0).toInt by omega])
      apply X86Routine.Prefix.step (middle := ⟨put s 0 (-s.regs 0),none,0x418de⟩) (by simp) (by rfl) (by rfl)
      apply X86Routine.Prefix.step (middle := result s) (by simp) (by rfl) (by
        simp [X86Routine.execute,result,h,put,write])
      exact .nil _
    exact ⟨4,by omega,(OriginalGroupBounds.prefix_join start path).transfer program [] decoded (by simp)⟩
  · have path : X86Routine.Prefix listed [] 2 ⟨s,some (logical32 (s.regs 0)),0x418da⟩ (result s) := by
      apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x418de⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,logical_ge,logical_ge_prop,show 0≤(s.regs 0).toInt by omega])
      apply X86Routine.Prefix.step (middle := result s) (by simp) (by rfl) (by simp [X86Routine.execute,result,h])
      exact .nil _
    exact ⟨3,by omega,(OriginalGroupBounds.prefix_join start path).transfer program [] decoded (by simp)⟩

theorem registers (s : X86Memory.State) :
    (result s).core.regs 0=value (s.regs 0) ∧
    (∀ r, r≠0 → r≠4 → (result s).core.regs r=s.regs r) ∧
    (result s).core.regs 4=s.regs 4+4 := by
  unfold result value
  split <;> simp [put,write]
  all_goals intro r h0 h4; simp_all
theorem memory (s : X86Memory.State) : (result s).core.memory=s.memory := by
  unfold result; split <;> rfl

theorem wrapped (a : Fixed) : value a.raw.toBitVec=(Fixed.absWrap a.raw).toBitVec := by
  simp only [value,Fixed.absWrap,Int32.lt_iff_toInt_lt,Int32.toInt_zero]
  by_cases h : a.raw.toInt<0
  · simp_all
  · have hv : ¬a.raw.toBitVec.toInt<0 := h
    simp only [if_neg h,if_neg hv]

/-- The engine rejects INT_MIN; on its successful domain this is the DOS helper. -/
theorem checked (a b : Fixed) (ok : Collision.checkedPathAbs a=.ok b) :
    value a.raw.toBitVec=b.raw.toBitVec := by
  unfold Collision.checkedPathAbs at ok
  split at ok
  · contradiction
  · cases ok
    rw [wrapped]
    unfold Fixed.absWrap
    by_cases h : a.raw<0
    · rw [if_pos h]
      have neg : a.raw.toInt<0 := by simpa only [Int32.lt_iff_toInt_lt,Int32.toInt_zero] using h
      rw [Int.ofNat_natAbs_of_nonpos (by omega),←Int32.neg_ofInt,Int32.ofInt_toInt]
    · rw [if_neg h]
      have pos : 0≤a.raw.toInt := by
        simp only [Int32.lt_iff_toInt_lt,Int32.toInt_zero] at h
        omega
      rw [Int.ofNat_natAbs_of_nonneg pos,Int32.ofInt_toInt]
end Doom.Proofs.OriginalAbs
