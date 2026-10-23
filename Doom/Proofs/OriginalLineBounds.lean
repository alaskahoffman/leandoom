import Doom.Proofs.OriginalPathCell
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalLineBounds
open Verification X86 X86Memory X86Control BlockSummary
def lineEntry : List UInt8 := [0x57,0x83,0xec,0x4,0x89,0x1c,0x24,0x85,0xc0,0x7c,0x5c,0x85,0xd2,0x7c,0x58,0x8b,0x1d,0xfc,0xc0,0x2,0x0,0x39,0xd8,0x7d,0x4e,0x3b,0x15,0x10,0xc1,0x2,0x0,0x7d,0x46]
def lineReturn : List UInt8 := [0xb8,0x1,0x0,0x0,0x0,0x83,0xc4,0x4,0x5f,0xc3]
def bytesProgram (entry ret : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c520≤pc ∧ pc<0x2c541 then X86Routine.decodeAt entry (pc-0x2c520)
  else if 0x2c587≤pc ∧ pc<0x2c591 then X86Routine.decodeAt ret (pc-0x2c587) else none
def program := bytesProgram lineEntry lineReturn
def listed : X86Routine.Program
  | 0x2c520 => some (.push 7,1)
  | 0x2c521 => some (.addImmediate 4 (-4),3)
  | 0x2c524 => some (.control (.block (.store ⟨some 4,none,0,0⟩ 3)),3)
  | 0x2c527 => some (.control (.testWord 0 0),2)
  | 0x2c529 => some (.jumpSigned 3 92,2)
  | 0x2c52b => some (.control (.testWord 2 2),2)
  | 0x2c52d => some (.jumpSigned 3 88,2)
  | 0x2c52f => some (.control (.block (.load 3 ⟨none,none,0,0x2c0fc⟩)),6)
  | 0x2c535 => some (.compareRegisters 0 3,2)
  | 0x2c537 => some (.jumpSigned 0 78,2)
  | 0x2c539 => some (.control (.cmpMemory 2 ⟨none,none,0,0x2c110⟩),6)
  | 0x2c53f => some (.jumpSigned 0 70,2)
  | 0x2c587 => some (.immediate 0 1,5)
  | 0x2c58c => some (.addImmediate 4 4,3)
  | 0x2c58f => some (.pop 7,1)
  | 0x2c590 => some (.ret,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def e1 (s : X86Memory.State) := X86Routine.pushWord s (s.regs 7)
def e2 (s : X86Memory.State) := put (e1 s) 4 (s.regs 4-8)
def entry (s : X86Memory.State) : X86Memory.State :=
  {e2 s with memory:=store32 (e1 s).memory (s.regs 4-8) (s.regs 3)}
theorem entry_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2c520⟩ ⟨entry s,none,0x2c527⟩ := by
  have path : X86Routine.Prefix listed [] 3 ⟨s,f,0x2c520⟩ ⟨entry s,none,0x2c527⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨e1 s,f,0x2c521⟩) (by simp) (by rfl) (by rfl)
    apply X86Routine.Prefix.step (middle := ⟨e2 s,none,0x2c524⟩) (by simp) (by rfl) (by
      simp [e2,e1,X86Routine.execute,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc])
    apply X86Routine.Prefix.step (middle := ⟨entry s,none,0x2c527⟩) (by simp) (by rfl) (by
      simp [entry,e2,e1,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,X86Routine.pushWord,put,write])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def width (s : X86Memory.State) := load32 s.memory 0x2c0fc
def height (s : X86Memory.State) := load32 s.memory 0x2c110
def loaded (s : X86Memory.State) := put s 3 (width s)
def Inside (s : X86Memory.State) : Prop :=
  0≤(s.regs 0).toInt ∧ 0≤(s.regs 2).toInt ∧ (s.regs 0).toInt<(width s).toInt ∧ (s.regs 2).toInt<(height s).toInt
instance (s : X86Memory.State) : Decidable (Inside s) := inferInstanceAs (Decidable (_∧_))
def guarded (s : X86Memory.State) : X86Control.State :=
  if (s.regs 0).toInt<0 then ⟨s,some (logical32 (s.regs 0)),0x2c587⟩
  else if (s.regs 2).toInt<0 then ⟨s,some (logical32 (s.regs 2)),0x2c587⟩
  else if (width s).toInt≤(s.regs 0).toInt then ⟨loaded s,some (compare32 (s.regs 0) (width s)),0x2c587⟩
  else ⟨loaded s,some (compare32 (s.regs 2) (height s)),if (height s).toInt≤(s.regs 2).toInt then 0x2c587 else 0x2c541⟩

theorem logical_lt (v : Word) : ((logical32 v).sign != (logical32 v).overflow)=decide (v.toInt<0) := by
  have h : logical32 v=compare32 v 0 := by simp [logical32,compare32,BitVec.ult_eq_decide]
  rw [h,PlayerArmor.cmp_lt]
  rfl

theorem logical_lt_prop (v : Word) :
    (logical32 v).sign ≠ (logical32 v).overflow ↔ v.toInt<0 := by
  change (¬ (logical32 v).sign = (logical32 v).overflow) ↔ _
  rw [OriginalAbs.logical_ge_prop]
  omega

theorem guard_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤9 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2c527⟩ (guarded s) := by
  have path : ∃ n, n≤9 ∧ X86Routine.Prefix listed [] n ⟨s,f,0x2c527⟩ (guarded s) := by
    by_cases hx : (s.regs 0).toInt<0
    · refine ⟨2,by omega,?_⟩
      apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c529⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx] <;> repeat (first | rfl | omega | split))
      apply X86Routine.Prefix.step (middle := guarded s) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx] <;> repeat (first | rfl | omega | split))
      exact .nil _
    · by_cases hy : (s.regs 2).toInt<0
      · refine ⟨4,by omega,?_⟩
        apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c529⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy] <;> repeat (first | rfl | omega | split))
        apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c52b⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy] <;> repeat (first | rfl | omega | split))
        apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 2)),0x2c52d⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy] <;> repeat (first | rfl | omega | split))
        apply X86Routine.Prefix.step (middle := guarded s) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy] <;> repeat (first | rfl | omega | split))
        exact .nil _
      · by_cases hw : (width s).toInt≤(s.regs 0).toInt
        · refine ⟨7,by omega,?_⟩
          apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c529⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw] <;> repeat (first | rfl | omega | split))
          apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c52b⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw] <;> repeat (first | rfl | omega | split))
          apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 2)),0x2c52d⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw] <;> repeat (first | rfl | omega | split))
          apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 2)),0x2c52f⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw] <;> repeat (first | rfl | omega | split))
          apply X86Routine.Prefix.step (middle := ⟨loaded s,some (logical32 (s.regs 2)),0x2c535⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw] <;> repeat (first | rfl | omega | split))
          apply X86Routine.Prefix.step (middle := ⟨loaded s,some (compare32 (s.regs 0) (width s)),0x2c537⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw] <;> repeat (first | rfl | omega | split))
          apply X86Routine.Prefix.step (middle := guarded s) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw] <;> repeat (first | rfl | omega | split))
          exact .nil _
        · by_cases hh : (height s).toInt≤(s.regs 2).toInt
          · refine ⟨9,by omega,?_⟩
            apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c529⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c52b⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 2)),0x2c52d⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 2)),0x2c52f⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨loaded s,some (logical32 (s.regs 2)),0x2c535⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨loaded s,some (compare32 (s.regs 0) (width s)),0x2c537⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨loaded s,some (compare32 (s.regs 0) (width s)),0x2c539⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨loaded s,some (compare32 (s.regs 2) (height s)),0x2c53f⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := guarded s) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            exact .nil _
          · refine ⟨9,by omega,?_⟩
            apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c529⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c52b⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 2)),0x2c52d⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 2)),0x2c52f⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨loaded s,some (logical32 (s.regs 2)),0x2c535⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨loaded s,some (compare32 (s.regs 0) (width s)),0x2c537⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨loaded s,some (compare32 (s.regs 0) (width s)),0x2c539⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨loaded s,some (compare32 (s.regs 2) (height s)),0x2c53f⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := guarded s) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            exact .nil _
  obtain ⟨n,hn,path⟩ := path
  exact ⟨n,hn,path.transfer program [] decoded (by simp)⟩

def r1 (s : X86Memory.State) := put s 0 1
def r2 (s : X86Memory.State) := put (r1 s) 4 (s.regs 4+4)
def r3 (s : X86Memory.State) := put (put (r2 s) 4 (s.regs 4+8)) 7 (load32 s.memory (s.regs 4+4))
def returned (s : X86Memory.State) : X86Control.State :=
  ⟨put (r3 s) 4 (s.regs 4+12),none,(load32 s.memory (s.regs 4+8)).toNat⟩
theorem return_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 4 ⟨s,f,0x2c587⟩ (returned s) := by
  have path : X86Routine.Prefix listed [] 4 ⟨s,f,0x2c587⟩ (returned s) := by
    apply X86Routine.Prefix.step (middle := ⟨r1 s,f,0x2c58c⟩) (by simp) (by rfl) (by simp [returned,r3,r2,r1,X86Routine.execute,put,write,BitVec.add_assoc])
    apply X86Routine.Prefix.step (middle := ⟨r2 s,none,0x2c58f⟩) (by simp) (by rfl) (by simp [returned,r3,r2,r1,X86Routine.execute,put,write,BitVec.add_assoc])
    apply X86Routine.Prefix.step (middle := ⟨r3 s,none,0x2c590⟩) (by simp) (by rfl) (by simp [returned,r3,r2,r1,X86Routine.execute,put,write,BitVec.add_assoc])
    apply X86Routine.Prefix.step (middle := returned s) (by simp) (by rfl) (by simp [returned,r3,r2,r1,X86Routine.execute,put,write,BitVec.add_assoc])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

theorem guarded_pc (s : X86Memory.State) :
    (guarded s).pc=if Inside s then 0x2c541 else 0x2c587 := by
  unfold guarded Inside
  split <;> rename_i hx
  · simp [show ¬0≤(s.regs 0).toInt by omega]
  · split <;> rename_i hy
    · simp [show ¬0≤(s.regs 2).toInt by omega]
    · split <;> rename_i hw
      · simp [show ¬(s.regs 0).toInt<(width s).toInt by omega]
      · split <;> rename_i hh
        · simp [show ¬(s.regs 2).toInt<(height s).toInt by omega]
        · simp [show 0≤(s.regs 0).toInt by omega,show 0≤(s.regs 2).toInt by omega,
            show (s.regs 0).toInt<(width s).toInt by omega,show (s.regs 2).toInt<(height s).toInt by omega]

def result (s : X86Memory.State) : X86Control.State :=
  if Inside (entry s) then guarded (entry s) else returned (guarded (entry s)).core

/-- Outside cells return true via the original epilogue; inside cells stop
before the first BLOCKMAP index lookup. Neither path invokes a callback. -/
theorem execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤16 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2c520⟩ (result s) := by
  have a := entry_execution s f
  obtain ⟨n,hn,b⟩ := guard_execution (entry s) none
  have ab := OriginalGroupBounds.prefix_join a b
  by_cases h : Inside (entry s)
  · exact ⟨3+n,by omega,by simpa only [result,if_pos h] using ab⟩
  · have c := return_execution (guarded (entry s)).core (guarded (entry s)).flags
    have pc : (guarded (entry s)).pc=0x2c587 := by rw [guarded_pc,if_neg h]
    rw [OriginalPathXStep.at_pc _ _ pc] at c
    exact ⟨3+n+4,by omega,by simpa only [result,if_neg h] using OriginalGroupBounds.prefix_join ab c⟩

/-- The prologue writes only the saved EDI and callback stack words. -/
theorem entry_frame (s : X86Memory.State) (a : Word)
    (saved : Apart a (s.regs 4-4)) (local_ : Apart a (s.regs 4-8)) :
    load32 (entry s).memory a=load32 s.memory a := by
  change load32 (store32 (store32 s.memory (s.regs 4-4) _) (s.regs 4-8) _) a=_
  rw [load_store_apart _ _ _ _ local_,load_store_apart _ _ _ _ saved]

theorem guard_frame (s : X86Memory.State) :
    (guarded s).core.memory=s.memory ∧ (guarded s).core.regs 4=s.regs 4 := by
  unfold guarded
  split <;> (try split) <;> (try split) <;> simp [loaded,put,write]

theorem entry_coordinates (s : X86Memory.State) :
    (entry s).regs 0=s.regs 0 ∧ (entry s).regs 2=s.regs 2 ∧ (entry s).regs 4=s.regs 4-8 := by
  simp [entry,e2,e1,X86Routine.pushWord,put,write]

/-- A natural map dimension must fit a nonnegative signed DOS word. -/
theorem dimension_int (n : Nat) (h : n<2147483648) :
    (BitVec.ofNat 32 n).toInt=(n : Int) := by
  have hn : n<2^32 := by omega
  have nat : (BitVec.ofNat 32 n).toNat=n := by simp [Nat.mod_eq_of_lt hn]
  rw [BitVec.toInt_eq_toNat_of_lt (by rw [nat]; omega),nat]

/-- Representation and stack separation at the actual iterator entry. -/
structure Inputs (s : X86Memory.State) (x y : Int32) (w h : Nat) : Prop where
  mapX : s.regs 0=x.toBitVec
  mapY : s.regs 2=y.toBitVec
  width : load32 s.memory 0x2c0fc=BitVec.ofNat 32 w
  height : load32 s.memory 0x2c110=BitVec.ofNat 32 h
  widthBound : w<2147483648
  heightBound : h<2147483648
  safe : ∀ a∈[(0x2c0fc#32),0x2c110], Apart a (s.regs 4-4) ∧ Apart a (s.regs 4-8)

theorem live_bounds (s : X86Memory.State) (x y : Int32) (w h : Nat)
    (encoding : Inputs s x y w h) :
    Inside (entry s) ↔ Collision.pathCellInside x y w h=true := by
  have ew := entry_frame s 0x2c0fc (encoding.safe _ (by simp)).1 (encoding.safe _ (by simp)).2
  have eh := entry_frame s 0x2c110 (encoding.safe _ (by simp)).1 (encoding.safe _ (by simp)).2
  unfold Inside width height
  rw [(entry_coordinates s).1,(entry_coordinates s).2.1,ew,eh,
    encoding.mapX,encoding.mapY,encoding.width,encoding.height,
    dimension_int _ encoding.widthBound,dimension_int _ encoding.heightBound]
  simp [Collision.pathCellInside,and_assoc]

/-- The bounds decision is the production decision, not an assumed branch. -/
theorem live_pc (s : X86Memory.State) (x y : Int32) (w h : Nat)
    (encoding : Inputs s x y w h) :
    (guarded (entry s)).pc=if Collision.pathCellInside x y w h then 0x2c541 else 0x2c587 := by
  simp only [guarded_pc,live_bounds s x y w h encoding]

/-- A rejected cell returns success and removes its frame plus the CALL word. -/
theorem outside_return (s : X86Memory.State) (outside : ¬Inside (entry s)) :
    (result s).core.regs 0=1 ∧ (result s).core.regs 4=s.regs 4+4 ∧
    (result s).pc=(load32 s.memory (s.regs 4)).toNat := by
  have apart4 : Apart (s.regs 4) (s.regs 4-4) := by
    have h := OriginalPathXStep.apart_translate (s.regs 4) 0 (-4) (by unfold Apart; decide)
    simpa [BitVec.sub_eq_add_neg] using h
  have apart8 : Apart (s.regs 4) (s.regs 4-8) := by
    have h := OriginalPathXStep.apart_translate (s.regs 4) 0 (-8) (by unfold Apart; decide)
    simpa [BitVec.sub_eq_add_neg] using h
  simp only [result,if_neg outside,returned,r3,r2,r1,put,write]
  simp only [(guard_frame (entry s)).1,(guard_frame (entry s)).2,(entry_coordinates s).2.2]
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc,entry_frame s _ apart4 apart8]

end Doom.Proofs.OriginalLineBounds
