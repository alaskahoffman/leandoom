import Doom.Proofs.OriginalLineCell
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalThingEntry
open Verification X86 X86Memory X86Control BlockSummary
def thingEntry : List UInt8 := [0x83,0xec,0x4,0x89,0x1c,0x24,0x85,0xc0,0x7c,0x38,0x85,0xd2,0x7c,0x34,0x8b,0x1d,0xfc,0xc0,0x2,0x0,0x39,0xd8,0x7d,0x2a,0x3b,0x15,0x10,0xc1,0x2,0x0,0x7d,0x22]
def thingLookup : List UInt8 := [0xf,0xaf,0xd3,0x1,0xd0,0x8b,0x15,0xf8,0xc0,0x2,0x0,0x8b,0x14,0x82,0x85,0xd2,0x74,0x10]
def thingReturn : List UInt8 := [0xb8,0x1,0x0,0x0,0x0,0x83,0xc4,0x4,0xc3]
def bytesProgram (entry lookup ret : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c5a0≤pc ∧ pc<0x2c5c0 then X86Routine.decodeAt entry (pc-0x2c5a0)
  else if 0x2c5c0≤pc ∧ pc<0x2c5d2 then X86Routine.decodeAt lookup (pc-0x2c5c0)
  else if 0x2c5e2≤pc ∧ pc<0x2c5eb then X86Routine.decodeAt ret (pc-0x2c5e2) else none
def program := bytesProgram thingEntry thingLookup thingReturn
def listed : X86Routine.Program
  | 0x2c5a0 => some (.addImmediate 4 (-4),3)
  | 0x2c5a3 => some (.control (.block (.store ⟨some 4,none,0,0⟩ 3)),3)
  | 0x2c5a6 => some (.control (.testWord 0 0),2)
  | 0x2c5a8 => some (.jumpSigned 3 56,2)
  | 0x2c5aa => some (.control (.testWord 2 2),2)
  | 0x2c5ac => some (.jumpSigned 3 52,2)
  | 0x2c5ae => some (.control (.block (.load 3 ⟨none,none,0,0x2c0fc⟩)),6)
  | 0x2c5b4 => some (.compareRegisters 0 3,2)
  | 0x2c5b6 => some (.jumpSigned 0 42,2)
  | 0x2c5b8 => some (.control (.cmpMemory 2 ⟨none,none,0,0x2c110⟩),6)
  | 0x2c5be => some (.jumpSigned 0 34,2)
  | 0x2c5c0 => some (.multiplyRegister 2 3,3)
  | 0x2c5c3 => some (.control (.block (.arithmetic (.add 0 2))),2)
  | 0x2c5c5 => some (.control (.block (.load 2 ⟨none,none,0,0x2c0f8⟩)),6)
  | 0x2c5cb => some (.control (.block (.load 2 ⟨some 2,some 0,2,0⟩)),3)
  | 0x2c5ce => some (.control (.testWord 2 2),2)
  | 0x2c5d0 => some (.control (.jumpZero true 16),2)
  | 0x2c5e2 => some (.immediate 0 1,5)
  | 0x2c5e7 => some (.addImmediate 4 4,3)
  | 0x2c5ea => some (.ret,1)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def allocated (s : X86Memory.State) := put s 4 (s.regs 4-(4#32))
def entry (s : X86Memory.State) : X86Memory.State :=
  {allocated s with memory:=store32 s.memory (s.regs 4-(4#32)) (s.regs 3)}
theorem entry_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 2 ⟨s,f,0x2c5a0⟩ ⟨entry s,none,0x2c5a6⟩ := by
  have path : X86Routine.Prefix listed [] 2 ⟨s,f,0x2c5a0⟩ ⟨entry s,none,0x2c5a6⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨allocated s,none,0x2c5a3⟩) (by simp) (by rfl)
      (by simp [allocated,X86Routine.execute,put,write,BitVec.sub_eq_add_neg])
    apply X86Routine.Prefix.step (middle := ⟨entry s,none,0x2c5a6⟩) (by simp) (by rfl)
      (by simp [entry,allocated,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def width (s : X86Memory.State) := load32 s.memory 0x2c0fc
def height (s : X86Memory.State) := load32 s.memory 0x2c110
def loaded (s : X86Memory.State) := put s 3 (width s)
def Inside (s : X86Memory.State) : Prop :=
  0≤(s.regs 0).toInt ∧ 0≤(s.regs 2).toInt ∧ (s.regs 0).toInt<(width s).toInt ∧ (s.regs 2).toInt<(height s).toInt
instance (s : X86Memory.State) : Decidable (Inside s) := inferInstanceAs (Decidable (_∧_))
def guarded (s : X86Memory.State) : X86Control.State :=
  if (s.regs 0).toInt<0 then ⟨s,some (logical32 (s.regs 0)),0x2c5e2⟩
  else if (s.regs 2).toInt<0 then ⟨s,some (logical32 (s.regs 2)),0x2c5e2⟩
  else if (width s).toInt≤(s.regs 0).toInt then ⟨loaded s,some (compare32 (s.regs 0) (width s)),0x2c5e2⟩
  else ⟨loaded s,some (compare32 (s.regs 2) (height s)),if (height s).toInt≤(s.regs 2).toInt then 0x2c5e2 else 0x2c5c0⟩

abbrev logical_lt := OriginalLineBounds.logical_lt
abbrev logical_lt_prop := OriginalLineBounds.logical_lt_prop

theorem guard_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n, n≤9 ∧ X86Routine.Prefix program [] n ⟨s,f,0x2c5a6⟩ (guarded s) := by
  have path : ∃ n, n≤9 ∧ X86Routine.Prefix listed [] n ⟨s,f,0x2c5a6⟩ (guarded s) := by
    by_cases hx : (s.regs 0).toInt<0
    · refine ⟨2,by omega,?_⟩
      apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c5a8⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx] <;> repeat (first | rfl | omega | split))
      apply X86Routine.Prefix.step (middle := guarded s) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx] <;> repeat (first | rfl | omega | split))
      exact .nil _
    · by_cases hy : (s.regs 2).toInt<0
      · refine ⟨4,by omega,?_⟩
        apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c5a8⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy] <;> repeat (first | rfl | omega | split))
        apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c5aa⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy] <;> repeat (first | rfl | omega | split))
        apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 2)),0x2c5ac⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy] <;> repeat (first | rfl | omega | split))
        apply X86Routine.Prefix.step (middle := guarded s) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy] <;> repeat (first | rfl | omega | split))
        exact .nil _
      · by_cases hw : (width s).toInt≤(s.regs 0).toInt
        · refine ⟨7,by omega,?_⟩
          apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c5a8⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw] <;> repeat (first | rfl | omega | split))
          apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c5aa⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw] <;> repeat (first | rfl | omega | split))
          apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 2)),0x2c5ac⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw] <;> repeat (first | rfl | omega | split))
          apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 2)),0x2c5ae⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw] <;> repeat (first | rfl | omega | split))
          apply X86Routine.Prefix.step (middle := ⟨loaded s,some (logical32 (s.regs 2)),0x2c5b4⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw] <;> repeat (first | rfl | omega | split))
          apply X86Routine.Prefix.step (middle := ⟨loaded s,some (compare32 (s.regs 0) (width s)),0x2c5b6⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw] <;> repeat (first | rfl | omega | split))
          apply X86Routine.Prefix.step (middle := guarded s) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw] <;> repeat (first | rfl | omega | split))
          exact .nil _
        · by_cases hh : (height s).toInt≤(s.regs 2).toInt
          · refine ⟨9,by omega,?_⟩
            apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c5a8⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c5aa⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 2)),0x2c5ac⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 2)),0x2c5ae⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨loaded s,some (logical32 (s.regs 2)),0x2c5b4⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨loaded s,some (compare32 (s.regs 0) (width s)),0x2c5b6⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨loaded s,some (compare32 (s.regs 0) (width s)),0x2c5b8⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨loaded s,some (compare32 (s.regs 2) (height s)),0x2c5be⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := guarded s) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            exact .nil _
          · refine ⟨9,by omega,?_⟩
            apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c5a8⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c5aa⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 2)),0x2c5ac⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 2)),0x2c5ae⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨loaded s,some (logical32 (s.regs 2)),0x2c5b4⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨loaded s,some (compare32 (s.regs 0) (width s)),0x2c5b6⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨loaded s,some (compare32 (s.regs 0) (width s)),0x2c5b8⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := ⟨loaded s,some (compare32 (s.regs 2) (height s)),0x2c5be⟩) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            apply X86Routine.Prefix.step (middle := guarded s) (by simp) (by rfl) (by simp_all [guarded,loaded,width,height,put,write,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,logical_lt,logical_lt_prop,OriginalAbs.logical_ge_prop,PlayerHeight.cmp_ge_prop,hx,hy,hw,hh] <;> repeat (first | rfl | omega | split))
            exact .nil _
  obtain ⟨n,hn,path⟩ := path
  exact ⟨n,hn,path.transfer program [] decoded (by simp)⟩

def r1 (s : X86Memory.State) := put s 0 1
def r2 (s : X86Memory.State) := put (r1 s) 4 (s.regs 4+(4#32))
def returned (s : X86Memory.State) : X86Control.State :=
  ⟨put (r2 s) 4 (s.regs 4+(8#32)),none,(load32 s.memory (s.regs 4+(4#32))).toNat⟩
theorem return_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2c5e2⟩ (returned s) := by
  have path : X86Routine.Prefix listed [] 3 ⟨s,f,0x2c5e2⟩ (returned s) := by
    apply X86Routine.Prefix.step (middle := ⟨r1 s,f,0x2c5e7⟩) (by simp) (by rfl) (by simp [r1,X86Routine.execute])
    apply X86Routine.Prefix.step (middle := ⟨r2 s,none,0x2c5ea⟩) (by simp) (by rfl) (by simp [r2,r1,X86Routine.execute,put,write])
    apply X86Routine.Prefix.step (middle := returned s) (by simp) (by rfl) (by simp [returned,r2,r1,X86Routine.execute,put,write,BitVec.add_assoc])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

theorem guarded_pc (s : X86Memory.State) :
    (guarded s).pc=if Inside s then 0x2c5c0 else 0x2c5e2 := by
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

def index (s : X86Memory.State) := s.regs 0+s.regs 2*s.regs 3
def table (s : X86Memory.State) := load32 s.memory (0x2c0f8#32)
def head (s : X86Memory.State) := load32 s.memory (table s+(index s <<< 2))
def l1 (s : X86Memory.State) := put s 2 (s.regs 2*s.regs 3)
def l2 (s : X86Memory.State) := put (l1 s) 0 (index s)
def l3 (s : X86Memory.State) := put (l2 s) 2 (table s)
def loadedHead (s : X86Memory.State) := put (l3 s) 2 (head s)
def lookup (s : X86Memory.State) : X86Control.State :=
  ⟨loadedHead s,some (logical32 (head s)),if head s=(0#32) then 0x2c5e2 else 0x2c5d2⟩
theorem lookup_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 6 ⟨s,f,0x2c5c0⟩ (lookup s) := by
  have path : X86Routine.Prefix listed [] 6 ⟨s,f,0x2c5c0⟩ (lookup s) := by
    apply X86Routine.Prefix.step (middle := ⟨l1 s,none,0x2c5c3⟩) (by simp) (by rfl) (by simp [l1,X86Routine.execute,put,write])
    apply X86Routine.Prefix.step (middle := ⟨l2 s,none,0x2c5c5⟩) (by simp) (by rfl) (by simp [l2,l1,index,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,put,write])
    apply X86Routine.Prefix.step (middle := ⟨l3 s,none,0x2c5cb⟩) (by simp) (by rfl) (by simp [l3,l2,l1,put,write,table,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags])
    apply X86Routine.Prefix.step (middle := ⟨loadedHead s,none,0x2c5ce⟩) (by simp) (by rfl) (by simp [loadedHead,l3,l2,l1,head,table,index,X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,put,write])
    apply X86Routine.Prefix.step (middle := ⟨loadedHead s,some (logical32 (head s)),0x2c5d0⟩) (by simp) (by rfl) (by simp [loadedHead,X86Routine.execute,X86Control.execute,put,write])
    apply X86Routine.Prefix.step (middle := lookup s) (by simp) (by rfl) (by
      by_cases h : head s=(0#32) <;> simp [lookup,X86Routine.execute,X86Control.execute,logical32,h])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def finishLookup (s : X86Memory.State) :=
  if head s=(0#32) then returned (lookup s).core else lookup s
def result (s : X86Memory.State) :=
  if Inside (entry s) then finishLookup (guarded (entry s)).core else returned (guarded (entry s)).core

theorem lookup_finish_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤9, X86Routine.Prefix program [] n ⟨s,f,0x2c5c0⟩ (finishLookup s) := by
  have a := lookup_execution s f
  by_cases h : head s=(0#32)
  · have b := return_execution (lookup s).core (lookup s).flags
    have pc : (lookup s).pc=0x2c5e2 := by simp [lookup,h]
    rw [OriginalPathXStep.at_pc _ _ pc] at b
    exact ⟨9,by omega,by simpa only [finishLookup,if_pos h] using OriginalGroupBounds.prefix_join a b⟩
  · exact ⟨6,by omega,by simpa only [finishLookup,if_neg h] using a⟩

/-- Bounds rejection and empty lists return true; a nonempty list stops just
before moving the first object pointer into the callback argument. -/
theorem execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤20, X86Routine.Prefix program [] n ⟨s,f,0x2c5a0⟩ (result s) := by
  have a := entry_execution s f
  obtain ⟨n,hn,b⟩ := guard_execution (entry s) none
  have ab := OriginalGroupBounds.prefix_join a b
  by_cases h : Inside (entry s)
  · obtain ⟨m,hm,c⟩ := lookup_finish_execution (guarded (entry s)).core (guarded (entry s)).flags
    have pc : (guarded (entry s)).pc=0x2c5c0 := by rw [guarded_pc,if_pos h]
    rw [OriginalPathXStep.at_pc _ _ pc] at c
    exact ⟨2+n+m,by omega,by simpa only [result,if_pos h] using OriginalGroupBounds.prefix_join ab c⟩
  · have c := return_execution (guarded (entry s)).core (guarded (entry s)).flags
    have pc : (guarded (entry s)).pc=0x2c5e2 := by rw [guarded_pc,if_neg h]
    rw [OriginalPathXStep.at_pc _ _ pc] at c
    exact ⟨2+n+3,by omega,by simpa only [result,if_neg h] using OriginalGroupBounds.prefix_join ab c⟩


/-- Only the callback slot is written. Stack wraparound is intentional. -/
theorem entry_frame (s : X86Memory.State) (a : Word) (safe : Apart a (s.regs 4-(4#32))) :
    load32 (entry s).memory a=load32 s.memory a := load_store_apart _ _ _ _ safe

theorem guard_frame (s : X86Memory.State) :
    (guarded s).core.memory=s.memory ∧ (guarded s).core.regs 4=s.regs 4 := by
  unfold guarded
  split <;> (try split) <;> (try split) <;> simp [loaded,put,write]

theorem entry_coordinates (s : X86Memory.State) :
    (entry s).regs 0=s.regs 0 ∧ (entry s).regs 2=s.regs 2 ∧ (entry s).regs 4=s.regs 4-(4#32) := by
  simp [entry,allocated,put,write]

structure Inputs (s : X86Memory.State) (x y : Int32) (w h : Nat) : Prop where
  mapX : s.regs 0=x.toBitVec
  mapY : s.regs 2=y.toBitVec
  width : load32 s.memory 0x2c0fc=BitVec.ofNat 32 w
  height : load32 s.memory 0x2c110=BitVec.ofNat 32 h
  widthBound : w<2147483648
  heightBound : h<2147483648
  safe : ∀ a∈[(0x2c0fc#32),0x2c110], Apart a (s.regs 4-(4#32))

theorem live_bounds (s : X86Memory.State) (x y : Int32) (w h : Nat) (encoding : Inputs s x y w h) :
    Inside (entry s) ↔ Collision.pathCellInside x y w h=true := by
  unfold Inside width height
  rw [(entry_coordinates s).1,(entry_coordinates s).2.1,
    entry_frame s _ (encoding.safe _ (by simp)),entry_frame s _ (encoding.safe _ (by simp)),
    encoding.mapX,encoding.mapY,encoding.width,encoding.height,
    OriginalLineBounds.dimension_int _ encoding.widthBound,OriginalLineBounds.dimension_int _ encoding.heightBound]
  simp [Collision.pathCellInside,and_assoc]

theorem inside_state (s : X86Memory.State) (inside : Inside s) :
    (guarded s).core=loaded s := by
  rcases inside with ⟨hx,hy,hw,hh⟩
  simp [guarded,show ¬(s.regs 0).toInt<0 by omega,show ¬(s.regs 2).toInt<0 by omega,
    show ¬(width s).toInt≤(s.regs 0).toInt by omega,show ¬(height s).toInt≤(s.regs 2).toInt by omega]

theorem result_memory (s : X86Memory.State) : (result s).core.memory=(entry s).memory := by
  simp only [result,finishLookup,lookup,returned,r2,r1,loadedHead,l3,l2,l1,put]
  split <;> (try split) <;> exact (guard_frame (entry s)).1

theorem frame (s : X86Memory.State) (a : Word) (safe : Apart a (s.regs 4-(4#32))) :
    load32 (result s).core.memory a=load32 s.memory a := by
  rw [result_memory]; exact entry_frame s a safe

theorem return_word (s : X86Memory.State) :
    load32 (entry s).memory (s.regs 4)=load32 s.memory (s.regs 4) := by
  apply entry_frame
  simpa [BitVec.sub_eq_add_neg] using OriginalPathXStep.apart_translate (s.regs 4) 0 (-(4#32)) (by unfold Apart; decide)

theorem outside_return (s : X86Memory.State) (outside : ¬Inside (entry s)) :
    (result s).core.regs 0=(1#32) ∧ (result s).core.regs 4=s.regs 4+(4#32) ∧
    (result s).pc=(load32 s.memory (s.regs 4)).toNat := by
  simp only [result,if_neg outside,returned,r2,r1,put,write]
  simp only [(guard_frame (entry s)).1,(guard_frame (entry s)).2,(entry_coordinates s).2.2]
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc,return_word]

/-- First object lookup is a word-pointer table, indexed by x + y*width. -/
theorem live_head (s : X86Memory.State) (x y : Int32) (w h : Nat) (encoding : Inputs s x y w h)
    (inside : Collision.pathCellInside x y w h=true) (links object : Word)
    (global : load32 s.memory (0x2c0f8#32)=links)
    (selected : load32 s.memory (links+(BitVec.ofNat 32 (Collision.pathCellIndex x y w) <<< 2))=object)
    (globalSafe : Apart (0x2c0f8#32) (s.regs 4-(4#32)))
    (headSafe : Apart (links+(BitVec.ofNat 32 (Collision.pathCellIndex x y w) <<< 2)) (s.regs 4-(4#32))) :
    head (guarded (entry s)).core=object := by
  have ins := (live_bounds s x y w h encoding).mpr inside
  rw [inside_state _ ins]
  have wreg : (loaded (entry s)).regs 3=BitVec.ofNat 32 w := by
    change load32 (entry s).memory (0x2c0fc#32)=_
    exact (entry_frame s _ (encoding.safe _ (by simp))).trans encoding.width
  have nonneg := inside
  simp only [Collision.pathCellInside,Bool.and_eq_true,decide_eq_true_eq] at nonneg
  have idx := OriginalLineCell.live_index (loaded (entry s)) x y w nonneg.1.1.1 nonneg.1.1.2
    (by simpa [loaded,entry,allocated,put,write] using encoding.mapX) (by simpa [loaded,entry,allocated,put,write] using encoding.mapY) wreg
  change index (loaded (entry s))=BitVec.ofNat 32 (Collision.pathCellIndex x y w) at idx
  unfold head
  rw [idx]
  change load32 (entry s).memory (load32 (entry s).memory (0x2c0f8#32)+_) = _
  rw [entry_frame s _ globalSafe,global,entry_frame s _ headSafe,selected]

theorem nonempty (s : X86Memory.State) (inside : Inside (entry s))
    (present : head (guarded (entry s)).core≠(0#32)) :
    (result s).pc=0x2c5d2 ∧ (result s).core.regs 2=head (guarded (entry s)).core ∧
    (result s).core.regs 4=s.regs 4-(4#32) ∧
    load32 (result s).core.memory ((result s).core.regs 4)=s.regs 3 := by
  simp only [result,if_pos inside,finishLookup,if_neg present,lookup,loadedHead,l3,l2,l1,put,write]
  simp only [ite_true,ite_false,(guard_frame (entry s)).1,(guard_frame (entry s)).2,(entry_coordinates s).2.2]
  exact ⟨trivial,trivial,rfl,load_store _ _ _⟩

theorem empty_return (s : X86Memory.State) (inside : Inside (entry s))
    (empty : head (guarded (entry s)).core=(0#32)) :
    (result s).core.regs 0=(1#32) ∧ (result s).core.regs 4=s.regs 4+(4#32) ∧
    (result s).pc=(load32 s.memory (s.regs 4)).toNat := by
  simp only [result,if_pos inside,finishLookup,if_pos empty,returned,r2,r1,lookup,loadedHead,l3,l2,l1,put,write]
  simp only [ite_true,ite_false,(guard_frame (entry s)).1,(guard_frame (entry s)).2,(entry_coordinates s).2.2]
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc,return_word]

end Doom.Proofs.OriginalThingEntry
