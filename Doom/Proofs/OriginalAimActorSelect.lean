import Doom.Proofs.E1M1AimActorBottomCycle
import Doom.Proofs.OriginalPlayerBob
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalAimActorSelect
open Verification X86 X86Memory X86Control BlockSummary Collision
attribute [local irreducible] load32 store32
def code : List UInt8 := [0x39,0xde,0x7e,0x2,0x89,0xdf,0x8b,0x15,0xe4,0xc1,0x2,0x0,0x39,0xd0,0x7d,0x2,0x89,0xd0,0x8d,0x14,0x7,0x89,0xd0,0xc1,0xfa,0x1f,0x2b,0xc2,0xd1,0xf8,0x89,0xd,0xf8,0xb9,0x2,0x0,0xa3,0xb4,0xb9,0x2,0x0]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2b8a9≤pc ∧ pc<0x2b8d2 then X86Routine.decodeAt bytes (pc-0x2b8a9) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2b8a9 => some (.compareRegisters 6 3,2)
  | 0x2b8ab => some (.jumpSigned 1 2,2)
  | 0x2b8ad => some (.control (.block (.legacy (.mov 7 3))),2)
  | 0x2b8af => some (.control (.block (.load 2 ⟨none,none,0,0x2c1e4⟩)),6)
  | 0x2b8b5 => some (.compareRegisters 0 2,2)
  | 0x2b8b7 => some (.jumpSigned 0 2,2)
  | 0x2b8b9 => some (.control (.block (.legacy (.mov 0 2))),2)
  | 0x2b8bb => some (.control (.block (.lea 2 ⟨some 7,some 0,0,0⟩)),3)
  | 0x2b8be => some (.control (.block (.legacy (.mov 0 2))),2)
  | 0x2b8c0 => some (.sar 2 31,3)
  | 0x2b8c3 => some (.control (.block (.arithmetic (.sub 0 2))),2)
  | 0x2b8c5 => some (.sar 0 1,2)
  | 0x2b8c7 => some (.control (.block (.store ⟨none,none,0,0x2b9f8⟩ 1)),6)
  | 0x2b8cd => some (.control (.storeEax 0x2b9b4),5)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def topClip (s : X86Memory.State) := if (s.regs 6).toInt≤(s.regs 3).toInt then s else put s 7 (s.regs 3)
def topFlags (s : X86Memory.State) := some (compare32 (s.regs 6) (s.regs 3))
def lower (s : X86Memory.State) := load32 s.memory (0x2c1e4#32)
def loaded (s : X86Memory.State) := put s 2 (lower s)
def bottomClip (s : X86Memory.State) :=
  if (s.regs 0).toInt<(lower s).toInt then put (loaded s) 0 (lower s) else loaded s
def bottomFlags (s : X86Memory.State) := some (compare32 (s.regs 0) (lower s))
def clipped (s : X86Memory.State) := bottomClip (topClip s)
def sum (s : X86Memory.State) := s.regs 7+s.regs 0
def c1 (s : X86Memory.State) := put s 2 (sum s)
def c2 (s : X86Memory.State) := put (c1 s) 0 (sum s)
def c3 (s : X86Memory.State) := put (c2 s) 2 ((sum s).sshiftRight 31)
def c4 (s : X86Memory.State) := put (c3 s) 0 (sum s-(sum s).sshiftRight 31)
def half (s : X86Memory.State) := (sum s-(sum s).sshiftRight 31).sshiftRight 1
def c5 (s : X86Memory.State) := put (c4 s) 0 (half s)
def c6 (s : X86Memory.State) : X86Memory.State :=
  {c5 s with memory:=store32 s.memory 0x2b9f8 (s.regs 1)}
def finish (s : X86Memory.State) : X86Control.State :=
  ⟨{c6 s with memory:=store32 (c6 s).memory 0x2b9b4 (half s)},none,0x2b8d2⟩
def result (s : X86Memory.State) := finish (clipped s)

/-- Signed minimum for the target's top, retaining the saved copy on equality. -/
theorem top_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤3, X86Routine.Prefix program [] n ⟨s,f,0x2b8a9⟩ ⟨topClip s,topFlags s,0x2b8af⟩ := by
  have run : ∃ n≤3, X86Routine.Prefix listed [] n ⟨s,f,0x2b8a9⟩ ⟨topClip s,topFlags s,0x2b8af⟩ := by
    by_cases le : (s.regs 6).toInt≤(s.regs 3).toInt
    · refine ⟨2,by omega,?_⟩
      apply X86Routine.Prefix.step (middle := ⟨s,topFlags s,0x2b8ab⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,topClip,topFlags,lower,loaded,bottomClip,bottomFlags,sum,c1,c2,c3,c4,half,c5,c6,finish,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,le])
      apply X86Routine.Prefix.step (middle := ⟨topClip s,topFlags s,0x2b8af⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,topClip,topFlags,lower,loaded,bottomClip,bottomFlags,sum,c1,c2,c3,c4,half,c5,c6,finish,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,le])
      exact .nil _
    · refine ⟨3,by omega,?_⟩
      apply X86Routine.Prefix.step (middle := ⟨s,topFlags s,0x2b8ab⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,topClip,topFlags,lower,loaded,bottomClip,bottomFlags,sum,c1,c2,c3,c4,half,c5,c6,finish,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,le])
      apply X86Routine.Prefix.step (middle := ⟨s,topFlags s,0x2b8ad⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,topClip,topFlags,lower,loaded,bottomClip,bottomFlags,sum,c1,c2,c3,c4,half,c5,c6,finish,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,le])
      apply X86Routine.Prefix.step (middle := ⟨topClip s,topFlags s,0x2b8af⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,topClip,topFlags,lower,loaded,bottomClip,bottomFlags,sum,c1,c2,c3,c4,half,c5,c6,finish,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,le])
      exact .nil _
  obtain ⟨n,hn,run⟩ := run
  exact ⟨n,hn,run.transfer program [] decoded (by simp)⟩

/-- Signed maximum for the bottom, reading the current lower aim bound. -/
theorem bottom_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤4, X86Routine.Prefix program [] n ⟨s,f,0x2b8af⟩ ⟨bottomClip s,bottomFlags s,0x2b8bb⟩ := by
  have run : ∃ n≤4, X86Routine.Prefix listed [] n ⟨s,f,0x2b8af⟩ ⟨bottomClip s,bottomFlags s,0x2b8bb⟩ := by
    by_cases lt : (s.regs 0).toInt<(lower s).toInt
    · simp only [lower] at lt
      refine ⟨4,by omega,?_⟩
      apply X86Routine.Prefix.step (middle := ⟨loaded s,f,0x2b8b5⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,topClip,topFlags,lower,loaded,bottomClip,bottomFlags,sum,c1,c2,c3,c4,half,c5,c6,finish,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,lt])
      apply X86Routine.Prefix.step (middle := ⟨loaded s,bottomFlags s,0x2b8b7⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,topClip,topFlags,lower,loaded,bottomClip,bottomFlags,sum,c1,c2,c3,c4,half,c5,c6,finish,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,lt])
      apply X86Routine.Prefix.step (middle := ⟨loaded s,bottomFlags s,0x2b8b9⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,topClip,topFlags,lower,loaded,bottomClip,bottomFlags,sum,c1,c2,c3,c4,half,c5,c6,finish,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,lt])
      apply X86Routine.Prefix.step (middle := ⟨bottomClip s,bottomFlags s,0x2b8bb⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,topClip,topFlags,lower,loaded,bottomClip,bottomFlags,sum,c1,c2,c3,c4,half,c5,c6,finish,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,lt])
      exact .nil _
    · simp only [lower] at lt
      refine ⟨3,by omega,?_⟩
      apply X86Routine.Prefix.step (middle := ⟨loaded s,f,0x2b8b5⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,topClip,topFlags,lower,loaded,bottomClip,bottomFlags,sum,c1,c2,c3,c4,half,c5,c6,finish,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,lt])
      apply X86Routine.Prefix.step (middle := ⟨loaded s,bottomFlags s,0x2b8b7⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,topClip,topFlags,lower,loaded,bottomClip,bottomFlags,sum,c1,c2,c3,c4,half,c5,c6,finish,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,lt])
      apply X86Routine.Prefix.step (middle := ⟨bottomClip s,bottomFlags s,0x2b8bb⟩) (by simp) (by rfl) (by
        simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,topClip,topFlags,lower,loaded,bottomClip,bottomFlags,sum,c1,c2,c3,c4,half,c5,c6,finish,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge,lt])
      exact .nil _
  obtain ⟨n,hn,run⟩ := run
  exact ⟨n,hn,run.transfer program [] decoded (by simp)⟩

/-- Wrapped addition, signed division toward zero, target and slope stores. -/
theorem finish_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 7 ⟨s,f,0x2b8bb⟩ (finish s) := by
  have run : X86Routine.Prefix listed [] 7 ⟨s,f,0x2b8bb⟩ (finish s) := by
    apply X86Routine.Prefix.step (middle := ⟨c1 s,f,0x2b8be⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,topClip,topFlags,lower,loaded,bottomClip,bottomFlags,sum,c1,c2,c3,c4,half,c5,c6,finish,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge])
    apply X86Routine.Prefix.step (middle := ⟨c2 s,f,0x2b8c0⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,topClip,topFlags,lower,loaded,bottomClip,bottomFlags,sum,c1,c2,c3,c4,half,c5,c6,finish,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge])
    apply X86Routine.Prefix.step (middle := ⟨c3 s,none,0x2b8c3⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,topClip,topFlags,lower,loaded,bottomClip,bottomFlags,sum,c1,c2,c3,c4,half,c5,c6,finish,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge])
    apply X86Routine.Prefix.step (middle := ⟨c4 s,none,0x2b8c5⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,topClip,topFlags,lower,loaded,bottomClip,bottomFlags,sum,c1,c2,c3,c4,half,c5,c6,finish,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge])
    apply X86Routine.Prefix.step (middle := ⟨c5 s,none,0x2b8c7⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,topClip,topFlags,lower,loaded,bottomClip,bottomFlags,sum,c1,c2,c3,c4,half,c5,c6,finish,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge])
    apply X86Routine.Prefix.step (middle := ⟨c6 s,none,0x2b8cd⟩) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,topClip,topFlags,lower,loaded,bottomClip,bottomFlags,sum,c1,c2,c3,c4,half,c5,c6,finish,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge])
    apply X86Routine.Prefix.step (middle := finish s) (by simp) (by rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,topClip,topFlags,lower,loaded,bottomClip,bottomFlags,sum,c1,c2,c3,c4,half,c5,c6,finish,cmp32_signed_le,PlayerHeight.cmp_ge_prop,PlayerHeight.cmp_ge])
    exact .nil _
  exact run.transfer program [] decoded (by simp)

theorem execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤14, X86Routine.Prefix program [] n ⟨s,f,0x2b8a9⟩ (result s) := by
  obtain ⟨n,hn,first⟩ := top_execution s f
  obtain ⟨k,hk,second⟩ := bottom_execution (topClip s) (topFlags s)
  exact ⟨n+k+7,by omega,OriginalGroupBounds.prefix_join
    (OriginalGroupBounds.prefix_join first second) (finish_execution (clipped s) (bottomFlags (topClip s)))⟩
end Doom.Proofs.OriginalAimActorSelect
