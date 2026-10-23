import Doom.Proofs.E1M1MinimumScan
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalInterceptGate
open Verification X86 X86Memory X86Control BlockSummary
attribute [local irreducible] load32 store32
def code : List UInt8 := [0x89,0xd,0x28,0xc0,0x2,0x0,0x39,0xfa,0x7f,0x1f,0x89,0xd8,0xff,0x14,0x24,0x85,0xc0,0x75,0x8,0x8b,0xd,0x28,0xc0,0x2,0x0,0xeb,0x13,0x8b,0xd,0x28,0xc0,0x2,0x0,0xc7,0x3,0xff,0xff,0xff,0x7f,0xeb,0xb3]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c85e≤pc ∧ pc<0x2c887 then X86Routine.decodeAt bytes (pc-0x2c85e) else none
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2c85e => some (.control (.block (.store ⟨none,none,0,0x2c028⟩ 1)),6)
  | 0x2c864 => some (.compareRegisters 2 7,2)
  | 0x2c866 => some (.jumpSigned 2 31,2)
  | 0x2c868 => some (.control (.block (.legacy (.mov 0 3))),2)
  | 0x2c86a => some (.callMemory ⟨some 4,none,0,0⟩,3)
  | 0x2c86d => some (.control (.testWord 0 0),2)
  | 0x2c86f => some (.control (.jumpZero false 8),2)
  | 0x2c871 => some (.control (.block (.load 1 ⟨none,none,0,0x2c028⟩)),6)
  | 0x2c877 => some (.jump 19,2)
  | 0x2c879 => some (.control (.block (.load 1 ⟨none,none,0,0x2c028⟩)),6)
  | 0x2c87f => some (.storeImmediate ⟨some 3,none,0,0⟩ 0x7fffffff,6)
  | 0x2c885 => some (.jump (-77),2)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def saved (s : X86Memory.State) : X86Memory.State :=
  {s with memory := store32 s.memory 0x2c028 (s.regs 1)}
def beyond (s : X86Memory.State) : Prop := (s.regs 7).toInt < (s.regs 2).toInt
instance (s : X86Memory.State) : Decidable (beyond s) := inferInstanceAs (Decidable (_<_))
def gate (s : X86Memory.State) : X86Control.State :=
  ⟨saved s,some (compare32 (s.regs 2) (s.regs 7)),if beyond s then 0x2c887 else 0x2c868⟩
def called (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨X86Routine.pushWord (put s 0 (s.regs 3)) 0x2c86d,f,
    (load32 s.memory (s.regs 4)).toNat⟩
def restored (s : X86Memory.State) := put s 1 (load32 s.memory 0x2c028)
def marked (s : X86Memory.State) : X86Memory.State :=
  {restored s with memory := store32 s.memory (s.regs 3) 0x7fffffff}
def resumed (s : X86Memory.State) : X86Control.State :=
  ⟨if s.regs 0=0 then restored s else marked s,
    some (logical32 (s.regs 0)),if s.regs 0=0 then 0x2c88c else 0x2c83a⟩
def resumeSteps (s : X86Memory.State) := if s.regs 0=0 then 4 else 5

/-- Save the scan cursor and test the signed maximum fraction before touching
any selected record. Equality at the maximum is admitted. -/
theorem gate_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 3 ⟨s,f,0x2c85e⟩ (gate s) := by
  have run : X86Routine.Prefix listed [] 3 ⟨s,f,0x2c85e⟩ (gate s) := by
    by_cases h : beyond s
    ·
      apply X86Routine.Prefix.step (middle := ⟨saved s,f,0x2c864⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
          saved,beyond,gate,called,restored,marked,resumed,resumeSteps,logical32]
        all_goals split <;> simp_all)
      apply X86Routine.Prefix.step (middle := ⟨saved s,some (compare32 (s.regs 2) (s.regs 7)),0x2c866⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
          saved,beyond,gate,called,restored,marked,resumed,resumeSteps,logical32]
        all_goals split <;> simp_all)
      apply X86Routine.Prefix.step (middle := gate s) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
          saved,beyond,gate,called,restored,marked,resumed,resumeSteps,logical32]
        all_goals split <;> simp_all)
      exact .nil _
    ·
      apply X86Routine.Prefix.step (middle := ⟨saved s,f,0x2c864⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
          saved,beyond,gate,called,restored,marked,resumed,resumeSteps,logical32]
        all_goals split <;> simp_all)
      apply X86Routine.Prefix.step (middle := ⟨saved s,some (compare32 (s.regs 2) (s.regs 7)),0x2c866⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
          saved,beyond,gate,called,restored,marked,resumed,resumeSteps,logical32]
        all_goals split <;> simp_all)
      apply X86Routine.Prefix.step (middle := gate s) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
          saved,beyond,gate,called,restored,marked,resumed,resumeSteps,logical32]
        all_goals split <;> simp_all)
      exact .nil _
  exact run.transfer program [] decoded (by simp)

/-- Pass the hit pointer in EAX and execute the real indirect CALL, including
its return-address push. This stops at callee entry; it assumes no callback. -/
theorem call_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 2 ⟨s,f,0x2c868⟩ (called s f) := by
  have run : X86Routine.Prefix listed [] 2 ⟨s,f,0x2c868⟩ (called s f) := by
      apply X86Routine.Prefix.step (middle := ⟨put s 0 (s.regs 3),f,0x2c86a⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
          saved,beyond,gate,called,restored,marked,resumed,resumeSteps,logical32]
        all_goals split <;> simp_all)
      apply X86Routine.Prefix.step (middle := called s f) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
          saved,beyond,gate,called,restored,marked,resumed,resumeSteps,logical32]
        all_goals split <;> simp_all)
      exact .nil _
  exact run.transfer program [] decoded (by simp)

/-- Resume from the callback's actual return site. A false result preserves
record memory; any nonzero result marks the chosen fraction and repeats. -/
theorem resume_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] (resumeSteps s) ⟨s,f,0x2c86d⟩ (resumed s) := by
  have run : X86Routine.Prefix listed [] (resumeSteps s) ⟨s,f,0x2c86d⟩ (resumed s) := by
    by_cases h : s.regs 0=0
    · simp only [resumeSteps,h,↓reduceIte]
      apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c86f⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
          saved,beyond,gate,called,restored,marked,resumed,resumeSteps,logical32]
        all_goals split <;> simp_all)
      apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c871⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
          saved,beyond,gate,called,restored,marked,resumed,resumeSteps,logical32]
        all_goals split <;> simp_all)
      apply X86Routine.Prefix.step (middle := ⟨restored s,some (logical32 (s.regs 0)),0x2c877⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
          saved,beyond,gate,called,restored,marked,resumed,resumeSteps,logical32]
        all_goals split <;> simp_all)
      apply X86Routine.Prefix.step (middle := resumed s) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
          saved,beyond,gate,called,restored,marked,resumed,resumeSteps,logical32]
        all_goals split <;> simp_all)
      exact .nil _
    · simp only [resumeSteps,h,↓reduceIte]
      apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c86f⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
          saved,beyond,gate,called,restored,marked,resumed,resumeSteps,logical32]
        all_goals split <;> simp_all)
      apply X86Routine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x2c879⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
          saved,beyond,gate,called,restored,marked,resumed,resumeSteps,logical32]
        all_goals split <;> simp_all)
      apply X86Routine.Prefix.step (middle := ⟨restored s,some (logical32 (s.regs 0)),0x2c87f⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
          saved,beyond,gate,called,restored,marked,resumed,resumeSteps,logical32]
        all_goals split <;> simp_all)
      apply X86Routine.Prefix.step (middle := ⟨marked s,some (logical32 (s.regs 0)),0x2c885⟩) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
          saved,beyond,gate,called,restored,marked,resumed,resumeSteps,logical32]
        all_goals split <;> simp_all)
      apply X86Routine.Prefix.step (middle := resumed s) (by simp) (by rfl) (by
        simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,
          X86Block.Address.eval,put,write,blockPreservesFlags,cmp32_signed_le,
          saved,beyond,gate,called,restored,marked,resumed,resumeSteps,logical32]
        all_goals split <;> simp_all)
      exact .nil _
  exact run.transfer program [] decoded (by simp)
end Doom.Proofs.OriginalInterceptGate
