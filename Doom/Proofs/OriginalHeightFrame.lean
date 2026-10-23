import Doom.Proofs.OriginalPlayerBob

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
namespace Doom.Proofs.PlayerHeight
open Verification X86 X86Memory X86Control BlockSummary

/-- Unchanged four-byte reads outside the block's writes, including unaligned
and wrapping addresses. This is the frame information needed at block seams. -/
def Frame (before after : Memory) (writes : List Word) : Prop :=
  ∀ a, (∀ b, b ∈ writes → Apart a b) → load32 after a = load32 before a

theorem load_byte (m : Memory) (a : Word) :
    (load32 m a).extractLsb' 0 8 = m a := by
  simp only [load32]
  bv_decide

theorem Frame.byte {m m' : Memory} {writes : List Word} (h : Frame m m' writes)
    (a : Word) (safe : ∀ b, b ∈ writes → Apart a b) : m' a = m a := by
  have eq := congrArg (fun v : Word => v.extractLsb' 0 8) (h a safe)
  simpa only [load_byte] using eq

theorem amplitude_frame (s : X86Memory.State) (f : Option Flags)
    (a : Word) (safe : ∀ b, b ∈ [s.regs 0+(28#32)] → Apart a b) :
    (X86Routine.run program [64] 20 ⟨s,f,6⟩).map (fun t => load32 t.core.memory a) =
      some (load32 s.memory a) := by
  have keep28 (m : Memory) (v : Word) : load32 (store32 m (s.regs 0+(28#32)) v) a = load32 m a :=
    load_store_apart _ _ _ _ (safe _ (by simp))
  by_cases h : ((bobSum s).sshiftRight 2).toInt ≤ 1048576 <;>
    simp only [bobSum] at h <;>
    simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86.execute,X86Block.Address.eval,put,write,eax,ebx,edx,blockPreservesFlags,
      multiply,load_store,keep28,cmp32_signed_le,bobSum,amplitudeWord,h,
      -BitVec.toInt_add,-BitVec.toInt_sub,-BitVec.toInt_sshiftRight]

theorem recovery_frame (s : X86Memory.State) (f : Option Flags)
    (live : s.regs 5 = 0)
    (a : Word) (safe : ∀ b, b ∈ [s.regs 1+(20#32),s.regs 1+(24#32)] → Apart a b) :
    (X86Routine.run program [263] 30 ⟨s,f,177⟩).map (fun t => load32 t.core.memory a) =
      some (load32 s.memory a) := by
  have keep20 (m : Memory) (v : Word) : load32 (store32 m (s.regs 1+(20#32)) v) a = load32 m a :=
    load_store_apart _ _ _ _ (safe _ (by simp))
  have keep24 (m : Memory) (v : Word) : load32 (store32 m (s.regs 1+(24#32)) v) a = load32 m a :=
    load_store_apart _ _ _ _ (safe _ (by simp))
  by_cases high : (load32 s.memory (s.regs 1+(20#32)) + load32 s.memory (s.regs 1+(24#32))).toInt ≤ 2686976 <;>
    by_cases low : (load32 s.memory (s.regs 1+(20#32)) + load32 s.memory (s.regs 1+(24#32))).toInt < 1343488 <;>
    by_cases positive : 0 < (load32 s.memory (s.regs 1+(24#32))).toInt <;>
    have lower : (1343488 ≤ (load32 s.memory (s.regs 1+(20#32)) + load32 s.memory (s.regs 1+(24#32))).toInt) ↔
      ¬ (load32 s.memory (s.regs 1+(20#32)) + load32 s.memory (s.regs 1+(24#32))).toInt < 1343488 := by omega
  all_goals have nonpos : (load32 s.memory (s.regs 1+(24#32))).toInt ≤ 0 ↔
      ¬ 0 < (load32 s.memory (s.regs 1+(24#32))).toInt := by omega
  all_goals simp [X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,
    live,load_store,keep20,keep24,cmp32_signed_le,cmp_ge,cmp_ge_prop,logical_le,logical_gt,recover,high,low,positive,lower,nonpos,-BitVec.toInt_add]
  all_goals by_cases zero : load32 s.memory (s.regs 1+(24#32)) = (0#32) <;>
    by_cases cancel : load32 s.memory (s.regs 1+(24#32)) + (16384#32) = (0#32) <;>
    simp [zero,cancel,X86Routine.execute,X86Control.execute,X86Block.execute,
      X86Memory.execute,X86.execute,X86Block.Address.eval,put,write,blockPreservesFlags,
      load_store,keep20,keep24,-BitVec.toInt_add]

theorem ceiling_frame (s : X86Memory.State) (f : Option Flags)
    (a : Word) (safe : ∀ b, b ∈ [s.regs 1+(16#32)] → Apart a b) :
    (X86Routine.run program [295] 12 ⟨s,f,263⟩).map (fun t => load32 t.core.memory a) =
      some (load32 s.memory a) := by
  have keep16 (m : Memory) (v : Word) : load32 (store32 m (s.regs 1+(16#32)) v) a = load32 m a :=
    load_store_apart _ _ _ _ (safe _ (by simp))
  simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
    X86.execute,X86Block.Address.eval,put,write,eax,blockPreservesFlags,load_store,keep16,
    cmp_ge_prop,-BitVec.toInt_add,-BitVec.toInt_sub]
  split <;> simp [X86Routine.execute,X86Control.execute,X86Block.execute,
    X86Block.Address.eval,put,write,eax,load_store,keep16,blockPreservesFlags]

end Doom.Proofs.PlayerHeight
