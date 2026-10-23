import Doom.Proofs.E1M1AimQueryPersistent
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimCallerCursor
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1AimSavedWords (Protect)
attribute [local irreducible] load32 store32 E1M1AimCompletedReturn.result E1M1AimTraversalReturn.result

open E1M1AimSavedCaller (slots words Image Restores slot addresses)

/-- The return chain writes the intercept cursor, but executes no callback.
It needs only separation from that write, including on an empty query. -/
def CursorSafe (base : Word) : Prop :=
  ∀ addr∈words base, Apart addr 0x2c028

theorem cursor_safe (base off : Word) (safe : CursorSafe base) (member : off∈slots) :
    Apart (base+off) 0x2c028 := by
  exact safe _ (List.mem_map.mpr ⟨off,member,rfl⟩)

/-- Restore the caller's entry-memory values using only return-chain write protection. This uses the completed real return chain, including RET 8. -/
theorem restores (start finish : X86Control.State) (base : Word)
    (image : Image start finish base) (stack : finish.core.regs 4=base)
    (protect : CursorSafe base) :
    Restores start base (E1M1AimCompletedReturn.result finish) := by
  have safe : ∀ off∈[(96#32),100,104,108,112], Apart (finish.core.regs 4+off) 0x2c028 := by
    intro off member
    rw [stack]
    exact cursor_safe base off protect (by simpa [slots] using Or.inr (Or.inr (Or.inr member)))
  obtain ⟨pc,bp,di,si,cx⟩ := E1M1AimCompletedReturn.saved_caller finish safe
  rw [stack] at pc bp di si cx
  exact ⟨(E1M1AimCompletedReturn.layout finish).1.trans (by rw [stack]),
    pc.trans (congrArg BitVec.toNat (slot start finish base 112 image (by simp [slots]))),
    bp.trans (slot start finish base 96 image (by simp [slots])),
    di.trans (slot start finish base 100 image (by simp [slots])),
    si.trans (slot start finish base 104 image (by simp [slots])),
    cx.trans (slot start finish base 108 image (by simp [slots]))⟩

/-- Join an ordered-loop prefix and its proved saved-word image to the entire
return chain. Only final stack position, not final return-word contents, remains
an endpoint obligation. The pointer-validity and source exit relation are unchanged. -/
theorem execution (initial : Array Intercept) (resolve : Intercept → Word)
    (start finish : X86Control.State) (base : Word) (steps : Nat) (answer : AimResult)
    (run : X86CodeMemory.Prefix FloorCaller.cm E1M1AimActorSelect.program [] steps start finish)
    (exit : E1M1AimHitMemory.Exit initial resolve finish answer)
    (nonnull : ∀ j<initial.size, resolve initial[j]!≠0)
    (image : Image start finish base) (stack : finish.core.regs 4=base)
    (protect : CursorSafe base)
    (first : load32 start.core.memory (base+20)=0x2cb0b)
    (second : load32 start.core.memory (base+84)=0x2bbff) :
    ∃ n≤steps+21,
      X86ReturnCleanup.Prefix FloorCaller.cm E1M1AimCompletedReturn.program [] n start (E1M1AimCompletedReturn.result finish) ∧
      (E1M1AimCompletedReturn.result finish).core.regs 0=answer.slope.raw.toBitVec ∧
      Restores start base (E1M1AimCompletedReturn.result finish) := by
  have returns := addresses start finish base image stack first second
  have safe20 : Apart (finish.core.regs 4+20) 0x2c028 := by
    rw [stack]; exact cursor_safe base 20 protect (by simp [slots])
  have safe84 : Apart (finish.core.regs 4+84) 0x2c028 := by
    rw [stack]; exact cursor_safe base 84 protect (by simp [slots])
  obtain ⟨n,bound,all⟩ := E1M1AimCompletedReturn.append start finish steps run exit.1.1 safe20 returns.1 safe84 returns.2
  exact ⟨n,bound,all,E1M1AimCompletedReturn.value initial resolve finish answer exit nonnull,
    restores start finish base image stack protect⟩
end Doom.Proofs.E1M1AimCallerCursor
