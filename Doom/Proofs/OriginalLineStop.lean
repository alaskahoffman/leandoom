import Doom.Proofs.OriginalLineReject
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.OriginalLineStop
open Verification X86 X86Memory X86Control BlockSummary
abbrev program := OriginalLineDispatch.program
abbrev tested (s : X86Memory.State) := OriginalLineCrossing.tested (OriginalLineDispatch.entry s).core
abbrev finished (s : X86Memory.State) := OriginalLineTail.finished (tested s).core
abbrev result := OriginalLineDispatch.result

def Stops (frac : Fixed) (flags : Nat) (line : Collision.Line) : Prop :=
  ¬frac.raw<0 ∧ (flags &&& 4 != 0 && frac.raw<65536 && line.back.isNone)=true

variable (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
  (frac : Fixed) (flags : Nat) (p v w : Word)
  (h : OriginalLineDispatch.Ready s trace line frac flags p v w) (stop : Stops frac flags line)
include h stop

theorem zero : (finished s).core.regs 0=(0#32) := by
  have k := OriginalLineTail.live_value (tested s).core trace line frac flags p v
    (OriginalLineCrossing.ready (OriginalLineDispatch.entry s).core trace line p v w
      (OriginalLineDispatch.crossing_inputs s trace line p v w h.geometry h.geometrySafe) frac flags
      (OriginalLineDispatch.tail_inputs s trace line frac flags p v h.fresh h.tail))
  simp only [if_neg stop.1,stop.2,ite_true] at k
  exact k.trans (show (0 : Word)=(0#32) by decide)

omit stop

theorem finish_stack : (finished s).core.regs 4=s.regs 4 := by
  rw [finished,OriginalLineTail.finished,OriginalLineFinish.result_sp,
    (OriginalLineFraction.returned (tested s).core).2.1,
    (OriginalLineCrossing.tested_regs (OriginalLineDispatch.entry s).core trace line p v w
      (OriginalLineDispatch.crossing_inputs s trace line p v w h.geometry h.geometrySafe)).2.1,
    (OriginalLineDispatch.entry_regs s).2.2]
  bv_decide

include stop

theorem observed : (result s).core.regs 0=(0#32) ∧
    (result s).core.regs 4=s.regs 4+(12#32) ∧
    (result s).core.regs 7=load32 (result s).core.memory (s.regs 4+(4#32)) ∧
    (result s).pc=(load32 (result s).core.memory (s.regs 4+(8#32))).toNat := by
  have k := OriginalLineResume.stopped (finished s).core (zero s trace line frac flags p v w h stop)
  rw [finish_stack s trace line frac flags p v w h] at k
  have eq : result s=OriginalLineResume.result (finished s).core := rfl
  rw [eq,OriginalLineResume.memory]
  exact k

/-- The stop path returns through the iterator's original saved frame when the
frame words are protected across dispatch and the callback. -/
theorem parent_return
    (dispatch : ∀ a∈[s.regs 4+(4#32),s.regs 4+(8#32)], OriginalLineDispatch.Safe s a)
    (safe : ∀ a∈[s.regs 4+(4#32),s.regs 4+(8#32)],
      OriginalLineCrossing.Protected (OriginalLineDispatch.view s) a) :
    (result s).core.regs 0=(0#32) ∧ (result s).core.regs 4=s.regs 4+(12#32) ∧
    (result s).core.regs 7=load32 s.memory (s.regs 4+(4#32)) ∧
    (result s).pc=(load32 s.memory (s.regs 4+(8#32))).toNat := by
  have k := observed s trace line frac flags p v w h stop
  rw [OriginalLineDispatch.frame s trace line frac flags p v w h _ (dispatch _ (by simp)) (safe _ (by simp)),
    OriginalLineDispatch.frame s trace line frac flags p v w h _ (dispatch _ (by simp)) (safe _ (by simp))] at k
  exact k

end Doom.Proofs.OriginalLineStop
