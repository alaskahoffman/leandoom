import Doom.Proofs.OriginalLineInvariant
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.OriginalLineDispatchAppend
open Verification X86 X86Memory X86Control BlockSummary

/-- Transport the represented ordered array across the real stamp and CALL.
No array facts are assumed in the post-dispatch memory. -/
theorem entry_encodes (s : X86Memory.State) (base : Word) (resolve : Collision.Intercept → Word)
    (hits : Array Collision.Intercept) (encoded : OriginalLineFinish.Encodes s.memory base resolve hits)
    (safe : ∀ i<hits.size, ∀ off∈[(0#32),4,8],
      OriginalLineDispatch.Safe s (base+BitVec.ofNat 32 (12*i)+off)) :
    OriginalLineFinish.Encodes (OriginalLineDispatch.entry s).core.memory base resolve hits := by
  intro i hi
  have keep (off : Word) (ho : off∈[(0#32),4,8]) :=
    OriginalLineDispatch.entry_frame s (base+BitVec.ofNat 32 (12*i)+off) (safe i hi off ho)
  have old := encoded i hi
  unfold OriginalLineFinish.RecordAt at old ⊢
  rw [show load32 (OriginalLineDispatch.entry s).core.memory (base+BitVec.ofNat 32 (12*i))=
      load32 s.memory (base+BitVec.ofNat 32 (12*i)) by simpa using keep 0 (by simp),
    keep (4#32) (by simp),keep (8#32) (by simp)]
  exact old

/-- Original append correspondence starts at the iterator header, before the
stamp, indirect CALL, side tests and fraction helper. -/
theorem live_append (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (frac : Fixed) (flags : Nat) (p v w : Word)
    (h : OriginalLineDispatch.Ready s trace line frac flags p v w)
    (r : Collision.PathResult) (id : Nat) (base : Word) (resolve : Collision.Intercept → Word)
    (nonnegative : ¬frac.raw<0) (clear : (flags &&& 4 != 0 && frac.raw<65536 && line.back.isNone)=false)
    (capacity : r.collected.size<128)
    (encoded : OriginalLineFinish.Encodes s.memory base resolve r.collected)
    (atEnd : OriginalLineFinish.cursor s=base+BitVec.ofNat 32 (12*r.collected.size))
    (pointer : resolve ⟨frac,true,id⟩=p)
    (newSafe : ∀ off∈[(0#32),4,8], Apart (OriginalLineFinish.cursor s+off) (0x2c028#32))
    (oldDispatch : ∀ i<r.collected.size, ∀ off∈[(0#32),4,8],
      OriginalLineDispatch.Safe s (base+BitVec.ofNat 32 (12*i)+off))
    (oldSafe : ∀ i<r.collected.size, ∀ off∈[(0#32),4,8],
      OriginalLineCrossing.Protected (OriginalLineDispatch.view s) (base+BitVec.ofNat 32 (12*i)+off)) :
    Collision.appendIntercept r ⟨frac,true,id⟩=.ok {r with collected:=r.collected.push ⟨frac,true,id⟩} ∧
    OriginalLineFinish.Encodes (OriginalLineDispatch.result s).core.memory base resolve (r.collected.push ⟨frac,true,id⟩) ∧
    load32 (OriginalLineDispatch.result s).core.memory (0x2c028#32)=base+BitVec.ofNat 32 (12*(r.collected.size+1)) := by
  have cursor := h.tail.dispatchSafe (0x2c028#32) (by simp)
  have eq : OriginalLineFinish.cursor (OriginalLineDispatch.entry s).core=OriginalLineFinish.cursor s :=
    OriginalLineDispatch.entry_frame s _ cursor
  apply OriginalLineCrossing.live_append (OriginalLineDispatch.entry s).core trace line p v w
    (OriginalLineDispatch.crossing_inputs s trace line p v w h.geometry h.geometrySafe) frac flags
    (OriginalLineDispatch.tail_inputs s trace line frac flags p v h.fresh h.tail) r id base resolve
  · exact nonnegative
  · exact clear
  · exact capacity
  · exact entry_encodes s base resolve r.collected encoded oldDispatch
  · exact eq.trans atEnd
  · exact pointer
  · simpa only [eq] using newSafe
  · intro i hi off ho
    have protect := oldSafe i hi off ho
    exact ⟨protect.1,protect.2.1,OriginalLineDispatch.record_safe s _ cursor protect.2.2⟩

end Doom.Proofs.OriginalLineDispatchAppend
