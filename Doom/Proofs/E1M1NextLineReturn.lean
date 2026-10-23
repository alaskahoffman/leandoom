import Doom.Proofs.E1M1FiringNextLines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1NextLineReturn
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanContracts (LineData candidates)
open E1M1NextCallbackReady (Ready)
open OriginalLineMixedInvariant (Initial)
attribute [local irreducible] load32

section Scan
variable (s : X86Memory.State) (sp cursor lines : Word) (objects : Nat → Word)
    (trace : Collision.Divline) (c : E1M1PathMap.Cell) (data : Nat → LineData)
    (stack : s.regs 4=sp-(124#32)) (list : s.regs 2=cursor)
    (items : E1M1PathMapLookup.ScanWords s lines c)
    (ids : ∀ i : Fin c.ids.length, c.ids[i.val]<475)
    (ready : Ready s lines trace c data)
    (layout : E1M1ScanContracts.Layout sp cursor lines c.ids.length (candidates trace lines c.ids data))
include stack list items ids ready layout


/-- Extend protection without changing the executed candidate list or result. -/
def extended (extra : List Word)
    (safe : ∀ a∈extra, E1M1ThingGeometry.ScanSafe sp lines a) :
    Initial s c.ids.length 0x2ba20 (E1M1ThingFinish.resolve lines objects) := by
  apply E1M1ScanReturn.protect _ _ _ _
    (E1M1NextLineScan.initial s sp cursor lines objects trace c data stack list items ids ready layout)
    extra _ (fun a ha => (safe a ha).array)
  intro i hi a ha
  exact E1M1ScanContracts.protection s sp lines stack i _ (ids ⟨i,hi⟩)
    (items.pointers ⟨i,hi⟩ (Fixed.ofInt 0)) a (safe a ha).scan

/-- Preserve arbitrary additional data under initial address separation. -/
theorem read_word (f : Option Flags) (r : Collision.PathResult)
    (tracked : OriginalLineCollection.Tracks s 0x2ba20 (E1M1ThingFinish.resolve lines objects) r.collected c.ids.length)
    (a : Word) (safe : E1M1ThingGeometry.ScanSafe sp lines a) :
    load32 (E1M1NextLineScan.result s lines trace c data f r).1.core.memory a=load32 s.memory a := by
  let h := extended s sp cursor lines objects trace c data stack list items ids ready layout [a]
    (fun b hb => by
      have eq : b=a := by simpa using hb
      subst b
      exact safe)
  have keep : ∀ j<c.ids.length, (h.candidates j).crosses=true → (h.candidates j).Continues := by
    intro j _ _; exact E1M1ScanContracts.candidate_continues trace lines c.ids[j]! (data j)
  have frame := (OriginalLineMixedInvariant.through_sentinel s c.ids.length 0x2ba20
    (E1M1ThingFinish.resolve lines objects) h r f tracked keep items.sentinel).2.2.2
  exact frame a (List.mem_append_right _ (by simp))

/-- Protect the real saved EDI and return address across every callback. -/
theorem parent_return (returns : E1M1ScanReturn.ReturnSafe sp lines) (f : Option Flags)
    (r : Collision.PathResult)
    (tracked : OriginalLineCollection.Tracks s 0x2ba20 (E1M1ThingFinish.resolve lines objects) r.collected c.ids.length) :
    let out := (E1M1NextLineScan.result s lines trace c data f r).1
    out.core.regs 0=(1#32) ∧ out.core.regs 4=sp-(112#32) ∧
    out.core.regs 7=load32 s.memory (sp-(120#32)) ∧
    out.pc=(load32 s.memory (sp-(116#32))).toNat := by
  let h := extended s sp cursor lines objects trace c data stack list items ids ready layout
    (E1M1ScanReturn.returnWords sp) (fun a ha =>
      ⟨E1M1ScanReturn.stack_protected sp lines a ha (returns.stamps a ha),returns.array a ha⟩)
  have keep : ∀ j<c.ids.length, (h.candidates j).crosses=true → (h.candidates j).Continues := by
    intro j _ _; exact E1M1ScanContracts.candidate_continues trace lines c.ids[j]! (data j)
  have member (off : Word) (ho : off∈[(4#32),8]) : s.regs 4+off∈h.words := by
    apply List.mem_append_right
    rw [stack]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl <;> simp [E1M1ScanReturn.returnWords,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have ret := OriginalLineMixedInvariant.parent_return s c.ids.length 0x2ba20
    (E1M1ThingFinish.resolve lines objects) h r f tracked keep (member 4 (by simp)) (member 8 (by simp))
  have same : OriginalLineMixedInvariant.finished s c.ids.length 0x2ba20
      (E1M1ThingFinish.resolve lines objects) h f r=E1M1NextLineScan.result s lines trace c data f r := rfl
  rw [same] at ret
  simpa [stack,BitVec.sub_eq_add_neg,BitVec.add_assoc] using ret

/-- The object-enable option survives the complete next line scan. -/
theorem flag_word (flag : E1M1ThingGate.FlagSafe sp lines) (f : Option Flags)
    (r : Collision.PathResult)
    (tracked : OriginalLineCollection.Tracks s 0x2ba20 (E1M1ThingFinish.resolve lines objects) r.collected c.ids.length)
    (value : load32 s.memory (E1M1ThingGate.flagWord sp)=(3#32)) :
    load32 (E1M1NextLineScan.result s lines trace c data f r).1.core.memory (E1M1ThingGate.flagWord sp)=(3#32) :=
  (read_word s sp cursor lines objects trace c data stack list items ids ready layout f r tracked _
    ⟨E1M1ThingGate.flag_protected sp lines flag.stamps,flag.array⟩).trans value
end Scan
end Doom.Proofs.E1M1NextLineReturn
