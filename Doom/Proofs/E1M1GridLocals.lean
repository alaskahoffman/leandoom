import Doom.Proofs.E1M1FiringGridRegisters
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1GridLocals
open Verification X86 X86Memory X86Control BlockSummary

def offsets : List Word := [20,24,28,32,36,40,44]
def address (sp off : Word) := sp-(112#32)+off

/-- Only address separation is assumed, never the values of initialized locals.
These obligations must ultimately come from the reachable memory layout. -/
structure Safe (sp lines : Word) : Prop where
  stamps : ∀ off∈offsets, ∀ id<475, Apart (address sp off) (OriginalLineVisits.stamp lines id)
  array : ∀ off∈offsets, OriginalLineMixedInvariant.ArraySafe 0x2ba20 (address sp off)

/-- All visitor stack writes lie below the seven grid locals, including modular
wraparound and unaligned stacks. -/
theorem below (sp off : Word) (member : off∈offsets) (i : Fin 25) :
    Apart (address sp off) (sp-BitVec.ofNat 32 (116+4*i.val)) := by
  have base : ∀ j : Fin 25, Apart (-(112#32)+off) (-BitVec.ofNat 32 (116+4*j.val)) := by
    simp only [offsets,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
  simpa [address,BitVec.sub_eq_add_neg,BitVec.add_assoc] using
    OriginalPathXStep.apart_translate sp _ _ (base i)

theorem scan_safe (sp lines off : Word) (member : off∈offsets) (safe : Safe sp lines) :
    E1M1ThingGeometry.ScanSafe sp lines (address sp off) := by
  refine ⟨⟨safe.stamps off member,?_,?_,?_⟩,safe.array off member⟩
  · exact below sp off member ⟨3,by decide⟩
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨4,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨5,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨6,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨7,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨8,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨13,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨14,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨15,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨16,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨17,by decide⟩
  · intro k hk
    simp only [OriginalLineTail.stackOffsets,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨12,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨11,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨10,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨9,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨13,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨14,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨15,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨16,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨17,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨18,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨19,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨20,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨21,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨22,by decide⟩

theorem thing_safe (sp lines off : Word) (member : off∈offsets) (safe : Safe sp lines) :
    E1M1ThingVisit.ReadSafe (sp-(120#32)) (address sp off) := by
  refine ⟨?_,⟨?_,?_⟩,?_,?_,safe.array off member⟩
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨2,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨3,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨4,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨5,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨6,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨7,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨8,by decide⟩
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨9,by decide⟩
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨15,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨16,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨17,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨18,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨19,by decide⟩
  · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨10,by decide⟩
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨14,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨13,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨12,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨11,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨15,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨16,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨17,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨18,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨19,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨20,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨21,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨22,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨23,by decide⟩
    · simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using below sp off member ⟨24,by decide⟩

/-- Both endpoint slots survive the axis and intercept initialization blocks. -/
theorem endpoints (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey) :
    let t := E1M1PathMapSetup.grid s
    load32 t.core.memory (t.core.regs 4+(20#32))=(Collision.pathStart ox oy sx sy ex ey).endBlockX.toBitVec ∧
    load32 t.core.memory (t.core.regs 4+(24#32))=(Collision.pathStart ox oy sx sy ex ey).endBlockY.toBitVec := by
  have init := OriginalPathInit.ready s ox oy sx sy ex ey geometry
  have keep (off : Word) (h : off∈[(20#32),24]) :
      load32 (E1M1PathMapSetup.grid s).core.memory ((E1M1PathMapSetup.grid s).core.regs 4+off)=
        load32 (OriginalPathInit.result s).core.memory (s.regs 4-(60#32)+off) := by
    rw [E1M1PathMapSetup.grid_stack s ox oy sx sy ex ey geometry]
    apply E1M1PathMapSetup.after_frame
    rw [init.stack]
    intro k hk
    apply OriginalPathXStep.apart_translate
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    simp only [E1M1PathMapSetup.offsets,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases h with rfl|rfl <;> rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
  constructor
  · rw [keep _ (by simp)]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using congrArg (fun v => v.2.2.1) init.blocks
  · rw [keep _ (by simp)]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using congrArg (fun v => v.2.2.2) init.blocks
end Doom.Proofs.E1M1GridLocals
