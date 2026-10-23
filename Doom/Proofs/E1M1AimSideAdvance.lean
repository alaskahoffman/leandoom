import Doom.Proofs.OriginalSideAdvance
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1AimSideAdvance
open Verification X86 X86Memory X86Control BlockSummary
open OriginalSideAdvance (result prepared)
open E1M1AimSideEncoding (Input sectorAddress)
open E1M1NoiseImage (Realizes word)

theorem progress (s : X86Memory.State) :
    (result s).core.regs 3=s.regs 3+30 ∧
    (result s).core.regs 2=s.regs 2+18 ∧
    (result s).core.regs 5=s.regs 5+1 ∧
    (result s).core.regs 4=s.regs 4 ∧
    (result s).core.regs 1=s.regs 1+30 ∧
    (result s).core.regs 7=s.regs 7+30 ∧
    (result s).core.regs 6=s.regs 6+30 := by
  simp [result,OriginalSideAdvance.advanced,OriginalSideLoader.linked,put,write]

/-- The branch consumes the count AFTER the pointer and scratch writes. -/
theorem exit_pc (s : X86Memory.State) :
    (result s).pc=(if (s.regs 5+1).toInt<
      (load32 (OriginalSideLoader.linked s).core.memory 0x2c11c).toInt
      then 0x2e46a else 0x2e4dd) := by
  simp [result,OriginalSideAdvance.advanced,OriginalSideLoader.linked,put,write]

theorem count_preserved (s : X86Memory.State)
    (scratchSafe : Apart 0x2c11c (s.regs 4))
    (pointerSafe : Apart 0x2c11c (s.regs 2+14)) :
    load32 (result s).core.memory 0x2c11c=load32 s.memory 0x2c11c := by
  change load32 (store32 (store32 s.memory (s.regs 4) (OriginalSideLoader.offset s))
    (s.regs 2+14) (OriginalSideLoader.target s)) 0x2c11c=_
  rw [load_store_apart _ _ _ _ pointerSafe,load_store_apart _ _ _ _ scratchSafe]

/-- Finite positive-count loop reasoning, retaining the DOS signed comparison.
No branch decision or successful trace is assumed. -/
theorem bounded_branch (s : X86Memory.State) (i total : Nat)
    (index : (s.regs 5).toNat=i) (count : (load32 s.memory 0x2c11c).toNat=total)
    (small : total<2147483648) (inside : i<total)
    (scratchSafe : Apart 0x2c11c (s.regs 4))
    (pointerSafe : Apart 0x2c11c (s.regs 2+14)) :
    (result s).pc=(if i+1<total then 0x2e46a else 0x2e4dd) ∧
    ((result s).core.regs 5).toNat=i+1 := by
  have next : (s.regs 5+1).toNat=i+1 := by
    simp only [BitVec.toNat_add,index]
    change (i+1)%4294967296=i+1
    omega
  have signedNext : (s.regs 5+1).toInt=(i+1 : Nat) := by
    simp only [BitVec.toInt_eq_toNat_cond,next]
    split <;> omega
  have signedCount : (load32 s.memory 0x2c11c).toInt=(total : Int) := by
    simp only [BitVec.toInt_eq_toNat_cond,count]
    split <;> omega
  have stable := count_preserved s scratchSafe pointerSafe
  change load32 (OriginalSideLoader.linked s).core.memory 0x2c11c=_ at stable
  refine ⟨?_,by rw [(progress s).2.2.1,next]⟩
  rw [exit_pc,stable,signedNext,signedCount]
  have same : ((i+1 : Nat) : Int)<(total : Int) ↔ i+1<total := by omega
  simp only [same]

theorem emitted (s : X86Memory.State) (f : Option Flags) (side : BitVec 16)
    (index : Nat) (sideBase sectorBase : Word)
    (input : Input s side index sideBase sectorBase) :
    X86Routine.run OriginalSideAdvance.program [0x2e46a,0x2e4dd] 15 ⟨s,f,0x2e4af⟩=
      some (result s) ∧
    Realizes (word (E1M1NoiseGraph.sideAddress sideBase side) (sectorAddress sectorBase index))
      (result s).core.memory := by
  exact ⟨OriginalSideAdvance.linked_execution s f,
    (E1M1AimSideEncoding.link_encoding s f side index sideBase sectorBase input).2⟩

/-- The just-emitted pointer is at +14; the next record's offsets are at +18
and +22. Their byte ranges are disjoint even across 32-bit address wraparound. -/
theorem next_offsets_preserve (s : X86Memory.State) :
    load32 (prepared (result s).core).core.memory (s.regs 2+14)=
      load32 (result s).core.memory (s.regs 2+14) := by
  apply OriginalSideAdvance.offsets_frame
  · rw [(progress s).2.1]
    have h := PlayerHeight.slots_apart (s.regs 2+14) 0 1 (by decide)
    change Apart (s.regs 2+14+0) (s.regs 2+14+4) at h
    simpa [BitVec.add_assoc] using h
  · rw [(progress s).2.1]
    have h := PlayerHeight.slots_apart (s.regs 2+14) 0 2 (by decide)
    change Apart (s.regs 2+14+0) (s.regs 2+14+8) at h
    simpa [BitVec.add_assoc] using h

/-- Actual suffix, loop branch and next offset writes, up to the first texture
lookup CALL. No extra pointer-preservation premise is needed for this interval. -/
theorem continuing_emitted (s : X86Memory.State) (f : Option Flags) (side : BitVec 16)
    (index : Nat) (sideBase sectorBase : Word)
    (input : Input s side index sideBase sectorBase)
    (next : (result s).pc=0x2e46a) :
    X86Routine.run OriginalSideAdvance.program [0x2e47e,0x2e4dd] 22 ⟨s,f,0x2e4af⟩=
      some (prepared (result s).core) ∧
    Realizes (word (E1M1NoiseGraph.sideAddress sideBase side) (sectorAddress sectorBase index))
      (prepared (result s).core).core.memory := by
  refine ⟨OriginalSideAdvance.continued_execution s f next,E1M1AimSideEncoding.word_of_load _ _ _ ?_⟩
  have address : E1M1NoiseGraph.sideAddress sideBase side=s.regs 2+14 := by
    simp [E1M1NoiseGraph.sideAddress,input.record,BitVec.add_comm]
  have initial := E1M1NoiseImage.read_word (emitted s f side index sideBase sectorBase input).2
  rw [address] at initial ⊢
  exact (next_offsets_preserve s).trans initial

theorem bounded_continuation (s : X86Memory.State) (f : Option Flags) (side : BitVec 16)
    (sectorIndex i total : Nat) (sideBase sectorBase : Word)
    (input : Input s side sectorIndex sideBase sectorBase)
    (index : (s.regs 5).toNat=i) (count : (load32 s.memory 0x2c11c).toNat=total)
    (small : total<2147483648) (more : i+1<total)
    (scratchSafe : Apart 0x2c11c (s.regs 4))
    (pointerSafe : Apart 0x2c11c (s.regs 2+14)) :
    X86Routine.run OriginalSideAdvance.program [0x2e47e,0x2e4dd] 22 ⟨s,f,0x2e4af⟩=
      some (prepared (result s).core) ∧
    Realizes (word (E1M1NoiseGraph.sideAddress sideBase side) (sectorAddress sectorBase sectorIndex))
      (prepared (result s).core).core.memory := by
  apply continuing_emitted s f side sectorIndex sideBase sectorBase input
  rw [(bounded_branch s i total index count small (by omega) scratchSafe pointerSafe).1,if_pos more]

/-- The last admitted side exits toward cleanup with its pointer still encoded. -/
theorem bounded_finished (s : X86Memory.State) (f : Option Flags) (side : BitVec 16)
    (sectorIndex i total : Nat) (sideBase sectorBase : Word)
    (input : Input s side sectorIndex sideBase sectorBase)
    (index : (s.regs 5).toNat=i) (count : (load32 s.memory 0x2c11c).toNat=total)
    (small : total<2147483648) (last : i+1=total)
    (scratchSafe : Apart 0x2c11c (s.regs 4))
    (pointerSafe : Apart 0x2c11c (s.regs 2+14)) :
    X86Routine.run OriginalSideAdvance.program [0x2e46a,0x2e4dd] 15 ⟨s,f,0x2e4af⟩=
      some (result s) ∧ (result s).pc=0x2e4dd ∧
    Realizes (word (E1M1NoiseGraph.sideAddress sideBase side) (sectorAddress sectorBase sectorIndex))
      (result s).core.memory := by
  have done := emitted s f side sectorIndex sideBase sectorBase input
  refine ⟨done.1,?_,done.2⟩
  rw [(bounded_branch s i total index count small (by omega) scratchSafe pointerSafe).1,if_neg (by omega)]

end Doom.Proofs.E1M1AimSideAdvance
