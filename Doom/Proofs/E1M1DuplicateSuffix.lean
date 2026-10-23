import Doom.Proofs.E1M1FiringVisitedNext
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1DuplicateSuffix
open Verification X86 X86Memory X86Control BlockSummary
attribute [local irreducible] load32
abbrev program := E1M1FiringAdvance.program

def tailCell (c : E1M1PathMap.Cell) : E1M1PathMap.Cell := ⟨c.offset+1,c.ids.tail⟩

theorem contains_resume (pc : Nat) (h : OriginalLineResume.program pc≠none) :
    program pc=OriginalLineResume.program pc := by
  have a : OriginalLineMixedInvariant.program pc=OriginalLineResume.program pc := E1M1LineResume.contains_resume pc h
  have b := E1M1ThingEntry.contains_prior pc (by rw [a]; exact h)
  have c := E1M1FiringThings.contains_entry pc (by rw [b,a]; exact h)
  exact (E1M1FiringAdvance.contains_prior pc (by
    change E1M1FiringThings.program pc≠none
    rw [c,b,a]; exact h)).trans (c.trans (b.trans a))

/-- A duplicate consumes ten original instructions and one 16-bit list entry,
but no memory store, callback or intercept slot. -/
theorem skip (s : X86Control.State) (pc : s.pc=0x2c57f)
    (nonlast : OriginalLineCell.itemWord s.core≠(0xffffffff#32))
    (seen : OriginalLineCell.already (OriginalLineCell.header s.core).core) :
    let out := OriginalLineCell.visit s.core
    (∃ n≤10, X86CodeMemory.Prefix FloorCaller.cm program [] n s out) ∧
    out.core.memory=s.core.memory ∧ out.core.regs 2=s.core.regs 2+(2#32) ∧
    out.core.regs 4=s.core.regs 4 ∧ out.pc=0x2c57f := by
  obtain ⟨n,hn,path⟩ := OriginalLineResume.skip_execution 1 s pc ⟨nonlast,seen,trivial⟩
  have obs := OriginalLineResume.skip_observe 1 s ⟨nonlast,seen,trivial⟩
  exact ⟨⟨n,by simpa using hn,X86CodeMemory.lift_success
    (path.transfer program [] contains_resume (by simp)) FloorCaller.cm⟩,
    obs.1,obs.2.1,obs.2.2,(OriginalLineCell.skip_observe s.core nonlast seen).2.2⟩

theorem address (s t : X86Memory.State) (cursor : t.regs 2=s.regs 2+(2#32)) (i : Nat) :
    OriginalLineInvariant.address t i=OriginalLineInvariant.address s (i+1) := by
  simp only [OriginalLineInvariant.address,cursor,Nat.mul_add,BitVec.ofNat_add]
  change s.regs 2+2+BitVec.ofNat 32 (2*i)=s.regs 2+(BitVec.ofNat 32 (2*i)+2)
  ac_rfl

/-- The next cursor exposes exactly the original list tail, including its
sentinel. A tail is not itself a fresh BLOCKMAP list with a leading zero. -/
theorem scan_tail (s t : X86Memory.State) (lines : Word) (c : E1M1PathMap.Cell)
    (nonempty : c.ids≠[]) (items : E1M1PathMapLookup.ScanWords s lines c)
    (memory : t.memory=s.memory) (cursor : t.regs 2=s.regs 2+(2#32)) :
    E1M1PathMapLookup.ScanWords t lines (tailCell c) := by
  have length : c.ids.tail.length+1=c.ids.length := by
    cases ids : c.ids <;> simp_all
  have item (i : Nat) :
      OriginalLineCell.itemWord (OriginalLineInvariant.atIndex t i)=
        OriginalLineCell.itemWord (OriginalLineInvariant.atIndex s (i+1)) := by
    change (load16 t.memory (OriginalLineInvariant.address t i)).signExtend 32=
      (load16 s.memory (OriginalLineInvariant.address s (i+1))).signExtend 32
    rw [memory,address s t cursor]
  have ptr (i : Nat) :
      OriginalLineDispatch.pointer (OriginalLineInvariant.atIndex t i)=
        OriginalLineDispatch.pointer (OriginalLineInvariant.atIndex s (i+1)) := by
    unfold OriginalLineDispatch.pointer
    rw [item]
    change _+load32 t.memory 0x2c120=_+load32 s.memory 0x2c120
    rw [memory]
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    have bound : i.val+1<c.ids.length := by have := i.isLt; change i.val<c.ids.tail.length at this; omega
    rw [item,items.items ⟨i.val+1,bound⟩]
    simp [tailCell,List.getElem_tail]
  · intro i
    rw [item]
    exact items.nonlast ⟨i.val+1,by have := i.isLt; change i.val<c.ids.tail.length at this; omega⟩
  · intro i frac
    have bound : i.val+1<c.ids.length := by have := i.isLt; change i.val<c.ids.tail.length at this; omega
    rw [ptr,items.pointers ⟨i.val+1,bound⟩ frac]
    simp [tailCell,List.getElem_tail]
  · change load16 t.memory (OriginalLineInvariant.address t c.ids.tail.length)=(0xffff#16)
    rw [memory,address s t cursor,length]
    exact items.sentinel
end Doom.Proofs.E1M1DuplicateSuffix
