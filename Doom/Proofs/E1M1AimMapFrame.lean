import Doom.Proofs.E1M1AimCycleInvariant
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimMapFrame
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1MinimumScan (address)
open E1M1AimHistoryCycle (Frame)
attribute [local irreducible] load32 store32

/-- Map words are protected from every possible intercept-fraction mark, not
just the current one. This permits reuse after a different record is selected. -/
def StableWord (s : X86Memory.State) (a : Word) : Prop :=
  E1M1AimRecordFrame.ReadSafe s a ∧ (∀ i<128, Apart a (address i)) ∧
    Apart a 0x2c028 ∧ Apart a (s.regs 4)

def Region (s : X86Memory.State) (line front back : Word) : Prop :=
  ∀ a∈(line+(16#32))::E1M1OpeningHeights.reads line front back, StableWord s a

/-- Stack-dependent protection remains valid at the next callback. -/
theorem stable_word (s t : X86Memory.State) (a : Word)
    (stack : t.regs 4=s.regs 4) (safe : StableWord s a) : StableWord t a := by
  simpa only [StableWord,E1M1AimRecordFrame.ReadSafe,stack] using safe

theorem region (s t : X86Memory.State) (line front back : Word)
    (stack : t.regs 4=s.regs 4) (safe : Region s line front back) : Region t line front back := by
  intro a member
  exact stable_word s t a stack (safe a member)

/-- A full-cycle word frame also preserves byte and halfword map fields. -/
theorem word (s : X86Memory.State) (out : X86Control.State) (marked : Nat) (a : Word)
    (frame : Frame s out) (pointer : s.regs 3=address marked) (bounded : marked<128)
    (safe : StableWord s a) : load32 out.core.memory a=load32 s.memory a := by
  exact frame a safe.1 (by rw [pointer]; exact safe.2.1 marked bounded) safe.2.2.1 safe.2.2.2

theorem byte (s : X86Memory.State) (out : X86Control.State) (marked : Nat) (a : Word)
    (frame : Frame s out) (pointer : s.regs 3=address marked) (bounded : marked<128)
    (safe : StableWord s a) : out.core.memory a=s.memory a := by
  have low := congrArg (fun w : Word => w.extractLsb' 0 8) (word s out marked a frame pointer bounded safe)
  simpa only [E1M1PathCell.low_byte] using low

theorem half (s : X86Memory.State) (out : X86Control.State) (marked : Nat) (a : Word)
    (frame : Frame s out) (pointer : s.regs 3=address marked) (bounded : marked<128)
    (safe : StableWord s a) : load16 out.core.memory a=load16 s.memory a := by
  have low := congrArg (fun w : Word => w.extractLsb' 0 16) (word s out marked a frame pointer bounded safe)
  simpa only [load32,BitVec.extractLsb'_append_eq_right,load16] using low

/-- Preserve a line that need not be the one just processed: both sector
pointers, all four heights, the halfword side index and the flags byte. -/
theorem image (s : X86Memory.State) (out : X86Control.State) (marked : Nat)
    (line front back ff fc bf bc : Word)
    (frame : Frame s out) (pointer : s.regs 3=address marked) (bounded : marked<128)
    (safe : Region s line front back)
    (before : E1M1AimOpeningFrame.Image s.memory line front back ff fc bf bc) :
    E1M1AimOpeningFrame.Image out.core.memory line front back ff fc bf bc ∧
    out.core.memory (line+(16#32))=s.memory (line+(16#32)) := by
  have keep (a : Word) (member : a∈E1M1OpeningHeights.reads line front back) :=
    word s out marked a frame pointer bounded (safe a (List.mem_cons_of_mem _ member))
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,byte s out marked _ frame pointer bounded (safe _ (by simp))⟩
  · rw [half s out marked _ frame pointer bounded (safe _ (by simp [E1M1OpeningHeights.reads]))]
    exact before.side
  · rw [keep _ (by simp [E1M1OpeningHeights.reads])]; exact before.frontPtr
  · rw [keep _ (by simp [E1M1OpeningHeights.reads])]; exact before.backPtr
  · rw [keep _ (by simp [E1M1OpeningHeights.reads])]; exact before.frontFloor
  · rw [keep _ (by simp [E1M1OpeningHeights.reads])]; exact before.frontCeiling
  · rw [keep _ (by simp [E1M1OpeningHeights.reads])]; exact before.backFloor
  · rw [keep _ (by simp [E1M1OpeningHeights.reads])]; exact before.backCeiling

/-- Existing callback read protection includes every opening-helper write. -/
theorem opening_safe (s : X86Memory.State) (a : Word) (safe : E1M1AimRecordFrame.ReadSafe s a) :
    ∀ b∈E1M1AimOpeningFrame.writes (s.regs 4), Apart a b := by
  intro b member
  simp only [E1M1AimOpeningFrame.writes,List.mem_append] at member
  rcases member with (pushes|locals)|globals
  · simp only [E1M1AimOpeningFrame.pushes,List.mem_cons,List.not_mem_nil,or_false] at pushes
    rcases pushes with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact safe.1 4 (by simp)
    · exact safe.1 8 (by simp)
    · exact safe.1 12 (by simp)
    · exact safe.1 16 (by simp)
    · exact safe.1 20 (by simp)
    · exact safe.1 24 (by simp)
    · exact safe.2 _ (by simp [E1M1AimReturnFrame.writes])
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at locals
    rcases locals with rfl|rfl|rfl|rfl <;> exact safe.2 _ (by simp [E1M1AimReturnFrame.writes])
  · exact safe.2 b (by simp only [E1M1AimReturnFrame.writes,List.mem_append]; exact Or.inl (Or.inr globals))

/-- The floor-division writes form a subset of the full callback's write set. -/
theorem floor_safe (s : X86Memory.State) (a : Word) (safe : E1M1AimRecordFrame.ReadSafe s a) :
    ∀ b∈E1M1AimClipFrame.writes (s.regs 4-(24#32)), Apart a b := by
  intro b member
  simp only [E1M1AimClipFrame.writes,BitVec.sub_sub,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl <;>
    exact safe.2 _ (by simp [E1M1AimReturnFrame.writes])

theorem map_safe (s : X86Memory.State) (line front back : Word) (safe : Region s line front back) :
    E1M1AimOpeningFrame.MapSafe s line front back := by
  intro a member
  exact opening_safe s a (safe a (List.mem_cons_of_mem _ member)).1
end Doom.Proofs.E1M1AimMapFrame
