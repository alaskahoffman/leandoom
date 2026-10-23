import Doom.Proofs.E1M1LineTail
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
open OriginalLineTail

def trace : Collision.Divline := ⟨⟨0⟩,⟨0⟩,⟨65536⟩,⟨0⟩⟩
def wall : Collision.Line := {(default : Collision.Line) with x:=⟨32768⟩,dy:=⟨65536⟩}
def mem : Memory :=
  [(0x600401,0x600501),(0x600409,0),(0x60040d,65536),(0x600433,0),
   (0x600501,32768),(0x600505,0),(0x2ba10,0),(0x2ba14,0),(0x2ba18,65536),(0x2ba1c,0),
   (0x2c024,0),(0x2c028,0x600801),(24,0x600301),(36,0x2c578),(44,777),(48,0x4f000),
   (0x600301,0x00000009),(0x600305,0xffff),(0x13580,99),(0x2c120,0x600600),(0x600636,99)].foldl
    (fun m (a,v) => store32 m a v) (fun _ => 0)
def start : X86Memory.State := ⟨fun r => if r=1 then 0x600401 else 0,mem⟩

theorem geometry : OriginalLineFraction.Inputs start trace wall 0x600401 0x600501 := by
  constructor <;> try decide
  intro a ha off ho
  simp only [OriginalLineFraction.reads,List.mem_cons,List.not_mem_nil,or_false] at ha ho
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide

theorem stack_safe (a : Word) (ha : a∈[(0x2c028#32),0x2c024,0x600433,24,36,0x600303,0x600305,0x13580,0x2c120,0x600636]) : StackSafe start a := by
  intro off ho
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  simp only [stackOffsets,List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide

theorem protection (a : Word) (ha : a∈[(24#32),36,0x600303,0x600305,0x13580,0x2c120,0x600636]) : Protected start a := by
  constructor
  · apply stack_safe
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha ⊢
    rcases ha with h|h|h|h|h|h|h <;> simp [h]
  · intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      rcases hw with rfl|rfl|rfl|rfl <;> unfold Apart <;> decide

theorem input : Inputs start trace wall ⟨32768⟩ 0 0x600401 0x600501 := by
  refine ⟨geometry,by rfl,by decide,by decide,?_,?_⟩
  · exact stack_safe _ (by simp)
  · exact stack_safe _ (by simp)
theorem layout : Layout start := ⟨stack_safe _ (by simp),protection _ (by simp [start])⟩
example : (result start).core.regs 2=(0x600303#32) := by decide
example : (result start).pc=0x2c57f := by decide
example : load32 (result start).core.memory (0x2c028#32)=(0x60080d#32) := by decide
example : load32 (result start).core.memory (0x600801#32)=(32768#32) := by decide
example : load32 (result start).core.memory (0x600805#32)=(1#32) := by decide
example : load32 (result start).core.memory (0x600809#32)=(0x600401#32) := by decide

theorem seen : ∀ i<1, OriginalLineResume.SeenAt start.memory ((0x600301#32)+BitVec.ofNat 32 (2*(i+1))) := by
  intro i hi
  have : i=0 := by omega
  subst i
  unfold OriginalLineResume.SeenAt
  decide
theorem seen_safe : ∀ i<1, ∀ a∈seenReads start.memory ((0x600301#32)+BitVec.ofNat 32 (2*(i+1))), Protected start a := by
  intro i hi a ha
  have : i=0 := by omega
  subst i
  have eq : seenReads start.memory ((0x600301#32)+BitVec.ofNat 32 (2*(0+1)))=[(0x600303#32),0x13580,0x2c120,0x600636] := by decide
  rw [eq] at ha
  apply protection
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha ⊢
  rcases ha with h|h|h|h <;> simp [h]
example : ∃ steps≤125, X86Routine.Prefix program [] steps ⟨start,none,0x2c691⟩
    (OriginalLineBounds.returned (OriginalLineCell.header (OriginalLineResume.skipMany 1 (result start)).core).core) :=
  through_sentinel start none trace wall ⟨32768⟩ 0 0x600401 0x600501 0x600301 input layout
    (by decide) (by decide) (protection _ (by simp [start])) (by decide)
    1 seen seen_safe (by decide) (protection _ (by decide))
