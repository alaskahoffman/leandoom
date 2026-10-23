import Doom.Proofs.E1M1NoiseFrame
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Doom.Verification.NoiseFrameFixture
open Doom Doom.Proofs X86 X86Memory X86Control BlockSummary E1M1NoiseFrame

def stack (i : Fin 3) : Word := if i=0 then 0x602e01 else if i=1 then 1 else 0xfffffff5

def parentAt (sp : Word) (pruned : Bool) : X86Memory.State :=
  ⟨fun r => if r=0 then 0x600101 else if r=2 then 0 else if r=4 then sp
    else if r=6 then 7 else if r=5 then 28 else BitVec.ofNat 32 (10+r.val),
    ([(0x13580,7),(0x2b958,0x600d01),(0x600143,if pruned then 7 else 6),
      (0x600113,1),(0x60014f,if pruned then 3 else 0)] : List (Word × Word)).foldl
        (fun m p => store32 m p.1 p.2) (fun _ => 0)⟩
def parent (i : Fin 3) (pruned : Bool) := parentAt (stack i) pruned
def child (i : Fin 3) (pruned : Bool) := NoiseTraversal.recursiveCall (parent i pruned) none
def boundary (i : Fin 3) (pruned : Bool) := E1M1NoiseAlert.sectorResult (child i pruned).core

theorem safe (i : Fin 3) (pruned : Bool) : SectorSafe (child i pruned).core := by
  have cases : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases cases with rfl|rfl|rfl <;> cases pruned
  all_goals
    intro a ha b hb
    simp only [slots,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with rfl|rfl|rfl
      all_goals unfold Apart; decide

theorem terminal (i : Fin 3) (pruned : Bool) : (boundary i pruned).pc=0x27011 := by
  have cases : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases cases with rfl|rfl|rfl <;> cases pruned <;> decide

example (i : Fin 3) (pruned : Bool) :
    E1M1NoiseRecursive.Runs 36 (child i pruned)
      (NoiseTraversal.advanced (NoiseTraversal.returned (boundary i pruned).core).core) :=
  terminal_child_execution _ _ (safe i pruned) (terminal i pruned)

example (i : Fin 3) (pruned : Bool) :
    (NoiseTraversal.returned (boundary i pruned).core).pc=0x27006 ∧
    (NoiseTraversal.returned (boundary i pruned).core).core.regs 4=stack i := by
  have h := child_restores (parent i pruned) _ none (sector_saved _ (safe i pruned))
  exact ⟨h.1,h.2.1⟩

example (i : Fin 3) (pruned : Bool) :
    (NoiseTraversal.advanced (NoiseTraversal.returned (boundary i pruned).core).core).core.regs 6=8 ∧
    (NoiseTraversal.advanced (NoiseTraversal.returned (boundary i pruned).core).core).core.regs 5=32 :=
  child_progress (parent i pruned) _ none (sector_saved _ (safe i pruned))

-- A child may overwrite the parent's saved EBX if its sector overlaps the
-- stack. This real counterexample makes the separation premise necessary.
def aliased := parentAt 0x60011b false
def badChild := NoiseTraversal.recursiveCall aliased none
def badReturn := E1M1NoiseTraversal.sectorReturn badChild.core
example : badReturn.core.regs 3≠aliased.regs 3 := by decide

-- Signed-loop limits: the final admitted index advances without wrapping.
example (s : X86Memory.State) (h : s.regs 6=2147483646) :
    2147483647-((NoiseTraversal.advanced s).core.regs 6).toNat <
      2147483647-(s.regs 6).toNat :=
  remaining_decreases s _ (by rw [h]; decide) (by decide)
end Doom.Verification.NoiseFrameFixture
