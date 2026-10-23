import Doom.Proofs.E1M1AimAllocatedEntry
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.E1M1AimSetupFootprint
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoiseAllocation (Region)
open E1M1PathMapQuery (withStack)

/-- Fixed globals written by aim setup and path initialization. -/
def globals : List Word :=
  [0x2b9ac,0x2b9b8,0x2b9f8,0x2b9a8,0x2c1e4,0x2c1e8,
   0x2c028,0x2c024,0x13580,0x2ba18,0x2ba10,0x2ba14,0x2ba1c]

/-- Conservative stack window through axis/intercept setup and the iterator
entry slots already covered by PathMapQuery.Safe. Not a whole-query bound. -/
def offsets : List Nat := [4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 72, 76, 80, 84, 88, 92, 96, 100, 104]

def writes (s : X86Memory.State) : List Word :=
  globals ++ offsets.map (fun n => s.regs 4-BitVec.ofNat 32 n)

def Reserve (stack : Region) (s : X86Memory.State) : Prop :=
  stack.lo+104 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat ≤ stack.hi ∧ stack.hi ≤ 2^32

theorem stack_word (stack : Region) (s : X86Memory.State)
    (reserve : Reserve stack s) (n : Nat) (low : 4 ≤ n) (high : n ≤ 104) :
    stack.Contains (s.regs 4-BitVec.ofNat 32 n) := by
  have size := (s.regs 4).isLt
  simp only [Reserve] at reserve
  simp only [Region.Contains,BitVec.toNat_sub,BitVec.toNat_ofNat]
  omega

/-- Scalar reserve at the outer controller becomes the query's 104-byte reserve
under its explicit twenty-byte prologue layout. -/
theorem controller_reserve (stack : Region) (s : X86Memory.State) (angle : Angle)
    (room : stack.lo+124 ≤ (s.regs 4).toNat)
    (top : (s.regs 4).toNat ≤ stack.hi) (bound : stack.hi ≤ 2^32) :
    Reserve stack (E1M1AimControllerInputs.layout s angle) := by
  have size := (s.regs 4).isLt
  simp [Reserve,E1M1AimControllerInputs.layout,put,write,BitVec.toNat_sub]
  omega

/-- Reduce every existing query-setup protection field to the single finite
write footprint; no new instruction semantics or executed state is assumed. -/
theorem safe (s : X86Memory.State) (a : Word)
    (apart : ∀ b∈writes s, Apart a b) : E1M1PathMapQuery.Safe s a := by
  constructor
  · intro b member
    apply apart b
    simp only [OriginalAimQuery.saveWrites,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> simp [writes,globals,offsets]
  · intro b member
    apply apart b
    simp [OriginalAimSetup.writes,withStack,write] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [writes,globals,offsets,BitVec.sub_sub]
  · constructor
    · intro b member
      apply apart b
      simp [OriginalPathInit.writes,withStack,write] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [writes,globals,offsets,BitVec.sub_sub]
    · intro off member
      apply apart
      simp only [E1M1PathMapSetup.offsets,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [withStack,write,writes,globals,offsets,BitVec.sub_eq_add_neg,BitVec.add_assoc]

/-- A read region disjoint from the stack needs only the fixed-global checks. -/
theorem region_safe (stack region : Region) (s : X86Memory.State) (a : Word)
    (reserve : Reserve stack s) (inside : region.Contains a) (separate : region.Disjoint stack)
    (fixed : ∀ b∈globals, Apart a b) : E1M1PathMapQuery.Safe s a := by
  apply safe s a
  intro b member
  simp only [writes,List.mem_append] at member
  rcases member with global|stackWrite
  · exact fixed b global
  · obtain ⟨n,hn,rfl⟩ := List.mem_map.mp stackWrite
    have bounds : 4 ≤ n ∧ n ≤ 104 := by
      simp only [offsets,List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
    exact Region.apart inside (stack_word stack s reserve n bounds.1 bounds.2) separate
end Doom.Proofs.E1M1AimSetupFootprint
