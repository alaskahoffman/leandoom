import Doom.Proofs.E1M1AimControllerSetup
import Doom.Proofs.E1M1NoiseAllocation
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.E1M1AimRegions
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoiseAllocation (Region)

/-- Twenty bytes below the incoming stack pointer contain all five controller
stores. This sufficient range criterion excludes address wraparound. -/
def StackReserve (stack : Region) (s : X86Memory.State) : Prop :=
  stack.lo+20 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat ≤ stack.hi ∧ stack.hi ≤ 2^32

/-- A read set may span several allocations; only separation from the stack is
needed here. This does not assert that DOS allocated these regions. -/
def Covered (stack : Region) (addresses : List Word) : Prop :=
  ∀ a∈addresses, ∃ r : Region, r.Contains a ∧ r.Disjoint stack

theorem stack_word (stack : Region) (s : X86Memory.State)
    (reserve : StackReserve stack s) (n : Nat) (low : 4 ≤ n) (high : n ≤ 20) :
    stack.Contains (s.regs 4-BitVec.ofNat 32 n) := by
  have size := (s.regs 4).isLt
  simp only [StackReserve] at reserve
  simp only [Region.Contains,BitVec.toNat_sub,BitVec.toNat_ofNat]
  omega

theorem writes_contained (stack : Region) (s : X86Memory.State)
    (reserve : StackReserve stack s) :
    ∀ b∈E1M1AimControllerEntry.writes s, stack.Contains b := by
  intro b member
  simp only [E1M1AimControllerEntry.writes,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl <;>
    exact stack_word stack s reserve _ (by decide) (by decide)

theorem safe_reads (stack : Region) (s : X86Memory.State) (addresses : List Word)
    (reserve : StackReserve stack s) (covered : Covered stack addresses) :
    E1M1AimControllerInputs.SafeReads s addresses := by
  intro a ha b hb
  obtain ⟨r,inside,separate⟩ := covered a ha
  exact Region.apart inside (writes_contained stack s reserve b hb) separate

/-- Scalar bounds for an allocation imply containment of any four-byte field. -/
theorem field (base : Word) (bytes offset : Nat)
    (bound : base.toNat+bytes ≤ 2^32) (fits : offset+4 ≤ bytes) :
    (Region.mk base.toNat (base.toNat+bytes)).Contains (base+BitVec.ofNat 32 offset) := by
  have size := base.isLt
  simp only [Region.Contains,BitVec.toNat_add,BitVec.toNat_ofNat]
  omega

/-- All fields remain equal after the actual authenticated prologue. -/
theorem kept (stack : Region) (s : X86Memory.State) (f : Option Flags)
    (addresses : List Word) (reserve : StackReserve stack s) (covered : Covered stack addresses) :
    ∀ a∈addresses, load32 (E1M1AimControllerEntry.entry s f).core.memory a=load32 s.memory a := by
  intro a ha
  exact E1M1AimControllerEntry.frame s f a (safe_reads stack s addresses reserve covered a ha)
end Doom.Proofs.E1M1AimRegions
