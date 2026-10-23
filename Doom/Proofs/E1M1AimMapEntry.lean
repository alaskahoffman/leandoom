import Doom.Proofs.E1M1AimMapRegions
set_option backward.isDefEq.respectTransparency false
namespace Doom.Proofs.E1M1AimMapEntry
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoiseAllocation (Region)
open E1M1AimSetupFootprint (Reserve)
open E1M1AimMapRegions (Layout)

/-- Only original memory contents. All MapInputs protection predicates are
constructed below rather than included in this representation contract. -/
structure Values (memory : Memory) (base lines : Word) (words : Array Nat) : Prop where
  width : load32 memory 0x2c0fc=36
  height : load32 memory 0x2c110=23
  table : load32 memory 0x2c100=base+8
  lists : load32 memory 0x2c10c=base
  lines : load32 memory 0x2c120=lines
  image : E1M1PathMap.WordImage memory base words

/-- Reconstruct the existing pinned-map contract from data, region placement,
and a scalar stack reserve. There are no pairwise protection premises. -/
theorem inputs (stack : Region) (s : X86Memory.State) (base lines : Word) (words : Array Nat)
    (reserve : Reserve stack s) (placement : Layout stack base) (size : words.size=3461)
    (values : Values s.memory base lines words) :
    E1M1PathMapQuery.MapInputs s base lines words 36 23 := by
  refine ⟨values.width,values.height,by decide,by decide,values.table,values.lists,
    values.lines,?_,values.image,?_⟩
  · intro a member
    exact E1M1AimMapRegions.global_safe stack s base a reserve placement member
  · intro i hi
    exact E1M1AimMapRegions.word_safe stack s base reserve placement i (by omega)

/-- The constructed input contract feeds the existing authenticated query
execution through the actual P_PathTraverse CALL, not an abstract copy of it. -/
theorem execution (stack : Region) (s : X86Memory.State) (f : Option Flags)
    (base lines : Word) (words : Array Nat) (reserve : Reserve stack s)
    (placement : Layout stack base) (size : words.size=3461)
    (values : Values s.memory base lines words) :
    X86CodeMemory.Prefix FloorCaller.cm E1M1AimSetup.program [] 36
      ⟨s,f,0x2bb80⟩ (E1M1PathMapQuery.traversal s) ∧
    E1M1PathMapSetup.MapInputs (E1M1PathMapQuery.traversal s).core base lines words 36 23 :=
  E1M1PathMapQuery.query_execution s f base lines words 36 23
    (inputs stack s base lines words reserve placement size values)

/-- The same map data can be supplied before the outer controller prologue.
The real first-call stack pointer is derived directly; no angle-content premise
is needed to transport map data. The 124-byte bound includes the prologue. -/
theorem controller_map (stack : Region) (s : X86Memory.State) (f : Option Flags)
    (base lines : Word) (words : Array Nat) (placement : Layout stack base)
    (room : stack.lo+124 ≤ (s.regs 4).toNat)
    (top : (s.regs 4).toNat ≤ stack.hi) (bound : stack.hi ≤ 2^32)
    (size : words.size=3461) (values : Values s.memory base lines words) :
    E1M1PathMapQuery.MapInputs (E1M1AimControllerEntry.entry s f).core base lines words 36 23 := by
  let view := E1M1AimControllerInputs.layout s (⟨0⟩ : Angle)
  have reserve := E1M1AimSetupFootprint.controller_reserve stack s (⟨0⟩ : Angle) room top bound
  have before := inputs stack view base lines words reserve placement size values
  have sp : (E1M1AimControllerEntry.entry s f).core.regs 4=view.regs 4 := by
    simp [view,E1M1AimControllerInputs.layout,E1M1AimControllerEntry.entry,
      OriginalBulletSlope.firstCall,OriginalBulletSlope.saved,X86Routine.pushWord,put,write,
      BitVec.sub_eq_add_neg,BitVec.add_assoc]
  apply E1M1AimRetryData.map view _ base lines words 36 23 sp before
  have small : E1M1AimRegions.StackReserve stack s := by
    unfold E1M1AimRegions.StackReserve
    exact ⟨by omega,top,bound⟩
  exact E1M1AimRegions.kept stack s f _ small
    (E1M1AimMapRegions.covered stack base words placement size)
end Doom.Proofs.E1M1AimMapEntry
