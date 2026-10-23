import Doom.Proofs.E1M1LineGeometry
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Verification.LineGeometryFixture
open Doom Doom.Proofs X86 X86Memory X86Control BlockSummary OriginalLineGeometry E1M1LineGeometry E1M1NoiseImage
local instance (a b : Word) : Decidable (Apart a b) := by unfold Apart; infer_instance
local instance (n k : Nat) (a b : Word) : Decidable (HalfMemory.Separate n k a b) := by unfold HalfMemory.Separate; infer_instance
local instance (a b : Word) : Decidable (E1M1LineLoad.CopySafe a b) := by unfold E1M1LineLoad.CopySafe; infer_instance
-- Enumerate the four field offsets explicitly; do not enumerate all 32-bit words.
macro "geometry_safe" : tactic => `(tactic| (
  intro off member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h <;> rw [h] <;> decide +kernel))

def state : X86Memory.State :=
  ⟨fun r => if r=0 then 0x620009 else if r=1 then 0x690101 else if r=3 then 0x680101
    else if r=5 then 474 else if r=6 then 0x620001 else if r=7 then 0x620009 else 0x12345678,
    applyPatch (half 0x690101 0 ++ half 0x690103 1 ++ half 0x69010b 0 ++ half 0x69010d 1)
      (store32 (store32 (store32 (store32 (store32 (store32 (store32 (store32 (store32 (fun _ => 0xaa)
        0x2c138 0x620001) 0x2c118 0x600001) 0x2c134 475)
        0x620001 0xfffe0000) 0x620005 0x30000) 0x620009 0x50000) 0x62000d 0xffff0000)
        0x60000f 0x610001) 0x600021 0x630001)⟩
def entry : OriginalGroupOutput.Line := ⟨0x680101,0x610001,0x630001⟩
def source : E1M1LineLoad.Source entry state where
  frontIndex := 0
  backIndex := 1
  sides := 0x600001
  line := by decide +kernel
  base := by decide +kernel
  frontRead := by decide +kernel
  backRead := by decide +kernel
  nextRead := by decide +kernel
  frontSide := by decide +kernel
  backSide := by decide +kernel
  copyBase := by decide +kernel
  copyFront := fun _ => by decide +kernel
  copyBack := fun _ => by decide +kernel
  cacheBase := by decide +kernel
  cacheBack := fun _ => by decide +kernel

example : ∃ out, X86Routine.run E1M1LineGeometry.program [0x2e29a,0x2e3c1] 42 ⟨state,none,0x2e326⟩=some out ∧
    OriginalGroupOutput.Inputs [entry] out.core.memory ∧
    (∀ off∈[(34#32),38,30,26],load32 out.core.memory (entry.address+off)=load32 (bounds state).core.memory (entry.address+off)) :=
  establishes entry state none source (by geometry_safe) (by geometry_safe) (by geometry_safe)
    (fun _ => by geometry_safe) (fun _ => by geometry_safe)

example : v1 state=0x620001 ∧ v2 state=0x620009 := by decide +kernel
example : load32 (prepared state).core.memory 0x680109=0x70000 := by decide +kernel
example : load32 (prepared state).core.memory 0x68010d=0xfffc0000 := by decide +kernel
example : X86Routine.run OriginalLineGeometry.program [0x2e2ec] 18 ⟨state,none,0x2e2b2⟩=some (prepared state) := prefix_execution state none
example : load32 (result state).core.memory (entry.address+34)=0xfffe0000 := by decide +kernel
example : load32 (result state).core.memory (entry.address+38)=0x50000 := by decide +kernel
example : load32 (result state).core.memory (entry.address+30)=0xffff0000 := by decide +kernel
example : load32 (result state).core.memory (entry.address+26)=0x30000 := by decide +kernel
example : (result state).pc=0x2e3c1 := by decide +kernel

-- Original signed vertex indexing: 65535 selects the record eight bytes BEFORE base.
def negative : X86Memory.State := {state with memory := applyPatch (half 0x690101 65535) state.memory}
example : v1 negative=0x61fff9 := by decide +kernel
-- The loaded vertex base survives even if its global is overwritten by v1.
def globalAlias := put {state with memory := applyPatch (half 0x690101 3) state.memory} 3 0x2c138
example : v2 globalAlias=0x620009 := by decide +kernel
example : load32 (vertices globalAlias).core.memory 0x2c138=0x620019 := by decide +kernel
-- Reloading a maximum after writing a minimum is observable with aliasing.
-- v1.x=5, v2.x=-2; minimum is stored exactly over v1.x, then reread as maximum.
def overlap : X86Memory.State :=
  ⟨fun r => if r=3 then 0x680101 else if r=6 then 0x680123 else if r=7 then 0x620001 else state.regs r,
    store32 (store32 state.memory 0x680123 5) 0x620001 0xfffffffe⟩
example : load32 (horizontal overlap).core.memory 0x680123=0xfffffffe := by decide +kernel
example : load32 (horizontal overlap).core.memory 0x680127=0xfffffffe := by decide +kernel
example : ¬Apart (overlap.regs 6) (overlap.regs 3+34) := by decide +kernel
-- A signed comparison must distinguish extrema, not compare their raw unsigned words.
def extrema : X86Memory.State := {state with memory := store32 (store32 state.memory 0x620001 0x80000000) 0x620009 0x7fffffff}
example : load32 (horizontal extrema).core.memory 0x680123=0x80000000 := by decide +kernel
example : load32 (horizontal extrema).core.memory 0x680127=0x7fffffff := by decide +kernel
-- The generic frame lemma protects an unrelated word across both bound axes.
example : load32 (bounds state).core.memory 0x700001=load32 state.memory 0x700001 :=
  bounds_frame state 0x700001 (by geometry_safe)
end Doom.Verification.LineGeometryFixture
