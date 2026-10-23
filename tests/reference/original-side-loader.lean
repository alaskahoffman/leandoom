import Doom.Proofs.OriginalSideLoader
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Verification.SideLoaderFixture
open Doom Doom.Proofs X86 X86Memory X86Control BlockSummary OriginalSideLoader E1M1NoiseImage
local instance (a b : Word) : Decidable (Apart a b) := by unfold Apart; infer_instance

def state (index : BitVec 16) (stack : Word) : X86Memory.State :=
  ⟨fun r => if r=3 then 0x600201 else if r=2 then 0x600401 else if r=4 then stack
    else if r=5 then 0xffffffff else 0x12345678,
    applyPatch (half 0x60021d index) (store32 (fun _ => 0xaa) 0x2c148 0x610001)⟩

-- The newly supported encoding is INC EBP; flags remain conservatively unknown.
example : X86Routine.decode [0x45]=some (.addImmediate 5 1,[]) := by decide +kernel
example : (linked (state 84 0x600801)).core.regs 5=0 := by decide +kernel
example : (linked (state 84 0x600801)).core.regs 6=0x12345678 := by decide +kernel
example : offset (state 84 0x600801)=84*86 := by decide +kernel
example : offset (state 65535 0x600801)=0xffffffaa := by decide +kernel
example : offset (state 32768 0x600801)=0xffd50000 := by decide +kernel
example : target (state 84 0x600801)=0x610001+84*86 := by decide +kernel
example : load32 (linked (state 84 0xffffffff)).core.memory 0x60040f=0x610001+84*86 := by decide +kernel

-- Overwriting the sector-base global changes the answer, as in the original.
-- The unconditional machine summary handles this; the separated formula cannot.
example : target (state 3 0x2c148)=2*(3*86) := by decide +kernel
example : target (state 3 0x2c148)≠0x610001+3*86 := by decide +kernel
example : ¬Apart 0x2c148 ((state 3 0x2c148).regs 4) := by decide +kernel

example : (linked (state 84 0x600801)).core.memory 0x987654=(state 84 0x600801).memory 0x987654 :=
  untouched _ _ (by decide +kernel)
example : load32 (published (state 84 0x600801) none).core.memory 0x2c118=0x12345678 := by decide +kernel

example : ∃ out, X86Routine.run program [0x2e4d1] 11 ⟨state 84 0x600801,none,0x2e4af⟩=some out ∧
    out.core.memory=applyPatch (linkPatch (state 84 0x600801)) (state 84 0x600801).memory ∧
    load32 out.core.memory 0x60040f=0x610001+BitVec.ofNat 32 (84*86) :=
  link_execution_pointer (state 84 0x600801) none 84 0x610001
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end Doom.Verification.SideLoaderFixture
