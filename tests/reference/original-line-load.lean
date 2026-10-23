import Doom.Proofs.E1M1LineLoad
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Verification.LineLoadFixture
open Doom Doom.Proofs X86 X86Memory X86Control BlockSummary OriginalLineLoad E1M1LineLoad HalfMemory E1M1NoiseImage
local instance (n k : Nat) (a b : Word) : Decidable (Separate n k a b) := by unfold Separate; infer_instance
local instance (a b : Word) : Decidable (Apart a b) := by unfold Apart; infer_instance
local instance (a b : Word) : Decidable (CopySafe a b) := by unfold CopySafe; infer_instance

def state (line record : Word) (fi bi : BitVec 16) (count counter : Word) : X86Memory.State :=
  ⟨fun r => if r=0 then 0xabcd5678 else if r=1 then record else if r=3 then line else if r=5 then counter else 0x12345678,
    applyPatch (half (record+10) fi ++ half (record+12) bi)
      (store32 (store32 (store32 (store32 (fun _ => 0xaa)
        0x2c118 0x600001) 0x2c134 count) 0x60000f 0x610001) 0x600021 0x630001)⟩
def ordinary := state 0x680101 0x690101 0 1 475 474
def entry : OriginalGroupOutput.Line := ⟨0x680101,0x610001,0x630001⟩
def source : Source entry ordinary where
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

example : ∃ out, X86Routine.run program [0x2e29a,0x2e3c1] 26 ⟨ordinary,none,0x2e358⟩=some out ∧
    OriginalGroupOutput.Inputs [entry] out.core.memory ∧
    out.core.regs 1=ordinary.regs 1+14 ∧ out.core.regs 3=entry.address+62 ∧ out.core.regs 5=ordinary.regs 5+1 :=
  establishes entry ordinary none source
example : (copied ordinary).regs 0=0xabcd0001 := by decide +kernel
example : load16 (copied ordinary).memory 0x680117=0 := by decide +kernel
example : load16 (copied ordinary).memory 0x680119=1 := by decide +kernel
example : (result ordinary).pc=0x2e3c1 := by decide +kernel
example : (result (state 0x680101 0x690101 0 1 475 473)).pc=0x2e29a := by decide +kernel
example : (result (state 0x680101 0x690101 0 1 0 0x7fffffff)).pc=0x2e29a := by decide +kernel
example : (result (state 0x680101 0x690101 0 1 1 0xffffffff)).core.regs 5=0 := by decide +kernel
example : (result (state 0x680101 0x690101 65535 65535 1 0)).core.regs 0=0xffffffff := by decide +kernel

-- Both complete and partial overlaps retain the actual read/write order.
def aliased := state 0x680101 (0x680101+10) 7 9 475 0
example : load16 aliased.memory (aliased.regs 1+12)=9 := by decide +kernel
example : second aliased=7 := by decide +kernel
example : load16 (copied aliased).memory (aliased.regs 3+24)=7 := by decide +kernel
example : ¬Separate 2 2 (aliased.regs 1+12) (aliased.regs 3+22) := by decide +kernel
example : load16 (copied (state 0xffffffe9 0x690101 0x1234 0x5678 1 0)).memory 0xffffffff=0x1234 := by decide +kernel
example : load16 (copied (state 0xffffffe9 0x690101 0x1234 0x5678 1 0)).memory 1=0x5678 := by decide +kernel
example : load32 (result ordinary).core.memory 0x700001=load32 ordinary.memory 0x700001 :=
  E1M1LineLoad.frame ordinary 0x700001 (by decide +kernel) (by decide +kernel) (by decide +kernel)

-- New decoder forms are exact and fail closed on register-only/truncated data.
example : X86Routine.decode [0x66,0x89,0x43,0x16]=some (.storeHalf ⟨some 3,none,0,22⟩ 0,[]) := by decide +kernel
example : X86Routine.decode [0x66,0x89,0xc3]=none := by decide +kernel
example : X86Routine.decode [0x66,0x89,0x43]=none := by decide +kernel
example : X86Routine.decode [0x0f,0x8c,0xd9,0xfe,0xff,0xff]=some (.jumpSigned 3 (-295),[]) := by decide +kernel
example : X86Routine.decode [0x0f,0x8c,0xd9]=none := by decide +kernel
end Doom.Verification.LineLoadFixture
