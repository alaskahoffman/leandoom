import Doom.Proofs.E1M1LineCache
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Verification.LineCacheFixture
open Doom Doom.Proofs X86 X86Memory X86Control BlockSummary OriginalLineCache E1M1LineCache E1M1NoiseImage
local instance (a b : Word) : Decidable (Apart a b) := by unfold Apart; infer_instance

def state (line : Word) (fi bi : BitVec 16) : X86Memory.State :=
  ⟨fun r => if r=3 then line else 0x12345678,
    applyPatch (half (line+22) fi ++ half (line+24) bi)
      (store32 (store32 (store32 (store32 (store32 (store32 (fun _ => 0xaa)
        0x2c118 0x600001) 0x60000f 0x610001) 0x600021 0x630001)
        0x610021 0x620003) 0x57000f 0x640005) 0x70012f 0x55555555)⟩
def ordinary := state 0x680101 0 1

def entry : OriginalGroupOutput.Line := ⟨0x680101,0x610001,0x630001⟩
def source : Source entry ordinary :=
  ⟨0,1,0x600001,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    by decide +kernel,by decide +kernel,by decide +kernel,fun _ => by decide +kernel⟩

example : value ordinary 22=0x610001 := by decide +kernel
example : value (front ordinary).core 24=0x630001 := by decide +kernel
example : (result ordinary).core.regs 3=0x680101 := by decide +kernel
example : (result ordinary).core.regs 1=0x12345678 := by decide +kernel
example : ∃ out, X86Routine.run program [0x2e3ac] 16 ⟨ordinary,none,0x2e368⟩=some out ∧
    OriginalGroupOutput.Inputs [entry] out.core.memory := establishes entry ordinary none source

-- Missing front AND back sides write null; EDX is untouched and EAX is -1.
example : value (state 0x680101 65535 65535) 22=0 := by decide +kernel
example : (result (state 0x680101 65535 65535)).core.regs 0=0xffffffff := by decide +kernel
example : (result (state 0x680101 65535 65535)).core.regs 2=0x12345678 := by decide +kernel
example : load32 (result (state 0x680101 65535 65535)).core.memory 0x680133=0 := by decide +kernel
-- Signed malformed indices still follow the original machine instructions.
example : value (state 0x680101 32768 65535) 22=0x640005 := by decide +kernel
-- Pointer destinations can wrap; the two four-byte fields remain disjoint.
example : load32 (result (state 0xffffffe0 0 1)).core.memory 14=0x610001 := by decide +kernel
example : load32 (result (state 0xffffffe0 0 1)).core.memory 18=0x630001 := by decide +kernel
-- The front store replaces the side-table base, so the back lookup changes.
def aliased := state (0x2c118-46) 0 1
example : value aliased 24=0x630001 := by decide +kernel
example : value (front aliased).core 24=0x620003 := by decide +kernel
example : ¬Apart 0x2c118 (aliased.regs 3+46) := by decide +kernel
example : load32 (result aliased).core.memory (aliased.regs 3+50)=0x620003 := by decide +kernel

-- Existing cached lines are carried through the newly executed segment.
def old : OriginalGroupOutput.Line := ⟨0x700101,0x55555555,0xaaaaaaaa⟩
example : ∃ out, X86Routine.run program [0x2e3ac] 16 ⟨ordinary,none,0x2e368⟩=some out ∧
    OriginalGroupOutput.Inputs [entry,old] out.core.memory :=
  extend_inputs entry [old] ordinary none source (by intro l hl; simp only [List.mem_singleton] at hl; subst l; constructor <;> decide +kernel)
    (by intro l hl; simp only [List.mem_singleton] at hl; subst l
        intro off ho; rcases List.mem_cons.mp ho with eq|rest
        · subst off; constructor <;> decide +kernel
        · have eq : off=50 := by simpa using rest
          subst off; constructor <;> decide +kernel)
end Doom.Verification.LineCacheFixture
