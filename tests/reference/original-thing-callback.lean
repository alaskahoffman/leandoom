import Doom.Proofs.E1M1ThingCallback
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
namespace ThingCallbackFixture
-- Deliberately synthetic states, including unaligned and wrapping stacks.
def machine (sp object answer link : Word) : X86Memory.State :=
  ⟨fun r => if r=0 then answer else if r=2 then object else if r=4 then sp else BitVec.ofNat 32 (r.val+100),
    ([(sp,0x2c720),(object+44,link)] : List (Word × Word)).foldl
      (fun m (a,v) => store32 m a v) (fun _ => 0)⟩
example : let s := machine 1 0x700401 0xdead 0x700800
    let out := OriginalThingCallback.called s none
    out.pc=0x2c720 ∧ out.core.regs 0=0x700401 ∧ out.core.regs 4=4294967293 ∧
    load32 out.core.memory 4294967293=0x2c5d7 ∧ load32 out.core.memory 1=0x2c720 := by decide +kernel
example : let s := machine 1 0x700401 0xdead 0x700800
    let out := OriginalThingCallback.entered s none
    out.pc=0x2c72b ∧ out.core.regs 1=0x700401 ∧ out.core.regs 4=4294967245 ∧
    load32 out.core.memory 4294967281=0x700401 ∧ load32 out.core.memory 4294967293=0x2c5d7 := by decide +kernel
example : let out := OriginalThingCallback.resumed (machine 1 0x700401 0 0x700800)
    out.pc=0x2c5e7 ∧ out.core.regs 2=0x700401 ∧ out.core.regs 4=1 := by decide +kernel
example : let out := OriginalThingCallback.resumed (machine 1 0x700401 1 0)
    out.pc=0x2c5e2 ∧ out.core.regs 2=0 ∧ out.core.regs 4=1 := by decide +kernel
example : let out := OriginalThingCallback.resumed (machine 1 0xffffffe0 1 0x700800)
    out.pc=0x2c5d2 ∧ out.core.regs 2=0x700800 ∧ out.core.regs 4=1 := by decide +kernel
-- A callback-modified link is the link the iterator actually observes.
def changed : X86Memory.State :=
  let s := machine 1 0x700401 1 0x700800
  {s with memory:=store32 s.memory (0x700401+44) 0x700c00}
theorem follows_changed_link : (OriginalThingCallback.resumed changed).core.regs 2=0x700c00 := by decide +kernel
#print axioms follows_changed_link
end ThingCallbackFixture
