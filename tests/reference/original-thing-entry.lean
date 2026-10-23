import Doom.Proofs.E1M1ThingEntry
set_option maxRecDepth 32768
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
namespace ThingEntryFixture
-- Diagnostic states; reachability from level startup is not claimed.
def machine (x y width height sp links object : Word) : X86Memory.State :=
  ⟨fun r => if r=0 then x else if r=2 then y else if r=3 then 0x2c720 else if r=4 then sp else 0,
    ([(0x2c0fc,width),(0x2c110,height),(0x2c0f8,links),
     (links+((x+y*width) <<< 2),object),(sp,0x2cab1)] : List (Word × Word)).foldl
      (fun m (a,v) => store32 m a v) (fun _ => 0)⟩
example : let out := OriginalThingEntry.result (machine 4294967295 0 36 23 1 0x800900 0x700400)
    out.pc=0x2cab1 ∧ out.core.regs 0=1 ∧ out.core.regs 4=5 := by decide +kernel
example : let out := OriginalThingEntry.result (machine 0 4294967295 36 23 1 0x800900 0x700400)
    out.pc=0x2cab1 ∧ out.core.regs 0=1 ∧ out.core.regs 4=5 := by decide +kernel
example : let out := OriginalThingEntry.result (machine 36 0 36 23 1 0x800900 0x700400)
    out.pc=0x2cab1 ∧ out.core.regs 0=1 ∧ out.core.regs 4=5 := by decide +kernel
example : let out := OriginalThingEntry.result (machine 0 23 36 23 1 0x800900 0x700400)
    out.pc=0x2cab1 ∧ out.core.regs 0=1 ∧ out.core.regs 4=5 := by decide +kernel
example : let out := OriginalThingEntry.result (machine 0 0 0 23 1 0x800900 0x700400)
    out.pc=0x2cab1 ∧ out.core.regs 0=1 ∧ out.core.regs 4=5 := by decide +kernel
example : let out := OriginalThingEntry.result (machine 0 0 36 0 1 0x800900 0x700400)
    out.pc=0x2cab1 ∧ out.core.regs 0=1 ∧ out.core.regs 4=5 := by decide +kernel
example : let out := OriginalThingEntry.result (machine 2147483648 0 36 23 1 0x800900 0x700400)
    out.pc=0x2cab1 ∧ out.core.regs 0=1 ∧ out.core.regs 4=5 := by decide +kernel
example : let out := OriginalThingEntry.result (machine 2147483647 0 36 23 1 0x800900 0x700400)
    out.pc=0x2cab1 ∧ out.core.regs 0=1 ∧ out.core.regs 4=5 := by decide +kernel
example : let out := OriginalThingEntry.result (machine 0 0 2147483648 23 1 0x800900 0x700400)
    out.pc=0x2cab1 ∧ out.core.regs 0=1 ∧ out.core.regs 4=5 := by decide +kernel
example : let out := OriginalThingEntry.result (machine 3 2 36 23 1 8390912 0)
    out.pc=182961 ∧ out.core.regs 4=5 ∧ out.core.regs 0=1 := by decide +kernel
example : let out := OriginalThingEntry.result (machine 3 2 36 23 1 8390912 7341057)
    out.pc=181714 ∧ out.core.regs 4=4294967293 ∧ out.core.regs 2=7341057 ∧ load32 out.core.memory (out.core.regs 4)=0x2c720 := by decide +kernel
example : let out := OriginalThingEntry.result (machine 1 0 2 1 9437185 4294967292 0)
    out.pc=182961 ∧ out.core.regs 4=9437189 ∧ out.core.regs 0=1 := by decide +kernel
example : let out := OriginalThingEntry.result (machine 1 0 2 1 9437185 4294967292 7341057)
    out.pc=181714 ∧ out.core.regs 4=9437181 ∧ out.core.regs 2=7341057 ∧ load32 out.core.memory (out.core.regs 4)=0x2c720 := by decide +kernel
example : let out := OriginalThingEntry.result (machine 35 22 36 23 4294967295 8390912 0)
    out.pc=182961 ∧ out.core.regs 4=3 ∧ out.core.regs 0=1 := by decide +kernel
example : let out := OriginalThingEntry.result (machine 35 22 36 23 4294967295 8390912 7341057)
    out.pc=181714 ∧ out.core.regs 4=4294967291 ∧ out.core.regs 2=7341057 ∧ load32 out.core.memory (out.core.regs 4)=0x2c720 := by decide +kernel
theorem empty_true : (OriginalThingEntry.result (machine 0 0 36 23 1 0x800900 0)).core.regs 0=1 := by decide +kernel
example : ¬Apart (0x2c0fc#32) ((0x2c100#32)-(4#32)) := by
  intro h; exact h ⟨0,by decide⟩ ⟨0,by decide⟩ (by decide)
#print axioms empty_true
end ThingEntryFixture
