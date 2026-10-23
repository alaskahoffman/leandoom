import Doom.Proofs.E1M1ThingFinish
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
namespace ThingFinishFixture
-- Diagnostic callback-body states, not claims of reachable E1M1 states.
-- SP=1 exercises wrapping helper saves, while the caller's saved frame is above SP.
def machine (x y next : Word) : X86Memory.State :=
  ⟨fun r => if r=1 then 0x700401 else if r=4 then 1 else 0,
    ([(0x2ba10,0),(0x2ba14,0),(0x2ba18,65536),(0x2ba1c,131072),(0x2c028,0x2ba2c),
      (0x2ba20,99),(0x2ba24,1),(0x2ba28,0x1234),
      (0x70040d,x),(0x700411,y),(0x700441,65536),(0x70042d,next),
      (25,0x5555),(29,0x7777),(33,0x6666),(37,0x700401),(41,0x1111),(45,0x3333),(49,0x2c5d7)] : List (Word × Word)).foldl
      (fun m (a,v) => store32 m a v) (fun _ => 0)⟩
theorem appended_and_resumed : let out := E1M1ThingReturn.resumed (machine 65536 131072 0x700801)
    out.pc=0x2c5d2 ∧ out.core.regs 0=1 ∧ out.core.regs 2=0x700801 ∧ out.core.regs 4=53 ∧
    load32 out.core.memory 0x2c028=0x2ba38 ∧
    load32 out.core.memory 0x2ba2c=65536 ∧ load32 out.core.memory 0x2ba30=0 ∧
    load32 out.core.memory 0x2ba34=0x700401 ∧
    load32 out.core.memory 0x2ba20=99 ∧ load32 out.core.memory 0x2ba24=1 ∧ load32 out.core.memory 0x2ba28=0x1234 := by decide +kernel
example : let out := E1M1ThingReturn.finished (machine 65536 131072 0)
    out.pc=0x2c5d7 ∧ out.core.regs 2=0x700401 ∧ out.core.regs 4=53 ∧
    out.core.regs 5=0x5555 ∧ out.core.regs 7=0x7777 ∧ out.core.regs 6=0x6666 ∧
    out.core.regs 1=0x1111 ∧ out.core.regs 3=0x3333 := by decide +kernel
example : let out := E1M1ThingReturn.resumed (machine 4294901760 4294836224 0)
    out.pc=0x2c5e2 ∧ out.core.regs 0=1 ∧ out.core.regs 2=0 ∧ out.core.regs 4=53 ∧
    load32 out.core.memory 0x2c028=0x2ba2c := by decide +kernel
example : let out := E1M1ThingReturn.resumed (machine 196608 131072 0)
    out.pc=0x2c5e2 ∧ out.core.regs 0=1 ∧ load32 out.core.memory 0x2c028=0x2ba2c := by decide +kernel
example : let out := E1M1ThingReturn.resumed (machine 0 0 0)
    out.pc=0x2c5e2 ∧ load32 out.core.memory 0x2ba2c=0 ∧ load32 out.core.memory 0x2c028=0x2ba38 := by decide +kernel
-- Deliberate alias: insertion overwrites the next-link word. The iterator must read
-- the post-callback link, even though an actual object-layout proof would exclude it.
def aliased : X86Control.State :=
  ⟨⟨fun r => if r=0 then 65536 else if r=1 then 0x3fdc else if r=4 then 0x8001 else 0,
    ([(0x2c028,0x4000),(0x4008,0),(0x8025,0x3fdc),(0x8031,0x2c5d7)] : List (Word × Word)).foldl
      (fun m (a,v) => store32 m a v) (fun _ => 0)⟩,none,0x2c7e4⟩
example : let out := OriginalThingCallback.resumed (OriginalThingFinish.result aliased).core
    out.pc=0x2c5d2 ∧ out.core.regs 2=0x3fdc := by decide +kernel
#print axioms appended_and_resumed
end ThingFinishFixture
