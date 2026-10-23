import Doom.Proofs.OriginalGroupBounds
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
open Doom.Verification Doom.Proofs X86 X86Memory X86Control BlockSummary OriginalGroupBounds
-- Inverted incoming bounds deliberately exercise the original else-if rule.
def malformed : X86Memory.State :=
  let m : Memory := fun _ => 0
  let m := store32 m 0x100 0xfffffff6
  let m := store32 m 0x104 10
  let m := store32 m 0x108 10
  let m := store32 m 0x10c 0xfffffff6
  let m := store32 m 0x200 0x1234
  ⟨fun r => if r=0 then 0x100 else if r=4 then 0x200 else 0,m⟩
example : (boxResult malformed).pc=0x1234 ∧ (boxResult malformed).core.regs 4=0x204 ∧
    load32 (boxResult malformed).core.memory 0x108=0 ∧
    load32 (boxResult malformed).core.memory 0x10c=0xfffffff6 ∧
    load32 (boxResult malformed).core.memory 0x104=0 ∧
    load32 (boxResult malformed).core.memory 0x100=0xfffffff6 := by decide +kernel

-- The first Y update replaces the second vertex pointer. It must be reloaded
-- after that update: caching it before the first call produces a different box.
def aliased : X86Memory.State :=
  let m : Memory := fun _ => 0
  let m := store32 m 0x100 0x200
  let m := store32 m 0x104 0x400
  let m := store32 m 0x108 10
  let m := store32 m 0x10c 20
  let m := store32 m 0x200 5
  let m := store32 m 0x204 0x300
  let m := store32 m 0x300 0xfffffffb
  let m := store32 m 0x304 900
  let m := store32 m 0x400 2000
  let m := store32 m 0x404 3000
  let m := store32 m 0x2c134 2
  ⟨fun r => if r=1 ∨ r=4 then 0x100 else if r=6 then 0x500 else 0,m⟩
example : (result aliased).pc=0x2e676 ∧ (result aliased).core.regs 4=0x100 ∧
    (result aliased).core.regs 6=0x504 ∧ (result aliased).core.regs 1=0x13e ∧
    (result aliased).core.regs 7=1 ∧
    load32 (result aliased).core.memory 0x100=900 ∧
    load32 (result aliased).core.memory 0x104=0x300 ∧
    load32 (result aliased).core.memory 0x108=0xfffffffb ∧
    load32 (result aliased).core.memory 0x10c=20 ∧
    load32 (result aliased).core.memory 0xfc=0x2e6a2 := by decide +kernel
example : X86Routine.run program exits 38 ⟨aliased,none,0x2e682⟩=some (result aliased) :=
  joined_execution aliased none
example : Apart (0#32-4) 0 ∧ Apart (0#32-4) 4 ∧ Apart (0#32-4) 8 ∧ Apart (0#32-4) 12 :=
  stack_apart 0
-- Signed overflow of the scan counter follows the original signed JL.
def overflow : X86Memory.State := ⟨fun r => if r=7 then 0x7fffffff else 0,fun _ => 0⟩
example : (advanced overflow).pc=0x2e676 ∧ (advanced overflow).core.regs 7=0x80000000 := by decide +kernel
