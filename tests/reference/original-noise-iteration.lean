import Doom.Proofs.E1M1NoiseIteration
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
namespace Doom.Verification.NoiseIterationFixture
open Doom Doom.Proofs X86 X86Memory X86Control

def parent : Word := 0x600101
def child : Word := 0x600301
def closedSector : Word := 0x600501
def sides : Word := 0x600701
def lines : Word := 0x600901
def line (i : Nat) : Word := 0x601001+BitVec.ofNat 32 (i*64)
def initial (blocks : Word) : X86Memory.State :=
  ⟨fun r => if r=0 then parent else if r=2 then blocks else if r=4 then 1 else BitVec.ofNat 32 (10+r.val),
    ([ (parent,0),(parent+4,128),(parent+66,6),(parent+78,5),(parent+82,lines),
       (child,24),(child+4,96),(child+66,6),(child+18,0),(child+78,0),
       (closedSector,128),(closedSector+4,128),(0x13580,7),(0x2b958,0x600d01),(0x2c118,sides),
       (sides+14,parent),(sides+32,child),(sides+50,closedSector),(1,0x28000)] ++
     (List.range 5).flatMap (fun i => [(lines+BitVec.ofNat 32 (4*i),line i),
       (line i+16,if i=0 then 0 else if i=2 then 68 else 4),
       (line i+22,if i=1 then 0x20000 else 0x10000),(line i+46,parent),
       (line i+50,if i=1 then closedSector else child)]) : List (Word × Word)).foldl
      (fun m p => store32 m p.1 p.2) (fun _ => 0)⟩
def start (b : Word) := E1M1NoiseIteration.started (initial b)
def after (k : Nat) (b : Word) := E1M1NoiseIteration.loop k (start b)

theorem inputs_zero : E1M1NoiseIteration.LoopInputs 5 (start 0) := by
  simp only [E1M1NoiseIteration.LoopInputs]
  repeat' (first | constructor | intro)
  all_goals first | contradiction | decide
theorem inputs_one : E1M1NoiseIteration.LoopInputs 5 (start 1) := by
  simp only [E1M1NoiseIteration.LoopInputs]
  repeat' (first | constructor | intro)
  all_goals first | contradiction | decide
example : (after 4 0).pc=0x26fa8 ∧ (after 4 0).core.regs 6=4 := by decide
example : (after 5 0).pc=0x27011 ∧ (after 5 0).core.regs 6=5 ∧ (after 5 0).core.regs 5=20 := by decide
-- The blocking route first writes cost two; the ordinary route improves it.
example : load32 (after 3 0).core.memory (child+18)=2 ∧
    load32 (after 4 0).core.memory (child+18)=1 ∧
    load32 (after 5 0).core.memory (child+18)=1 := by decide
example : load32 (after 5 1).core.memory (child+18)=2 ∧
    load32 (after 5 1).core.memory (child+22)=0x600d01 := by decide
example : ∃ n, n≤95*5+32 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1NoiseIteration.program [] n
    ⟨initial 0,none,0x26f60⟩ (E1M1NoiseIteration.sectorResult 5 (initial 0)) :=
  E1M1NoiseIteration.sector_execution _ _ _ (by decide) inputs_zero (by decide)
example : (E1M1NoiseIteration.sectorResult 5 (initial 0)).pc=0x28000 ∧
    (E1M1NoiseIteration.sectorResult 5 (initial 0)).core.regs 4=5 ∧
    (E1M1NoiseIteration.sectorResult 5 (initial 0)).core.regs 3=13 := by decide
-- A truncated prefix cannot be described as a completed sector.
example : ¬(after 4 0).pc=0x27011 := by decide
end Doom.Verification.NoiseIterationFixture
