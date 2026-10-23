import Doom.Proofs.E1M1NoiseRecursive
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
namespace Doom.Verification.NoiseRecursiveFixture
open Doom Doom.Proofs X86 X86Memory X86Control

def sector (i : Nat) : Word := 0x600101+BitVec.ofNat 32 (256*i)
def line (i : Nat) : Word := 0x601001+BitVec.ofNat 32 (64*i)
def sides : Word := 0x600801
def initial (secondBlock : Bool) : X86Control.State :=
  ⟨⟨fun r => if r=0 then sector 0 else if r=2 then 0 else if r=4 then 1 else BitVec.ofNat 32 (10+r.val),
    ([(0x13580,7),(0x2b958,0x600d01),(0x2c118,sides),(1,0x28000)] ++
      (List.range 3).flatMap (fun i => [
        (sector i,0),(sector i+4,128),(sector i+66,6),(sector i+18,0),(sector i+22,0),
        (sector i+78,1),(sector i+82,0x600b01+BitVec.ofNat 32 (4*i)),
        (0x600b01+BitVec.ofNat 32 (4*i),line i),
        (line i+16,if i=0 ∨ (i=1 ∧ secondBlock) then 68 else 4),
        (line i+22,BitVec.ofNat 32 ((2*i)+65536*(2*i+1))),
        (line i+46,sector i),(line i+50,sector ((i+1)%3)),
        (sides+BitVec.ofNat 32 (36*i+14),sector i),
        (sides+BitVec.ofNat 32 (36*i+32),sector ((i+1)%3))]) : List (Word × Word)).foldl
      (fun m p => store32 m p.1 p.2) (fun _ => 0)⟩,none,0x26f60⟩
def evaluated (blocked : Bool) := E1M1NoiseRecursive.eval 10 .sector (initial blocked)
def finalState (blocked : Bool) := (evaluated blocked).getD (initial blocked)

theorem complete (blocked : Bool) : evaluated blocked=some (finalState blocked) := by
  have ok : (evaluated blocked).isSome=true := by cases blocked <;> decide
  cases h : evaluated blocked with
  | none => simp [h] at ok
  | some t => simp [finalState,h]
example : E1M1NoiseRecursive.Runs (E1M1NoiseRecursive.bound 10) (initial false) (finalState false) :=
  E1M1NoiseRecursive.execution _ .sector _ _ rfl (complete false)
example : (finalState false).pc=0x28000 ∧ (finalState false).core.regs 4=5 ∧
    (finalState false).core.regs 3=13 := by decide
example : load32 (finalState false).core.memory (sector 0+18)=1 ∧
    load32 (finalState false).core.memory (sector 1+18)=2 ∧
    load32 (finalState false).core.memory (sector 2+18)=2 ∧
    load32 (finalState false).core.memory (sector 2+22)=0x600d01 := by decide
-- Crossing a second sound-blocking line is rejected, leaving the third sector untouched.
example : load32 (finalState true).core.memory (sector 2+66)=6 ∧
    load32 (finalState true).core.memory (sector 2+22)=0 := by decide
-- Insufficient fuel does not certify a partial result as a completed call.
example : (E1M1NoiseRecursive.eval 3 .sector (initial false)).isNone=true := by decide
end Doom.Verification.NoiseRecursiveFixture
