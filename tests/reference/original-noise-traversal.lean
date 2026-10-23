import Doom.Proofs.E1M1NoiseTraversal
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Doom.Verification.NoiseTraversalFixture
open Doom Doom.Proofs X86 X86Memory X86Control

def parent : Word := 0x600101
def child : Word := 0x600301
def line : Word := 0x600501
def initial (flag blocks stamp : Word) : X86Memory.State :=
  ⟨fun r => if r=0 then child else if r=1 then blocks else if r=2 then line else
      if r=3 then parent else if r=4 then 1 else if r=5 then 0xfffffffc else 0,
    ([(line+16,flag),(parent+78,2),(parent+82,0x600701),(0x600701,line),
      (child+66,stamp),(child+18,1),(child+78,0),(0x13580,7),(0x2b958,0x600901)] : List (Word × Word)).foldl
      (fun m p => store32 m p.1 p.2) (fun _ => 0)⟩
def ordinary := initial 4 0 6
def blocking := initial 68 0 6
def pruned := initial 4 0 7
example : (E1M1NoiseTraversal.firstLine ordinary).pc=0x26fb4 ∧
    (E1M1NoiseTraversal.firstLine ordinary).core.regs 2=line := by decide
example : (E1M1NoiseTraversal.firstLine (initial 0 0 6)).pc=0x27006 := by decide
example : (NoiseTraversal.blockResult blocking).core.regs 2=1 ∧
    (NoiseTraversal.blockResult blocking).core.regs 4=0xfffffffd ∧
    load32 (NoiseTraversal.blockResult blocking).core.memory 0xfffffffd=0x27006 := by decide
example : (NoiseTraversal.blockResult (initial 68 1 6)).pc=0x27006 ∧
    (NoiseTraversal.blockResult (initial 68 0xffffffff 6)).pc=0x27006 := by decide
example : (E1M1NoiseTraversal.childReturn ordinary).pc=0x27006 ∧
    (E1M1NoiseTraversal.childReturn ordinary).core.regs 4=1 ∧
    (E1M1NoiseTraversal.childReturn ordinary).core.regs 3=parent ∧
    load32 (E1M1NoiseTraversal.childReturn ordinary).core.memory (child+22)=0x600901 := by decide
example : load32 (E1M1NoiseTraversal.childReturn pruned).core.memory (child+22)=0 := by decide
example : load32 (E1M1NoiseTraversal.childReturn blocking).core.memory (child+18)=2 := by decide
example : (NoiseTraversal.advanced (E1M1NoiseTraversal.childReturn blocking).core).pc=0x26fa8 ∧
    (NoiseTraversal.advanced (E1M1NoiseTraversal.childReturn blocking).core).core.regs 5=0 := by decide
example : ∃ n, n≤43 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1NoiseTraversal.program [] n
    ⟨blocking,none,0x26fee⟩ (NoiseTraversal.advanced (E1M1NoiseTraversal.childReturn blocking).core) :=
  E1M1NoiseTraversal.child_execution _ _ (by decide) (by decide) (by decide)
example : ∃ n, n≤43 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1NoiseTraversal.program [] n
    ⟨pruned,none,0x26fee⟩ (NoiseTraversal.advanced (E1M1NoiseTraversal.childReturn pruned).core) :=
  E1M1NoiseTraversal.child_execution _ _ (by decide) (by decide) (by decide)
def gap (v : Word) := NoiseTraversal.openingGate {ordinary with memory := store32 ordinary.memory 0x2c038 v}
example : (gap 0).pc=0x27006 ∧ (gap 0x80000000).pc=0x27006 ∧
    (gap 0x7fffffff).pc=0x26fc4 := by decide
example : (NoiseTraversal.advanced (X86Memory.put ordinary 6 0x7fffffff)).pc=0x26fa8 ∧
    (NoiseTraversal.advanced (X86Memory.put ordinary 6 0x7fffffff)).core.regs 6=0x80000000 := by decide
end Doom.Verification.NoiseTraversalFixture
