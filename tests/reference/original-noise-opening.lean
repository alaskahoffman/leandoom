import Doom.Proofs.E1M1NoiseOpening
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Doom.Verification.NoiseOpeningFixture
open Doom Doom.Proofs X86 X86Memory X86Control

def line : Word := 0x600101
def front : Word := 0x600301
def back : Word := 0x600501
def sides : Word := 0x600701
def initial : X86Memory.State :=
  ⟨fun r => if r=0 ∨ r=2 then line else if r=3 then front else if r=4 then 1 else 0,
    ([(line+16,4),(line+22,0x10000),(line+46,front),(line+50,back),
      (front,0),(front+4,128),(back,24),(back+4,96),(0x2c118,sides),
      (sides+14,front),(sides+32,back),(1,0x28000),(0x2c034,111)] : List (Word × Word)).foldl
      (fun m p => store32 m p.1 p.2) (fun _ => 0)⟩
def result := E1M1NoiseOpening.result initial
example : result.pc=0x28000 ∧ result.core.regs 4=5 ∧
    result.core.regs 2=line ∧ result.core.regs 3=front ∧
    load32 result.core.memory 0x2c034=96 ∧ load32 result.core.memory 0x2c030=24 ∧
    load32 result.core.memory 0x2c02c=0 ∧ load32 result.core.memory 0x2c038=72 := by decide
example : ∃ n, n≤31 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1NoiseOpening.program [] n
    ⟨initial,none,0x2c340⟩ result := E1M1NoiseOpening.opening_execution _ _
def blocked := {initial with memory := store32 initial.memory (back+4) 24}
example : (E1M1NoiseOpening.blockResult blocked none).pc=0x27006 := by decide
example : (E1M1NoiseOpening.blockResult initial none).pc=0x26f60 ∧
    (E1M1NoiseOpening.blockResult initial none).core.regs 0=back ∧
    (E1M1NoiseOpening.blockResult initial none).core.regs 2=0 ∧
    load32 (E1M1NoiseOpening.blockResult initial none).core.memory 0xfffffffd=0x27006 := by decide
example : ∃ n, n≤55 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1NoiseOpening.program [] n
    ⟨initial,none,0x26fb4⟩ (E1M1NoiseOpening.blockResult initial none) :=
  E1M1NoiseOpening.block_execution _ _ (by decide)
def missing := {initial with memory := X86Routine.store16 initial.memory (line+24) 0xffff}
example : load32 (E1M1NoiseOpening.result missing).core.memory 0x2c038=0 ∧
    load32 (E1M1NoiseOpening.result missing).core.memory 0x2c034=111 := by decide

def wrapped := {initial with memory := (
  ([(front,0x80000000),(back,0x80000000),(front+4,0x7fffffff),(back+4,0x7fffffff)] : List (Word × Word)).foldl
    (fun (m : Memory) (p : Word × Word) => store32 m p.1 p.2) initial.memory)}
example : load32 (E1M1NoiseOpening.result wrapped).core.memory 0x2c038=0xffffffff ∧
    (E1M1NoiseOpening.blockResult wrapped none).pc=0x27006 := by decide
-- The output write is deliberately also the next front-floor input.
def aliasOpening := {initial with memory := store32 (store32 initial.memory (line+46) 0x2c034) 0x2c038 96}
example : load32 (E1M1NoiseOpening.result aliasOpening).core.memory 0x2c034=96 ∧
    load32 (E1M1NoiseOpening.result aliasOpening).core.memory 0x2c030=96 ∧
    load32 (E1M1NoiseOpening.result aliasOpening).core.memory 0x2c038=0 := by decide
-- Neighbor lookup reads its front sector after storing the scratch word.
def aliasNeighbor := put initial 4 (sides+14)
example : (E1M1NoiseOpening.neighbor aliasNeighbor).core.regs 0=sides := by decide
-- A signed -1 front index addresses the record before the side-array base.
def negativeSide := {initial with memory := (store32
    (X86Routine.store16 initial.memory (line+22) 0xffff) (sides-18+14) back)}
example : (E1M1NoiseOpening.neighbor negativeSide).core.regs 0=back := by decide

example : X86Routine.decode [0x03,0x04,0x24]=some (.addMemory 0 ⟨some 4,none,0,0⟩,[]) := by decide
example : X86Routine.decode [0x2b,0x15,0x30,0xc0,0x02,0x00]=some (.subMemory 2 ⟨none,none,0,0x2c030⟩,[]) := by decide
example : X86Routine.decode [0x2b,0xc2]=some (.control (.block (.arithmetic (.sub 0 2))),[]) := by decide
example : X86Routine.decode [0x03,0xc0]=none := by decide
example : X86Routine.decode [0x03,0x04]=none ∧ X86Routine.decode [0x2b,0x15,0x30]=none := by decide
end Doom.Verification.NoiseOpeningFixture
