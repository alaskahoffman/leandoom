import Doom.Proofs.OriginalAimOpening
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1OpeningHeights
open Verification X86 X86Memory X86Control BlockSummary
attribute [local irreducible] load32 store32

def saves (s : X86Memory.State) : List Word :=
  [s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32),s.regs 4-(16#32)]
def reads (line front back : Word) : List Word :=
  [line+(24#32),line+(46#32),line+(50#32),front,front+(4#32),back,back+(4#32)]
def Safe (s : X86Memory.State) (front back : Word) : Prop :=
  E1M1NoiseLedger.Protect (reads (s.regs 0) front back)
    (saves s ++ E1M1NoiseLineProgress.openingGlobals)

theorem saved_frame (s : X86Memory.State) (a : Word)
    (safe : ∀ b∈saves s, Apart a b) :
    load32 (NoiseOpening.saved s).memory a=load32 s.memory a := by
  simp only [NoiseOpening.saved,X86Routine.pushWord,put,write]
  simp only [ite_true,ite_false,BitVec.sub_sub]
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [saves]))]

theorem saved_half (s : X86Memory.State) (a : Word)
    (safe : ∀ b∈saves s, Apart a b) :
    load16 (NoiseOpening.saved s).memory a=load16 s.memory a := by
  have h := congrArg (fun w : Word => w.extractLsb' 0 16) (saved_frame s a safe)
  simpa only [load32,BitVec.extractLsb'_append_eq_right,load16] using h

/-- The helper's signed min/max outputs, derived from its entry memory. Read
separation includes the helper's stack saves and global writes. -/
theorem heights (s : X86Memory.State) (front back ff fc bf bc : Word)
    (safe : Safe s front back)
    (side : load16 s.memory (s.regs 0+(24#32)) ≠ 0xffff)
    (frontPtr : load32 s.memory (s.regs 0+(46#32))=front)
    (backPtr : load32 s.memory (s.regs 0+(50#32))=back)
    (frontFloor : load32 s.memory front=ff) (frontCeiling : load32 s.memory (front+(4#32))=fc)
    (backFloor : load32 s.memory back=bf) (backCeiling : load32 s.memory (back+(4#32))=bc) :
    load32 (E1M1NoiseOpening.result s).core.memory (0x2c034#32)=(if bc.toInt≤fc.toInt then bc else fc) ∧
    load32 (E1M1NoiseOpening.result s).core.memory (0x2c030#32)=(if ff.toInt≤bf.toInt then bf else ff) := by
  have keep (a : Word) (ha : a∈reads (s.regs 0) front back) :=
    saved_frame s a (fun b hb => safe a ha b (List.mem_append_left _ hb))
  have half := saved_half s (s.regs 0+(24#32)) (fun b hb => safe _ (by simp [reads]) b (List.mem_append_left _ hb))
  have side' : (load16 s.memory (s.regs 0+(24#32))).signExtend 32 ≠ (0xffffffff#32) := by
    exact fun eq => side ((OriginalLineCell.sentinel _).mp eq)
  have r0 : (NoiseOpening.saved s).regs 0=s.regs 0 := by simp [NoiseOpening.saved,X86Routine.pushWord,put,write]
  have entry : (NoiseOpening.entry s).pc≠0x2c34f := by
    simp [NoiseOpening.entry,NoiseOpening.prepared,put,write,r0]
    change (load16 (NoiseOpening.saved s).memory (s.regs 0+(24#32))).signExtend 32 ≠ (0xffffffff#32)
    rw [half]
    exact side'
  have global (a : Word) (ha : a∈reads (s.regs 0) front back)
      (m : Memory) (v : Word) (b : Word) (hb : b∈E1M1NoiseLineProgress.openingGlobals) :=
    load_store_apart m b a v (safe a ha b (List.mem_append_right _ hb))
  simp only [E1M1NoiseOpening.result,if_neg entry]
  simp [NoiseOpening.returned,NoiseOpening.range,NoiseOpening.floor,NoiseOpening.floorInputs,
    NoiseOpening.ceiling,NoiseOpening.ceilingInputs,NoiseOpening.entry,NoiseOpening.prepared,
    PspriteLoop.popped,put,write,r0,BitVec.add_zero,keep,global,reads,
    E1M1NoiseLineProgress.openingGlobals,frontPtr,backPtr,frontFloor,frontCeiling,backFloor,backCeiling]
  try simp only [load_store_apart _ _ _ _ (by unfold Apart; decide : Apart (0x2c034#32) (0x2c038#32)),
    load_store_apart _ _ _ _ (by unfold Apart; decide : Apart (0x2c034#32) (0x2c02c#32)),
    load_store_apart _ _ _ _ (by unfold Apart; decide : Apart (0x2c034#32) (0x2c030#32)),
    load_store_apart _ _ _ _ (by unfold Apart; decide : Apart (0x2c030#32) (0x2c038#32)),
    load_store_apart _ _ _ _ (by unfold Apart; decide : Apart (0x2c030#32) (0x2c02c#32)),load_store]
  constructor <;> first | exact True.intro | rfl
end Doom.Proofs.E1M1OpeningHeights
