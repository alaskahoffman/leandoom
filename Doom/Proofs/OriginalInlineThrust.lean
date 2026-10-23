import Doom.Proofs.OriginalThrust

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

namespace Doom.Proofs
open Verification X86 X86Memory X86Block BlockSummary

def forwardThrustOps := (decodeBlock 23 Doom19.forwardThrustBytes).getD []
def sideThrustOps := (decodeBlock 24 Doom19.sideThrustBytes).getD []
theorem forward_thrust_decoded :
    decodeBlock 23 Doom19.forwardThrustBytes = some forwardThrustOps := by rfl
theorem side_thrust_decoded :
    decodeBlock 24 Doom19.sideThrustBytes = some sideThrustOps := by rfl

/-- DL holds the forward command; DH holds the side command. -/
def inlineCommand (s : State) (side : Bool) : BitVec 8 :=
  (s.regs edx).extractLsb' (if side then 8 else 0) 8

def inlineAngle (s : State) (side : Bool) : Word :=
  let angle := load32 s.memory (load32 s.memory (s.regs ecx) + 32)
  if side then angle - 0x40000000 else angle

def inlineIndex (s : State) (side : Bool) : Word := inlineAngle s side >>> 19 <<< 2

def inlineScratch (s : State) (side : Bool) : Memory :=
  store32 s.memory (s.regs 4) (inlineIndex s side)

/-- Literal ordered memory effect, including the local stack word. No
non-aliasing assumptions: even overlapping input memory retains its semantics. -/
def inlineThrustMemory (s : State) (side : Bool) : Memory :=
  let obj := load32 s.memory (s.regs ecx)
  let index := inlineIndex s side
  let move := (inlineCommand s side).signExtend 32 <<< 11
  let m := inlineScratch s side
  let cosine := load32 m (load32 s.memory 0x13584 + index)
  let mx := load32 m (obj + 72) + mulWord move cosine
  let index' := load32 m (s.regs 4)
  let m := store32 m (obj + 72) mx
  let sine := load32 m (index' + 0x5a84)
  let obj' := load32 m (s.regs ecx)
  store32 m (obj' + 76) (load32 m (obj' + 76) + mulWord move sine)

theorem original_forward_thrust_memory (s : State) :
    (X86Block.run 23 Doom19.forwardThrustBytes s).map (·.memory) =
      some (inlineThrustMemory s false) := by
  rw [certified _ _ _ forward_thrust_decoded]
  dsimp only [inlineThrustMemory, inlineScratch, inlineIndex, inlineAngle, inlineCommand]
  summarize_x86 forwardThrustOps

theorem original_side_thrust_memory (s : State) :
    (X86Block.run 24 Doom19.sideThrustBytes s).map (·.memory) =
      some (inlineThrustMemory s true) := by
  rw [certified _ _ _ side_thrust_decoded]
  dsimp only [inlineThrustMemory, inlineScratch, inlineIndex, inlineAngle, inlineCommand]
  summarize_x86 sideThrustOps

/-- State used only to reuse the already proved standalone thrust theorem.
The actual inlined bytes are proved separately above. -/
def inlineAsThrust (s : State) (side : Bool) : State :=
  { regs := write (write (write s.regs eax (s.regs ecx)) edx (inlineAngle s side))
      ebx ((inlineCommand s side).signExtend 32 <<< 11)
    memory := inlineScratch s side }

theorem inline_reuses_thrust (s : State) (side : Bool)
    (hp : Apart (s.regs ecx) (s.regs 4))
    (hc : Apart 0x13584 (s.regs 4)) :
    inlineThrustMemory s side = thrustMemory (inlineAsThrust s side) := by
  have hp' := load_store_apart s.memory (s.regs 4) (s.regs ecx) (inlineIndex s side) hp
  have hc' := load_store_apart s.memory (s.regs 4) 0x13584 (inlineIndex s side) hc
  simp only [inlineThrustMemory, thrustMemory, inlineAsThrust, write, eax, ecx, edx, ebx]
  simp only [↓reduceIte, show (0 : Reg) ≠ 3 by decide, show (0 : Reg) ≠ 2 by decide,
    show (2 : Reg) ≠ 3 by decide, inlineScratch, load_store, hp', hc']
  rw [BitVec.add_comm (load32 s.memory 0x13584)]
  rfl

def inlineAim (body : Motion) (side : Bool) : Angle :=
  if side then ⟨body.angle.raw - 0x40000000⟩ else body.angle

def commandThrust (cmd : Int8) : Fixed := ⟨Int32.ofInt (cmd.toInt * 2048)⟩

theorem command_thrust_exact (cmd : Int8) :
    cmd.toBitVec.signExtend 32 <<< 11 = (commandThrust cmd).raw.toBitVec := by
  simp only [commandThrust, Int32.toBitVec_ofInt, BitVec.signExtend,
    BitVec.shiftLeft_eq_mul_twoPow, BitVec.ofInt_mul]
  rfl

/-- Entry memory obligations, stated before the original scratch write.
All disjointness is bytewise, allowing unaligned and wrapping addresses. -/
structure InlineThrustInputs (s : State) (body : Motion) (side : Bool) (cmd : Int8) : Prop where
  angle : load32 s.memory (load32 s.memory (s.regs ecx) + 32) = body.angle.raw.toBitVec
  command : inlineCommand s side = cmd.toBitVec
  tables : ThrustTables s.memory
  momx : load32 s.memory (load32 s.memory (s.regs ecx) + 72) = body.momx.raw.toBitVec
  momy : load32 s.memory (load32 s.memory (s.regs ecx) + 76) = body.momy.raw.toBitVec
  scratchPlayer : Apart (s.regs ecx) (s.regs 4)
  scratchPointer : Apart 0x13584 (s.regs 4)
  scratchCosine : Apart (inlineIndex s side + 0x7a84) (s.regs 4)
  scratchSine : Apart (inlineIndex s side + 0x5a84) (s.regs 4)
  scratchMomx : Apart (load32 s.memory (s.regs ecx) + 72) (s.regs 4)
  scratchMomy : Apart (load32 s.memory (s.regs ecx) + 76) (s.regs 4)
  playerApart : Apart (s.regs ecx) (load32 s.memory (s.regs ecx) + 72)
  sineApart : Apart (inlineIndex s side + 0x5a84) (load32 s.memory (s.regs ecx) + 72)

theorem inline_angle_exact (s : State) (body : Motion) (side : Bool) (cmd : Int8)
    (h : InlineThrustInputs s body side cmd) :
    inlineAngle s side = (inlineAim body side).raw.toBitVec := by
  simp only [inlineAngle, h.angle, inlineAim]
  cases side <;> rfl

theorem inline_thrust_inputs (s : State) (body : Motion) (side : Bool) (cmd : Int8)
    (h : InlineThrustInputs s body side cmd) :
    ThrustInputs (inlineAsThrust s side) body (inlineAim body side) (commandThrust cmd) := by
  have ha := inline_angle_exact s body side cmd h
  have lookups := thrust_selected_tables s.memory (inlineAim body side) h.tables
  rw [← ha, h.tables.cosinePointer] at lookups
  have hp := load_store_apart s.memory (s.regs 4) (s.regs ecx) (inlineIndex s side) h.scratchPlayer
  have hc := load_store_apart s.memory (s.regs 4) 0x13584 (inlineIndex s side) h.scratchPointer
  have hx := load_store_apart s.memory (s.regs 4) _ (inlineIndex s side) h.scratchMomx
  have hy := load_store_apart s.memory (s.regs 4) _ (inlineIndex s side) h.scratchMomy
  have hcos := load_store_apart s.memory (s.regs 4) _ (inlineIndex s side) h.scratchCosine
  have hsin := load_store_apart s.memory (s.regs 4) _ (inlineIndex s side) h.scratchSine
  constructor <;> simp only [inlineAsThrust, write, eax, ecx, edx, ebx, ↓reduceIte,
    show (0 : Reg) ≠ 3 by decide, show (0 : Reg) ≠ 2 by decide,
    show (2 : Reg) ≠ 3 by decide, inlineScratch, hp, hc, h.tables.cosinePointer]
  · exact ha
  · rw [h.command, command_thrust_exact]
  · exact hcos.trans lookups.1
  · exact hsin.trans lookups.2
  · exact hx.trans h.momx
  · exact hy.trans h.momy
  · exact h.playerApart
  · exact h.sineApart

/-- Entire final memory: original scratch word followed by the engine's two
momentum words. This records, rather than hides, the extra stack write. -/
def inlineThrustResult (s : State) (body : Motion) (side : Bool) (cmd : Int8) : Memory :=
  let obj := load32 s.memory (s.regs ecx)
  let result := body.thrust (inlineAim body side) (commandThrust cmd)
  store32 (store32 (inlineScratch s side) (obj + 72) result.momx.raw.toBitVec)
    (obj + 76) result.momy.raw.toBitVec

theorem inline_thrust_matches_engine (s : State) (body : Motion) (side : Bool) (cmd : Int8)
    (h : InlineThrustInputs s body side cmd) :
    inlineThrustMemory s side = inlineThrustResult s body side cmd := by
  rw [inline_reuses_thrust s side h.scratchPlayer h.scratchPointer,
    thrust_memory_matches_engine _ _ _ _ (inline_thrust_inputs s body side cmd h)]
  have hp := load_store_apart s.memory (s.regs 4) (s.regs ecx) (inlineIndex s side) h.scratchPlayer
  simp only [thrustResultMemory, inlineThrustResult, inlineAsThrust, write, eax, ecx, edx, ebx,
    ↓reduceIte, show (0 : Reg) ≠ 3 by decide, show (0 : Reg) ≠ 2 by decide, inlineScratch, hp]

theorem forward_thrust_matches_doom19 (s : State) (body : Motion) (cmd : Int8)
    (h : InlineThrustInputs s body false cmd) :
    (X86Block.run 23 Doom19.forwardThrustBytes s).map (·.memory) =
      some (inlineThrustResult s body false cmd) := by
  rw [original_forward_thrust_memory, inline_thrust_matches_engine s body false cmd h]

theorem side_thrust_matches_doom19 (s : State) (body : Motion) (cmd : Int8)
    (h : InlineThrustInputs s body true cmd) :
    (X86Block.run 24 Doom19.sideThrustBytes s).map (·.memory) =
      some (inlineThrustResult s body true cmd) := by
  rw [original_side_thrust_memory, inline_thrust_matches_engine s body true cmd h]

end Doom.Proofs
