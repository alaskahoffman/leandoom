import Doom.Verification.X86Compose

namespace Doom.Verification.X86Control

abbrev Packet := X86Block.Op × Nat

/-- Instruction lengths are measured by the same byte decoder used for blocks. -/
def decodePackets : Nat → List UInt8 → Option (List Packet)
  | 0, [] => some []
  | 0, _ :: _ => none
  | n+1, code => do
    let (op, rest) ← X86Block.decode code
    let tail ← decodePackets n rest
    pure ((op, code.length - rest.length) :: tail)

def linearStep (packet : Packet) (s : State) : State :=
  { core := X86Block.execute packet.1 s.core
    flags := if blockPreservesFlags packet.1 then s.flags else none
    pc := s.pc + packet.2 }

def linearEnd : List Packet → State → State
  | [], s => s
  | packet :: rest, s => linearEnd rest (linearStep packet s)

/-- Static obligations for a straight-line block inside a control-flow program. -/
def LinearFits (program : Program) (exits : List Nat) : Nat → List Packet → Prop
  | _, [] => True
  | pc, packet :: rest => pc ∉ exits ∧ program pc = some (.block packet.1, packet.2) ∧
      LinearFits program exits (pc + packet.2) rest

def linearFitsDecidable (program : Program) (exits : List Nat) (pc : Nat) :
    (packets : List Packet) → Decidable (LinearFits program exits pc packets)
  | [] => isTrue trivial
  | packet :: rest => by
    dsimp only [LinearFits]
    letI := linearFitsDecidable program exits (pc + packet.2) rest
    infer_instance

instance (program : Program) (exits : List Nat) (pc : Nat) (packets : List Packet) :
    Decidable (LinearFits program exits pc packets) := linearFitsDecidable program exits pc packets

theorem linear_prefix (packets : List Packet) (program : Program) (exits : List Nat)
    (s : State) (fits : LinearFits program exits s.pc packets) :
    Prefix program exits packets.length s (linearEnd packets s) := by
  induction packets generalizing s with
  | nil => exact Prefix.nil s
  | cons packet rest ih =>
    exact Prefix.step fits.1 fits.2.1 (by rfl) (ih (linearStep packet s) fits.2.2)

theorem linear_core (packets : List Packet) (s : State) :
    (linearEnd packets s).core = X86Block.eval (packets.map Prod.fst) s.core := by
  induction packets generalizing s with
  | nil => rfl
  | cons packet rest ih => exact ih (linearStep packet s)

def linearSize (packets : List Packet) : Nat := (packets.map Prod.snd).sum

theorem linear_pc (packets : List Packet) (s : State) :
    (linearEnd packets s).pc = s.pc + linearSize packets := by
  induction packets generalizing s with
  | nil => simp [linearEnd, linearSize]
  | cons packet rest ih =>
    simp only [linearEnd, ih, linearStep, linearSize, List.map_cons, List.sum_cons]
    omega

def linearFlags : List Packet → Option Flags → Option Flags
  | [], flags => flags
  | packet :: rest, flags =>
      linearFlags rest (if blockPreservesFlags packet.1 then flags else none)

theorem linear_flags (packets : List Packet) (s : State) :
    (linearEnd packets s).flags = linearFlags packets s.flags := by
  induction packets generalizing s with
  | nil => rfl
  | cons packet rest ih => exact ih (linearStep packet s)

/-- A generic bridge from the straight-line register/memory semantics to a
continuous control-flow execution, including the outgoing flag projection. -/
theorem linear_state (packets : List Packet) (s : State) :
    linearEnd packets s = ⟨X86Block.eval (packets.map Prod.fst) s.core,
      linearFlags packets s.flags, s.pc + linearSize packets⟩ := by
  have hc := linear_core packets s
  have hp := linear_pc packets s
  have hf := linear_flags packets s
  cases he : linearEnd packets s
  simp_all

end Doom.Verification.X86Control
