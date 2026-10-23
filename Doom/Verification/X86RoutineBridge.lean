import Doom.Verification.X86Routine
import Doom.Verification.X86Paths

namespace Doom.Verification.X86Routine
open X86Control

/-- Lift a previously checked control-flow path into the call-capable machine.
Only PC is translated; memory, registers and flags are the same at every step. -/
theorem lift_control_prefix {p exits n s t} (path : X86Control.Prefix p exits n s t)
    (q : X86Routine.Program) (outer : List Nat) (base : Nat)
    (agree : ∀ pc op len, p pc = some (op,len) → q (base+pc) = some (.control op,len))
    (active : ∀ pc, p pc ≠ none → base+pc ∉ outer)
    (forward : ∀ pc op len, p pc = some (op,len) → ForwardOp op) :
    X86Routine.Prefix q outer n (shiftState base s) (shiftState base t) := by
  induction path with
  | nil => exact X86Routine.Prefix.nil _
  | @step n s middle last op len ha hd hx rest ih =>
    have valid : p s.pc ≠ none := by simp [hd]
    refine X86Routine.Prefix.step (active s.pc valid) (agree s.pc op len hd) ?_ ih
    have he := execute_shift base op {s with pc := s.pc+len} (forward s.pc op len hd)
    rw [hx] at he
    simpa only [X86Routine.execute,shiftState,Nat.add_assoc,Option.map_some] using he

/-- Unsupported addresses beyond the immutable byte slice never decode. -/
theorem control_decode_bound (code : List UInt8) (pc : Nat)
    (h : X86Control.decodeAt code pc ≠ none) : pc < code.length := by
  by_cases hp : pc < code.length
  · exact hp
  · have hz := List.drop_eq_nil_of_le (show code.length ≤ pc by omega)
    simp [X86Control.decodeAt,hz,X86Control.decode,X86Block.decode,X86Memory.decode,X86.decode] at h

theorem decodeAt_append (head tail : List UInt8) (pc : Nat) :
    X86Routine.decodeAt (head ++ tail) (head.length+pc) = X86Routine.decodeAt tail pc := by
  simp [X86Routine.decodeAt]

end Doom.Verification.X86Routine
