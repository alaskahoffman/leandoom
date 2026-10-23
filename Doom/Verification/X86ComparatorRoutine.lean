import Doom.Verification.X86BytePrefix
/-! Opt-in DEC register decoding. Like existing INC/DEC projections, forgets
flags; the loop-header TEST overwrites them before the next consumer. -/
namespace Doom.Verification.X86ComparatorRoutine
open X86 X86Memory X86Control

def decode (bytes : List UInt8) : Option (X86ByteRoutine.Op × List UInt8) :=
  match bytes with
  | op :: tail =>
      if 0x48≤op.toNat ∧ op.toNat≤0x4f then
        some (.base (.addImmediate (Fin.ofNat 8 (op.toNat-0x48)) (-1)),tail)
      else X86ByteRoutine.decode bytes
  | [] => none

def decodeAt (bytes : List UInt8) (pc : Nat) : Option (X86ByteRoutine.Op × Nat) :=
  (decode (bytes.drop pc)).map fun (op,tail) => (op,(bytes.drop pc).length-tail.length)

theorem decrement_core (s : X86Control.State) (r : Reg) :
    X86ByteRoutine.execute (.base (.addImmediate r (-1))) s=
      some ⟨put s.core r (s.core.regs r-1),none,s.pc⟩ := by
  simp [X86ByteRoutine.execute,X86Routine.execute,BitVec.sub_eq_add_neg]
end Doom.Verification.X86ComparatorRoutine
