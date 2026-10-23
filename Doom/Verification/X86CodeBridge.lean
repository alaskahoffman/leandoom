import Doom.Verification.X86CodeMemory

namespace Doom.Verification.X86CodeMemory
open X86 X86Memory X86Control

def routineOnly : X86Routine.Op → Bool
  | .jumpCode _ => false
  | _ => true

theorem execute_routine (cm : Memory) (op : X86Routine.Op) (s : X86Control.State)
    (h : routineOnly op = true) : execute cm op s = X86Routine.execute op s := by
  cases op <;> first | rfl | simp [routineOnly] at h

/-- Identical semantics for an existing routine path; no PC or memory rebasing. -/
theorem lift_routine {p exits n s t} (path : X86Routine.Prefix p exits n s t)
    (cm : Memory) (ordinary : ∀ pc op len, p pc = some (op,len) → routineOnly op = true) :
    Prefix cm p exits n s t := by
  induction path with
  | nil => exact Prefix.nil _
  | @step n s middle last op len active decoded executed rest ih =>
    exact Prefix.step active decoded ((execute_routine cm op _ (ordinary _ _ _ decoded)).trans executed) ih

/-- A successful ordinary execution cannot have executed a CS-relative jump:
the ordinary interpreter rejects that instruction. Thus only the executed path,
not every decoded byte in the surrounding program, needs to be considered. -/
theorem execute_success (cm : Memory) (op : X86Routine.Op) (s t : X86Control.State)
    (h : X86Routine.execute op s = some t) : execute cm op s = some t := by
  cases op <;> first | exact h | simp [X86Routine.execute] at h

/-- Lift any successful routine prefix, retaining all PCs, flags, registers and
memory. Unexecuted CS-relative jumps elsewhere in the program are unrestricted. -/
theorem lift_success {p exits n s t} (path : X86Routine.Prefix p exits n s t)
    (cm : Memory) : Prefix cm p exits n s t := by
  induction path with
  | nil => exact Prefix.nil _
  | @step n s middle last op len active decoded executed rest ih =>
    exact Prefix.step active decoded (execute_success cm op _ _ executed) ih

theorem run_lift_success {p exits n s t}
    (h : X86Routine.run p exits n s = some t) (cm : Memory) :
    X86CodeMemory.run cm p exits n s = some t := by
  obtain ⟨k,hk,path,done⟩ := X86Routine.run_path h
  exact (lift_success path cm).finish (fuel := 0)
    (by simp [X86CodeMemory.run,done]) n (by omega)

/-- Check a finite byte slice, including every decoder-recognized entry offset. -/
theorem routine_decode (code : List UInt8)
    (checked : ∀ i : Fin code.length, ((X86Routine.decodeAt code i.val).map (fun p => routineOnly p.1)).getD true = true)
    (pc : Nat) : ((X86Routine.decodeAt code pc).map (fun p => routineOnly p.1)).getD true = true := by
  by_cases hp : pc < code.length
  · exact checked ⟨pc,hp⟩
  · simp only [X86Routine.decodeAt, List.drop_eq_nil_of_le (show code.length ≤ pc by omega)]
    rfl

end Doom.Verification.X86CodeMemory
