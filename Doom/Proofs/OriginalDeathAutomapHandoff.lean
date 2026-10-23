import Doom.Proofs.OriginalAutomapHandoff
import Doom.Proofs.OriginalDeathAutomap
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.DeathAutomapHandoff
open Verification X86 X86Memory X86Control BlockSummary

def bytesProgram (guard tag unload stop responder responderReturn : List UInt8) : X86Routine.Program := fun pc =>
  match DeathAutomap.bytesProgram guard pc with
  | some op => some op
  | none => AutomapStop.bytesProgram tag unload stop responder responderReturn pc
def program := bytesProgram DeathAutomap.code AutomapStop.tagCode AutomapStop.unloadCode
  AutomapStop.stopCode AutomapStop.responderCode AutomapStop.responderReturnCode

theorem contains_guard (pc : Nat) (h : DeathAutomap.program pc≠none) :
    program pc=DeathAutomap.program pc := by
  unfold program bytesProgram
  cases eq : DeathAutomap.program pc with
  | none => exact False.elim (h eq)
  | some op => simp [DeathAutomap.program] at eq; rw [eq]

theorem contains_stop (pc : Nat) (h : AutomapStop.program pc≠none) :
    program pc=AutomapStop.program pc := by
  have outside : ¬(0x2a38c ≤ pc ∧ pc < 0x2a3c8) := by
    intro bound
    have b1 : ¬(0x399b0 ≤ pc ∧ pc < 0x399ea) := by omega
    have b2 : ¬(0x24e30 ≤ pc ∧ pc < 0x24e7c) := by omega
    have b3 : ¬(0x24f90 ≤ pc ∧ pc < 0x24fb7) := by omega
    have b4 : ¬(0x39aa0 ≤ pc ∧ pc < 0x39af8) := by omega
    have b5 : ¬(0x39f1c ≤ pc ∧ pc < 0x39f27) := by omega
    simp [AutomapStop.program,AutomapStop.bytesProgram,b1,b2,b3,b4,b5] at h
  simp [program,bytesProgram,DeathAutomap.bytesProgram,outside,AutomapStop.program]

/-- The actual stored DOS event, following the original death guard and CALL. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (v c : Fin 4)
    (console : load32 s.memory (0x2b3dc#32)=BitVec.ofNat 32 c.val)
    (victim : load32 s.memory (s.regs 3+(132#32))=DeathAutomap.player v)
    (active : DeathAutomap.stops s v c)
    (cache : AutomapStop.UnloadInputs (AutomapStop.stopUnload (DeathAutomap.result s v c).core))
    (kind : load32 s.memory (0x12c98#32)=0)
    (guardSafe : ∀ b, b ∈ DeathAutomap.writes s v c → Apart (0x12c98#32) b)
    (cacheSafe : ∀ b, b ∈ AutomapStop.dosWrites (DeathAutomap.result s v c).core → Apart (0x12c98#32) b) :
    X86Routine.run program [0x39af8] 239 ⟨s,f,0x2a38c⟩=
      some (AutomapStop.dosResponderResult (AutomapStop.stopResponder (DeathAutomap.result s v c).core)) := by
  let g := DeathAutomap.result s v c
  have pc : g.pc=0x24f90 := by simp [g,DeathAutomap.result,active]
  have kept := (DeathAutomap.frame s v c (0x12c98#32) guardSafe).trans kind
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path (DeathAutomap.execution s f v c console victim)
  have path := path.transfer program [0x39af8] contains_guard (by
    intro pc hp; simp only [List.mem_singleton]; intro eq; subst pc; exact hp (by decide))
  have run := AutomapStop.dos_execution g.core g.flags cache kept cacheSafe
  obtain ⟨k,hk,tail,done⟩ := X86Routine.run_path run
  have tail := tail.transfer program [0x39af8] contains_stop (by
    intro pc hp; simp only [List.mem_singleton]; intro eq; subst pc; exact hp (by decide))
  have tailRun : X86Routine.run program [0x39af8] 226 ⟨g.core,g.flags,0x24f90⟩=
      some (AutomapStop.dosResponderResult (AutomapStop.stopResponder g.core)) :=
    tail.finish (fuel := 0) (by simp [X86Routine.run,AutomapStop.dosResponderResult]) 226 (by omega)
  have start : (⟨g.core,g.flags,0x24f90⟩ : X86Control.State)=g := by rw [← pc]
  rw [start] at tailRun
  exact path.finish tailRun 239 (by omega)

end Doom.Proofs.DeathAutomapHandoff
