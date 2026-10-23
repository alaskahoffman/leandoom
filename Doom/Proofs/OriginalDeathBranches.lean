import Doom.Proofs.OriginalDeathAutomap
import Doom.Proofs.OriginalDeathChoice
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.DeathBranches
open Verification X86 X86Memory X86Control BlockSummary

def bytesProgram (guard choice : List UInt8) : X86Routine.Program := fun pc =>
  match DeathAutomap.bytesProgram guard pc with
  | some op => some op
  | none => DeathChoice.bytesProgram choice pc
def program := bytesProgram DeathAutomap.code DeathChoice.code

theorem contains_guard (pc : Nat) (h : DeathAutomap.program pc≠none) :
    program pc=DeathAutomap.program pc := by
  unfold program bytesProgram
  cases eq : DeathAutomap.program pc with
  | none => exact False.elim (h eq)
  | some op => exact congrArg (fun x => match x with | some op => some op | none => DeathChoice.program pc) eq

theorem contains_choice (pc : Nat) (h : DeathChoice.program pc≠none) :
    program pc=DeathChoice.program pc := by
  have bound : 0x2a3c8 ≤ pc ∧ pc < 0x2a3f1 := by
    by_cases yes : 0x2a3c8 ≤ pc ∧ pc < 0x2a3f1
    · exact yes
    · simp [DeathChoice.program,DeathChoice.bytesProgram,yes] at h
  have outside : ¬(0x2a38c ≤ pc ∧ pc < 0x2a3c8) := by omega
  simp [program,bytesProgram,DeathAutomap.bytesProgram,outside,DeathChoice.program]

theorem guard_active (pc : Nat) (h : DeathAutomap.program pc≠none) : pc ∉ [0x24f90,0x30ea0] := by
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]; intro eq
  rcases eq with rfl|rfl <;> exact h (by decide)
theorem choice_active (pc : Nat) (h : DeathChoice.program pc≠none) : pc ∉ [0x24f90,0x30ea0] := by
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]; intro eq
  rcases eq with rfl|rfl <;> exact h (by decide)

/-- Both original branches are followed to actual call entries. AM_Stop and
P_SetMobjState are boundaries, not assumed summaries of those callees. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (v : Fin 4) (world : Death.World)
    (hp : Int32) (info : Death.Info)
    (console : load32 s.memory (0x2b3dc#32)=BitVec.ofNat 32 world.console.val)
    (victim : load32 s.memory (s.regs 3+(132#32))=DeathAutomap.player v)
    (auto : (DeathAutomap.active s≠0) ↔ world.automap=true)
    (ins : DeathChoice.Inputs s hp info) :
    ∃ t, X86Routine.run program [0x24f90,0x30ea0] 26 ⟨s,f,0x2a38c⟩=some t ∧
      t.pc=(if Death.shouldStopAutomap v world then 0x24f90 else 0x30ea0) ∧
      (Death.shouldStopAutomap v world=false → t.core.regs 0=s.regs 3 ∧
        t.core.regs 2=BitVec.ofNat 32 (Death.deathState hp info)) ∧
      t.core.regs 3=s.regs 3 ∧ t.core.regs 4=s.regs 4-4 ∧
      load32 t.core.memory (s.regs 4-4)=(if Death.shouldStopAutomap v world then 0x2a3c8 else 0x2a3f1) ∧
      PlayerHeight.Frame s.memory t.core.memory [s.regs 4-4] := by
  let g := DeathAutomap.result s v world.console
  have grun := DeathAutomap.execution s f v world.console console victim
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path grun
  have path := path.transfer program [0x24f90,0x30ea0] contains_guard guard_active
  by_cases stop : DeathAutomap.stops s v world.console
  · have live := (DeathAutomap.live_guard s v world auto).mp stop
    refine ⟨g,path.finish (fuel := 0) ?_ 26 (by omega),?_,?_,?_,?_,?_,?_⟩
    · simp [X86Routine.run,g,DeathAutomap.result,stop]
    · simp [g,DeathAutomap.result,stop,live]
    · simp [live]
    · simp [g,DeathAutomap.result,stop,X86Routine.pushWord,DeathAutomap.middle,write]
    · simp [g,DeathAutomap.result,stop,X86Routine.pushWord,DeathAutomap.middle,write]
    · simp [g,DeathAutomap.result,stop,X86Routine.pushWord,DeathAutomap.middle,write,load_store,live]
    · simpa [g,DeathAutomap.writes,stop] using DeathAutomap.frame s v world.console
  · have live : Death.shouldStopAutomap v world=false := by
      cases eq : Death.shouldStopAutomap v world <;> simp_all [DeathAutomap.live_guard s v world auto]
    have gm : g.core.memory=s.memory := by simp [g,DeathAutomap.result,stop,DeathAutomap.middle]
    have gb : g.core.regs 3=s.regs 3 := by simp [g,DeathAutomap.result,stop,DeathAutomap.middle,write]
    have gs : g.core.regs 4=s.regs 4 := by simp [g,DeathAutomap.result,stop,DeathAutomap.middle,write]
    have gp : g.pc=0x2a3c8 := by simp [g,DeathAutomap.result,stop]
    have hi : DeathChoice.Inputs g.core hp info := by
      rcases ins with ⟨hh,hs,hn,he,hb⟩
      constructor <;> simp_all [DeathChoice.health,DeathChoice.spawn,DeathChoice.normal,DeathChoice.extreme,DeathChoice.infoPointer]
    obtain ⟨t,trun,tp,ta,td,tb,ts,tret,tf⟩ := DeathChoice.live_correspondence g.core g.flags hp info hi
    obtain ⟨k,hk,tail,_⟩ := X86Routine.run_path trun
    have tail := tail.transfer program [0x24f90,0x30ea0] contains_choice choice_active
    have tailRun : X86Routine.run program [0x24f90,0x30ea0] 13 g=some t := by
      have geq : g=⟨g.core,g.flags,0x2a3c8⟩ := by rw [← gp]
      rw [geq]
      exact tail.finish (fuel := 0) (by simp [X86Routine.run,tp]) 13 (by omega)
    refine ⟨t,path.finish tailRun 26 (by omega),?_,?_,tb.trans gb,?_,?_,?_⟩
    · simp [live,tp]
    · intro _; exact ⟨ta.trans gb,td⟩
    · simpa [gs] using ts
    · simpa [gs,live] using tret
    · simpa [gm,gs] using tf
end Doom.Proofs.DeathBranches
