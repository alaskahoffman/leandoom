import Doom.Proofs.OriginalAutomapFrame
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1200000
namespace Doom.Proofs.AutomapDeathChoice
open Verification X86 X86Memory X86Control BlockSummary

def bytesProgram (tag unload stop responder responderReturn choice : List UInt8) : X86Routine.Program := fun pc =>
  match AutomapStop.bytesProgram tag unload stop responder responderReturn pc with
  | some op => some op
  | none => DeathChoice.bytesProgram choice pc
def program := bytesProgram AutomapStop.tagCode AutomapStop.unloadCode AutomapStop.stopCode
  AutomapStop.responderCode AutomapStop.responderReturnCode DeathChoice.code

theorem contains_stop (pc : Nat) (h : AutomapStop.program pc≠none) : program pc=AutomapStop.program pc := by
  unfold program bytesProgram
  cases eq : AutomapStop.program pc with
  | none => exact False.elim (h eq)
  | some op => simp [AutomapStop.program] at eq; rw [eq]

theorem contains_choice (pc : Nat) (h : DeathChoice.program pc≠none) : program pc=DeathChoice.program pc := by
  have bound : 0x2a3c8 ≤ pc ∧ pc < 0x2a3f1 := by
    by_cases yes : 0x2a3c8 ≤ pc ∧ pc < 0x2a3f1
    · exact yes
    · simp [DeathChoice.program,DeathChoice.bytesProgram,yes] at h
  have b1 : ¬(0x399b0 ≤ pc ∧ pc < 0x399ea) := by omega
  have b2 : ¬(0x24e30 ≤ pc ∧ pc < 0x24e7c) := by omega
  have b3 : ¬(0x24f90 ≤ pc ∧ pc < 0x24fb7) := by omega
  have b4 : ¬(0x39aa0 ≤ pc ∧ pc < 0x39af8) := by omega
  have b5 : ¬(0x39f1c ≤ pc ∧ pc < 0x39f27) := by omega
  simp [program,bytesProgram,AutomapStop.bytesProgram,b1,b2,b3,b4,b5,DeathChoice.program]

def reads (s : X86Memory.State) := [s.regs 3+92,s.regs 3+108,
  DeathChoice.infoPointer s+8,DeathChoice.infoPointer s+48,DeathChoice.infoPointer s+52]

theorem execution (s : X86Memory.State) (f : Option Flags) (hp : Int32) (info : Death.Info)
    (stop : AutomapStop.StopInputs s) (choice : DeathChoice.Inputs s hp info)
    (safe : ∀ a, a ∈ reads s → ∀ b, b ∈ AutomapStop.stopWrites s → Apart a b) :
    ∃ t, X86Routine.run program [0x30ea0] 263 ⟨s,f,0x24f90⟩=some t ∧
      t.pc=0x30ea0 ∧ t.core.regs 0=s.regs 3 ∧ t.core.regs 2=BitVec.ofNat 32 (Death.deathState hp info) ∧
      t.core.regs 3=s.regs 3 ∧ t.core.regs 4=s.regs 4 ∧ load32 t.core.memory (s.regs 4)=0x2a3f1 ∧
      PlayerHeight.Frame s.memory t.core.memory (AutomapStop.stopWrites s ++ [s.regs 4]) := by
  let g := AutomapStop.stopResult s
  have gb : g.core.regs 3=s.regs 3 := (AutomapStop.stop_registers s).1
  have gs : g.core.regs 4=s.regs 4+4 := (AutomapStop.stop_registers s).2
  have keep (a : Word) (ha : a ∈ reads s) : load32 g.core.memory a=load32 s.memory a :=
    AutomapStop.stop_frame s a (safe a ha)
  have ptr : DeathChoice.infoPointer g.core=DeathChoice.infoPointer s := by
    unfold DeathChoice.infoPointer; rw [gb,keep _ (by simp [reads])]
  have ins : DeathChoice.Inputs g.core hp info := by
    refine ⟨?_,?_,?_,?_,choice.extremeBound⟩
    · unfold DeathChoice.health; rw [gb,keep _ (by simp [reads])]; exact choice.health
    · unfold DeathChoice.spawn; rw [ptr,keep _ (by simp [reads])]; exact choice.spawn
    · unfold DeathChoice.normal; rw [ptr,keep _ (by simp [reads])]; exact choice.normal
    · unfold DeathChoice.extreme; rw [ptr,keep _ (by simp [reads])]; exact choice.extreme
  obtain ⟨t,trun,tpc,ta,td,tb,ts,tr,tf⟩ := DeathChoice.live_correspondence g.core g.flags hp info ins
  obtain ⟨n,hn,path,_⟩ := X86Routine.run_path (AutomapStop.stop_execution s f stop)
  have path := path.transfer program [0x30ea0] contains_stop (by
    intro pc hp; simp only [List.mem_singleton]; intro eq; subst pc; exact hp (by decide))
  obtain ⟨k,hk,tail,_⟩ := X86Routine.run_path trun
  have tail := tail.transfer program [0x30ea0] contains_choice (by
    intro pc hp; simp only [List.mem_singleton]; intro eq; subst pc; exact hp (by decide))
  have tailRun : X86Routine.run program [0x30ea0] 13 g=some t := by
    exact tail.finish (fuel := 0) (by simp [X86Routine.run,tpc]) 13 (by omega)
  have slot : g.core.regs 4-(4#32)=s.regs 4 := by rw [gs]; simp [BitVec.add_sub_cancel]
  refine ⟨t,path.finish tailRun 263 (by omega),tpc,ta.trans gb,td,tb.trans gb,ts.trans slot,?_,?_⟩
  · simpa [slot] using tr
  · exact AutomapStop.frame_append (AutomapStop.stop_frame s) (by simpa [slot] using tf)

end Doom.Proofs.AutomapDeathChoice
