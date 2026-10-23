import Doom.Proofs.OriginalPspriteLoop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace Doom.Proofs.E1M1PspriteLoop
open Verification X86 X86Memory X86Control BlockSummary

def program (pc : Nat) : Option (X86Routine.Op × Nat) :=
  match PspriteLoop.program pc with
  | some op => some op
  | none => E1M1PspriteStep.program pc

theorem contains_tail (pc : Nat) (h : PspriteLoop.program pc≠none) :
    program pc=PspriteLoop.program pc := by
  unfold program
  cases e : PspriteLoop.program pc with
  | none => exact False.elim (h e)
  | some op => rfl

theorem contains_prior (pc : Nat) (h : E1M1PspriteStep.program pc≠none) :
    program pc=E1M1PspriteStep.program pc := by
  by_cases inside : 0x2dc95 ≤ pc ∧ pc < 0x2dcbc
  · have checked : ∀ i : Fin 39, E1M1PspriteStep.program (0x2dc95+i.val)=none := by decide
    have e : 0x2dc95+(pc-0x2dc95)=pc := by omega
    exact False.elim (h (by simpa only [e] using checked ⟨pc-0x2dc95,by omega⟩))
  · simp [program,PspriteLoop.program,PspriteLoop.bytesProgram,inside]

theorem contains_slot (pc : Nat) (h : PspriteStep.program pc≠none) :
    program pc=PspriteStep.program pc := by
  have old := E1M1PspriteStep.contains_step pc h
  have valid : E1M1PspriteStep.program pc≠none := by rw [old]; exact h
  rw [contains_prior pc valid,old]

private theorem tail_path {stops n s t}
    (run : X86Routine.run PspriteLoop.program stops n s=some t) :
    ∃ k, k ≤ n ∧ X86CodeMemory.Prefix FloorCaller.cm program [] k s t := by
  obtain ⟨k,hk,path,_⟩ := X86Routine.run_path run
  exact ⟨k,hk,(X86CodeMemory.lift_success path FloorCaller.cm).transfer program [] contains_tail (by simp)⟩

private theorem slot_path {stops n s t}
    (run : X86Routine.run PspriteStep.program stops n s=some t) :
    ∃ k, k ≤ n ∧ X86CodeMemory.Prefix FloorCaller.cm program [] k s t := by
  obtain ⟨k,hk,path,_⟩ := X86Routine.run_path run
  exact ⟨k,hk,(X86CodeMemory.lift_success path FloorCaller.cm).transfer program [] contains_slot (by simp)⟩

/-- Slot countdown and setter dispatch preserve ESI. This does not assert
anything about the subsequent setter's own execution. -/
theorem slot_index (s : X86Memory.State) : (PspriteStep.result s).core.regs 6=s.regs 6 := by
  unfold PspriteStep.result
  split <;> (try split) <;> (try split) <;>
    simp [PspriteStep.counting,PspriteStep.decremented,PspriteStep.dispatch,X86Routine.pushWord,put,write]

def flash (s : X86Control.State) := PspriteStep.result (PspriteLoop.advanced s.core).core
def finished (s : X86Control.State) :=
  let final := PspriteLoop.advanced (flash s).core
  PspriteLoop.returned (PspriteLoop.copied final.core) final.flags

/-- Continue after the weapon slot. This includes the flash countdown, position
copy, all five POPs, and actual RET. Flash expiration is an explicit boundary;
its setter must be proved before this path can cover it. -/
theorem suffix_execution (s : X86Control.State) (pc : s.pc=0x2dc95)
    (weapon : s.core.regs 6=0) (flashDone : (flash s).pc=0x2dc95) :
    ∃ n, n ≤ 33 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n s (finished s) := by
  have start : s=⟨s.core,s.flags,0x2dc95⟩ := by rw [←pc]
  have a := PspriteLoop.advance_execution s.core s.flags
  rw [←start] at a
  obtain ⟨na,ha,pa⟩ := tail_path a
  have onePC : (PspriteLoop.advanced s.core).pc=0x2dc6f := by simp [PspriteLoop.advanced,weapon]
  have one : PspriteLoop.advanced s.core=
      ⟨(PspriteLoop.advanced s.core).core,(PspriteLoop.advanced s.core).flags,0x2dc6f⟩ := by rw [←onePC]
  have b := PspriteStep.slot_execution (PspriteLoop.advanced s.core).core (PspriteLoop.advanced s.core).flags
  rw [←one] at b
  obtain ⟨nb,hb,pb⟩ := slot_path b
  have second : flash s=⟨(flash s).core,(flash s).flags,0x2dc95⟩ := by rw [←flashDone]
  have c := PspriteLoop.advance_execution (flash s).core (flash s).flags
  rw [←second] at c
  obtain ⟨nc,hc,pc'⟩ := tail_path c
  have index : (flash s).core.regs 6=(1#32) := by
    rw [flash,slot_index]; simp [PspriteLoop.advanced,weapon,put,write]
  have twoPC : (PspriteLoop.advanced (flash s).core).pc=0x2dc9e := by simp [PspriteLoop.advanced,index]
  have two : PspriteLoop.advanced (flash s).core=
      ⟨(PspriteLoop.advanced (flash s).core).core,(PspriteLoop.advanced (flash s).core).flags,0x2dc9e⟩ := by rw [←twoPC]
  have d := PspriteLoop.copy_execution (PspriteLoop.advanced (flash s).core).core (PspriteLoop.advanced (flash s).core).flags
  rw [←two] at d
  obtain ⟨nd,hd,pd⟩ := tail_path d
  have pe := (X86CodeMemory.lift_success
    (PspriteLoop.return_execution (PspriteLoop.copied (PspriteLoop.advanced (flash s).core).core)
      (PspriteLoop.advanced (flash s).core).flags) FloorCaller.cm).transfer program [] contains_tail (by simp)
  exact ⟨na+nb+nc+nd+6,by omega,
    E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans
      (E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans pa pb) pc') pd) pe⟩

/-- Attach the completed no-flash-transition continuation to an existing
620-instruction prefix. These boundary conditions remain explicit obligations. -/
theorem append_loop (s t : X86Control.State)
    (earlier : ∃ n, n ≤ 620 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteStep.program [] n s t)
    (pc : t.pc=0x2dc95) (weapon : t.core.regs 6=0) (flashDone : (flash t).pc=0x2dc95) :
    ∃ n, n ≤ 653 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n s (finished t) := by
  obtain ⟨n,hn,path⟩ := earlier
  have path := path.transfer program [] contains_prior (by simp)
  obtain ⟨m,hm,tail⟩ := suffix_execution t pc weapon flashDone
  exact ⟨n+m,by omega,E1M1PspriteStep.prefix_trans path tail⟩

end Doom.Proofs.E1M1PspriteLoop
