import Doom.Proofs.OriginalAimActorGuard
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimActorSkip
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1AimWall (Safe)
attribute [local irreducible] load32 store32

def program : X86Routine.Program := fun pc =>
  match E1M1AimRepeatProgram.program pc with
  | some op => some op
  | none => OriginalAimActorGuard.program pc

theorem contains_repeat (pc : Nat) (h : E1M1AimRepeatProgram.program pc≠none) :
    program pc=E1M1AimRepeatProgram.program pc := by
  unfold program; cases eq : E1M1AimRepeatProgram.program pc <;> simp_all

theorem contains_actor (pc : Nat) (h : OriginalAimActorGuard.program pc≠none) :
    program pc=OriginalAimActorGuard.program pc := by
  by_cases inside : 0x2b81a≤pc ∧ pc<0x2b843
  · have all : ∀ i : Fin 41, program (0x2b81a+i.val)=OriginalAimActorGuard.program (0x2b81a+i.val) := by decide
    have eq : 0x2b81a+(pc-0x2b81a)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2b81a,by omega⟩
  · have guard : OriginalAimActorGuard.program pc=OriginalAimGuard.program pc := by
      simp only [OriginalAimActorGuard.program,OriginalAimActorGuard.bytesProgram,if_neg inside]
    have old := E1M1AimClosedReturn.contains_guard pc (by rw [← guard]; exact h)
    exact (contains_repeat pc (by rw [old,← guard]; exact h)).trans (old.trans guard.symm)

theorem contains_guard (pc : Nat) (h : OriginalAimGuard.program pc≠none) :
    program pc=OriginalAimGuard.program pc := by
  have eq := OriginalAimActorGuard.contains_guard pc h
  exact (contains_actor pc (by rw [eq]; exact h)).trans eq

def input (s : X86Memory.State) := OriginalAimGuard.prepared s
def reached (s : X86Memory.State) := OriginalAimActorGuard.loaded (input s)
def returnFlags (s : X86Memory.State) :=
  if OriginalAimActorGuard.actor (input s)=OriginalAimActorGuard.shooter (input s) then
    (OriginalAimActorGuard.gate (input s)).flags else (OriginalAimActorGuard.flagGate (reached s)).flags
def returned (s : X86Memory.State) := OriginalAimWindow.returned (reached s) 1 (returnFlags s)
def result (s : X86Memory.State) := OriginalInterceptGate.resumed (returned s).core

theorem returned_fields (s : X86Memory.State) :
    (returned s).core.regs 0=1 ∧ (returned s).core.regs 4=s.regs 4+4 ∧
    (returned s).core.memory=(OriginalAimGuard.saved s).memory ∧
    (returned s).pc=(load32 s.memory (s.regs 4)).toNat ∧
    (returned s).core.regs 3=s.regs 3 ∧ (returned s).core.regs 6=s.regs 6 ∧
    (returned s).core.regs 7=s.regs 7 := by
  have stack : (reached s).regs 4=s.regs 4-24 := by
    simp [reached,input,OriginalAimActorGuard.loaded,OriginalAimActorGuard.first,
      OriginalAimGuard.prepared,OriginalAimGuard.saved,OriginalAimGuard.save6,OriginalAimGuard.save5,
      OriginalAimGuard.save4,OriginalAimGuard.save3,OriginalAimGuard.save2,OriginalAimGuard.save1,
      X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have memory : (reached s).memory=(OriginalAimGuard.saved s).memory := rfl
  have fields := OriginalAimWindow.returned_fields (reached s) 1 (returnFlags s)
  have saved := E1M1AimReturnFrame.saved_values s
  have keep := E1M1AimWall.saved_frame s (s.regs 4) (E1M1AimWall.return_safe _)
  simp [stack,memory,BitVec.sub_eq_add_neg,BitVec.add_assoc] at fields
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc] at saved
  obtain ⟨eax,sp,mem,pc,ebp,edi,esi,edx,ecx,ebx⟩ := fields
  obtain ⟨sv5,sv7,sv6,sv2,sv1,sv3⟩ := saved
  exact ⟨eax,sp,mem,pc.trans (congrArg BitVec.toNat keep),ebx.trans sv3,esi.trans sv6,edi.trans sv7⟩

/-- Real callback execution for self/nonshootable rejection. All reads are
transported from callback entry across its six-push prologue. -/
theorem callback (s : X86Memory.State) (f : Option Flags) (hit : Intercept) (pointer who : Word)
    (record : OriginalLineFinish.RecordAt s.memory (s.regs 0) hit pointer) (isThing : hit.isLine=false)
    (tagSafe : Safe (s.regs 4) (s.regs 0+4)) (pointerSafe : Safe (s.regs 4) (s.regs 0+8))
    (shooterSafe : Safe (s.regs 4) 0x2b9ac) (flagsSafe : Safe (s.regs 4) (pointer+104))
    (shooter : load32 s.memory 0x2b9ac=who)
    (reject : pointer=who ∨ s.memory (pointer+104) &&& (4#8)=0) :
    ∃ n≤23, X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ (returned s) := by
  have entryPc : (OriginalAimGuard.entry s).pc=0x2b81a := by
    rw [E1M1AimWall.entry_record s hit pointer record tagSafe,isThing]; rfl
  have ptr : OriginalAimActorGuard.actor (input s)=pointer := by
    change load32 (OriginalAimGuard.saved s).memory (s.regs 0+8)=pointer
    rw [E1M1AimWall.saved_frame s _ pointerSafe]; exact record.2.2
  have whoWord : OriginalAimActorGuard.shooter (input s)=who := by
    change load32 (OriginalAimGuard.saved s).memory 0x2b9ac=who
    rw [E1M1AimWall.saved_frame s _ shooterSafe]; exact shooter
  have flagWord : OriginalAimActorGuard.bits (reached s)=s.memory (pointer+104) &&& (4#8) := by
    change (OriginalAimGuard.saved s).memory (OriginalAimActorGuard.actor (input s)+104) &&& (4#8)=_
    rw [ptr,E1M1AimWall.saved_byte s _ flagsSafe]
  have entry := (X86CodeMemory.lift_success (OriginalAimGuard.entry_execution s f) FloorCaller.cm).transfer
    program [] contains_guard (by simp)
  have head := (X86CodeMemory.lift_success (OriginalAimActorGuard.head_execution (input s)
    (OriginalAimGuard.entry s).flags) FloorCaller.cm).transfer program [] contains_actor (by simp)
  change X86CodeMemory.Prefix FloorCaller.cm program [] 4
    ⟨(OriginalAimGuard.entry s).core,(OriginalAimGuard.entry s).flags,0x2b81a⟩ _ at head
  rw [OriginalPathXStep.at_pc _ _ entryPc] at head
  by_cases same : pointer=who
  · have gatePc : (OriginalAimActorGuard.gate (input s)).pc=0x2b827 := by
      simp only [OriginalAimActorGuard.gate,ptr,whoWord,if_pos same]
    have tail := (X86CodeMemory.lift_success (OriginalAimActorGuard.self_return_execution (reached s)
      (OriginalAimActorGuard.gate (input s)).flags) FloorCaller.cm).transfer program [] contains_actor (by simp)
    change X86CodeMemory.Prefix FloorCaller.cm program [] 9
      ⟨(OriginalAimActorGuard.gate (input s)).core,(OriginalAimActorGuard.gate (input s)).flags,0x2b827⟩ _ at tail
    rw [OriginalPathXStep.at_pc _ _ gatePc] at tail
    have eq : returned s=OriginalAimWindow.returned (reached s) 1 (OriginalAimActorGuard.gate (input s)).flags := by
      simp only [returned,returnFlags,ptr,whoWord,if_pos same]
    rw [← eq] at tail
    exact ⟨22,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans entry head) tail⟩
  · have zero := reject.resolve_left same
    have gatePc : (OriginalAimActorGuard.gate (input s)).pc=0x2b831 := by
      simp only [OriginalAimActorGuard.gate,ptr,whoWord,if_neg same]
    have check := (X86CodeMemory.lift_success (OriginalAimActorGuard.flags_execution (reached s)
      (OriginalAimActorGuard.gate (input s)).flags) FloorCaller.cm).transfer program [] contains_actor (by simp)
    change X86CodeMemory.Prefix FloorCaller.cm program [] 2
      ⟨(OriginalAimActorGuard.gate (input s)).core,(OriginalAimActorGuard.gate (input s)).flags,0x2b831⟩ _ at check
    rw [OriginalPathXStep.at_pc _ _ gatePc] at check
    have flagPc : (OriginalAimActorGuard.flagGate (reached s)).pc=0x2b837 := by
      simp only [OriginalAimActorGuard.flagGate,flagWord,zero,ite_true]
    have tail := (X86CodeMemory.lift_success (OriginalAimActorGuard.skip_return_execution (reached s)
      (OriginalAimActorGuard.flagGate (reached s)).flags) FloorCaller.cm).transfer program [] contains_actor (by simp)
    change X86CodeMemory.Prefix FloorCaller.cm program [] 8
      ⟨(OriginalAimActorGuard.flagGate (reached s)).core,(OriginalAimActorGuard.flagGate (reached s)).flags,0x2b837⟩ _ at tail
    rw [OriginalPathXStep.at_pc _ _ flagPc] at tail
    have eq : returned s=OriginalAimWindow.returned (reached s) 1 (OriginalAimActorGuard.flagGate (reached s)).flags := by
      simp only [returned,returnFlags,ptr,whoWord,if_neg same]
    rw [← eq] at tail
    exact ⟨23,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans entry head) check) tail⟩

/-- The successful skip returns to the actual parent and marks the selected
fraction before reaching the next-scan head. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (hit : Intercept) (pointer who : Word)
    (record : OriginalLineFinish.RecordAt s.memory (s.regs 0) hit pointer) (isThing : hit.isLine=false)
    (tagSafe : Safe (s.regs 4) (s.regs 0+4)) (pointerSafe : Safe (s.regs 4) (s.regs 0+8))
    (shooterSafe : Safe (s.regs 4) 0x2b9ac) (flagsSafe : Safe (s.regs 4) (pointer+104))
    (shooter : load32 s.memory 0x2b9ac=who)
    (reject : pointer=who ∨ s.memory (pointer+104) &&& (4#8)=0)
    (returnWord : load32 s.memory (s.regs 4)=0x2c86d) :
    (∃ n≤28, X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ (result s)) ∧
    (result s).pc=0x2c83a ∧ (result s).core.regs 4=s.regs 4+4 ∧
    (result s).core.regs 3=s.regs 3 ∧ (result s).core.regs 6=s.regs 6 ∧
    (result s).core.regs 7=s.regs 7 ∧
    (result s).core.memory=store32 (OriginalAimGuard.saved s).memory (s.regs 3) 0x7fffffff := by
  obtain ⟨n,hn,run⟩ := callback s f hit pointer who record isThing tagSafe pointerSafe shooterSafe flagsSafe shooter reject
  have fields := returned_fields s
  have pc : (returned s).pc=0x2c86d := by rw [fields.2.2.2.1,returnWord]; rfl
  have tail := (X86CodeMemory.lift_success (OriginalInterceptGate.resume_execution (returned s).core
    (returned s).flags) FloorCaller.cm).transfer program []
    (fun pc h => (contains_repeat pc (by rw [E1M1AimRepeatProgram.contains_call pc h]; exact h)).trans
      (E1M1AimRepeatProgram.contains_call pc h)) (by simp)
  rw [OriginalPathXStep.at_pc _ _ pc] at tail
  have count : OriginalInterceptGate.resumeSteps (returned s).core=5 := by simp [OriginalInterceptGate.resumeSteps,fields.1]
  rw [count] at tail
  refine ⟨⟨n+5,by omega,E1M1PspriteStep.prefix_trans run tail⟩,?_⟩
  simp [result,OriginalInterceptGate.resumed,OriginalInterceptGate.marked,OriginalInterceptGate.restored,
    fields.1,fields.2.1,fields.2.2.1,fields.2.2.2.2.1,fields.2.2.2.2.2.1,fields.2.2.2.2.2.2,put,write]

end Doom.Proofs.E1M1AimActorSkip
