import Doom.Proofs.E1M1AimActorSelectEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimActorReturn
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1AimActorSelect (program)
open E1M1AimIteration
attribute [local irreducible] load32 store32 SolidThing.shootHeight

def selected := E1M1AimActorSelectEntry.result
def returned (s : X86Memory.State) := OriginalAimGuard.stopped (selected s).core
def result (s : X86Memory.State) := OriginalInterceptGate.resumed (returned s).core

/-- The two selection stores must not overwrite a saved register or return word. -/
def Safe (s : X86Memory.State) : Prop :=
  ∀ off∈E1M1AimReturnFrame.slots,
    Apart (s.regs 4-off) 0x2b9f8 ∧ Apart (s.regs 4-off) 0x2b9b4

theorem contains_repeat (pc : Nat) (h : E1M1AimRepeatProgram.program pc≠none) :
    program pc=E1M1AimRepeatProgram.program pc := by
  have old := E1M1AimActorBottomReject.contains_repeat pc h
  exact (E1M1AimActorSelect.contains_prior pc (by rw [old]; exact h)).trans old

theorem contains_guard (pc : Nat) (h : OriginalAimGuard.program pc≠none) :
    program pc=OriginalAimGuard.program pc := by
  have old := E1M1AimClosedReturn.contains_guard pc h
  exact (contains_repeat pc (by rw [old]; exact h)).trans old

theorem clipped_frame (s : X86Memory.State) :
    (OriginalAimActorSelect.clipped s).regs 4=s.regs 4 ∧
    (OriginalAimActorSelect.clipped s).memory=s.memory := by
  have top : (OriginalAimActorSelect.topClip s).regs 4=s.regs 4 ∧
      (OriginalAimActorSelect.topClip s).memory=s.memory := by
    unfold OriginalAimActorSelect.topClip
    split <;> simp [put,write]
  unfold OriginalAimActorSelect.clipped OriginalAimActorSelect.bottomClip
  split <;> simp [OriginalAimActorSelect.loaded,put,write,top.1,top.2]

/-- Clipping changes registers only; the following stores are the whole memory effect. -/
theorem selected_fields (s : X86Memory.State) :
    (selected s).core.regs 4=s.regs 4-24 ∧
    (selected s).core.memory=
      store32 (store32 (E1M1AimActorBottomEntry.result s).core.memory 0x2b9f8
        ((OriginalAimActorSelect.clipped (E1M1AimActorBottomEntry.result s).core).regs 1))
        0x2b9b4 (OriginalAimActorSelect.half (OriginalAimActorSelect.clipped (E1M1AimActorBottomEntry.result s).core)) := by
  have stack := E1M1AimActorBottomReject.stack s
  change (E1M1AimActorBottomEntry.result s).core.regs 4=s.regs 4-24 at stack
  have clip := clipped_frame (E1M1AimActorBottomEntry.result s).core
  simp only [selected,E1M1AimActorSelectEntry.result,E1M1AimActorSelectEntry.input,
    OriginalAimActorSelect.result,OriginalAimActorSelect.finish,OriginalAimActorSelect.c6,
    OriginalAimActorSelect.c5,OriginalAimActorSelect.c4,OriginalAimActorSelect.c3,
    OriginalAimActorSelect.c2,OriginalAimActorSelect.c1,put,write]
  simp [clip.1,clip.2,stack]

theorem selected_frame (s : X86Memory.State) (a : Word)
    (target : Apart a 0x2b9f8) (slope : Apart a 0x2b9b4) :
    load32 (selected s).core.memory a=load32 (E1M1AimActorBottomEntry.result s).core.memory a := by
  rw [(selected_fields s).2,load_store_apart _ _ _ _ slope,load_store_apart _ _ _ _ target]

theorem saved_slot (s : X86Memory.State) (safe : Safe s)
    (off : Word) (member : off∈E1M1AimReturnFrame.slots) :
    load32 (selected s).core.memory (s.regs 4-off)=load32 (OriginalAimGuard.saved s).memory (s.regs 4-off) := by
  exact (selected_frame s _ (safe off member).1 (safe off member).2).trans
    (E1M1AimActorBottomReject.saved_slot s off member)

theorem returned_fields (s : X86Memory.State) (safe : Safe s) :
    (returned s).core.regs 0=0 ∧ (returned s).core.regs 4=s.regs 4+4 ∧
    (returned s).core.memory=(selected s).core.memory ∧
    (returned s).pc=(load32 s.memory (s.regs 4)).toNat ∧
    (returned s).core.regs 5=s.regs 5 ∧ (returned s).core.regs 7=s.regs 7 ∧
    (returned s).core.regs 6=s.regs 6 ∧ (returned s).core.regs 2=s.regs 2 ∧
    (returned s).core.regs 1=s.regs 1 ∧ (returned s).core.regs 3=s.regs 3 := by
  have fields := OriginalAimWindow.returned_fields (selected s).core 0 (some (logical32 0))
  have keep (off : Word) (h : off∈E1M1AimReturnFrame.slots) := saved_slot s safe off h
  have values := E1M1AimReturnFrame.saved_values s
  have ret := E1M1AimWall.saved_frame s (s.regs 4) (E1M1AimWall.return_safe _)
  rw [(selected_fields s).1] at fields
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc] at fields
  have k0 := keep 0 (by simp [E1M1AimReturnFrame.slots])
  have k4 := keep 4 (by simp [E1M1AimReturnFrame.slots])
  have k8 := keep 8 (by simp [E1M1AimReturnFrame.slots])
  have k12 := keep 12 (by simp [E1M1AimReturnFrame.slots])
  have k16 := keep 16 (by simp [E1M1AimReturnFrame.slots])
  have k20 := keep 20 (by simp [E1M1AimReturnFrame.slots])
  have k24 := keep 24 (by simp [E1M1AimReturnFrame.slots])
  simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.neg_zero,BitVec.add_zero] at k0 k4 k8 k12 k16 k20 k24 values
  simp only [show -(0 : Word)=(0#32) from rfl,BitVec.add_zero] at k0
  obtain ⟨eax,sp,mem,pc,ebp,edi,esi,edx,ecx,ebx⟩ := fields
  obtain ⟨sv5,sv7,sv6,sv2,sv1,sv3⟩ := values
  exact ⟨eax,sp,mem,pc.trans (congrArg BitVec.toNat (k0.trans ret)),
    ebp.trans (k24.trans sv5),edi.trans (k20.trans sv7),esi.trans (k16.trans sv6),
    edx.trans (k12.trans sv2),ecx.trans (k8.trans sv1),ebx.trans (k4.trans sv3)⟩

/-- The false branch reloads the cursor but never sentinel-marks the chosen hit. -/
theorem registers (s : X86Memory.State) (safe : Safe s) :
    (result s).pc=0x2c88c ∧ (result s).core.regs 0=0 ∧
    (result s).core.regs 4=s.regs 4+4 ∧ (result s).core.memory=(selected s).core.memory ∧
    (result s).core.regs 3=s.regs 3 ∧ (result s).core.regs 6=s.regs 6 ∧
    (result s).core.regs 7=s.regs 7 ∧ (result s).core.regs 5=s.regs 5 ∧
    (result s).core.regs 2=s.regs 2 ∧
    (result s).core.regs 1=load32 (selected s).core.memory 0x2c028 := by
  obtain ⟨eax,sp,mem,pc,ebp,edi,esi,edx,ecx,ebx⟩ := returned_fields s safe
  simp [result,OriginalInterceptGate.resumed,OriginalInterceptGate.restored,
    eax,sp,mem,ebx,esi,edi,ebp,edx,put,write]

/-- The authenticated eight-instruction false return and four-instruction parent stop. -/
theorem continuation (s : X86Memory.State) (safe : Safe s)
    (returnWord : load32 s.memory (s.regs 4)=0x2c86d) :
    X86CodeMemory.Prefix FloorCaller.cm program [] 12 (selected s) (result s) := by
  have first := (X86CodeMemory.lift_success (OriginalAimGuard.stop_execution (selected s).core (selected s).flags)
    FloorCaller.cm).transfer program [] contains_guard (by simp)
  have atStop : (selected s).pc=0x2b8d2 := rfl
  rw [OriginalPathXStep.at_pc _ _ atStop] at first
  have fields := returned_fields s safe
  have pc : (returned s).pc=0x2c86d := by rw [fields.2.2.2.1,returnWord]; rfl
  have tail := (X86CodeMemory.lift_success (OriginalInterceptGate.resume_execution (returned s).core
    (returned s).flags) FloorCaller.cm).transfer program []
    (fun pc h => (contains_repeat pc (by rw [E1M1AimRepeatProgram.contains_call pc h]; exact h)).trans
      (E1M1AimRepeatProgram.contains_call pc h)) (by simp)
  rw [OriginalPathXStep.at_pc _ _ pc] at tail
  have count : OriginalInterceptGate.resumeSteps (returned s).core=4 := by
    simp [OriginalInterceptGate.resumeSteps,fields.1]
  rw [count] at tail
  exact E1M1PspriteStep.prefix_trans first tail

/-- Return and parent stop preserve the selected stores and all other memory. -/
theorem frame (s : X86Memory.State) (safe : Safe s) (a : Word)
    (reads : E1M1AimActorBottomReject.ReadSafe s a)
    (target : Apart a 0x2b9f8) (slope : Apart a 0x2b9b4) :
    load32 (result s).core.memory a=load32 s.memory a := by
  rw [(registers s safe).2.2.2.1,selected_frame s a target slope]
  exact E1M1AimActorBottomReject.read_frame s a reads

theorem execution (s : X86Memory.State) (f : Option Flags)
    (scene : Scene) (shooterId : Nat) (thing : SolidThing) (path : PathResult)
    (range lower upper topSlope bottomSlope : Fixed) (log : Array AutoAim.Portal) (i : Nat) (rest : List Nat)
    (hit : Intercept) (pointer who : Word)
    (record : OriginalLineFinish.RecordAt s.memory (s.regs 0) hit pointer)
    (selected : path.visited[i]! = hit) (isThing : hit.isLine=false)
    (tagSafe : E1M1AimWall.Safe (s.regs 4) (s.regs 0+4)) (pointerSafe : E1M1AimWall.Safe (s.regs 4) (s.regs 0+8))
    (shooterSafe : E1M1AimWall.Safe (s.regs 4) 0x2b9ac) (flagsSafe : E1M1AimWall.Safe (s.regs 4) (pointer+104))
    (shooter : load32 s.memory 0x2b9ac=who)
    (identity : pointer=who ↔ hit.id=shooterId)
    (flags : (s.memory (pointer+104) &&& (4#8) != 0)=scene.things[hit.id]!.shootable)
    (different : hit.id≠shooterId) (shootable : scene.things[hit.id]!.shootable=true)
    (topSafe : E1M1AimActorTopEntry.ReadSafe s pointer) (safe : E1M1AimActorBottomEntry.ReadSafe s pointer)
    (r : load32 s.memory (0x2b9b8#32)=range.raw.toBitVec)
    (z0 : load32 s.memory (pointer+20)=scene.things[hit.id]!.z.raw.toBitVec)
    (ht : load32 s.memory (pointer+68)=scene.things[hit.id]!.height.raw.toBitVec)
    (eye0 : load32 s.memory (0x2b9a8#32)=thing.shootHeight.raw.toBitVec)
    (bound : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec)
    (high : load32 s.memory (0x2c1e8#32)=upper.raw.toBitVec)
    (topOk : checkedPathDiv (scene.things[hit.id]!.z+scene.things[hit.id]!.height-thing.shootHeight)
      (range*hit.frac)=.ok topSlope) (admitted : ¬topSlope.raw<lower.raw)
    (bottomOk : checkedPathDiv (scene.things[hit.id]!.z-thing.shootHeight)
      (range*hit.frac)=.ok bottomSlope) (bottomAdmitted : ¬upper.raw<bottomSlope.raw)
    (saveSafe : Safe s) (returnWord : load32 s.memory (s.regs 4)=0x2c86d) :
    (∃ n≤115, X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ (result s)) ∧
    (result s).pc=0x2c88c ∧ (result s).core.regs 0=0 ∧
    (result s).core.regs 4=s.regs 4+4 ∧
    (result s).core.memory=(E1M1AimActorReturn.selected s).core.memory ∧
    load32 (result s).core.memory (0x2b9f8#32)=pointer ∧
    load32 (result s).core.memory (0x2b9b4#32)=
      (E1M1AimActorSelectEntry.answer scene thing path range lower upper topSlope bottomSlope log i hit).slope.raw.toBitVec ∧
    remaining scene shooterId thing path range (i::rest) lower upper log =
      .ok (E1M1AimActorSelectEntry.answer scene thing path range lower upper topSlope bottomSlope log i hit) := by
  obtain ⟨⟨n,hn,run⟩,_,target,slope,source⟩ := E1M1AimActorSelectEntry.selected
    s f scene shooterId thing path range lower upper topSlope bottomSlope log i rest hit pointer who record
    selected isThing tagSafe pointerSafe shooterSafe flagsSafe shooter identity flags different shootable
    topSafe safe r z0 ht eye0 bound high topOk admitted bottomOk bottomAdmitted
  have fields := registers s saveSafe
  refine ⟨⟨n+12,by omega,E1M1PspriteStep.prefix_trans run (continuation s saveSafe returnWord)⟩,
    fields.1,fields.2.1,fields.2.2.1,fields.2.2.2.1,?_,?_,source⟩
  · rw [fields.2.2.2.1]; exact target
  · rw [fields.2.2.2.1]; exact slope
end Doom.Proofs.E1M1AimActorReturn
