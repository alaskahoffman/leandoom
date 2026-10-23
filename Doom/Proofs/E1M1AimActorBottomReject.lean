import Doom.Proofs.E1M1AimActorBottomEntry
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimActorBottomReject
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1AimWall (Safe)
open E1M1AimActorBottom (program)
open E1M1AimIteration
attribute [local irreducible] load32 store32 SolidThing.shootHeight

theorem contains_repeat (pc : Nat) (h : E1M1AimRepeatProgram.program pc≠none) :
    program pc=E1M1AimRepeatProgram.program pc := by
  have old := E1M1AimActorReject.contains_repeat pc h
  exact (E1M1AimActorBottom.contains_prior pc (by rw [old]; exact h)).trans old

theorem contains_window (pc : Nat) (h : OriginalAimWindow.program pc≠none) :
    program pc=OriginalAimWindow.program pc := by
  by_cases head : 0x2b800≤pc ∧ pc<0x2b81a
  · have all : ∀ i : Fin 26, program (0x2b800+i.val)=OriginalAimWindow.program (0x2b800+i.val) := by decide
    have eq : 0x2b800+(pc-0x2b800)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2b800,by omega⟩
  · have tail : 0x2b89d≤pc ∧ pc<0x2b8a9 := by
      by_cases yes : 0x2b89d≤pc ∧ pc<0x2b8a9
      · exact yes
      · exact False.elim (h (by simp [OriginalAimWindow.program,OriginalAimWindow.bytesProgram,head,yes]))
    have all : ∀ i : Fin 12, program (0x2b89d+i.val)=OriginalAimWindow.program (0x2b89d+i.val) := by decide
    have eq : 0x2b89d+(pc-0x2b89d)=pc := by omega
    simpa only [eq] using all ⟨pc-0x2b89d,by omega⟩

def bottom := E1M1AimActorBottomEntry.result
def returned (s : X86Memory.State) := OriginalAimWindow.returned (bottom s).core 1 (bottom s).flags
def result (s : X86Memory.State) := OriginalInterceptGate.resumed (returned s).core

def ReadSafe (s : X86Memory.State) (a : Word) : Prop :=
  ∀ off∈[(4#32),8,12,16,20,24,28,32,36,40], Apart a (s.regs 4-off)

theorem stack (s : X86Memory.State) : (bottom s).core.regs 4=s.regs 4-24 := by
  have h := (OriginalDivMemory.restored_registers (E1M1AimActorBottom.call (E1M1AimActorBottomEntry.input s).core)).2.2.2.1
  have sp : (E1M1AimActorBottomEntry.input s).core.regs 4=s.regs 4-24 := E1M1AimActorReject.stack s
  simpa [bottom,E1M1AimActorBottomEntry.result,E1M1AimActorBottom.result,E1M1AimActorBottom.divided,
    OriginalAimActorBottom.gate,OriginalAimActorBottom.loadedUpper,put,write,
    (E1M1AimActorBottom.call_fields (E1M1AimActorBottomEntry.input s).core).1,BitVec.sub_add_cancel,
    sp] using h

/-- The second division rewrites the same deeper slots, preserving all six saves. -/
theorem body_frame (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(28#32),32,36,40], Apart a (s.regs 4-off)) :
    load32 (bottom s).core.memory a=load32 (OriginalAimGuard.saved s).memory a := by
  exact (E1M1AimActorBottom.frame _ a (E1M1AimActorBottomEntry.body_safe s a safe)).trans
    (E1M1AimActorReject.top_frame s a safe)

theorem saved_slot (s : X86Memory.State) (off : Word) (member : off∈E1M1AimReturnFrame.slots) :
    load32 (bottom s).core.memory (s.regs 4-off)=load32 (OriginalAimGuard.saved s).memory (s.regs 4-off) := by
  apply body_frame
  intro other h
  apply E1M1AimReturnFrame.stack_apart _ _ _ member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl <;> simp

/-- All six saved registers and the caller return word survive actual FixedDiv,
including stacks whose subtraction wraps around the 32-bit address space. -/
theorem returned_fields (s : X86Memory.State) :
    (returned s).core.regs 0=1 ∧ (returned s).core.regs 4=s.regs 4+4 ∧
    (returned s).core.memory=(bottom s).core.memory ∧
    (returned s).pc=(load32 s.memory (s.regs 4)).toNat ∧
    (returned s).core.regs 5=s.regs 5 ∧ (returned s).core.regs 7=s.regs 7 ∧
    (returned s).core.regs 6=s.regs 6 ∧ (returned s).core.regs 2=s.regs 2 ∧
    (returned s).core.regs 1=s.regs 1 ∧ (returned s).core.regs 3=s.regs 3 := by
  have fields := OriginalAimWindow.returned_fields (bottom s).core 1 (bottom s).flags
  have keep (off : Word) (h : off∈E1M1AimReturnFrame.slots) := saved_slot s off h
  have values := E1M1AimReturnFrame.saved_values s
  have ret := E1M1AimWall.saved_frame s (s.regs 4) (E1M1AimWall.return_safe _)
  rw [stack] at fields
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

theorem registers (s : X86Memory.State) :
    (result s).pc=0x2c83a ∧ (result s).core.regs 4=s.regs 4+4 ∧
    (result s).core.regs 3=s.regs 3 ∧ (result s).core.regs 6=s.regs 6 ∧
    (result s).core.regs 7=s.regs 7 ∧
    (result s).core.regs 1=load32 (bottom s).core.memory 0x2c028 ∧
    (result s).core.memory=store32 (bottom s).core.memory (s.regs 3) 0x7fffffff := by
  obtain ⟨eax,sp,mem,pc,ebp,edi,esi,edx,ecx,ebx⟩ := returned_fields s
  simp [result,OriginalInterceptGate.resumed,OriginalInterceptGate.marked,OriginalInterceptGate.restored,
    eax,sp,mem,ebx,esi,edi,put,write]

theorem read_frame (s : X86Memory.State) (a : Word) (safe : ReadSafe s a) :
    load32 (bottom s).core.memory a=load32 s.memory a := by
  have subset (off : Word) (h : off∈[(28#32),32,36,40]) := safe off (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl <;> simp)
  rw [body_frame s a subset]
  apply E1M1AimWall.saved_frame
  intro off h
  apply safe off
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> simp

theorem frame (s : X86Memory.State) (a : Word) (safe : ReadSafe s a) (mark : Apart a (s.regs 3)) :
    load32 (result s).core.memory a=load32 s.memory a := by
  rw [(registers s).2.2.2.2.2.2,load_store_apart _ _ _ _ mark]
  exact read_frame s a safe

/-- Complete the authenticated rejection epilogue and the real parent mark.
The arithmetic decision is supplied by the preceding entry theorem. -/
theorem continuation (s : X86Memory.State) (atReject : (bottom s).pc=0x2b89d)
    (returnWord : load32 s.memory (s.regs 4)=0x2c86d) :
    X86CodeMemory.Prefix FloorCaller.cm program [] 13 (bottom s) (result s) := by
  have first := (X86CodeMemory.lift_success (OriginalAimWindow.continue_execution (bottom s).core (bottom s).flags)
    FloorCaller.cm).transfer program [] contains_window (by simp)
  rw [OriginalPathXStep.at_pc _ _ atReject] at first
  have fields := returned_fields s
  have pc : (returned s).pc=0x2c86d := by rw [fields.2.2.2.1,returnWord]; rfl
  have tail := (X86CodeMemory.lift_success (OriginalInterceptGate.resume_execution (returned s).core
    (returned s).flags) FloorCaller.cm).transfer program []
    (fun pc h => (contains_repeat pc (by rw [E1M1AimRepeatProgram.contains_call pc h]; exact h)).trans
      (E1M1AimRepeatProgram.contains_call pc h)) (by simp)
  rw [OriginalPathXStep.at_pc _ _ pc] at tail
  have count : OriginalInterceptGate.resumeSteps (returned s).core=5 := by simp [OriginalInterceptGate.resumeSteps,fields.1]
  rw [count] at tail
  exact E1M1PspriteStep.prefix_trans first tail
/-- Source actor representation and both successful divisions lead to the same
strict bottom rejection, completed callback return, parent mark and source suffix. -/
theorem execution (s : X86Memory.State) (f : Option Flags)
    (scene : Scene) (shooterId : Nat) (thing : SolidThing) (path : PathResult)
    (range lower upper topSlope bottomSlope : Fixed) (log : Array AutoAim.Portal) (i : Nat) (rest : List Nat)
    (hit : Intercept) (pointer who : Word)
    (record : OriginalLineFinish.RecordAt s.memory (s.regs 0) hit pointer)
    (selected : path.visited[i]! = hit) (isThing : hit.isLine=false)
    (tagSafe : Safe (s.regs 4) (s.regs 0+4)) (pointerSafe : Safe (s.regs 4) (s.regs 0+8))
    (shooterSafe : Safe (s.regs 4) 0x2b9ac) (flagsSafe : Safe (s.regs 4) (pointer+104))
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
      (range*hit.frac)=.ok bottomSlope) (above : upper.raw<bottomSlope.raw)
    (returnWord : load32 s.memory (s.regs 4)=0x2c86d) :
    (∃ n≤102, X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ (result s)) ∧
    (result s).pc=0x2c83a ∧ (result s).core.regs 4=s.regs 4+4 ∧
    (result s).core.regs 6=s.regs 6 ∧ (result s).core.regs 7=s.regs 7 ∧
    remaining scene shooterId thing path range (i::rest) lower upper log =
      remaining scene shooterId thing path range rest lower upper log := by
  have machineDifferent : pointer≠who := fun same => different (identity.mp same)
  have machineShootable : s.memory (pointer+104) &&& (4#8)≠0 := by
    rw [shootable] at flags; simpa using flags
  obtain ⟨⟨n,hn,run⟩,pc,_⟩ := E1M1AimActorBottomEntry.execution
    s f hit pointer who range scene.things[hit.id]!.z scene.things[hit.id]!.height thing.shootHeight
    lower upper topSlope bottomSlope record isThing tagSafe pointerSafe shooterSafe flagsSafe shooter
    machineDifferent machineShootable topSafe safe r z0 ht eye0 bound high topOk admitted bottomOk
  have pc : (bottom s).pc=0x2b89d := by simpa only [bottom,if_pos above] using pc
  have regs := registers s
  exact ⟨⟨n+13,by omega,E1M1PspriteStep.prefix_trans run (continuation s pc returnWord)⟩,
    regs.1,regs.2.1,regs.2.2.2.1,regs.2.2.2.2.1,
    E1M1AimActorBottomEntry.source_reject scene shooterId thing path range lower upper topSlope bottomSlope log
      i rest hit selected isThing different shootable topOk admitted bottomOk above⟩
end Doom.Proofs.E1M1AimActorBottomReject
