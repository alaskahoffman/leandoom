import Doom.Proofs.OriginalAimActorReject
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimActorReject
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1AimActorSkip (reached)
open E1M1AimWall (Safe)
open E1M1AimIteration
attribute [local irreducible] load32 store32 SolidThing.shootHeight

def program : X86Routine.Program := fun pc =>
  match OriginalAimActorReject.program pc with
  | some op => some op
  | none => E1M1AimActorTop.program pc

theorem contains_return (pc : Nat) (h : OriginalAimActorReject.program pc≠none) :
    program pc=OriginalAimActorReject.program pc := by
  unfold program; cases eq : OriginalAimActorReject.program pc <;> simp_all

theorem contains_top (pc : Nat) (h : E1M1AimActorTop.program pc≠none) :
    program pc=E1M1AimActorTop.program pc := by
  have absent : OriginalAimActorReject.program pc=none := by
    by_cases inside : 0x2b875≤pc ∧ pc<0x2b881
    · have all : ∀ i : Fin 12, E1M1AimActorTop.program (0x2b875+i.val)=none := by decide
      have eq : 0x2b875+(pc-0x2b875)=pc := by omega
      exact False.elim (h (by simpa only [eq] using all ⟨pc-0x2b875,by omega⟩))
    · simp [OriginalAimActorReject.program,OriginalAimActorReject.bytesProgram,inside]
  simp [program,absent]

theorem contains_repeat (pc : Nat) (h : E1M1AimRepeatProgram.program pc≠none) :
    program pc=E1M1AimRepeatProgram.program pc := by
  have a := E1M1AimActorSkip.contains_repeat pc h
  have b := E1M1AimActorTop.contains_skip pc (by rw [a]; exact h)
  exact (contains_top pc (by rw [b,a]; exact h)).trans (b.trans a)

def top := E1M1AimActorTopEntry.result
def returned (s : X86Memory.State) := OriginalAimWindow.returned (top s).core 1 (top s).flags
def result (s : X86Memory.State) := OriginalInterceptGate.resumed (returned s).core

def ReadSafe (s : X86Memory.State) (a : Word) : Prop :=
  ∀ off∈[(4#32),8,12,16,20,24,28,32,36,40], Apart a (s.regs 4-off)

theorem stack (s : X86Memory.State) : (top s).core.regs 4=s.regs 4-24 := by
  have h := (OriginalDivMemory.restored_registers (E1M1AimActorTop.call (reached s))).2.2.2.1
  simpa [top,E1M1AimActorTopEntry.result,E1M1AimActorTop.result,E1M1AimActorTop.divided,
    OriginalAimActorTop.gate,OriginalAimActorTop.slopes,OriginalAimActorTop.savedSlope,put,write,
    (E1M1AimActorTop.call_fields (reached s)).1,BitVec.sub_add_cancel,
    (E1M1AimActorTopEntry.reached_fields s).2.2.2] using h

/-- Only the four deeper division words are added after the callback prologue. -/
theorem top_frame (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(28#32),32,36,40], Apart a (s.regs 4-off)) :
    load32 (top s).core.memory a=load32 (OriginalAimGuard.saved s).memory a := by
  apply E1M1AimActorTop.frame (reached s) a
  intro off member
  rw [(E1M1AimActorTopEntry.reached_fields s).2.2.2]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl <;>
    simpa only [BitVec.sub_sub,show (24#32)+4=28 from rfl,show (24#32)+8=32 from rfl,
      show (24#32)+12=36 from rfl,show (24#32)+16=40 from rfl] using safe _ (by simp)

theorem saved_slot (s : X86Memory.State) (off : Word) (member : off∈E1M1AimReturnFrame.slots) :
    load32 (top s).core.memory (s.regs 4-off)=load32 (OriginalAimGuard.saved s).memory (s.regs 4-off) := by
  apply top_frame
  intro other h
  apply E1M1AimReturnFrame.stack_apart _ _ _ member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl <;> simp

/-- All six saved registers and the caller return word survive actual FixedDiv,
including stacks whose subtraction wraps around the 32-bit address space. -/
theorem returned_fields (s : X86Memory.State) :
    (returned s).core.regs 0=1 ∧ (returned s).core.regs 4=s.regs 4+4 ∧
    (returned s).core.memory=(top s).core.memory ∧
    (returned s).pc=(load32 s.memory (s.regs 4)).toNat ∧
    (returned s).core.regs 5=s.regs 5 ∧ (returned s).core.regs 7=s.regs 7 ∧
    (returned s).core.regs 6=s.regs 6 ∧ (returned s).core.regs 2=s.regs 2 ∧
    (returned s).core.regs 1=s.regs 1 ∧ (returned s).core.regs 3=s.regs 3 := by
  have fields := OriginalAimWindow.returned_fields (top s).core 1 (top s).flags
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
    (result s).core.regs 1=load32 (top s).core.memory 0x2c028 ∧
    (result s).core.memory=store32 (top s).core.memory (s.regs 3) 0x7fffffff := by
  obtain ⟨eax,sp,mem,pc,ebp,edi,esi,edx,ecx,ebx⟩ := returned_fields s
  simp [result,OriginalInterceptGate.resumed,OriginalInterceptGate.marked,OriginalInterceptGate.restored,
    eax,sp,mem,ebx,esi,edi,put,write]

theorem read_frame (s : X86Memory.State) (a : Word) (safe : ReadSafe s a) :
    load32 (top s).core.memory a=load32 s.memory a := by
  have subset (off : Word) (h : off∈[(28#32),32,36,40]) := safe off (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl <;> simp)
  rw [top_frame s a subset]
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
theorem continuation (s : X86Memory.State) (atReject : (top s).pc=0x2b875)
    (returnWord : load32 s.memory (s.regs 4)=0x2c86d) :
    X86CodeMemory.Prefix FloorCaller.cm program [] 13 (top s) (result s) := by
  have first := (X86CodeMemory.lift_success (OriginalAimActorReject.execution (top s).core (top s).flags)
    FloorCaller.cm).transfer program [] contains_return (by simp)
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
/-- Join the production actor rejection to the complete original callback and parent. -/
theorem execution (s : X86Memory.State) (f : Option Flags)
    (scene : Scene) (shooterId : Nat) (thing : SolidThing) (path : PathResult)
    (range lower upper slope : Fixed) (log : Array AutoAim.Portal) (i : Nat) (rest : List Nat)
    (hit : Intercept) (pointer who : Word)
    (record : OriginalLineFinish.RecordAt s.memory (s.regs 0) hit pointer)
    (selected : path.visited[i]! = hit) (isThing : hit.isLine=false)
    (tagSafe : Safe (s.regs 4) (s.regs 0+4)) (pointerSafe : Safe (s.regs 4) (s.regs 0+8))
    (shooterSafe : Safe (s.regs 4) 0x2b9ac) (flagsSafe : Safe (s.regs 4) (pointer+104))
    (shooter : load32 s.memory 0x2b9ac=who)
    (identity : pointer=who ↔ hit.id=shooterId)
    (flags : (s.memory (pointer+104) &&& (4#8) != 0)=scene.things[hit.id]!.shootable)
    (different : hit.id≠shooterId) (shootable : scene.things[hit.id]!.shootable=true)
    (safe : E1M1AimActorTopEntry.ReadSafe s pointer)
    (r : load32 s.memory (0x2b9b8#32)=range.raw.toBitVec)
    (z0 : load32 s.memory (pointer+20)=scene.things[hit.id]!.z.raw.toBitVec)
    (ht : load32 s.memory (pointer+68)=scene.things[hit.id]!.height.raw.toBitVec)
    (eye0 : load32 s.memory (0x2b9a8#32)=thing.shootHeight.raw.toBitVec)
    (bound : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec)
    (ok : checkedPathDiv (scene.things[hit.id]!.z+scene.things[hit.id]!.height-thing.shootHeight)
      (range*hit.frac)=.ok slope) (below : slope.raw<lower.raw)
    (returnWord : load32 s.memory (s.regs 4)=0x2c86d) :
    (∃ n≤69, X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ (result s)) ∧
    (result s).pc=0x2c83a ∧ (result s).core.regs 4=s.regs 4+4 ∧
    remaining scene shooterId thing path range (i::rest) lower upper log =
      remaining scene shooterId thing path range rest lower upper log := by
  obtain ⟨⟨n,hn,run⟩,pc,_,_,source⟩ := E1M1AimActorTopEntry.reject
    s f scene shooterId thing path range lower upper slope log i rest hit pointer who
    record selected isThing tagSafe pointerSafe shooterSafe flagsSafe shooter identity flags different shootable safe
    r z0 ht eye0 bound ok below
  have run := run.transfer program [] contains_top (by simp)
  exact ⟨⟨n+13,by omega,E1M1PspriteStep.prefix_trans run (continuation s pc returnWord)⟩,
    (registers s).1,(registers s).2.1,source⟩
end Doom.Proofs.E1M1AimActorReject
