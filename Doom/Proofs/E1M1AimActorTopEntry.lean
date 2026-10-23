import Doom.Proofs.E1M1AimActorTop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimActorTopEntry
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1AimWall (Safe)
open E1M1AimActorTop (program)
open E1M1AimActorSkip (input reached)
open E1M1AimIteration
attribute [local irreducible] load32 store32 SolidThing.shootHeight

def entered (s : X86Memory.State) := OriginalAimActorGuard.flagGate (reached s)
def result (s : X86Memory.State) := E1M1AimActorTop.result (reached s)

/-- Read protection stated entirely at callback entry, including the four words
used by the later division CALL and helper saves. -/
def ReadSafe (s : X86Memory.State) (pointer : Word) : Prop :=
  ∀ a∈[s.regs 0,(0x2b9b8#32),pointer+20,pointer+68,(0x2b9a8#32),(0x2c1e4#32)],
    ∀ off∈[(4#32),8,12,16,20,24,28,32,36,40], Apart a (s.regs 4-off)

theorem prologue_safe (s : X86Memory.State) (pointer a : Word) (safe : ReadSafe s pointer)
    (member : a∈[s.regs 0,(0x2b9b8#32),pointer+20,pointer+68,(0x2b9a8#32),(0x2c1e4#32)]) :
    Safe (s.regs 4) a := by
  intro off h
  apply safe a member off
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> simp

/-- The eligible branch reaches the slope code through the real prologue,
shooter identity comparison and shootable-bit test. -/
theorem entry (s : X86Memory.State) (f : Option Flags) (hit : Intercept) (pointer who : Word)
    (record : OriginalLineFinish.RecordAt s.memory (s.regs 0) hit pointer) (isThing : hit.isLine=false)
    (tagSafe : Safe (s.regs 4) (s.regs 0+4)) (pointerSafe : Safe (s.regs 4) (s.regs 0+8))
    (shooterSafe : Safe (s.regs 4) 0x2b9ac) (flagsSafe : Safe (s.regs 4) (pointer+104))
    (shooter : load32 s.memory 0x2b9ac=who)
    (different : pointer≠who) (shootable : s.memory (pointer+104) &&& (4#8)≠0) :
    X86CodeMemory.Prefix FloorCaller.cm program [] 15 ⟨s,f,0x2b760⟩ (entered s) ∧
    (entered s).pc=0x2b843 := by
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
  have head := (X86CodeMemory.lift_success (OriginalAimGuard.entry_execution s f) FloorCaller.cm).transfer
    program [] (fun pc h => (E1M1AimActorTop.contains_skip pc
      (by rw [E1M1AimActorSkip.contains_guard pc h]; exact h)).trans (E1M1AimActorSkip.contains_guard pc h)) (by simp)
  have contained (pc : Nat) (h : OriginalAimActorGuard.program pc≠none) : program pc=OriginalAimActorGuard.program pc :=
    (E1M1AimActorTop.contains_skip pc (by rw [E1M1AimActorSkip.contains_actor pc h]; exact h)).trans
      (E1M1AimActorSkip.contains_actor pc h)
  have compare := (X86CodeMemory.lift_success (OriginalAimActorGuard.head_execution (input s)
    (OriginalAimGuard.entry s).flags) FloorCaller.cm).transfer program [] contained (by simp)
  change X86CodeMemory.Prefix FloorCaller.cm program [] 4
    ⟨(OriginalAimGuard.entry s).core,(OriginalAimGuard.entry s).flags,0x2b81a⟩ _ at compare
  rw [OriginalPathXStep.at_pc _ _ entryPc] at compare
  have gatePc : (OriginalAimActorGuard.gate (input s)).pc=0x2b831 := by
    simp only [OriginalAimActorGuard.gate,ptr,whoWord,if_neg different]
  have check := (X86CodeMemory.lift_success (OriginalAimActorGuard.flags_execution (reached s)
    (OriginalAimActorGuard.gate (input s)).flags) FloorCaller.cm).transfer program [] contained (by simp)
  change X86CodeMemory.Prefix FloorCaller.cm program [] 2
    ⟨(OriginalAimActorGuard.gate (input s)).core,(OriginalAimActorGuard.gate (input s)).flags,0x2b831⟩ _ at check
  rw [OriginalPathXStep.at_pc _ _ gatePc] at check
  exact ⟨E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans head compare) check,
    by simp only [entered,OriginalAimActorGuard.flagGate,flagWord,if_neg shootable]⟩

theorem reached_fields (s : X86Memory.State) :
    (reached s).memory=(OriginalAimGuard.saved s).memory ∧
    (reached s).regs 1=load32 (OriginalAimGuard.saved s).memory (s.regs 0+8) ∧
    (reached s).regs 2=s.regs 0 ∧ (reached s).regs 4=s.regs 4-24 := by
  simp [reached,input,OriginalAimActorGuard.loaded,OriginalAimActorGuard.first,OriginalAimActorGuard.actor,
    OriginalAimGuard.prepared,OriginalAimGuard.saved,OriginalAimGuard.save6,OriginalAimGuard.save5,
    OriginalAimGuard.save4,OriginalAimGuard.save3,OriginalAimGuard.save2,OriginalAimGuard.save1,
    X86Routine.pushWord,put,X86.write,BitVec.sub_eq_add_neg,BitVec.add_assoc]

/-- The arithmetic operands are transported from the represented entry record
and actor fields, rather than postulating values in the reached registers. -/
theorem inputs (s : X86Memory.State) (hit : Intercept) (pointer : Word)
    (range targetZ targetHeight shootZ lower : Fixed)
    (record : OriginalLineFinish.RecordAt s.memory (s.regs 0) hit pointer)
    (pointerSafe : Safe (s.regs 4) (s.regs 0+8)) (safe : ReadSafe s pointer)
    (r : load32 s.memory (0x2b9b8#32)=range.raw.toBitVec)
    (z0 : load32 s.memory (pointer+20)=targetZ.raw.toBitVec)
    (ht : load32 s.memory (pointer+68)=targetHeight.raw.toBitVec)
    (eye0 : load32 s.memory (0x2b9a8#32)=shootZ.raw.toBitVec)
    (bound : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec) :
    OriginalAimDistance.range (reached s)=range.raw.toBitVec ∧
    OriginalAimDistance.fraction (reached s)=hit.frac.raw.toBitVec ∧
    OriginalAimActorTop.z (reached s)=targetZ.raw.toBitVec ∧
    OriginalAimActorTop.height (reached s)=targetHeight.raw.toBitVec ∧
    OriginalAimActorTop.eye (reached s)=shootZ.raw.toBitVec ∧
    load32 (reached s).memory (0x2c1e4#32)=lower.raw.toBitVec ∧
    (reached s).regs 1=pointer := by
  have fields := reached_fields s
  have ptr : (reached s).regs 1=pointer := by
    rw [fields.2.1,E1M1AimWall.saved_frame s _ pointerSafe]; exact record.2.2
  have keep (a : Word) (ha : a∈[s.regs 0,(0x2b9b8#32),pointer+20,pointer+68,(0x2b9a8#32),(0x2c1e4#32)]) :
      load32 (reached s).memory a=load32 s.memory a := by
    rw [fields.1]; exact E1M1AimWall.saved_frame s a (prologue_safe s pointer a safe ha)
  refine ⟨?_,?_,?_,?_,?_,?_,ptr⟩
  · exact (keep _ (by simp)).trans r
  · unfold OriginalAimDistance.fraction; rw [fields.2.2.1]; exact (keep _ (by simp)).trans record.1
  · unfold OriginalAimActorTop.z; rw [ptr]; exact (keep _ (by simp)).trans z0
  · unfold OriginalAimActorTop.height; rw [ptr]; exact (keep _ (by simp)).trans ht
  · exact (keep _ (by simp)).trans eye0
  · exact (keep _ (by simp)).trans bound

theorem lower_safe (s : X86Memory.State) (pointer : Word) (safe : ReadSafe s pointer) :
    E1M1AimActorTop.ReadSafe (reached s) (0x2c1e4#32) := by
  intro off member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl <;> rw [(reached_fields s).2.2.2] <;>
    simpa only [BitVec.sub_sub,show (24#32)+4=28 from rfl,show (24#32)+8=32 from rfl,
      show (24#32)+12=36 from rfl,show (24#32)+16=40 from rfl] using safe (0x2c1e4#32) (by simp) _ (by simp)

/-- Continuous eligible actor execution from callback entry through the top
slope and first vertical rejection decision. The rejection RET and the later
bottom-slope branch are not included in this prefix. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (hit : Intercept) (pointer who : Word)
    (range targetZ targetHeight shootZ lower slope : Fixed)
    (record : OriginalLineFinish.RecordAt s.memory (s.regs 0) hit pointer) (isThing : hit.isLine=false)
    (tagSafe : Safe (s.regs 4) (s.regs 0+4)) (pointerSafe : Safe (s.regs 4) (s.regs 0+8))
    (shooterSafe : Safe (s.regs 4) 0x2b9ac) (flagsSafe : Safe (s.regs 4) (pointer+104))
    (shooter : load32 s.memory 0x2b9ac=who)
    (different : pointer≠who) (shootable : s.memory (pointer+104) &&& (4#8)≠0)
    (safe : ReadSafe s pointer)
    (r : load32 s.memory (0x2b9b8#32)=range.raw.toBitVec)
    (z0 : load32 s.memory (pointer+20)=targetZ.raw.toBitVec)
    (ht : load32 s.memory (pointer+68)=targetHeight.raw.toBitVec)
    (eye0 : load32 s.memory (0x2b9a8#32)=shootZ.raw.toBitVec)
    (bound : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec)
    (ok : checkedPathDiv (targetZ+targetHeight-shootZ) (range*hit.frac)=.ok slope) :
    (∃ n≤56, X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ (result s)) ∧
    (result s).pc=(if slope.raw<lower.raw then 0x2b875 else 0x2b881) ∧
    (result s).core.regs 6=slope.raw.toBitVec ∧ (result s).core.regs 7=slope.raw.toBitVec ∧
    (result s).core.regs 3=(range*hit.frac).raw.toBitVec ∧
    (result s).core.regs 1=pointer ∧ (result s).core.regs 4=s.regs 4-24 ∧
    load32 (result s).core.memory (0x2c1e4#32)=lower.raw.toBitVec := by
  have head := entry s f hit pointer who record isThing tagSafe pointerSafe shooterSafe flagsSafe shooter different shootable
  obtain ⟨ri,fr,zi,hi,ei,lo,ptr⟩ := inputs s hit pointer range targetZ targetHeight shootZ lower record pointerSafe safe r z0 ht eye0 bound
  obtain ⟨⟨n,hn,tail⟩,pc,top1,top2,dist,actor,stack,lowerOut⟩ := E1M1AimActorTop.execution
    (reached s) (entered s).flags range hit.frac targetZ targetHeight shootZ lower slope ri fr zi hi ei lo (lower_safe s pointer safe) ok
  change X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨(entered s).core,(entered s).flags,0x2b843⟩ _ at tail
  rw [OriginalPathXStep.at_pc _ _ head.2] at tail
  exact ⟨⟨15+n,by omega,E1M1PspriteStep.prefix_trans head.1 tail⟩,pc,top1,top2,dist,
    actor.trans ptr,stack.trans (reached_fields s).2.2.2,lowerOut⟩

/-- The production loop rejects the same strictly-below actor top and advances
without a bottom-slope division or changing its window/portal history. -/
theorem source_reject (scene : Scene) (shooter : Nat) (thing : SolidThing) (path : PathResult)
    (distance lower upper slope : Fixed) (log : Array AutoAim.Portal) (i : Nat) (rest : List Nat)
    (hit : Intercept) (selected : path.visited[i]! = hit) (isThing : hit.isLine=false)
    (different : hit.id≠shooter) (shootable : scene.things[hit.id]!.shootable=true)
    (ok : checkedPathDiv (scene.things[hit.id]!.z+scene.things[hit.id]!.height-thing.shootHeight)
      (distance*hit.frac)=.ok slope) (below : slope.raw<lower.raw) :
    remaining scene shooter thing path distance (i::rest) lower upper log =
      remaining scene shooter thing path distance rest lower upper log := by
  have differentBool : (hit.id==shooter)=false := by simp [different]
  have step : visit scene shooter thing path distance i (none,upper,lower,log) =
      .ok (.yield (none,upper,lower,log)) := by
    simp only [visit,selected,isThing,Bool.false_eq_true,↓reduceIte,differentBool,shootable,
      Bool.not_true,Bool.or_self]
    rw [ok]
    simp only [bind,Except.bind,below,↓reduceIte]
    rfl
  unfold remaining
  rw [List.forIn_cons,step]
  rfl
/-- Join the represented production actor to the original first rejection
branch. The original prefix stops before the rejection epilogue and parent scan. -/
theorem reject (s : X86Memory.State) (f : Option Flags)
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
    (safe : ReadSafe s pointer)
    (r : load32 s.memory (0x2b9b8#32)=range.raw.toBitVec)
    (z0 : load32 s.memory (pointer+20)=scene.things[hit.id]!.z.raw.toBitVec)
    (ht : load32 s.memory (pointer+68)=scene.things[hit.id]!.height.raw.toBitVec)
    (eye0 : load32 s.memory (0x2b9a8#32)=thing.shootHeight.raw.toBitVec)
    (bound : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec)
    (ok : checkedPathDiv (scene.things[hit.id]!.z+scene.things[hit.id]!.height-thing.shootHeight)
      (range*hit.frac)=.ok slope) (below : slope.raw<lower.raw) :
    (∃ n≤56, X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ (result s)) ∧
    (result s).pc=0x2b875 ∧ (result s).core.regs 6=slope.raw.toBitVec ∧
    load32 (result s).core.memory (0x2c1e4#32)=lower.raw.toBitVec ∧
    remaining scene shooterId thing path range (i::rest) lower upper log =
      remaining scene shooterId thing path range rest lower upper log := by
  have machineDifferent : pointer≠who := fun same => different (identity.mp same)
  have machineShootable : s.memory (pointer+104) &&& (4#8)≠0 := by
    rw [shootable] at flags; simpa using flags
  have run := execution s f hit pointer who range scene.things[hit.id]!.z scene.things[hit.id]!.height
    thing.shootHeight lower slope record isThing tagSafe pointerSafe shooterSafe flagsSafe shooter
    machineDifferent machineShootable safe r z0 ht eye0 bound ok
  exact ⟨run.1,by simpa only [if_pos below] using run.2.1,run.2.2.1,run.2.2.2.2.2.2.2,
    source_reject scene shooterId thing path range lower upper slope log i rest hit selected isThing different shootable ok below⟩
end Doom.Proofs.E1M1AimActorTopEntry
