import Doom.Proofs.E1M1AimActorSelect
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimActorSelectEntry
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1AimWall (Safe)
open E1M1AimActorSelect (program)
open E1M1AimIteration E1M1AimSource
attribute [local irreducible] load32 store32 SolidThing.shootHeight E1M1AimActorBottomEntry.result

def input := E1M1AimActorBottomEntry.result
def result (s : X86Memory.State) := OriginalAimActorSelect.result (input s).core

/-- Actual callback entry through both admitted slopes, clipping, midpoint and
selected-target/slope stores. This stops before the false-return epilogue. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (hit : Intercept) (pointer who : Word)
    (range targetZ targetHeight shootZ lower upper topSlope bottomSlope : Fixed)
    (record : OriginalLineFinish.RecordAt s.memory (s.regs 0) hit pointer) (isThing : hit.isLine=false)
    (tagSafe : Safe (s.regs 4) (s.regs 0+4)) (pointerSafe : Safe (s.regs 4) (s.regs 0+8))
    (shooterSafe : Safe (s.regs 4) 0x2b9ac) (flagsSafe : Safe (s.regs 4) (pointer+104))
    (shooter : load32 s.memory 0x2b9ac=who)
    (different : pointer≠who) (shootable : s.memory (pointer+104) &&& (4#8)≠0)
    (topSafe : E1M1AimActorTopEntry.ReadSafe s pointer) (safe : E1M1AimActorBottomEntry.ReadSafe s pointer)
    (r : load32 s.memory (0x2b9b8#32)=range.raw.toBitVec)
    (z0 : load32 s.memory (pointer+20)=targetZ.raw.toBitVec)
    (ht : load32 s.memory (pointer+68)=targetHeight.raw.toBitVec)
    (eye0 : load32 s.memory (0x2b9a8#32)=shootZ.raw.toBitVec)
    (low : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec)
    (high : load32 s.memory (0x2c1e8#32)=upper.raw.toBitVec)
    (topOk : checkedPathDiv (targetZ+targetHeight-shootZ) (range*hit.frac)=.ok topSlope)
    (admitted : ¬topSlope.raw<lower.raw)
    (bottomOk : checkedPathDiv (targetZ-shootZ) (range*hit.frac)=.ok bottomSlope)
    (bottomAdmitted : ¬upper.raw<bottomSlope.raw) :
    (∃ n≤103, X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ (result s)) ∧
    (result s).pc=0x2b8d2 ∧
    load32 (result s).core.memory (0x2b9f8#32)=pointer ∧
    load32 (result s).core.memory (0x2b9b4#32)=
      (AutoAim.center (max bottomSlope.raw lower.raw) (min topSlope.raw upper.raw)).raw.toBitVec ∧
    (result s).core.regs 4=s.regs 4-24 ∧
    load32 (result s).core.memory (0x2c1e4#32)=lower.raw.toBitVec ∧
    load32 (result s).core.memory (0x2c1e8#32)=upper.raw.toBitVec := by
  obtain ⟨⟨n,hn,first⟩,pc,bot,up,top1,top2,actor,sp,lowOut,highOut⟩ := E1M1AimActorBottomEntry.execution
    s f hit pointer who range targetZ targetHeight shootZ lower upper topSlope bottomSlope record isThing
    tagSafe pointerSafe shooterSafe flagsSafe shooter different shootable topSafe safe r z0 ht eye0 low high topOk admitted bottomOk
  have pc : (input s).pc=0x2b8a9 := by simpa only [input,if_neg bottomAdmitted] using pc
  obtain ⟨⟨k,hk,tail⟩,pcOut,_,_,stack,memory,target,slope⟩ := E1M1AimActorSelect.execution
    (input s).core (input s).flags lower.raw upper.raw bottomSlope.raw topSlope.raw pointer
    lowOut up bot top1 top2 actor
  rw [OriginalPathXStep.at_pc _ _ pc] at tail
  have first := first.transfer program [] E1M1AimActorSelect.contains_prior (by simp)
  refine ⟨⟨n+k,by omega,E1M1PspriteStep.prefix_trans first tail⟩,pcOut,target,slope,stack.trans sp,?_,?_⟩
  · change load32 (OriginalAimActorSelect.result (input s).core).core.memory (0x2c1e4#32)=_
    rw [memory,load_store_apart _ _ _ _ (by unfold Apart; decide),load_store_apart _ _ _ _ (by unfold Apart; decide)]
    exact lowOut
  · change load32 (OriginalAimActorSelect.result (input s).core).core.memory (0x2c1e8#32)=_
    rw [memory,load_store_apart _ _ _ _ (by unfold Apart; decide),load_store_apart _ _ _ _ (by unfold Apart; decide)]
    exact highOut


/-- The actual source result, retaining the stopped path and portal evidence. -/
def window (scene : Scene) (thing : SolidThing) (range lower upper topSlope bottomSlope : Fixed)
    (log : Array AutoAim.Portal) (hit : Intercept) : AutoAim.Window :=
  {portalBottom:=lower.raw, portalTop:=upper.raw, targetBottom:=bottomSlope.raw,
   targetTop:=topSlope.raw, distance:=range*hit.frac, shootZ:=thing.shootHeight,
   target:=hit.id, targetZ:=scene.things[hit.id]!.z, targetHeight:=scene.things[hit.id]!.height, portals:=log}

def answer (scene : Scene) (thing : SolidThing) (path : PathResult)
    (range lower upper topSlope bottomSlope : Fixed) (log : Array AutoAim.Portal) (i : Nat) (hit : Intercept) : AimResult :=
  {slope:=AutoAim.center (max bottomSlope.raw lower.raw) (min topSlope.raw upper.raw),
   target:=some hit.id, path:=stopped path (i+1),
   window:=some (window scene thing range lower upper topSlope bottomSlope log hit)}

theorem source_selection (scene : Scene) (shooter : Nat) (thing : SolidThing) (path : PathResult)
    (distance lower upper topSlope bottomSlope : Fixed) (log : Array AutoAim.Portal) (i : Nat) (rest : List Nat)
    (hit : Intercept) (selected : path.visited[i]! = hit) (isThing : hit.isLine=false)
    (different : hit.id≠shooter) (shootable : scene.things[hit.id]!.shootable=true)
    (topOk : checkedPathDiv (scene.things[hit.id]!.z+scene.things[hit.id]!.height-thing.shootHeight)
      (distance*hit.frac)=.ok topSlope) (admitted : ¬topSlope.raw<lower.raw)
    (bottomOk : checkedPathDiv (scene.things[hit.id]!.z-thing.shootHeight)
      (distance*hit.frac)=.ok bottomSlope) (bottomAdmitted : ¬upper.raw<bottomSlope.raw) :
    remaining scene shooter thing path distance (i::rest) lower upper log =
      .ok (answer scene thing path distance lower upper topSlope bottomSlope log i hit) := by
  have differentBool : (hit.id==shooter)=false := by simp [different]
  have step : visit scene shooter thing path distance i (none,upper,lower,log) =
      .ok (.done (some (answer scene thing path distance lower upper topSlope bottomSlope log i hit),upper,lower,log)) := by
    simp only [visit,selected,isThing,Bool.false_eq_true,↓reduceIte,differentBool,shootable,
      Bool.not_true,Bool.or_self]
    rw [topOk]
    simp only [bind,Except.bind,admitted,↓reduceIte]
    rw [bottomOk]
    simp only [bind,Except.bind,bottomAdmitted,↓reduceIte]
    rfl
  unfold remaining
  rw [List.forIn_cons,step]
  rfl

theorem selected (s : X86Memory.State) (f : Option Flags)
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
      (range*hit.frac)=.ok bottomSlope) (bottomAdmitted : ¬upper.raw<bottomSlope.raw) :
    (∃ n≤103, X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ (result s)) ∧
    (result s).pc=0x2b8d2 ∧
    load32 (result s).core.memory (0x2b9f8#32)=pointer ∧
    load32 (result s).core.memory (0x2b9b4#32)=
      (answer scene thing path range lower upper topSlope bottomSlope log i hit).slope.raw.toBitVec ∧
    remaining scene shooterId thing path range (i::rest) lower upper log =
      .ok (answer scene thing path range lower upper topSlope bottomSlope log i hit) := by
  have machineDifferent : pointer≠who := fun same => different (identity.mp same)
  have machineShootable : s.memory (pointer+104) &&& (4#8)≠0 := by
    rw [shootable] at flags; simpa using flags
  obtain ⟨run,pc,target,slope,_⟩ := execution
    s f hit pointer who range scene.things[hit.id]!.z scene.things[hit.id]!.height thing.shootHeight
    lower upper topSlope bottomSlope record isThing tagSafe pointerSafe shooterSafe flagsSafe shooter
    machineDifferent machineShootable topSafe safe r z0 ht eye0 bound high topOk admitted bottomOk bottomAdmitted
  exact ⟨run,pc,target,slope,source_selection scene shooterId thing path range lower upper topSlope bottomSlope log
    i rest hit selected isThing different shootable topOk admitted bottomOk bottomAdmitted⟩
end Doom.Proofs.E1M1AimActorSelectEntry
