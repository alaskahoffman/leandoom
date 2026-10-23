import Doom.Proofs.E1M1AimActorBottom
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimActorBottomEntry
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1AimWall (Safe)
open E1M1AimActorBottom (program)
open E1M1AimIteration
attribute [local irreducible] load32 store32 SolidThing.shootHeight E1M1AimActorTopEntry.result

def input := E1M1AimActorTopEntry.result
def result (s : X86Memory.State) := E1M1AimActorBottom.result (input s).core

def ReadSafe (s : X86Memory.State) (pointer : Word) : Prop :=
  ∀ a∈[pointer+20,(0x2b9a8#32),(0x2c1e4#32),(0x2c1e8#32)], E1M1AimActorReject.ReadSafe s a

theorem contains_top (pc : Nat) (h : E1M1AimActorTop.program pc≠none) :
    program pc=E1M1AimActorTop.program pc := by
  have old := E1M1AimActorReject.contains_top pc h
  exact (E1M1AimActorBottom.contains_prior pc (by rw [old]; exact h)).trans old

/-- Both divisions reuse the same four deeper stack slots. -/
theorem body_safe (s : X86Memory.State) (a : Word)
    (safe : ∀ off∈[(28#32),32,36,40], Apart a (s.regs 4-off)) :
    E1M1AimActorBottom.ReadSafe (input s).core a := by
  intro off member
  have stack : (input s).core.regs 4=s.regs 4-24 := E1M1AimActorReject.stack s
  rw [stack]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl <;>
    simpa only [BitVec.sub_sub,show (24#32)+4=28 from rfl,show (24#32)+8=32 from rfl,
      show (24#32)+12=36 from rfl,show (24#32)+16=40 from rfl] using safe _ (by simp)

theorem frame (s : X86Memory.State) (a : Word) (safe : E1M1AimActorReject.ReadSafe s a) :
    load32 (result s).core.memory a=load32 s.memory a := by
  have deeper : ∀ off∈[(28#32),32,36,40], Apart a (s.regs 4-off) := by
    intro off member
    apply safe off
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> simp
  exact (E1M1AimActorBottom.frame (input s).core a (body_safe s a deeper)).trans
    (E1M1AimActorReject.read_frame s a safe)

/-- Continuous eligible callback entry through both exact slopes and the second
vertical decision. The first top decision must admit this actor. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (hit : Intercept) (pointer who : Word)
    (range targetZ targetHeight shootZ lower upper topSlope bottomSlope : Fixed)
    (record : OriginalLineFinish.RecordAt s.memory (s.regs 0) hit pointer) (isThing : hit.isLine=false)
    (tagSafe : Safe (s.regs 4) (s.regs 0+4)) (pointerSafe : Safe (s.regs 4) (s.regs 0+8))
    (shooterSafe : Safe (s.regs 4) 0x2b9ac) (flagsSafe : Safe (s.regs 4) (pointer+104))
    (shooter : load32 s.memory 0x2b9ac=who)
    (different : pointer≠who) (shootable : s.memory (pointer+104) &&& (4#8)≠0)
    (topSafe : E1M1AimActorTopEntry.ReadSafe s pointer) (safe : ReadSafe s pointer)
    (r : load32 s.memory (0x2b9b8#32)=range.raw.toBitVec)
    (z0 : load32 s.memory (pointer+20)=targetZ.raw.toBitVec)
    (ht : load32 s.memory (pointer+68)=targetHeight.raw.toBitVec)
    (eye0 : load32 s.memory (0x2b9a8#32)=shootZ.raw.toBitVec)
    (low : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec)
    (high : load32 s.memory (0x2c1e8#32)=upper.raw.toBitVec)
    (topOk : checkedPathDiv (targetZ+targetHeight-shootZ) (range*hit.frac)=.ok topSlope)
    (admitted : ¬topSlope.raw<lower.raw)
    (bottomOk : checkedPathDiv (targetZ-shootZ) (range*hit.frac)=.ok bottomSlope) :
    (∃ n≤89, X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ (result s)) ∧
    (result s).pc=(if upper.raw<bottomSlope.raw then 0x2b89d else 0x2b8a9) ∧
    (result s).core.regs 0=bottomSlope.raw.toBitVec ∧ (result s).core.regs 3=upper.raw.toBitVec ∧
    (result s).core.regs 6=topSlope.raw.toBitVec ∧ (result s).core.regs 7=topSlope.raw.toBitVec ∧
    (result s).core.regs 1=pointer ∧ (result s).core.regs 4=s.regs 4-24 ∧
    load32 (result s).core.memory (0x2c1e4#32)=lower.raw.toBitVec ∧
    load32 (result s).core.memory (0x2c1e8#32)=upper.raw.toBitVec := by
  obtain ⟨⟨n,hn,first⟩,pc,top1,top2,dist,ptr,sp,_⟩ := E1M1AimActorTopEntry.execution
    s f hit pointer who range targetZ targetHeight shootZ lower topSlope record isThing
    tagSafe pointerSafe shooterSafe flagsSafe shooter different shootable topSafe r z0 ht eye0 low topOk
  have pc : (input s).pc=0x2b881 := by simpa only [input,if_neg admitted] using pc
  have zi : OriginalAimActorBottom.z (input s).core=targetZ.raw.toBitVec := by
    change load32 (input s).core.memory ((input s).core.regs 1+20)=_
    unfold input
    rw [ptr]; exact (E1M1AimActorReject.read_frame s _ (safe _ (by simp))).trans z0
  have ei : OriginalAimActorBottom.eye (input s).core=shootZ.raw.toBitVec :=
    (E1M1AimActorReject.read_frame s _ (safe _ (by simp))).trans eye0
  have up : load32 (input s).core.memory (0x2c1e8#32)=upper.raw.toBitVec :=
    (E1M1AimActorReject.read_frame s _ (safe _ (by simp))).trans high
  have upperSafe : E1M1AimActorBottom.ReadSafe (input s).core (0x2c1e8#32) := by
    apply body_safe
    intro off member
    apply safe _ (by simp) off
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> simp
  obtain ⟨⟨k,hk,tail⟩,pcOut,bottom,upperOut,top1Out,top2Out,ptrOut,spOut,_⟩ :=
    E1M1AimActorBottom.execution (input s).core (input s).flags (range*hit.frac) targetZ shootZ upper bottomSlope
      dist zi ei up upperSafe bottomOk
  rw [OriginalPathXStep.at_pc _ _ pc] at tail
  have first := first.transfer program [] contains_top (by simp)
  exact ⟨⟨n+k,by omega,E1M1PspriteStep.prefix_trans first tail⟩,pcOut,bottom,upperOut,
    top1Out.trans top1,top2Out.trans top2,ptrOut.trans ptr,spOut.trans sp,
    (frame s _ (safe _ (by simp))).trans low,(frame s _ (safe _ (by simp))).trans high⟩

/-- The live source loop skips exactly this actor after the admitted top and
strictly-too-high bottom, leaving the aim window and portal history unchanged. -/
theorem source_reject (scene : Scene) (shooter : Nat) (thing : SolidThing) (path : PathResult)
    (distance lower upper topSlope bottomSlope : Fixed) (log : Array AutoAim.Portal) (i : Nat) (rest : List Nat)
    (hit : Intercept) (selected : path.visited[i]! = hit) (isThing : hit.isLine=false)
    (different : hit.id≠shooter) (shootable : scene.things[hit.id]!.shootable=true)
    (topOk : checkedPathDiv (scene.things[hit.id]!.z+scene.things[hit.id]!.height-thing.shootHeight)
      (distance*hit.frac)=.ok topSlope) (admitted : ¬topSlope.raw<lower.raw)
    (bottomOk : checkedPathDiv (scene.things[hit.id]!.z-thing.shootHeight)
      (distance*hit.frac)=.ok bottomSlope) (above : upper.raw<bottomSlope.raw) :
    remaining scene shooter thing path distance (i::rest) lower upper log =
      remaining scene shooter thing path distance rest lower upper log := by
  have differentBool : (hit.id==shooter)=false := by simp [different]
  have step : visit scene shooter thing path distance i (none,upper,lower,log) =
      .ok (.yield (none,upper,lower,log)) := by
    simp only [visit,selected,isThing,Bool.false_eq_true,↓reduceIte,differentBool,shootable,
      Bool.not_true,Bool.or_self]
    rw [topOk]
    simp only [bind,Except.bind,admitted,↓reduceIte]
    rw [bottomOk]
    simp only [bind,Except.bind,above,↓reduceIte]
    rfl
  unfold remaining
  rw [List.forIn_cons,step]
  rfl
end Doom.Proofs.E1M1AimActorBottomEntry
