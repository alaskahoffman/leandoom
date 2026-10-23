import Doom.Proofs.E1M1AimResume
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimLineJoin
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1AimIteration
attribute [local irreducible] load32 store32

theorem bits_eq (a b : Fixed) : a.raw.toBitVec=b.raw.toBitVec ↔ a=b := by
  cases a; cases b
  simp [Int32.toBitVec_inj]

theorem floor_word (a b : Fixed) :
    Int32.ofBitVec (if a.raw.toBitVec.toInt≤b.raw.toBitVec.toInt then b.raw.toBitVec else a.raw.toBitVec)=max a.raw b.raw := by
  by_cases h : a.raw≤b.raw
  all_goals simp only [Int32.le_iff_toInt_le] at h
  all_goals simp [Int32.toInt_toBitVec,max,Int32.le_iff_toInt_le,h]

theorem ceiling_word (a b : Fixed) :
    Int32.ofBitVec (if b.raw.toBitVec.toInt≤a.raw.toBitVec.toInt then b.raw.toBitVec else a.raw.toBitVec)=min a.raw b.raw := by
  apply Int32.toInt_inj.mp
  by_cases h : b.raw≤a.raw <;> by_cases k : a.raw≤b.raw
  all_goals simp only [Int32.le_iff_toInt_le] at h k
  all_goals simp [Int32.toInt_toBitVec,min,Int32.le_iff_toInt_le,h,k] <;> omega

theorem bottom_word (front back : Heights) (lower slope : Fixed) :
    (if back.floor.raw.toBitVec=front.floor.raw.toBitVec then lower.raw else max lower.raw slope.raw)=
      (bottomAfter front back lower slope).raw := by
  simp only [bits_eq,eq_comm (a:=back.floor),bottomAfter]
  split <;> rfl

theorem top_word (front back : Heights) (upper slope : Fixed) :
    (if front.ceiling.raw.toBitVec=back.ceiling.raw.toBitVec then upper.raw else min upper.raw slope.raw)=
      (topAfter front back upper slope).raw := by
  simp only [bits_eq,topAfter]
  split <;> rfl

/-- An arbitrary open line hit in the live source loop and the original machine
agree on the carried window and the enclosing traversal's stop/continue choice.
No equality of callback outputs is assumed. Entry representations, path selection,
static memory separation and successful height-dependent divisions remain inputs. -/
theorem correspondence (s : X86Memory.State) (f : Option Flags)
    (scene : Scene) (shooter : Nat) (thing : SolidThing) (path : PathResult)
    (distance : Fixed) (i : Nat) (rest : List Nat)
    (lower upper floorSlope ceilingSlope : Fixed) (history : Array AutoAim.Portal)
    (hit : Intercept) (back : Heights) (line frontPtr backPtr : Word)
    (h : E1M1AimMapped.Inputs s hit line frontPtr backPtr
      scene.lines[hit.id]!.front.floor.raw.toBitVec scene.lines[hit.id]!.front.ceiling.raw.toBitVec
      back.floor.raw.toBitVec back.ceiling.raw.toBitVec)
    (distanceReads : E1M1AimDistance.ReadSafe s) (floorReads : E1M1AimFloorEntry.ReadSafe s)
    (reads : E1M1AimCeilingEntry.ReadSafe s) (clip : E1M1AimCeilingEntry.ClipSafe s line frontPtr backPtr)
    (range : load32 s.memory (0x2b9b8#32)=distance.raw.toBitVec)
    (eye : load32 s.memory (0x2b9a8#32)=thing.shootHeight.raw.toBitVec)
    (bottom : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec)
    (top : load32 s.memory (0x2c1e8#32)=upper.raw.toBitVec)
    (selectedPointer : s.regs 3=s.regs 0)
    (selected : path.visited[i]! = hit)
    (two : scene.lines[hit.id]!.twoSided=true) (backSector : scene.lines[hit.id]!.back=some back)
    (pass : max scene.lines[hit.id]!.front.floor.raw back.floor.raw <
      min scene.lines[hit.id]!.front.ceiling.raw back.ceiling.raw)
    (floorOk : scene.lines[hit.id]!.front.floor≠back.floor →
      checkedPathDiv (⟨max scene.lines[hit.id]!.front.floor.raw back.floor.raw⟩-thing.shootHeight)
        (distance*hit.frac)=.ok floorSlope)
    (ceilingOk : scene.lines[hit.id]!.front.ceiling≠back.ceiling →
      checkedPathDiv (⟨min scene.lines[hit.id]!.front.ceiling.raw back.ceiling.raw⟩-thing.shootHeight)
        (distance*hit.frac)=.ok ceilingSlope)
    (returnSafe : E1M1AimReturnFrame.Safe s)
    (returnWord : load32 s.memory (s.regs 4)=0x2c86d)
    (markSafe : Apart (0x2c1e4#32) (s.regs 3) ∧ Apart (0x2c1e8#32) (s.regs 3)) :
    (∃ n, n≤144 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1AimResume.program [] n
      ⟨s,f,0x2b760⟩ (E1M1AimResume.result s)) ∧
    (E1M1AimResume.result s).pc=(if (bottomAfter scene.lines[hit.id]!.front back lower floorSlope).raw <
      (topAfter scene.lines[hit.id]!.front back upper ceilingSlope).raw then 0x2c83a else 0x2c88c) ∧
    load32 (E1M1AimResume.result s).core.memory (0x2c1e4#32)=
      (bottomAfter scene.lines[hit.id]!.front back lower floorSlope).raw.toBitVec ∧
    load32 (E1M1AimResume.result s).core.memory (0x2c1e8#32)=
      (topAfter scene.lines[hit.id]!.front back upper ceilingSlope).raw.toBitVec ∧
    ((bottomAfter scene.lines[hit.id]!.front back lower floorSlope).raw <
      (topAfter scene.lines[hit.id]!.front back upper ceilingSlope).raw →
      load32 (E1M1AimResume.result s).core.memory (s.regs 0)=0x7fffffff) ∧
    remaining scene shooter thing path distance (i::rest) lower upper history =
      if (E1M1AimResume.result s).pc=0x2c83a then
        remaining scene shooter thing path distance rest
          (bottomAfter scene.lines[hit.id]!.front back lower floorSlope)
          (topAfter scene.lines[hit.id]!.front back upper ceilingSlope)
          (history.push (portal scene.lines[hit.id]!.front back distance hit))
      else .ok {path := E1M1AimSource.stopped path (i+1)} := by
  have passWord : (if scene.lines[hit.id]!.front.floor.raw.toBitVec.toInt≤back.floor.raw.toBitVec.toInt
      then back.floor.raw.toBitVec else scene.lines[hit.id]!.front.floor.raw.toBitVec).toInt <
    (if back.ceiling.raw.toBitVec.toInt≤scene.lines[hit.id]!.front.ceiling.raw.toBitVec.toInt
      then back.ceiling.raw.toBitVec else scene.lines[hit.id]!.front.ceiling.raw.toBitVec).toInt := by
    have bounds := E1M1AimPortalSource.signed_bounds scene.lines[hit.id]!.front.floor
      scene.lines[hit.id]!.front.ceiling back.floor back.ceiling
    simp only [Int32.lt_iff_toInt_lt,Int32.le_iff_toInt_le] at pass bounds
    omega
  have floorWord : back.floor.raw.toBitVec≠scene.lines[hit.id]!.front.floor.raw.toBitVec →
    checkedPathDiv (⟨Int32.ofBitVec (if scene.lines[hit.id]!.front.floor.raw.toBitVec.toInt≤back.floor.raw.toBitVec.toInt
      then back.floor.raw.toBitVec else scene.lines[hit.id]!.front.floor.raw.toBitVec)⟩-thing.shootHeight)
      (distance*hit.frac)=.ok floorSlope := by
    simpa only [floor_word,ne_eq,bits_eq,eq_comm (a:=back.floor)] using floorOk
  have ceilingWord : scene.lines[hit.id]!.front.ceiling.raw.toBitVec≠back.ceiling.raw.toBitVec →
    checkedPathDiv (⟨Int32.ofBitVec (if back.ceiling.raw.toBitVec.toInt≤scene.lines[hit.id]!.front.ceiling.raw.toBitVec.toInt
      then back.ceiling.raw.toBitVec else scene.lines[hit.id]!.front.ceiling.raw.toBitVec)⟩-thing.shootHeight)
      (distance*hit.frac)=.ok ceilingSlope := by
    simpa only [ceiling_word,ne_eq,bits_eq] using ceilingOk
  have run := E1M1AimResume.execution s f hit line frontPtr backPtr _ _ _ _
    distance thing.shootHeight lower upper floorSlope ceilingSlope h distanceReads floorReads reads clip
    range eye bottom top passWord floorWord ceilingWord returnSafe returnWord markSafe
  simp only [bottom_word,top_word,← Int32.lt_iff_toInt_lt] at run
  refine ⟨run.1,run.2.1,run.2.2.2.2.2.1,run.2.2.2.2.2.2,?_,?_⟩
  · simpa only [selectedPointer] using run.2.2.2.2.1
  · rw [next_line scene shooter thing path distance i rest lower upper floorSlope ceilingSlope history hit back
      selected h.isLine two backSector pass floorOk ceilingOk,run.2.1]
    split <;> simp
end Doom.Proofs.E1M1AimLineJoin
