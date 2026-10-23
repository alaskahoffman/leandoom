import Doom.Proofs.E1M1AimRepeat
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimRepeatSource
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1AimIteration
open E1M1MinimumScan (address)
open E1M1AimLineJoin (bits_eq floor_word ceiling_word bottom_word top_word)
open E1M1AimRepeatProgram (program)
attribute [local irreducible] load32 store32

/-- One continuing source line carries its window and portal history forward,
while the original binary consumes that buffer entry and reaches its next boundary.
This does not assume the precomputed source suffix is the entire remaining
selection sequence; that ordered-prefix invariant is still a separate obligation. -/
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
    (markSafe : Apart (0x2c1e4#32) (s.regs 3) ∧ Apart (0x2c1e8#32) (s.regs 3))
    (hits : Array Intercept) (resolve : Intercept → Word) (j : Nat)
    (inside : j<hits.size) (bounded : hits.size≤128)
    (image : OriginalLineFinish.Encodes s.memory 0x2ba20 resolve hits)
    (safe : E1M1AimRecordFrame.RecordsSafe s hits)
    (pointer : s.regs 0=address j)
    (listedHit : hits[j]! = hit)
    (stable : resolve {hits[j]! with frac := ⟨2147483647⟩}=resolve hits[j]!)
    (cursorSafe : E1M1AimRecordFrame.ReadSafe s 0x2c028)
    (cursor : load32 s.memory 0x2c028=address hits.size) (maximum : s.regs 7=65536)
    (targetSafe : Apart (s.regs 4+4) 0x2c028)
    (recordSafe : ∀ i<hits.size, ∀ off∈[(0#32),4,8],
      Apart (OriginalLineCollection.slot 0x2ba20 i off) (s.regs 4))
    (boundsSafe : Apart (0x2c1e4#32) (s.regs 4) ∧ Apart (0x2c1e8#32) (s.regs 4))
    (slotSafe : E1M1AimRecordFrame.ReadSafe s (s.regs 4+4))
    (slotMark : Apart (s.regs 4+4) (s.regs 3)) :
    ∃ n≤157+7*hits.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ out ∧
      (if (bottomAfter scene.lines[hit.id]!.front back lower floorSlope).raw <
          (topAfter scene.lines[hit.id]!.front back upper ceilingSlope).raw then
        (s.regs 6=0 ∧ out=E1M1AimNextSelection.head (E1M1AimResume.result s).core) ∨
        (s.regs 6≠0 ∧ E1M1CallbackEntry.Outcome (hits.set! j {hit with frac := ⟨2147483647⟩}) resolve
          (load32 s.memory (s.regs 4+4)) (s.regs 4+4) out)
       else out=E1M1AimResume.result s ∧ out.pc=0x2c88c) ∧
      load32 out.core.memory (0x2c1e4#32)=(bottomAfter scene.lines[hit.id]!.front back lower floorSlope).raw.toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=(topAfter scene.lines[hit.id]!.front back upper ceilingSlope).raw.toBitVec ∧
      remaining scene shooter thing path distance (i::rest) lower upper history =
        if (bottomAfter scene.lines[hit.id]!.front back lower floorSlope).raw < (topAfter scene.lines[hit.id]!.front back upper ceilingSlope).raw then
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
  obtain ⟨n,hn,out,run,done,bounds⟩ := E1M1AimRepeat.execution s f hit line frontPtr backPtr _ _ _ _
    distance thing.shootHeight lower upper floorSlope ceilingSlope h distanceReads floorReads reads clip
    range eye bottom top passWord floorWord ceilingWord returnSafe returnWord markSafe
    hits resolve j inside bounded image safe (selectedPointer.trans pointer) stable cursorSafe cursor maximum targetSafe recordSafe boundsSafe slotSafe slotMark
  simp only [bottom_word,top_word,← Int32.lt_iff_toInt_lt] at done bounds
  simp only [E1M1InterceptMark.consume,listedHit] at done
  exact ⟨n,hn,out,run,done,bounds.1,bounds.2,
    next_line scene shooter thing path distance i rest lower upper floorSlope ceilingSlope history hit back
      selected h.isLine two backSector pass floorOk ceilingOk⟩
end Doom.Proofs.E1M1AimRepeatSource
