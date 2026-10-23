import Doom.Proofs.E1M1AimActorBottomReject
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimActorBottomCycle
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1MinimumScan (address)
open E1M1InterceptMark (consume)
open E1M1AimActorBottom (program)
open E1M1AimActorBottomReject (bottom result)
open E1M1AimHistoryCycle (Frame)
open E1M1AimCatalog (Portal)
open E1M1AimTraversalInvariant (Persistent)
open E1M1AimWall (Safe)
open E1M1AimIteration
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- The existing traversal layout already protects all actor-division writes. -/
theorem read_safe (s : X86Memory.State) (a : Word) (safe : E1M1AimRecordFrame.ReadSafe s a) :
    E1M1AimActorBottomReject.ReadSafe s a := by
  intro off member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact safe.1 _ (by simp)
  · exact safe.1 _ (by simp)
  · exact safe.1 _ (by simp)
  · exact safe.1 _ (by simp)
  · exact safe.1 _ (by simp)
  · exact safe.1 _ (by simp)
  · exact safe.2 _ (by simp [E1M1AimReturnFrame.writes])
  · exact safe.2 _ (by simp [E1M1AimReturnFrame.writes])
  · exact safe.2 _ (by simp [E1M1AimReturnFrame.writes])
  · exact safe.2 _ (by simp [E1M1AimReturnFrame.writes])

theorem records (s : X86Memory.State) (work : Array Intercept) (resolve : Intercept → Word)
    (image : OriginalLineFinish.Encodes s.memory 0x2ba20 resolve work)
    (safe : E1M1AimRecordFrame.RecordsSafe s work) :
    OriginalLineFinish.Encodes (bottom s).core.memory 0x2ba20 resolve work := by
  intro i hi
  have addr : (0x2ba20 : Word)+BitVec.ofNat 32 (12*i)=address i := by simp [E1M1MinimumScan.address,BitVec.ofNat_add]
  have keep (off : Word) (member : off∈[(0#32),4,8]) := E1M1AimActorBottomReject.read_frame s _ (read_safe s _ (safe i hi off member))
  have old := image i hi
  simp only [OriginalLineFinish.RecordAt,addr] at old ⊢
  rw [show load32 (bottom s).core.memory (address i)=load32 s.memory (address i) by
      simpa using keep (0#32) (by simp),keep (4#32) (by simp),keep (8#32) (by simp)]
  exact old

/-- Mark the selected record and execute the complete next scan. All scan inputs
and its encoded buffer are derived from the incoming selection and actual return. -/
theorem scan (s : X86Memory.State) (f : Option Flags)
    (initial work : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (target sp : Word) (fraction : Int32) (j : Nat)
    (history : History initial work seen visits)
    (selection : Selection initial work seen resolve target sp ⟨s,f,0x2b760⟩ fraction j)
    (layout : E1M1AimCycleInvariant.Layout s work) (bounded : initial.size≤128)
    (stable : resolve {work[j]! with frac:=⟨2147483647⟩}=resolve work[j]!) :
    ∃ n≤13+7*work.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n (result s) out ∧
      History initial (consume work j) (j::seen) (visits.push work[j]!) ∧
      E1M1AimRepeatProgram.ReadFrame (result s).core out ∧ Frame s out ∧
      E1M1HistoryDispatch.Outcome (result s).core initial (consume work j) (j::seen) resolve out := by
  have r := E1M1AimActorBottomReject.registers s
  have size := (E1M1SelectionHistory.image history).size
  have inside : j<work.size := by have := selection.inside; omega
  have ptr : s.regs 3=address j := selection.ready.pointer.trans selection.argument
  have encoded : OriginalLineFinish.Encodes (result s).core.memory 0x2ba20 resolve (consume work j) := by
    rw [r.2.2.2.2.2.2,ptr]
    exact E1M1InterceptMark.encoded _ work resolve j inside (by omega)
      (records s work resolve selection.ready.records layout.recordsSafe) stable
  have cursor := E1M1AimActorBottomReject.read_frame s 0x2c028 (read_safe s _ layout.cursorSafe)
  have advanced := History.push history fraction j selection.chosen selection.within
  obtain ⟨n,hn,out,run,keep,done⟩ := E1M1HistoryDispatch.execution
    (result s).core (result s).flags initial (consume work j) (j::seen) (visits.push work[j]!) resolve
    advanced bounded (r.2.2.2.1.trans selection.counter)
    (by rw [E1M1InterceptMark.size]; exact r.2.2.2.2.2.1.trans (cursor.trans selection.ready.cursor)) encoded
    (r.2.2.2.2.1.trans selection.maximum) (by rw [r.2.1]; exact layout.targetSafe)
    (by rw [r.2.1]; simpa [BitVec.add_sub_cancel] using layout.cursorStore)
    (by rw [r.2.1]; simpa [E1M1InterceptMark.size,BitVec.add_sub_cancel] using layout.recordStore)
  have run := run.transfer program [] E1M1AimActorBottomReject.contains_repeat (by simp)
  rw [OriginalPathXStep.at_pc _ _ r.1] at run
  refine ⟨n,by simpa only [E1M1InterceptMark.size] using hn,out,run,advanced,keep,?_,done⟩
  intro a safe mark cursor stack
  exact (keep a cursor (by rw [r.2.1]; simpa [BitVec.add_sub_cancel] using stack)).trans
    (E1M1AimActorBottomReject.frame s a (read_safe s a safe) mark)

/-- Exact exits or another selected callback, with the reusable traversal invariant. -/
def Next (s : X86Memory.State) (initial work : Array Intercept) (seen : List Nat)
    (resolve : Intercept → Word) (portals : Nat → Option Portal) (distance z : Fixed)
    (out : X86Control.State) : Prop :=
  (seen.length=initial.size ∧ out=E1M1AimNextSelection.head (result s).core ∧ out.core.regs 6=0xffffffff) ∨
  (∃ best, E1M1InterceptMinimum.minimum work=.ok best ∧ best.1>65536 ∧ out.pc=0x2c887 ∧
    out.core.regs 6=BitVec.ofNat 32 (initial.size-seen.length-1)) ∨
  (∃ fraction j, Selection initial work seen resolve 0x2b760 (s.regs 4+4) out fraction j ∧
    Persistent out.core initial work resolve portals distance z)

theorem carried (s : X86Memory.State) (initial work : Array Intercept) (marked : Nat)
    (seen : List Nat) (visits : Array Intercept) (resolve : Intercept → Word)
    (portals : Nat → Option Portal) (distance z : Fixed) (out : X86Control.State)
    (history : History initial (consume work marked) seen visits)
    (before : Persistent s initial work resolve portals distance z)
    (keep : Frame s out) (pointer : s.regs 3=address marked) (inside : marked<initial.size)
    (done : E1M1HistoryDispatch.Outcome (result s).core initial (consume work marked) seen resolve out) :
    Next s initial (consume work marked) seen resolve portals distance z out := by
  have r := E1M1AimActorBottomReject.registers s
  have slot := E1M1AimActorBottomReject.frame s (s.regs 4+4) (read_safe s _ before.layout.slotSafe)
    (by rw [pointer]; exact before.slotMarks marked inside)
  unfold E1M1HistoryDispatch.Outcome at done
  rw [r.2.1,slot,before.callback] at done
  rcases done with exhausted|far|⟨fraction,j,selected⟩
  · exact Or.inl exhausted
  · exact Or.inr (Or.inl far)
  · exact Or.inr (Or.inr ⟨fraction,j,selected,
      E1M1AimTraversalInvariant.preserved s initial work marked seen visits resolve portals distance z
        0x2b760 out fraction j history selected before keep pointer inside⟩)
/-- Continuous callback entry, strict bottom rejection, true return, mark and next scan;
source progress and the next callback invariant are derived together. -/
theorem execution (s : X86Memory.State) (f : Option Flags)
    (scene : Scene) (shooter : Nat) (thing : SolidThing) (path original : PathResult)
    (distance lower upper topSlope bottomSlope : Fixed) (log : Array AutoAim.Portal)
    (work : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (target sp who : Word) (fraction : Int32) (j : Nat)
    (history : History original.collected work seen visits)
    (selection : Selection original.collected work seen resolve target sp ⟨s,f,0x2b760⟩ fraction j)
    (portals : Nat → Option Portal)
    (before : Persistent s original.collected work resolve portals distance thing.shootHeight)
    (empty : original.visited=#[])
    (query : E1M1QuerySource.visitHits original (fun _ _ => true)=.ok path)
    (bottom : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec)
    (top : load32 s.memory (0x2c1e8#32)=upper.raw.toBitVec)
    (isThing : (work[j]!).isLine=false)
    (shooterSafe : Safe (s.regs 4) 0x2b9ac)
    (flagsSafe : Safe (s.regs 4) (resolve original.collected[j]!+104))
    (shooterWord : load32 s.memory 0x2b9ac=who)
    (identity : resolve original.collected[j]! = who ↔ (work[j]!).id=shooter)
    (flags : (s.memory (resolve original.collected[j]!+104) &&& (4#8) != 0)=scene.things[work[j]!.id]!.shootable)
    (different : (work[j]!).id≠shooter) (shootable : scene.things[work[j]!.id]!.shootable=true)
    (topSafe : E1M1AimActorTopEntry.ReadSafe s (resolve original.collected[j]!))
    (safe : E1M1AimActorBottomEntry.ReadSafe s (resolve original.collected[j]!))
    (z0 : load32 s.memory (resolve original.collected[j]!+20)=scene.things[work[j]!.id]!.z.raw.toBitVec)
    (ht : load32 s.memory (resolve original.collected[j]!+68)=scene.things[work[j]!.id]!.height.raw.toBitVec)
    (topOk : checkedPathDiv (scene.things[work[j]!.id]!.z+scene.things[work[j]!.id]!.height-thing.shootHeight)
      (distance*(work[j]!).frac)=.ok topSlope) (admitted : ¬topSlope.raw<lower.raw)
    (bottomOk : checkedPathDiv (scene.things[work[j]!.id]!.z-thing.shootHeight)
      (distance*(work[j]!).frac)=.ok bottomSlope) (above : upper.raw<bottomSlope.raw) :
    ∃ n≤115+7*work.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ out ∧
      History original.collected (consume work j) (j::seen) (visits.push work[j]!) ∧
      Next s original.collected (consume work j) (j::seen) resolve portals distance thing.shootHeight out ∧
      load32 out.core.memory (0x2c1e4#32)=lower.raw.toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=upper.raw.toBitVec ∧ Frame s out ∧
      remaining scene shooter thing path distance
        (List.range' seen.length (path.visited.size-seen.length)) lower upper log =
      remaining scene shooter thing path distance
        (List.range' (seen.length+1) (path.visited.size-(seen.length+1))) lower upper log := by
  have size := (E1M1SelectionHistory.image history).size
  have inside : j<work.size := by have := selection.inside; omega
  have bound : j<128 := by have := selection.inside; have := before.bounded; omega
  have pointer : s.regs 3=address j := selection.ready.pointer.trans selection.argument
  have record := E1M1AimCycleInvariant.record original.collected work seen visits resolve target sp
    ⟨s,f,0x2b760⟩ fraction j history selection
  have tagSafe : Safe (s.regs 4) (s.regs 0+4) := by
    rw [selection.argument]; exact (before.layout.recordsSafe j inside 4 (by simp)).1
  have ptrSafe : Safe (s.regs 4) (s.regs 0+8) := by
    rw [selection.argument]; exact (before.layout.recordsSafe j inside 8 (by simp)).1
  have aligned := E1M1AimPathBridge.selected original path work seen visits resolve target sp
    ⟨s,f,0x2b760⟩ fraction j history selection empty query
  obtain ⟨⟨n,hn,first⟩,_,_,_,_,source⟩ := E1M1AimActorBottomReject.execution
    s f scene shooter thing path distance lower upper topSlope bottomSlope log seen.length
    (List.range' (seen.length+1) (path.visited.size-(seen.length+1))) work[j]!
    (resolve original.collected[j]!) who (by simpa only [selection.original] using record)
    aligned.2.1 isThing tagSafe ptrSafe shooterSafe flagsSafe shooterWord identity flags different shootable
    topSafe safe before.range z0 ht before.eye bottom top topOk admitted bottomOk above selection.ready.returnWord
  have stable : resolve {work[j]! with frac:=⟨2147483647⟩}=resolve work[j]! := by
    rw [selection.original]; exact before.resolver j selection.inside
  obtain ⟨k,hk,out,tail,advanced,reads,keep,done⟩ := scan s f original.collected work seen visits resolve target sp fraction j
    history selection before.layout before.bounded stable
  have r := E1M1AimActorBottomReject.registers s
  have bounds := E1M1AimTraversalInvariant.bounds_mark j bound
  have low : load32 (result s).core.memory (0x2c1e4#32)=lower.raw.toBitVec := by
    apply Eq.trans (E1M1AimActorBottomReject.frame s _ ?_ ?_) bottom
    · intro off h
      apply before.layout.floorReads (0x2c1e4#32) (by simp) (s.regs 4-off)
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [E1M1AimOpeningFrame.writes,E1M1AimOpeningFrame.pushes]
    · rw [pointer]; exact bounds.1
  have high : load32 (result s).core.memory (0x2c1e8#32)=upper.raw.toBitVec := by
    apply Eq.trans (E1M1AimActorBottomReject.frame s _ ?_ ?_) top
    · intro off h
      apply before.layout.ceilingReads (0x2c1e8#32) (by simp) (s.regs 4-off)
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [E1M1AimOpeningFrame.writes,E1M1AimOpeningFrame.pushes]
    · rw [pointer]; exact bounds.2
  refine ⟨n+k,by omega,out,E1M1PspriteStep.prefix_trans first tail,advanced,
    carried s original.collected work j (j::seen) (visits.push work[j]!) resolve portals distance thing.shootHeight
      out advanced before keep pointer selection.inside done,?_,?_,keep,?_⟩
  · exact (reads (0x2c1e4#32) (by unfold Apart; decide)
      (by rw [r.2.1]; simpa [BitVec.add_sub_cancel] using before.layout.boundsStore.1)).trans low
  · exact (reads (0x2c1e8#32) (by unfold Apart; decide)
      (by rw [r.2.1]; simpa [BitVec.add_sub_cancel] using before.layout.boundsStore.2)).trans high
  · rw [E1M1AimSynchronizedCycle.indices seen.length path.visited.size aligned.1]
    exact source
end Doom.Proofs.E1M1AimActorBottomCycle
