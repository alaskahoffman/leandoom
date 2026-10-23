import Doom.Proofs.E1M1AimActorSkipJoin
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimActorSkipCycle
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1MinimumScan (address)
open E1M1InterceptMark (consume)
open E1M1AimActorSkip (program result returned)
open E1M1AimWall (Safe)
open E1M1AimHistoryCycle (Frame)
open E1M1AimCatalog (Portal)
open E1M1AimTraversalInvariant (Persistent)
open E1M1AimIteration
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- Recover the actual parent scan inputs from the actor return, including the
cursor reload before the selected fraction is marked. -/
theorem registers (s : X86Memory.State) (safe : Safe (s.regs 4) 0x2c028) :
    (result s).core.regs 1=load32 s.memory 0x2c028 ∧
    (result s).core.regs 4=s.regs 4+4 ∧
    (result s).core.regs 6=s.regs 6 ∧ (result s).core.regs 7=s.regs 7 ∧
    (result s).core.memory=store32 (OriginalAimGuard.saved s).memory (s.regs 3) 0x7fffffff ∧
    (result s).pc=0x2c83a := by
  have fields := E1M1AimActorSkip.returned_fields s
  have cursor := E1M1AimWall.saved_frame s 0x2c028 safe
  simp [result,OriginalInterceptGate.resumed,OriginalInterceptGate.marked,OriginalInterceptGate.restored,
    fields.1,fields.2.1,fields.2.2.1,fields.2.2.2.2.1,fields.2.2.2.2.2.1,fields.2.2.2.2.2.2,
    put,X86.write]
  exact cursor

/-- Actor skips only write the saved registers and selected fraction. -/
theorem frame (s : X86Memory.State) (a : Word)
    (safe : Safe (s.regs 4) a) (mark : Apart a (s.regs 3)) :
    load32 (result s).core.memory a=load32 s.memory a := by
  have fields := E1M1AimActorSkip.returned_fields s
  unfold result OriginalInterceptGate.resumed
  simp only [fields.1]
  change load32 (store32 (returned s).core.memory ((returned s).core.regs 3) 0x7fffffff) a=_
  rw [fields.2.2.1,fields.2.2.2.2.1,load_store_apart _ _ _ _ mark]
  exact E1M1AimWall.saved_frame s a safe

/-- Run the existing minimum scan from the reached actor-skip state. The cursor,
remaining budget, maximum and stack are derived from the original selection. -/
theorem scan (s : X86Memory.State) (f : Option Flags)
    (initial work : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (target sp : Word) (fraction : Int32) (j : Nat)
    (selection : Selection initial work seen resolve target sp ⟨s,f,0x2b760⟩ fraction j)
    (layout : E1M1AimCycleInvariant.Layout s work) (bounded : initial.size≤128)
    (history : History initial (consume work j) (j::seen) (visits.push work[j]!))
    (encoded : OriginalLineFinish.Encodes (result s).core.memory 0x2ba20 resolve (consume work j)) :
    ∃ n≤13+7*work.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n (result s) out ∧
      E1M1AimRepeatProgram.ReadFrame (result s).core out ∧
      E1M1HistoryDispatch.Outcome (result s).core initial (consume work j) (j::seen) resolve out := by
  have r := registers s layout.cursorSafe.1
  obtain ⟨n,hn,out,run,keep,done⟩ := E1M1HistoryDispatch.execution
    (result s).core (result s).flags initial (consume work j) (j::seen) (visits.push work[j]!) resolve
    history bounded (r.2.2.1.trans selection.counter)
    (by rw [E1M1InterceptMark.size]; exact r.1.trans selection.ready.cursor) encoded
    (r.2.2.2.1.trans selection.maximum) (by rw [r.2.1]; exact layout.targetSafe)
    (by rw [r.2.1]; simpa [BitVec.add_sub_cancel] using layout.cursorStore)
    (by rw [r.2.1]; simpa [E1M1InterceptMark.size,BitVec.add_sub_cancel] using layout.recordStore)
  have run := run.transfer program [] E1M1AimActorSkip.contains_repeat (by simp)
  rw [OriginalPathXStep.at_pc _ _ r.2.2.2.2.2] at run
  exact ⟨n,by simpa only [E1M1InterceptMark.size] using hn,out,run,keep,done⟩

/-- The exhaustion state is the actor skip's actual state; admitted callbacks
carry the same reusable portal invariant as after line callbacks. -/
def Next (s : X86Memory.State) (initial work : Array Intercept) (seen : List Nat)
    (resolve : Intercept → Word) (portals : Nat → Option Portal) (distance z : Fixed)
    (out : X86Control.State) : Prop :=
  (seen.length=initial.size ∧ out=E1M1AimNextSelection.head (result s).core ∧ out.core.regs 6=0xffffffff) ∨
  (∃ best, E1M1InterceptMinimum.minimum work=.ok best ∧ best.1>65536 ∧ out.pc=0x2c887 ∧
    out.core.regs 6=BitVec.ofNat 32 (initial.size-seen.length-1)) ∨
  (∃ fraction j, Selection initial work seen resolve 0x2b760 (s.regs 4+4) out fraction j ∧
    Persistent out.core initial work resolve portals distance z)

/-- Carry the indirect callback slot and reusable invariant through actor skip,
mark, scan and CALL; no post-scan callback facts are assumed. -/
theorem carried (s : X86Memory.State) (initial work : Array Intercept) (marked : Nat)
    (seen : List Nat) (visits : Array Intercept) (resolve : Intercept → Word)
    (portals : Nat → Option Portal) (distance z : Fixed) (out : X86Control.State)
    (history : History initial (consume work marked) seen visits)
    (before : Persistent s initial work resolve portals distance z)
    (keep : Frame s out) (pointer : s.regs 3=address marked) (inside : marked<initial.size)
    (done : E1M1HistoryDispatch.Outcome (result s).core initial (consume work marked) seen resolve out) :
    Next s initial (consume work marked) seen resolve portals distance z out := by
  have r := registers s before.layout.cursorSafe.1
  have slot := frame s (s.regs 4+4) before.layout.slotSafe.1
    (by rw [pointer]; exact before.slotMarks marked inside)
  unfold E1M1HistoryDispatch.Outcome at done
  rw [r.2.1,slot,before.callback] at done
  rcases done with exhausted|far|⟨fraction,j,selected⟩
  · exact Or.inl exhausted
  · exact Or.inr (Or.inl far)
  · exact Or.inr (Or.inr ⟨fraction,j,selected,
      E1M1AimTraversalInvariant.preserved s initial work marked seen visits resolve portals distance z
        0x2b760 out fraction j history selected before keep pointer inside⟩)

/-- Execute a rejected actor and the complete following scan, retaining unchanged
bounds and source suffix, exact terminal outcomes, and the next callback invariant. -/
theorem execution (s : X86Memory.State) (f : Option Flags)
    (scene : Scene) (shooter : Nat) (thing : SolidThing) (path original : PathResult)
    (distance lower upper : Fixed) (log : Array AutoAim.Portal)
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
    (ignored : (work[j]!).id=shooter ∨ scene.things[work[j]!.id]!.shootable=false) :
    ∃ n≤41+7*work.size, ∃ out,
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ out ∧
      History original.collected (consume work j) (j::seen) (visits.push work[j]!) ∧
      Next s original.collected (consume work j) (j::seen) resolve portals distance thing.shootHeight out ∧
      load32 out.core.memory (0x2c1e4#32)=lower.raw.toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=upper.raw.toBitVec ∧ Frame s out ∧
      remaining scene shooter thing path distance
        (List.range' seen.length (path.visited.size-seen.length)) lower upper log =
      remaining scene shooter thing path distance
        (List.range' (seen.length+1) (path.visited.size-(seen.length+1))) lower upper log := by
  have stable : resolve {work[j]! with frac:=⟨2147483647⟩}=resolve work[j]! := by
    rw [selection.original]; exact before.resolver j selection.inside
  obtain ⟨⟨n,hn,first⟩,pc,encoded,historyNext,low,high,source⟩ := E1M1AimActorSkipJoin.execution
    s f scene shooter thing path original distance lower upper log work seen visits resolve target sp who fraction j
    history selection before.layout before.bounded empty query bottom top isThing shooterSafe flagsSafe shooterWord identity flags ignored stable
  obtain ⟨k,hk,out,tail,reads,done⟩ := scan s f original.collected work seen visits resolve target sp fraction j
    selection before.layout before.bounded historyNext encoded
  have r := registers s before.layout.cursorSafe.1
  have keep : Frame s out := by
    intro a safe mark cursor stack
    exact (reads a cursor (by rw [r.2.1]; simpa [BitVec.add_sub_cancel] using stack)).trans
      (frame s a safe.1 mark)
  refine ⟨n+k,by omega,out,E1M1PspriteStep.prefix_trans first tail,historyNext,
    carried s original.collected work j (j::seen) (visits.push work[j]!) resolve portals distance thing.shootHeight
      out historyNext before keep (selection.ready.pointer.trans selection.argument) selection.inside done,?_,?_,keep,source⟩
  · exact (reads (0x2c1e4#32) (by unfold Apart; decide)
      (by rw [r.2.1]; simpa [BitVec.add_sub_cancel] using before.layout.boundsStore.1)).trans low
  · exact (reads (0x2c1e8#32) (by unfold Apart; decide)
      (by rw [r.2.1]; simpa [BitVec.add_sub_cancel] using before.layout.boundsStore.2)).trans high

end Doom.Proofs.E1M1AimActorSkipCycle
