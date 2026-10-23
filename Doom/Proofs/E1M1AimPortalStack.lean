import Doom.Proofs.E1M1AimOpenStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimPortalStack
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1MinimumScan (address)
open E1M1SelectionHistory (History)
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMark (consume)
open E1M1AimHistoryCycle (Frame)
open E1M1AimCycleInvariant (Layout QuerySafe)
open E1M1AimNextLine (ClipGlobalsSafe)
open E1M1AimCatalog (Portal Catalog)
open E1M1AimRepeatProgram (program)
attribute [local irreducible] load32 store32

open E1M1AimStackShape (Shape)
open E1M1AimTraversalInvariant (Persistent Next bounds_mark carried)
theorem execution (s : X86Memory.State) (f : Option Flags)
    (initial work : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (portals : Nat → Option Portal) (distance z : Fixed)
    (target sp : Word) (fraction : Int32) (j : Nat) (p : Portal)
    (history : History initial work seen visits)
    (selection : Selection initial work seen resolve target sp ⟨s,f,0x2b760⟩ fraction j)
    (before : Persistent s initial work resolve portals distance z) (listed : portals j=some p)
    (lower upper floorSlope ceilingSlope : Fixed)
    (bottom : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec)
    (top : load32 s.memory (0x2c1e8#32)=upper.raw.toBitVec)
    (pass : (if p.ff.toInt≤p.bf.toInt then p.bf else p.ff).toInt <
      (if p.bc.toInt≤p.fc.toInt then p.bc else p.fc).toInt)
    (floorOk : p.bf≠p.ff → checkedPathDiv (⟨Int32.ofBitVec (if p.ff.toInt≤p.bf.toInt then p.bf else p.ff)⟩-z)
      (distance*work[j]!.frac)=.ok floorSlope)
    (ceilingOk : p.fc≠p.bc → checkedPathDiv (⟨Int32.ofBitVec (if p.bc.toInt≤p.fc.toInt then p.bc else p.fc)⟩-z)
      (distance*work[j]!.frac)=.ok ceilingSlope) :
    ∃ n≤157+7*work.size, ∃ out,
      Shape (s.regs 4+4) out ∧
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ out ∧
      (if (if p.bf=p.ff then lower.raw else max lower.raw floorSlope.raw).toInt <
          (if p.fc=p.bc then upper.raw else min upper.raw ceilingSlope.raw).toInt then
        History initial (consume work j) (j::seen) (visits.push work[j]!) ∧
        Next s initial (consume work j) (j::seen) resolve portals distance z out
       else out=E1M1AimResume.result s ∧ out.pc=0x2c88c) ∧
      load32 out.core.memory (0x2c1e4#32)=(if p.bf=p.ff then lower.raw else max lower.raw floorSlope.raw).toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=(if p.fc=p.bc then upper.raw else min upper.raw ceilingSlope.raw).toBitVec ∧ Frame s out := by
  obtain ⟨h,reads,clip⟩ := E1M1AimCatalog.inputs ⟨s,f,0x2b760⟩ initial work seen visits resolve portals
    target sp fraction j p history selection before.catalog listed before.layout before.query before.globals
  have pointer : s.regs 3=address j := selection.ready.pointer.trans selection.argument
  have bound : j<128 := by have := selection.inside; have := before.bounded; omega
  have mark := bounds_mark j bound
  have stable : resolve {work[j]! with frac := ⟨2147483647⟩}=resolve work[j]! := by
    rw [selection.original]; exact before.resolver j selection.inside
  obtain ⟨n,hn,out,shape,run,done,low,high,frame⟩ := E1M1AimOpenStack.execution s f initial work seen visits
    resolve target sp fraction j history selection (resolve initial[j]!) p.front p.back p.ff p.fc p.bf p.bc
    distance z lower upper floorSlope ceilingSlope h reads before.layout.floorReads before.layout.ceilingReads clip
    before.range before.eye bottom top pass floorOk ceilingOk before.layout.returnSafe
    (by rw [pointer]; exact mark) before.bounded before.layout.recordsSafe stable before.layout.cursorSafe
    before.layout.targetSafe before.layout.cursorStore before.layout.recordStore before.layout.boundsStore
    before.layout.slotSafe (by rw [pointer]; exact before.slotMarks j selection.inside) before.callback
  refine ⟨n,hn,out,shape,run,?_,low,high,frame⟩
  by_cases openWindow : (if p.bf=p.ff then lower.raw else max lower.raw floorSlope.raw).toInt <
      (if p.fc=p.bc then upper.raw else min upper.raw ceilingSlope.raw).toInt
  · simp only [if_pos openWindow] at done ⊢
    exact ⟨done.1,carried s initial work j (j::seen) (visits.push work[j]!) resolve portals distance z out
      done.1 before frame pointer selection.inside done.2⟩
  · simpa only [if_neg openWindow] using done
end Doom.Proofs.E1M1AimPortalStack
