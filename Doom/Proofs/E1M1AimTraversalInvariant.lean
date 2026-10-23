import Doom.Proofs.E1M1AimCatalog
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimTraversalInvariant
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

/-- Persistent state for the proved two-sided-line branch. Portal descriptors
refer to the immutable original collection; the marked work buffer varies. -/
structure Persistent (s : X86Memory.State) (initial work : Array Intercept)
    (resolve : Intercept → Word) (portals : Nat → Option Portal) (distance z : Fixed) : Prop where
  bounded : initial.size≤128
  layout : Layout s work
  query : QuerySafe s
  globals : ClipGlobalsSafe s
  catalog : Catalog s initial resolve portals
  range : load32 s.memory (0x2b9b8#32)=distance.raw.toBitVec
  eye : load32 s.memory (0x2b9a8#32)=z.raw.toBitVec
  callback : load32 s.memory (s.regs 4+4)=0x2b760
  slotMarks : ∀ i<initial.size, Apart (s.regs 4+4) (address i)
  resolver : ∀ i<initial.size,
    resolve {initial[i]! with frac := ⟨2147483647⟩}=resolve initial[i]!

/-- Every bounded intercept fraction is disjoint from both aim-window globals. -/
theorem bounds_mark (j : Nat) (inside : j<128) :
    Apart (0x2c1e4#32) (address j) ∧ Apart (0x2c1e8#32) (address j) := by
  have all : ∀ i : Fin 128,
      Apart (0x2c1e4#32) (address i.val) ∧ Apart (0x2c1e8#32) (address i.val) := by
    unfold Apart E1M1MinimumScan.address; decide
  exact all ⟨j,inside⟩

/-- Transport the whole invariant to the next callback, including all catalog
entries and the real indirect callback slot. No next-state invariant is assumed. -/
theorem preserved (s : X86Memory.State) (initial work : Array Intercept) (marked : Nat)
    (seen : List Nat) (visits : Array Intercept) (resolve : Intercept → Word)
    (portals : Nat → Option Portal) (distance z : Fixed)
    (target : Word) (out : X86Control.State) (fraction : Int32) (j : Nat)
    (history : History initial (consume work marked) seen visits)
    (selection : Selection initial (consume work marked) seen resolve target (s.regs 4+4) out fraction j)
    (before : Persistent s initial work resolve portals distance z)
    (frame : Frame s out) (pointer : s.regs 3=address marked) (inside : marked<initial.size) :
    Persistent out.core initial (consume work marked) resolve portals distance z := by
  obtain ⟨stack,layout,query,record,range,eye⟩ := E1M1AimCycleInvariant.entry s initial work marked seen visits
    resolve target out fraction j history selection before.bounded before.layout before.query frame
  have bound : marked<128 := by have := before.bounded; omega
  have adjacent : Apart (s.regs 4+4) (s.regs 4) := by
    have small : Apart (4#32) (0#32) := by unfold Apart; decide
    simpa using OriginalPathXStep.apart_translate (s.regs 4) (4#32) (0#32) small
  have slot := frame (s.regs 4+4) before.layout.slotSafe
    (by rw [pointer]; exact before.slotMarks marked inside) before.layout.targetSafe adjacent
  refine ⟨before.bounded,layout,query,E1M1AimNextLine.clip_globals s out.core stack before.globals,
    E1M1AimCatalog.preserved s out marked initial resolve portals frame stack pointer bound before.catalog,
    range.trans before.range,eye.trans before.eye,?_,?_,before.resolver⟩
  · rw [stack,slot]; exact before.callback
  · simpa only [stack] using before.slotMarks

/-- A reached callback is ready to reuse the same invariant. Exit cases remain
separate, including the original counter's wrap on exhaustion. -/
def Next (s : X86Memory.State) (initial work : Array Intercept) (seen : List Nat)
    (resolve : Intercept → Word) (portals : Nat → Option Portal) (distance z : Fixed)
    (out : X86Control.State) : Prop :=
  (seen.length=initial.size ∧ out=E1M1AimNextSelection.head (E1M1AimResume.result s).core ∧ out.core.regs 6=0xffffffff) ∨
  (∃ best, E1M1InterceptMinimum.minimum work=.ok best ∧ best.1>65536 ∧ out.pc=0x2c887 ∧
    out.core.regs 6=BitVec.ofNat 32 (initial.size-seen.length-1)) ∨
  (∃ fraction j, Selection initial work seen resolve 0x2b760 (s.regs 4+4) out fraction j ∧
    Persistent out.core initial work resolve portals distance z)

theorem carried (s : X86Memory.State) (initial work : Array Intercept) (marked : Nat)
    (seen : List Nat) (visits : Array Intercept) (resolve : Intercept → Word)
    (portals : Nat → Option Portal) (distance z : Fixed) (out : X86Control.State)
    (history : History initial (consume work marked) seen visits)
    (before : Persistent s initial work resolve portals distance z)
    (frame : Frame s out) (pointer : s.regs 3=address marked) (inside : marked<initial.size)
    (done : E1M1AimHistoryCycle.Next s initial (consume work marked) seen resolve out) :
    Next s initial (consume work marked) seen resolve portals distance z out := by
  rcases done with exhausted|far|⟨fraction,j,selected⟩
  · exact Or.inl exhausted
  · exact Or.inr (Or.inl far)
  · rw [before.callback] at selected
    exact Or.inr (Or.inr ⟨fraction,j,selected,preserved s initial work marked seen visits resolve portals
      distance z 0x2b760 out fraction j history selected before frame pointer inside⟩)

/-- Run one actual open-two-sided-line cycle using the persistent catalog and
selected history. All next callback representation/layout premises are rebuilt
in the result; openness and successful conditional divisions remain explicit. -/
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
  obtain ⟨n,hn,out,run,done,low,high,frame⟩ := E1M1AimHistoryCycle.execution s f initial work seen visits
    resolve target sp fraction j history selection (resolve initial[j]!) p.front p.back p.ff p.fc p.bf p.bc
    distance z lower upper floorSlope ceilingSlope h reads before.layout.floorReads before.layout.ceilingReads clip
    before.range before.eye bottom top pass floorOk ceilingOk before.layout.returnSafe
    (by rw [pointer]; exact mark) before.bounded before.layout.recordsSafe stable before.layout.cursorSafe
    before.layout.targetSafe before.layout.cursorStore before.layout.recordStore before.layout.boundsStore
    before.layout.slotSafe (by rw [pointer]; exact before.slotMarks j selection.inside)
  refine ⟨n,hn,out,run,?_,low,high,frame⟩
  by_cases openWindow : (if p.bf=p.ff then lower.raw else max lower.raw floorSlope.raw).toInt <
      (if p.fc=p.bc then upper.raw else min upper.raw ceilingSlope.raw).toInt
  · simp only [if_pos openWindow] at done ⊢
    exact ⟨done.1,carried s initial work j (j::seen) (visits.push work[j]!) resolve portals distance z out
      done.1 before frame pointer selection.inside done.2⟩
  · simpa only [if_neg openWindow] using done
end Doom.Proofs.E1M1AimTraversalInvariant
