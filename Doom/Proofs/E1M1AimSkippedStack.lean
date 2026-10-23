import Doom.Proofs.E1M1AimStackShape
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimSkippedStack
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

open E1M1AimActorSkipCycle (Next carried)
open E1M1AimStackShape (Shape)
open E1M1AimActorSkipCycle (registers frame)
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
      Shape (s.regs 4+4) out ∧
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
  obtain ⟨k,hk,out,tail,reads,done,stack⟩ := E1M1AimActorScanStack.skipped s f original.collected work seen visits resolve target sp fraction j
    selection before.layout before.bounded historyNext encoded
  have shape := E1M1AimStackShape.scan _ out (E1M1AimActorScanStack.skipped_position
    s original.collected work resolve portals distance thing.shootHeight out j before
    (selection.ready.pointer.trans selection.argument) selection.inside stack)
  have r := registers s before.layout.cursorSafe.1
  have keep : Frame s out := by
    intro a safe mark cursor stack
    exact (reads a cursor (by rw [r.2.1]; simpa [BitVec.add_sub_cancel] using stack)).trans
      (frame s a safe.1 mark)
  refine ⟨n+k,by omega,out,shape,E1M1PspriteStep.prefix_trans first tail,historyNext,
    carried s original.collected work j (j::seen) (visits.push work[j]!) resolve portals distance thing.shootHeight
      out historyNext before keep (selection.ready.pointer.trans selection.argument) selection.inside done,?_,?_,keep,source⟩
  · exact (reads (0x2c1e4#32) (by unfold Apart; decide)
      (by rw [r.2.1]; simpa [BitVec.add_sub_cancel] using before.layout.boundsStore.1)).trans low
  · exact (reads (0x2c1e8#32) (by unfold Apart; decide)
      (by rw [r.2.1]; simpa [BitVec.add_sub_cancel] using before.layout.boundsStore.2)).trans high

end Doom.Proofs.E1M1AimSkippedStack
