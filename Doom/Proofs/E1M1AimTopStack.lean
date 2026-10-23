import Doom.Proofs.E1M1AimStackShape
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimTopStack
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1MinimumScan (address)
open E1M1InterceptMark (consume)
open E1M1AimActorReject (program top result)
open E1M1AimHistoryCycle (Frame)
open E1M1AimCatalog (Portal)
open E1M1AimTraversalInvariant (Persistent)
open E1M1AimWall (Safe)
open E1M1AimIteration
attribute [local irreducible] load32 store32 SolidThing.shootHeight

open E1M1AimActorRejectCycle (Next carried)
open E1M1AimStackShape (Shape)
theorem execution (s : X86Memory.State) (f : Option Flags)
    (scene : Scene) (shooter : Nat) (thing : SolidThing) (path original : PathResult)
    (distance lower upper slope : Fixed) (log : Array AutoAim.Portal)
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
    (safe : E1M1AimActorTopEntry.ReadSafe s (resolve original.collected[j]!))
    (z0 : load32 s.memory (resolve original.collected[j]!+20)=scene.things[work[j]!.id]!.z.raw.toBitVec)
    (ht : load32 s.memory (resolve original.collected[j]!+68)=scene.things[work[j]!.id]!.height.raw.toBitVec)
    (ok : checkedPathDiv (scene.things[work[j]!.id]!.z+scene.things[work[j]!.id]!.height-thing.shootHeight)
      (distance*(work[j]!).frac)=.ok slope) (below : slope.raw<lower.raw) :
    ∃ n≤82+7*work.size, ∃ out,
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
  obtain ⟨⟨n,hn,first⟩,_,_,source⟩ := E1M1AimActorReject.execution
    s f scene shooter thing path distance lower upper slope log seen.length
    (List.range' (seen.length+1) (path.visited.size-(seen.length+1))) work[j]!
    (resolve original.collected[j]!) who (by simpa only [selection.original] using record)
    aligned.2.1 isThing tagSafe ptrSafe shooterSafe flagsSafe shooterWord identity flags different shootable
    safe before.range z0 ht before.eye bottom ok below selection.ready.returnWord
  have stable : resolve {work[j]! with frac:=⟨2147483647⟩}=resolve work[j]! := by
    rw [selection.original]; exact before.resolver j selection.inside
  obtain ⟨k,hk,out,tail,advanced,reads,keep,done,stack⟩ := E1M1AimActorScanStack.top_rejected s f original.collected work seen visits resolve target sp fraction j
    history selection before.layout before.bounded stable
  have shape := E1M1AimStackShape.scan _ out (E1M1AimActorScanStack.top_rejected_position
    s original.collected work resolve portals distance thing.shootHeight out j before pointer selection.inside stack)
  have r := E1M1AimActorReject.registers s
  have bounds := E1M1AimTraversalInvariant.bounds_mark j bound
  have low : load32 (result s).core.memory (0x2c1e4#32)=lower.raw.toBitVec := by
    apply Eq.trans (E1M1AimActorReject.frame s _ ?_ ?_) bottom
    · intro off h
      apply before.layout.floorReads (0x2c1e4#32) (by simp) (s.regs 4-off)
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [E1M1AimOpeningFrame.writes,E1M1AimOpeningFrame.pushes]
    · rw [pointer]; exact bounds.1
  have high : load32 (result s).core.memory (0x2c1e8#32)=upper.raw.toBitVec := by
    apply Eq.trans (E1M1AimActorReject.frame s _ ?_ ?_) top
    · intro off h
      apply before.layout.ceilingReads (0x2c1e8#32) (by simp) (s.regs 4-off)
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [E1M1AimOpeningFrame.writes,E1M1AimOpeningFrame.pushes]
    · rw [pointer]; exact bounds.2
  refine ⟨n+k,by omega,out,shape,E1M1PspriteStep.prefix_trans first tail,advanced,
    carried s original.collected work j (j::seen) (visits.push work[j]!) resolve portals distance thing.shootHeight
      out advanced before keep pointer selection.inside done,?_,?_,keep,?_⟩
  · exact (reads (0x2c1e4#32) (by unfold Apart; decide)
      (by rw [r.2.1]; simpa [BitVec.add_sub_cancel] using before.layout.boundsStore.1)).trans low
  · exact (reads (0x2c1e8#32) (by unfold Apart; decide)
      (by rw [r.2.1]; simpa [BitVec.add_sub_cancel] using before.layout.boundsStore.2)).trans high
  · rw [E1M1AimSynchronizedCycle.indices seen.length path.visited.size aligned.1]
    exact source
end Doom.Proofs.E1M1AimTopStack
