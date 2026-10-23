import Doom.Proofs.E1M1AimCompletedReturn
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimSavedWords
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1MinimumScan (address)
open E1M1AimCatalog (Portal)
open E1M1AimTraversalInvariant (Persistent)
open E1M1AimWall (Safe)
open E1M1AimIteration
open E1M1AimActorSelect (program)
open E1M1AimActorReturn (result)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- Protection covers continuing callback writes and the two additional stores
performed when an actor is selected. Addresses are fixed, not re-based at exit. -/
def Protect (s : X86Memory.State) (a : Word) : Prop :=
  E1M1AimMapFrame.StableWord s a ∧ Apart a 0x2b9f8 ∧ Apart a 0x2b9b4
def Preserved (s : X86Memory.State) (out : X86Control.State) : Prop :=
  ∀ a, Protect s a → load32 out.core.memory a=load32 s.memory a

theorem transport (s t : X86Memory.State) (a : Word)
    (stack : t.regs 4=s.regs 4) (safe : Protect s a) : Protect t a := by
  exact ⟨E1M1AimMapFrame.stable_word s t a stack safe.1,safe.2⟩

theorem from_cycle (s : X86Memory.State) (out : X86Control.State) (j : Nat)
    (frame : E1M1AimHistoryCycle.Frame s out) (pointer : s.regs 3=address j) (bounded : j<128) :
    Preserved s out := by
  intro a safe
  exact E1M1AimMapFrame.word s out j a frame pointer bounded safe.1

theorem selected_frame (s : X86Memory.State) (safe : E1M1AimActorReturn.Safe s) :
    Preserved s (result s) := by
  intro a protect
  exact E1M1AimActorReturn.frame s safe a
    (E1M1AimActorBottomCycle.read_safe s a protect.1.1) protect.2.1 protect.2.2

theorem selected (s : X86Memory.State) (f : Option Flags)
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
      (distance*(work[j]!).frac)=.ok bottomSlope) (bottomAdmitted : ¬upper.raw<bottomSlope.raw)
    (saveSafe : E1M1AimActorReturn.Safe s) :
    ∃ n≤115, ∃ out,
      Preserved s out ∧
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ out ∧
      out.pc=0x2c88c ∧ out.core.regs 0=0 ∧ out.core.regs 4=s.regs 4+4 ∧
      OriginalLineFinish.Encodes out.core.memory 0x2ba20 resolve work ∧
      load32 out.core.memory (0x2b9f8#32)=resolve original.collected[j]! ∧
      load32 out.core.memory (0x2b9b4#32)=
        (E1M1AimActorSelectEntry.answer scene thing path distance lower upper topSlope bottomSlope log seen.length work[j]!).slope.raw.toBitVec ∧
      load32 out.core.memory (0x2c1e4#32)=lower.raw.toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=upper.raw.toBitVec ∧
      remaining scene shooter thing path distance
        (List.range' seen.length (path.visited.size-seen.length)) lower upper log =
        .ok (E1M1AimActorSelectEntry.answer scene thing path distance lower upper topSlope bottomSlope log seen.length work[j]!) := by
  have size := (E1M1SelectionHistory.image history).size
  have inside : j<work.size := by have := selection.inside; omega
  have record := E1M1AimCycleInvariant.record original.collected work seen visits resolve target sp
    ⟨s,f,0x2b760⟩ fraction j history selection
  have tagSafe : Safe (s.regs 4) (s.regs 0+4) := by
    rw [selection.argument]; exact (before.layout.recordsSafe j inside 4 (by simp)).1
  have ptrSafe : Safe (s.regs 4) (s.regs 0+8) := by
    rw [selection.argument]; exact (before.layout.recordsSafe j inside 8 (by simp)).1
  have aligned := E1M1AimPathBridge.selected original path work seen visits resolve target sp
    ⟨s,f,0x2b760⟩ fraction j history selection empty query
  obtain ⟨⟨n,hn,run⟩,pc,zero,stack,_,targetOut,slopeOut,source⟩ := E1M1AimActorReturn.execution
    s f scene shooter thing path distance lower upper topSlope bottomSlope log seen.length
    (List.range' (seen.length+1) (path.visited.size-(seen.length+1))) work[j]!
    (resolve original.collected[j]!) who (by simpa only [selection.original] using record)
    aligned.2.1 isThing tagSafe ptrSafe shooterSafe flagsSafe shooterWord identity flags different shootable
    topSafe safe before.range z0 ht before.eye bottom top topOk admitted bottomOk bottomAdmitted saveSafe selection.ready.returnWord
  have bounds := E1M1AimActorSelectEntry.execution
    s f work[j]! (resolve original.collected[j]!) who distance scene.things[work[j]!.id]!.z
    scene.things[work[j]!.id]!.height thing.shootHeight lower upper topSlope bottomSlope
    (by simpa only [selection.original] using record) isThing tagSafe ptrSafe shooterSafe flagsSafe shooterWord
    (fun same => different (identity.mp same))
    (by rw [shootable] at flags; simpa using flags) topSafe safe before.range z0 ht before.eye bottom top topOk admitted bottomOk bottomAdmitted
  have memory := (E1M1AimActorReturn.registers s saveSafe).2.2.2.1
  refine ⟨n,hn,result s,selected_frame s saveSafe,run,pc,zero,stack,E1M1AimActorStop.records s work resolve saveSafe
    (by have := before.bounded; omega) selection.ready.records before.layout.recordsSafe,
    targetOut,slopeOut,?_,?_,?_⟩
  · rw [memory]; exact bounds.2.2.2.2.2.1
  · rw [memory]; exact bounds.2.2.2.2.2.2
  · rw [E1M1AimSynchronizedCycle.indices seen.length path.visited.size aligned.1]
    exact source
end Doom.Proofs.E1M1AimSavedWords
