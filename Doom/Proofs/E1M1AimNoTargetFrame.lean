import Doom.Proofs.E1M1AimOrderedResult
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Doom.Proofs.E1M1AimNoTargetFrame
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1AimCatalog (Portal)
open E1M1AimTraversalInvariant (Persistent)
open E1M1AimSourceCatalog (Represents front back)
open E1M1AimIteration
open E1M1AimRepeatProgram (program)
open E1M1AimWall (Safe returned)
attribute [local irreducible] load32 store32

open E1M1AimHistoryCycle (Frame)
open E1M1AimBlockingCycle (wall_execution prologue_safe)

/-- The generic cycle read protection includes the shorter opening-helper writes. -/
theorem opening_safe (s : X86Memory.State) (a : Word) (safe : E1M1AimRecordFrame.ReadSafe s a) :
    ∀ b∈E1M1AimOpeningFrame.writes (s.regs 4), Apart a b := by
  intro b member
  simp only [E1M1AimOpeningFrame.writes,E1M1AimOpeningFrame.pushes,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ((rfl|rfl|rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl))|global
  all_goals solve
    | apply safe.1; simp
    | apply safe.2; simp_all [E1M1AimReturnFrame.writes]

theorem wall (s : X86Memory.State) (f : Option Flags)
    (scene : Scene) (shooter : Nat) (thing : SolidThing) (path result : PathResult)
    (work : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (distance : Fixed) (target sp : Word) (fraction : Int32) (j : Nat)
    (history : History result.collected work seen visits)
    (selection : Selection result.collected work seen resolve target sp ⟨s,f,0x2b760⟩ fraction j)
    (layout : E1M1AimCycleInvariant.Layout s work)
    (empty : result.visited=#[])
    (query : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok path)
    (lower upper : Fixed) (log : Array AutoAim.Portal)
    (bottom : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec)
    (top : load32 s.memory (0x2c1e8#32)=upper.raw.toBitVec)
    (isLine : (work[j]!).isLine=true)
    (flagsSafe : Safe (s.regs 4) (resolve result.collected[j]!+16))
    (flags : (s.memory (resolve result.collected[j]!+16) &&& (4#8) != 0)=scene.lines[work[j]!.id]!.twoSided)
    (solid : scene.lines[work[j]!.id]!.twoSided=false) :
    ∃ out,
      Frame s out ∧
      X86CodeMemory.Prefix FloorCaller.cm program [] 24 ⟨s,f,0x2b760⟩ out ∧
      out.pc=0x2c88c ∧ out.core.regs 0=0 ∧ out.core.regs 4=s.regs 4+4 ∧
      load32 out.core.memory (0x2c1e4#32)=lower.raw.toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=upper.raw.toBitVec ∧
      remaining scene shooter thing path distance
        (List.range' seen.length (path.visited.size-seen.length)) lower upper log =
        .ok {path:=E1M1AimSource.stopped path (seen.length+1)} := by
  have record := E1M1AimCycleInvariant.record result.collected work seen visits resolve target sp
    ⟨s,f,0x2b760⟩ fraction j history selection
  have size := (E1M1SelectionHistory.image history).size
  have inside : j<work.size := by have := selection.inside; omega
  have tagSafe : Safe (s.regs 4) (s.regs 0+4) := by
    rw [selection.argument]; exact (layout.recordsSafe j inside 4 (by simp)).1
  have pointerSafe : Safe (s.regs 4) (s.regs 0+8) := by
    rw [selection.argument]; exact (layout.recordsSafe j inside 8 (by simp)).1
  have oneSided : s.memory (resolve result.collected[j]!+16) &&& (4#8)=0 := by
    rw [solid] at flags
    simpa using flags
  obtain ⟨run,pc,zero,stack,memory⟩ := wall_execution ⟨s,f,0x2b760⟩ work[j]!
    (resolve result.collected[j]!) rfl selection.ready.returnWord (by simpa only [selection.original] using record) isLine tagSafe pointerSafe flagsSafe oneSided
  have aligned := E1M1AimPathBridge.selected result path work seen visits resolve target sp
    ⟨s,f,0x2b760⟩ fraction j history selection empty query
  refine ⟨E1M1AimStop.result s,?_,run,pc,zero,stack,?_,?_,?_⟩
  · intro a safe _ _ _
    rw [memory]
    exact E1M1AimWall.saved_frame s a safe.1
  · rw [memory,E1M1AimWall.saved_frame s _ (prologue_safe s _ (layout.floorReads _ (by simp)))]
    exact bottom
  · rw [memory,E1M1AimWall.saved_frame s _ (prologue_safe s _ (layout.ceilingReads _ (by simp)))]
    exact top
  · rw [E1M1AimSynchronizedCycle.indices seen.length path.visited.size aligned.1]
    exact E1M1AimBlockingSource.wall scene shooter thing path distance lower upper log seen.length _
      work[j]! aligned.2.1 isLine solid

theorem closed (s : X86Memory.State) (f : Option Flags)
    (scene : Scene) (shooter : Nat) (thing : SolidThing) (path result : PathResult)
    (work : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (portals : Nat → Option Portal) (distance : Fixed)
    (target sp : Word) (fraction : Int32) (j : Nat) (p : Portal)
    (history : History result.collected work seen visits)
    (selection : Selection result.collected work seen resolve target sp ⟨s,f,0x2b760⟩ fraction j)
    (before : Persistent s result.collected work resolve portals distance thing.shootHeight)
    (represented : Represents scene result.collected portals) (listed : portals j=some p)
    (empty : result.visited=#[])
    (query : E1M1QuerySource.visitHits result (fun _ _ => true)=.ok path)
    (lower upper : Fixed) (log : Array AutoAim.Portal)
    (bottom : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec)
    (top : load32 s.memory (0x2c1e8#32)=upper.raw.toBitVec)
    (blocked : min (front p).ceiling.raw (back p).ceiling.raw ≤ max (front p).floor.raw (back p).floor.raw) :
    ∃ n≤60, ∃ out,
      Frame s out ∧
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ out ∧
      out.pc=0x2c88c ∧ out.core.regs 0=0 ∧ out.core.regs 4=s.regs 4+4 ∧
      load32 out.core.memory (0x2c1e4#32)=lower.raw.toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=upper.raw.toBitVec ∧
      remaining scene shooter thing path distance
        (List.range' seen.length (path.visited.size-seen.length)) lower upper log =
        .ok {path:=E1M1AimSource.stopped path (seen.length+1)} := by
  have sourceMap := E1M1AimSourceCatalog.entry scene result.collected work seen resolve portals
    target sp ⟨s,f,0x2b760⟩ fraction j p selection represented listed
  have inputs := E1M1AimCatalog.inputs ⟨s,f,0x2b760⟩ result.collected work seen visits resolve portals
    target sp fraction j p history selection before.catalog listed before.layout before.query before.globals
  have aligned := E1M1AimPathBridge.selected result path work seen visits resolve target sp
    ⟨s,f,0x2b760⟩ fraction j history selection empty query
  have bounds := E1M1AimPortalSource.signed_bounds (front p).floor (front p).ceiling
    (back p).floor (back p).ceiling
  simp only [E1M1AimSourceCatalog.front,E1M1AimSourceCatalog.back,Int32.toBitVec_ofBitVec] at bounds
  have blockedWord := bounds.mpr blocked
  obtain ⟨⟨n,hn,run⟩,pc,zero,stack,_⟩ := E1M1AimClosedReturn.execution s f work[j]!
    (resolve result.collected[j]!) p.front p.back p.ff p.fc p.bf p.bc inputs.1
    before.layout.returnSafe selection.ready.returnWord blockedWord
  refine ⟨n,hn,E1M1AimClosedReturn.result s,?_,run,pc,zero,stack,?_,?_,?_⟩
  · intro a safe _ _ _
    exact E1M1AimClosedReturn.frame s a (opening_safe s a safe)
  · rw [E1M1AimClosedReturn.frame s _ (before.layout.floorReads _ (by simp))]
    exact bottom
  · rw [E1M1AimClosedReturn.frame s _ (before.layout.ceilingReads _ (by simp))]
    exact top
  · rw [E1M1AimSynchronizedCycle.indices seen.length path.visited.size aligned.1]
    exact E1M1AimBlockingSource.closed scene shooter thing path distance lower upper log seen.length _
      work[j]! (back p) aligned.2.1 inputs.1.isLine sourceMap.2.2 sourceMap.2.1
      (by simpa only [sourceMap.1] using blocked)

end Doom.Proofs.E1M1AimNoTargetFrame
