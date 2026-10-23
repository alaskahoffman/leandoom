import Doom.Proofs.E1M1AimActorSkip
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimActorSkipJoin
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1MinimumScan (address)
open E1M1InterceptMark (consume)
open E1M1AimIteration
open E1M1AimActorSkip (program result)
open E1M1AimWall (Safe)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- Skipping the shooter or an unshootable actor leaves bounds and portal log
unchanged and visits the canonical next index without a division. -/
theorem source (scene : Scene) (shooter : Nat) (thing : SolidThing) (path : PathResult)
    (distance lower upper : Fixed) (log : Array AutoAim.Portal) (i : Nat) (rest : List Nat)
    (hit : Intercept) (selected : path.visited[i]! = hit) (isThing : hit.isLine=false)
    (ignored : hit.id=shooter ∨ scene.things[hit.id]!.shootable=false) :
    remaining scene shooter thing path distance (i::rest) lower upper log =
      remaining scene shooter thing path distance rest lower upper log := by
  have gate : (hit.id==shooter || !scene.things[hit.id]!.shootable)=true := by
    rcases ignored with same|no
    · simp [same]
    · simp [no]
  simp [remaining,List.forIn_cons,visit,selected,isThing,gate]

/-- The six-push prologue preserves the whole represented intercept buffer. -/
theorem saved_records (s : X86Memory.State) (work : Array Intercept) (resolve : Intercept → Word)
    (records : OriginalLineFinish.Encodes s.memory 0x2ba20 resolve work)
    (safe : E1M1AimRecordFrame.RecordsSafe s work) :
    OriginalLineFinish.Encodes (OriginalAimGuard.saved s).memory 0x2ba20 resolve work := by
  intro i hi
  have old := records i hi
  have addr : (0x2ba20 : Word)+BitVec.ofNat 32 (12*i)=address i := by
    simp [E1M1MinimumScan.address,BitVec.ofNat_add]
  simp only [OriginalLineFinish.RecordAt,addr] at old ⊢
  have first : Safe (s.regs 4) (address i) := by simpa only [BitVec.add_zero] using (safe i hi (0#32) (by simp)).1
  rw [E1M1AimWall.saved_frame s _ first,E1M1AimWall.saved_frame s _ (safe i hi (4#32) (by simp)).1,
    E1M1AimWall.saved_frame s _ (safe i hi (8#32) (by simp)).1]
  exact old

/-- A skipped selected actor reaches the actual next-scan head with the consumed
buffer and history matching source progress. Actor identity/flag representation
and static read separation remain explicit; the next scan itself is not assumed. -/
theorem execution (s : X86Memory.State) (f : Option Flags)
    (scene : Scene) (shooter : Nat) (thing : SolidThing) (path original : PathResult)
    (distance lower upper : Fixed) (log : Array AutoAim.Portal)
    (work : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (target sp who : Word) (fraction : Int32) (j : Nat)
    (history : History original.collected work seen visits)
    (selection : Selection original.collected work seen resolve target sp ⟨s,f,0x2b760⟩ fraction j)
    (layout : E1M1AimCycleInvariant.Layout s work) (bounded : original.collected.size≤128)
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
    (ignored : (work[j]!).id=shooter ∨ scene.things[work[j]!.id]!.shootable=false)
    (stable : resolve {work[j]! with frac:=⟨2147483647⟩}=resolve work[j]!) :
    (∃ n≤28, X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ (result s)) ∧
    (result s).pc=0x2c83a ∧
    OriginalLineFinish.Encodes (result s).core.memory 0x2ba20 resolve (consume work j) ∧
    History original.collected (consume work j) (j::seen) (visits.push work[j]!) ∧
    load32 (result s).core.memory (0x2c1e4#32)=lower.raw.toBitVec ∧
    load32 (result s).core.memory (0x2c1e8#32)=upper.raw.toBitVec ∧
    remaining scene shooter thing path distance
      (List.range' seen.length (path.visited.size-seen.length)) lower upper log =
      remaining scene shooter thing path distance
        (List.range' (seen.length+1) (path.visited.size-(seen.length+1))) lower upper log := by
  have size := (E1M1SelectionHistory.image history).size
  have inside : j<work.size := by have := selection.inside; omega
  have bound : j<128 := by have := selection.inside; omega
  have pointer : s.regs 3=address j := selection.ready.pointer.trans selection.argument
  have record := E1M1AimCycleInvariant.record original.collected work seen visits resolve target sp
    ⟨s,f,0x2b760⟩ fraction j history selection
  have tagSafe : Safe (s.regs 4) (s.regs 0+4) := by
    rw [selection.argument]; exact (layout.recordsSafe j inside 4 (by simp)).1
  have ptrSafe : Safe (s.regs 4) (s.regs 0+8) := by
    rw [selection.argument]; exact (layout.recordsSafe j inside 8 (by simp)).1
  have reject : resolve original.collected[j]! = who ∨ s.memory (resolve original.collected[j]!+104) &&& (4#8)=0 := by
    rcases ignored with same|no
    · exact Or.inl (identity.mpr same)
    · apply Or.inr
      rw [no] at flags
      simpa using flags
  obtain ⟨run,pc,_,_,_,_,memory⟩ := E1M1AimActorSkip.execution s f work[j]! (resolve original.collected[j]!) who
    (by simpa only [selection.original] using record) isThing tagSafe ptrSafe shooterSafe flagsSafe shooterWord reject
    selection.ready.returnWord
  have bounds := E1M1AimTraversalInvariant.bounds_mark j bound
  have aligned := E1M1AimPathBridge.selected original path work seen visits resolve target sp
    ⟨s,f,0x2b760⟩ fraction j history selection empty query
  refine ⟨run,pc,?_,History.push history fraction j selection.chosen selection.within,?_,?_,?_⟩
  · rw [memory,pointer]
    exact E1M1InterceptMark.encoded _ work resolve j inside (by omega)
      (saved_records s work resolve selection.ready.records layout.recordsSafe) stable
  · rw [memory,load_store_apart _ _ _ _ (by rw [pointer]; exact bounds.1),
      E1M1AimWall.saved_frame s _ (E1M1AimBlockingCycle.prologue_safe s _ (layout.floorReads _ (by simp)))]
    exact bottom
  · rw [memory,load_store_apart _ _ _ _ (by rw [pointer]; exact bounds.2),
      E1M1AimWall.saved_frame s _ (E1M1AimBlockingCycle.prologue_safe s _ (layout.ceilingReads _ (by simp)))]
    exact top
  · rw [E1M1AimSynchronizedCycle.indices seen.length path.visited.size aligned.1]
    exact source scene shooter thing path distance lower upper log seen.length _ work[j]! aligned.2.1 isThing ignored

end Doom.Proofs.E1M1AimActorSkipJoin
