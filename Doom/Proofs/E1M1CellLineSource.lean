import Doom.Proofs.E1M1TraversalLineJoin
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1CellLineSource
open Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant (Context Cell Common Static State Images caller_safe)
attribute [local irreducible] load32

/-- Source scene data for an in-map raw line list, independent of reached memory. -/
structure SceneLines (q : Context) (c : Cell) : Prop where
  ids : q.world.grid.cells[Collision.pathCellIndex c.x c.y q.width]?=some c.cell.ids.tail.toArray
  lookup : ∀ i : Fin c.cell.ids.length, q.world.lines[c.cell.ids[i.val]]?=some (c.data i.val).line

/-- Derive the checked source line result from the actual cell gate. No scan-entry
state, reached callback geometry, capacity or visited history is postulated. -/
theorem lines (q : Context) (c : Cell) (s : X86Control.State) (r : Collision.PathResult) (seen : Array Bool)
    (common : Common q) (static : Static q c) (state : State q s r seen)
    (images : Images q [c] s.core.memory) (pc : s.pc=0x2ca7f)
    (x : (E1M1PathAdvance.observe s.core).mapX=c.x.toBitVec)
    (y : (E1M1PathAdvance.observe s.core).mapY=c.y.toBitVec)
    (room : r.collected.size+c.cell.ids.length≤128) (scene : SceneLines q c) :
    E1M1LineSourceLoop.lineCell q.trace q.world.lines c.cell.ids.toArray seen r=.ok
      (E1M1CellWalk.visits q c seen,E1M1CellWalk.lineResult q c s r) := by
  have callerSafe (a : Word) (safe : E1M1FiringVisitedNext.TailSafe q.sp a) :=
    (E1M1FiringVisitedNext.next_safe s.core q.sp a state.stack safe).2
  obtain ⟨_,items,entryPC,entryStack,entryMaps,lookupFrame,entryHits,entryVisits⟩ :=
    E1M1CellMapInvariant.inside s q.sp q.base q.lines q.words q.width q.height pc state.stack state.maps common.mapLayout
      c.x c.y x y c.cell static.inside static.valid static.selected
      (E1M1ThingFinish.resolve q.lines q.objects) r.collected 0 state.tracked
      (caller_safe s.core q.sp _ state.stack common.cursor)
      (fun i hi off ho => caller_safe s.core q.sp _ state.stack (common.records i (by omega) off ho))
      q.epoch seen state.represented (callerSafe _ common.epochSafe)
      (fun j hj => callerSafe _ (common.stampSafe j (by simpa only [state.size] using hj)))
  have facts := E1M1CellMapInvariant.inputs s.core q.sp q.base q.lines q.words q.width q.height state.stack state.maps common.mapLayout
  have cursor := E1M1FiringScan.caller_cursor s.core q.base q.lines q.words c.cell c.x c.y q.width q.height
    facts.1 x y facts.2.1 static.inside static.valid state.maps.encoded facts.2.2 static.selected
  have target : load32 (E1M1PathMapCaller.scan s.core).core.memory ((E1M1PathMapCaller.scan s.core).core.regs 4)=(0x2c5f0#32) := by
    rw [entryStack]
    have saved := E1M1NextCallbackMemory.caller_callback s.core
    rw [state.stack] at saved
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using saved
  have payload := E1M1CellSceneInvariant.transport _ _ q.sp q.lines q.trace c.cell c.data c.nodes
    (images c (by simp)).1 static.payloadSafe lookupFrame
  have ids := fun i => (static.valid.2.2.2.1 i).1
  have ready := E1M1CellSceneInvariant.lines_ready _ q.sp q.lines q.trace c.cell c.data q.objects c.nodes
    payload static.contracts entryStack target items ids
  have capacity : OriginalLineCollection.Tracks (E1M1PathMapCaller.scan s.core).core 0x2ba20
      (E1M1ThingFinish.resolve q.lines q.objects) r.collected c.cell.ids.length :=
    ⟨entryHits.encoded,entryHits.cursor,room⟩
  exact E1M1LineSourceScan.source_result _ q.sp _ q.lines q.objects q.trace c.cell c.data entryStack cursor
    items ids ready static.layout common.stamps (E1M1PathMapCaller.scan s.core).flags r capacity q.epoch seen state.size
    entryVisits q.world.lines scene.lookup
end Doom.Proofs.E1M1CellLineSource
