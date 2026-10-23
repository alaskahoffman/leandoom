import Doom.Proofs.E1M1AimStampCellTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimStampCell
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanContracts (LineData candidates)
open OriginalLineVisits (Represents stamp markPrefix)
open E1M1FiringVisitedNext (TailSafe)
attribute [local irreducible] load32

/-- Complete line and object phases plus the numeric step keep the same
origin memory and mark exactly the visited line prefix. -/
theorem scan (s : X86Control.State) (sp cursor base lines epoch : Word) (words : Array Nat) (w h : Nat)
    (objects : Nat → Word) (trace : Collision.Divline) (cell : E1M1PathMap.Cell)
    (data : Nat → LineData) (nodes : List E1M1ThingList.Node) (r : Collision.PathResult) (seen : Array Bool)
    (pc : s.pc=0x2c57f) (stack : s.core.regs 4=sp-(124#32)) (list : s.core.regs 2=cursor)
    (items : E1M1PathMapLookup.ScanWords s.core lines cell)
    (ids : ∀ i : Fin cell.ids.length, cell.ids[i.val]<475)
    (target : load32 s.core.memory (s.core.regs 4)=(0x2c5f0#32))
    (returnWord : load32 s.core.memory (sp-(116#32))=(0x2ca94#32))
    (maps : E1M1CellMapInvariant.Image s.core.memory sp base lines words w h)
    (mapLayout : E1M1CellMapInvariant.Layout sp base lines words)
    (payload : E1M1CellSceneInvariant.Image s.core.memory lines trace cell data nodes)
    (payloadSafe : E1M1CellSceneInvariant.Protected sp lines cell data nodes)
    (contracts : E1M1CellSceneInvariant.Contracts sp lines trace cell data objects nodes)
    (layout : E1M1ScanContracts.Layout sp cursor lines cell.ids.length (candidates trace lines cell.ids data))
    (x y : Int32) (mapX : s.core.regs 6=x.toBitVec) (mapY : s.core.regs 1=y.toBitVec)
    (inMap : Collision.pathCellInside x y w h=true) (links : Word)
    (selection : E1M1CellObjectSelection.Image s.core.memory links x y w nodes)
    (selectionSafe : E1M1CellObjectSelection.Protected sp lines links x y w)
    (tracked : OriginalLineCollection.Tracks s.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) r.collected 0)
    (capacity : r.collected.size+cell.ids.length+nodes.length≤128)
    (represented : Represents s.core.memory lines epoch seen) (size : seen.size=475)
    (stamps : E1M1ScanContracts.Stamps sp lines) (returns : E1M1ScanReturn.ReturnSafe sp lines)
    (epochSafe : TailSafe sp (0x13580#32)) (stampSafe : ∀ j<475, TailSafe sp (stamp lines j))
    (locals : E1M1GridLocals.Safe sp lines)
    (world : Collision.Scene) (dimension : world.grid.width=w)
    (sceneIds : world.links[Collision.pathCellIndex x y w]?=some (nodes.map E1M1ThingList.Node.id).toArray)
    (scene : ∀ node∈nodes, world.things[node.id]?=some node.target)
    (origin : Memory) (image : E1M1AimStampImage.Image origin s.core.memory lines epoch seen) :
    let scan := E1M1NextLineScan.result s.core lines trace cell data s.flags r
    let out := E1M1CellScanAdvance.result s lines trace cell data nodes r
    (∃ n≤59+281*cell.ids.length+230*nodes.length,
      X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
    out.core.regs 4=sp-(112#32) ∧
    E1M1PathAdvance.observe out.core=E1M1PathAdvance.step (E1M1PathAdvance.observe (E1M1CellLineBoundary.view s.core sp)) ∧
    out.pc=E1M1PathAdvance.nextPc (E1M1PathAdvance.observe (E1M1CellLineBoundary.view s.core sp)) ∧
    (∃ after, E1M1FiringThings.sceneCell trace world x y scan.2=.ok after ∧
      after.collected.size≤r.collected.size+cell.ids.length+nodes.length ∧
      OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1ThingFinish.resolve lines objects)
        after.collected (128-(r.collected.size+cell.ids.length+nodes.length))) ∧
    Represents out.core.memory lines epoch (markPrefix (candidates trace lines cell.ids data) cell.ids.length 0 seen) ∧
    E1M1CellMapInvariant.Image out.core.memory sp base lines words w h ∧
    E1M1CellSceneInvariant.Image out.core.memory lines trace cell data nodes ∧
    E1M1CellObjectSelection.Image out.core.memory links x y w nodes ∧
    E1M1CellMapInvariant.Frame sp lines s.core.memory out.core.memory ∧
    E1M1AimStampImage.Image origin out.core.memory lines epoch
      (markPrefix (candidates trace lines cell.ids data) cell.ids.length 0 seen) := by
  have ready := E1M1CellSceneInvariant.lines_ready s.core sp lines trace cell data objects nodes payload contracts stack target items ids
  have lineCapacity : OriginalLineCollection.Tracks s.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) r.collected cell.ids.length :=
    ⟨tracked.encoded,tracked.cursor,by omega⟩
  obtain ⟨⟨n,hn,run⟩,_,hits,visits,_,_⟩ := E1M1NextLineScan.execution s.core sp cursor lines objects trace cell data stack list items ids ready layout
    stamps s.flags r lineCapacity epoch seen size represented
  have scanImage := (E1M1AimStampNextScan.execution s.core sp cursor lines objects trace cell data
    stack list items ids ready layout stamps s.flags r lineCapacity epoch seen size represented origin image).2.2.2.2.2.2.1
  rw [OriginalPathXStep.at_pc _ _ pc] at run
  have ret := E1M1NextLineReturn.parent_return s.core sp cursor lines objects trace cell data stack list items ids ready layout returns s.flags r lineCapacity
  have returnPC : (E1M1NextLineScan.result s.core lines trace cell data s.flags r).1.pc=0x2ca94 := by
    simpa using ret.2.2.2.trans (congrArg BitVec.toNat returnWord)
  have numeric := E1M1CellLineBoundary.observe s.core sp cursor lines objects trace cell data stack list items ids ready layout s.flags r lineCapacity returns locals
  have frame := E1M1CellLineBoundary.frame s.core sp cursor lines objects trace cell data stack list items ids ready layout s.flags r lineCapacity
  have coords (axis : Bool) := E1M1NextCoordinates.scan_coordinate s.core sp cursor lines objects trace cell data stack list items ids ready layout s.flags r lineCapacity axis
  have lineBound := E1M1NextObjectMemory.scan_size s.core lines trace cell data s.flags r
  obtain ⟨⟨m,hm,objectRun⟩,outStack,obs,outPC,⟨after,production,bound,outHits⟩,outVisits,outMaps,outPayload,outSelection,outFrame,_,outImage⟩ :=
    E1M1AimStampCellTail.advance _ sp base lines epoch words w h objects trace cell data nodes _ _
      returnPC ret.1 ret.2.1
      (E1M1CellMapInvariant.transport _ _ sp base lines words w h maps mapLayout frame) mapLayout
      (E1M1CellSceneInvariant.transport _ _ sp lines trace cell data nodes payload payloadSafe frame) payloadSafe contracts
      x y ((coords true).trans mapX) ((coords false).trans mapY) inMap links
      (E1M1CellObjectSelection.transport _ _ sp lines links x y w nodes selection selectionSafe frame) selectionSafe
      hits (by omega) visits returns epochSafe (fun j hj => stampSafe j (by simpa only [OriginalLineVisitedRun.mark_size,size] using hj))
      locals world dimension sceneIds scene origin scanImage
  rw [numeric] at obs outPC
  have finalBound : after.collected.size≤r.collected.size+cell.ids.length+nodes.length := by omega
  have finalHits := E1M1CellCapacity.reserve _ _ _ _ _
    (show OriginalLineCollection.Tracks _ _ _ after.collected 0 from ⟨outHits.encoded,outHits.cursor,by have := outHits.room; omega⟩)
    finalBound capacity
  exact ⟨⟨n+m,by omega,E1M1PspriteStep.prefix_trans run objectRun⟩,outStack,obs,outPC,
    ⟨after,production,finalBound,finalHits⟩,outVisits,outMaps,outPayload,outSelection,
    E1M1CellMapInvariant.frame_trans sp lines _ _ _ frame outFrame,outImage⟩

/-- Derive that strengthened cell transition from the actual lookup gate. -/
theorem gate (s : X86Control.State) (sp base lines epoch : Word) (words : Array Nat) (w h : Nat)
    (objects : Nat → Word) (trace : Collision.Divline) (cell : E1M1PathMap.Cell)
    (data : Nat → LineData) (nodes : List E1M1ThingList.Node) (r : Collision.PathResult) (seen : Array Bool)
    (pc : s.pc=0x2ca7f) (stack : s.core.regs 4=sp-(112#32))
    (valid : cell.Valid words)
    (maps : E1M1CellMapInvariant.Image s.core.memory sp base lines words w h)
    (mapLayout : E1M1CellMapInvariant.Layout sp base lines words)
    (payload : E1M1CellSceneInvariant.Image s.core.memory lines trace cell data nodes)
    (payloadSafe : E1M1CellSceneInvariant.Protected sp lines cell data nodes)
    (contracts : E1M1CellSceneInvariant.Contracts sp lines trace cell data objects nodes)
    (layout : E1M1ScanContracts.Layout sp (base+BitVec.ofNat 32 (2*cell.offset)) lines cell.ids.length (candidates trace lines cell.ids data))
    (x y : Int32) (mapX : s.core.regs 6=x.toBitVec) (mapY : s.core.regs 1=y.toBitVec)
    (selected : words[4+Collision.pathCellIndex x y w]?=some cell.offset)
    (inMap : Collision.pathCellInside x y w h=true) (links : Word)
    (selection : E1M1CellObjectSelection.Image s.core.memory links x y w nodes)
    (selectionSafe : E1M1CellObjectSelection.Protected sp lines links x y w)
    (tracked : OriginalLineCollection.Tracks s.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) r.collected 0)
    (cursorSafe : E1M1PathMapCaller.Safe s.core (0x2c028#32))
    (recordsSafe : ∀ i<r.collected.size, ∀ off∈[(0#32),4,8],
      E1M1PathMapCaller.Safe s.core (OriginalLineCollection.slot 0x2ba20 i off))
    (capacity : r.collected.size+cell.ids.length+nodes.length≤128)
    (represented : Represents s.core.memory lines epoch seen) (size : seen.size=475)
    (stamps : E1M1ScanContracts.Stamps sp lines) (returns : E1M1ScanReturn.ReturnSafe sp lines)
    (epochSafe : TailSafe sp (0x13580#32)) (stampSafe : ∀ j<475, TailSafe sp (stamp lines j))
    (locals : E1M1GridLocals.Safe sp lines)
    (world : Collision.Scene) (dimension : world.grid.width=w)
    (sceneIds : world.links[Collision.pathCellIndex x y w]?=some (nodes.map E1M1ThingList.Node.id).toArray)
    (scene : ∀ node∈nodes, world.things[node.id]?=some node.target)
    (origin : Memory) (image : E1M1AimStampImage.Image origin s.core.memory lines epoch seen) :
    let entry := E1M1PathMapCaller.scan s.core
    let scan := E1M1NextLineScan.result entry.core lines trace cell data entry.flags r
    let out := E1M1CellAdvance.result s lines trace cell data nodes r
    (∃ n≤89+281*cell.ids.length+230*nodes.length,
      X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
    out.core.regs 4=sp-(112#32) ∧
    E1M1PathAdvance.observe out.core=E1M1PathAdvance.step (E1M1PathAdvance.observe s.core) ∧
    out.pc=E1M1PathAdvance.nextPc (E1M1PathAdvance.observe s.core) ∧
    (∃ after, E1M1FiringThings.sceneCell trace world x y scan.2=.ok after ∧
      after.collected.size≤r.collected.size+cell.ids.length+nodes.length ∧
      OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1ThingFinish.resolve lines objects)
        after.collected (128-(r.collected.size+cell.ids.length+nodes.length))) ∧
    Represents out.core.memory lines epoch (markPrefix (candidates trace lines cell.ids data) cell.ids.length 0 seen) ∧
    E1M1CellMapInvariant.Image out.core.memory sp base lines words w h ∧
    E1M1CellSceneInvariant.Image out.core.memory lines trace cell data nodes ∧
    E1M1CellObjectSelection.Image out.core.memory links x y w nodes ∧
    E1M1CellMapInvariant.Frame sp lines s.core.memory out.core.memory ∧
    E1M1AimStampImage.Image origin out.core.memory lines epoch
      (markPrefix (candidates trace lines cell.ids data) cell.ids.length 0 seen) := by
  have callerSafe (a : Word) (safe : TailSafe sp a) := (E1M1FiringVisitedNext.next_safe s.core sp a stack safe).2
  obtain ⟨⟨n,hn,lookup⟩,items,entryPC,entryStack,entryMaps,lookupFrame,entryHits,entryVisits⟩ :=
    E1M1CellMapInvariant.inside s sp base lines words w h pc stack maps mapLayout x y mapX mapY cell inMap valid selected
      (E1M1ThingFinish.resolve lines objects) r.collected 0 tracked cursorSafe recordsSafe epoch seen represented
      (callerSafe _ epochSafe) (fun j hj => callerSafe _ (stampSafe j (by simpa only [size] using hj)))
  have facts := E1M1CellMapInvariant.inputs s.core sp base lines words w h stack maps mapLayout
  have cursor := E1M1FiringScan.caller_cursor s.core base lines words cell x y w h facts.1 mapX mapY facts.2.1 inMap valid maps.encoded facts.2.2 selected
  have target : load32 (E1M1PathMapCaller.scan s.core).core.memory ((E1M1PathMapCaller.scan s.core).core.regs 4)=(0x2c5f0#32) := by
    rw [entryStack]
    have saved := E1M1NextCallbackMemory.caller_callback s.core
    rw [stack] at saved
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using saved
  have returnWord : load32 (E1M1PathMapCaller.scan s.core).core.memory (sp-(116#32))=(0x2ca94#32) := by
    have saved := (E1M1ScanReturn.caller_words s.core).2
    rw [stack] at saved
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using saved
  have entryImage := E1M1AimStampImage.transport origin _ _ lines epoch seen image
    (E1M1NextCellMemory.caller_frame s.core _ (callerSafe _ epochSafe))
    (fun j hj => E1M1NextCellMemory.caller_frame s.core _ (callerSafe _ (stampSafe j (by simpa only [size] using hj))))
  obtain ⟨⟨m,hm,scanRun⟩,outStack,obs,outPC,hits,visits,outMaps,outPayload,outSelection,outFrame,outImage⟩ :=
    scan _ sp _ base lines epoch words w h objects trace cell data nodes r seen
      entryPC entryStack cursor items (fun i => (valid.2.2.2.1 i).1) target returnWord
      entryMaps mapLayout
      (E1M1CellSceneInvariant.transport _ _ sp lines trace cell data nodes payload payloadSafe lookupFrame) payloadSafe contracts layout
      x y ((E1M1ThingCoordinates.caller_coordinate s.core true).trans mapX)
      ((E1M1ThingCoordinates.caller_coordinate s.core false).trans mapY) inMap links
      (E1M1CellObjectSelection.transport _ _ sp lines links x y w nodes selection selectionSafe lookupFrame) selectionSafe
      entryHits capacity entryVisits size stamps returns epochSafe stampSafe locals world dimension sceneIds scene origin entryImage
  rw [E1M1CellLineBoundary.lookup_view s.core sp stack] at obs outPC
  exact ⟨⟨n+m,by omega,E1M1PspriteStep.prefix_trans lookup scanRun⟩,outStack,obs,outPC,hits,visits,
    outMaps,outPayload,outSelection,E1M1CellMapInvariant.frame_trans sp lines _ _ _ lookupFrame outFrame,outImage⟩
end Doom.Proofs.E1M1AimStampCell
