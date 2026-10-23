import Doom.Proofs.E1M1NextThingLookup
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1FiringNextLookup
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open E1M1ThingListInputs (before)
open E1M1FiringGridState (initial)
open E1M1FiringLineVisits (seenAfter)
open E1M1FiringVisitedNext (TailSafe)
open OriginalLineVisits (Represents stamp)
attribute [local irreducible] load32 Collision.pathFirstIntercept

section Firing
variable (gun : Fire.Gun) (s : X86Memory.State) (weapon : Weapon.Context)
    (actor : Word) (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (xout yout : Int32 × Fixed × Fixed) (base lines : Word) (words : Array Nat)
    (c : E1M1PathMap.Cell) (w h : Nat) (data : Nat → LineData)
    (input : E1M1FiringScan.Inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data)
include input


attribute [local irreducible] Collision.SolidThing.attackEndpoint

variable (returns : E1M1ScanReturn.ReturnSafe (s.regs 4) lines)
    (flag : E1M1ThingGate.FlagSafe (s.regs 4) lines)
    (links : Word) (nodes : List E1M1ThingList.Node)
    (lookupSafe : ∀ a∈E1M1ThingEntry.reads thing angle ox oy w links, E1M1ThingEntry.ReadSafe gun s lines a)
    (global : load32 s.memory (0x2c0f8#32)=links)
    (selected : load32 s.memory (links+(BitVec.ofNat 32 (Collision.pathCellIndex
      (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY w) <<< 2))=E1M1ThingList.head nodes)
include returns flag lookupSafe global selected

variable (objects : Nat → Word)
    (d : E1M1ThingListInputs.Data gun s lines (path thing angle ox oy).trace objects nodes)
include d



variable (stamps : E1M1ScanContracts.Stamps (s.regs 4) lines)
    (epochBefore : E1M1ScanMemory.BeforeInit gun s (0x13580#32))
    (epochAfter : E1M1PathMapSetup.StackSafe (s.regs 4-(112#32)) (0x13580#32))
    (stampSetup : ∀ j<475, E1M1PathMapFiring.Safe gun s (stamp lines j))
    (fresh : ∀ j<475, load32 s.memory (stamp lines j)≠load32 s.memory 0x13580+1)
    (epochTail : TailSafe (s.regs 4) (0x13580#32))
    (stampTail : ∀ j<475, TailSafe (s.regs 4) (stamp lines j))
include stamps epochBefore epochAfter stampSetup fresh epochTail stampTail

variable (room : c.ids.length+nodes.length≤128)
    (world : Collision.Scene) (dimension : world.grid.width=w)
    (ids : world.links[Collision.pathCellIndex (path thing angle ox oy).startBlockX
      (path thing angle ox oy).startBlockY w]?=some (nodes.map E1M1ThingList.Node.id).toArray)
    (scene : ∀ node∈nodes, world.things[node.id]?=some node.target)
include room dimension ids scene

variable (locals : E1M1GridLocals.Safe (s.regs 4) lines)
include locals

open E1M1NextCallbackReady (Ready)
open E1M1ScanGeometry (linePointer)
/-- Continuous post-sound execution now selects the second cell's object head.
Read values come from firing entry and protected addresses, not reached memory.
The empty branch returns to the caller; the nonempty branch stops before its
first object callback. Both retain the accumulated intercepts and visit stamps. -/
theorem execution (f : Option Flags)
    (globalsSafe : ∀ a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120], E1M1FiringMapState.Safe (s.regs 4) lines a)
    (imageSafe : ∀ i<words.size, E1M1FiringMapState.Safe (s.regs 4) lines (base+BitVec.ofNat 32 (2*i)))
    (notEnd : E1M1PathAdvance.ended (initial (path thing angle ox oy) xout yout)=false)
    (x y : Int32)
    (mapX : (E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout)).mapX=x.toBitVec)
    (mapY : (E1M1PathAdvance.step (initial (path thing angle ox oy) xout yout)).mapY=y.toBitVec)
    (nextCell : E1M1PathMap.Cell) (inMap : Collision.pathCellInside x y w h=true)
    (valid : nextCell.Valid words) (selectedCell : words[4+Collision.pathCellIndex x y w]?=some nextCell.offset)
    (nextData : Nat → LineData)
    (nextInput : E1M1NextCallbackReady.Data gun s lines (path thing angle ox oy).trace
      (E1M1DuplicateSuffix.tailCell nextCell) nextData)
    (traceSafe : ∀ a∈E1M1ThingGeometry.traceReads, E1M1FiringMapState.Safe (s.regs 4) lines a)
    (activeSafe : E1M1FiringMapState.Safe (s.regs 4) lines (0x2c024#32))
    (nextLayout : E1M1ScanContracts.Layout (s.regs 4) (base+BitVec.ofNat 32 (2*(nextCell.offset+1)))
      lines nextCell.ids.tail.length
      (E1M1ScanContracts.candidates (path thing angle ox oy).trace lines nextCell.ids.tail nextData))
    (budget : c.ids.length+nodes.length+nextCell.ids.tail.length≤128)
    (nextHead : Word)
    (headValue : load32 s.memory (links+(BitVec.ofNat 32 (Collision.pathCellIndex x y w) <<< 2))=nextHead)
    (nextSetup : ∀ a∈[(0x2c0f8#32),links+(BitVec.ofNat 32 (Collision.pathCellIndex x y w) <<< 2)],
      E1M1PathMapFiring.Safe gun s a)
    (nextSafe : ∀ a∈[(0x2c0f8#32),links+(BitVec.ofNat 32 (Collision.pathCellIndex x y w) <<< 2)],
      E1M1FiringMapState.Safe (s.regs 4) lines a) :
    let start := E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    ∃ after, E1M1FiringThings.sceneCell (path thing angle ox oy).trace world
      (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY
      (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input)=.ok after ∧
    let scan := E1M1NextLineScan.result start.core lines (path thing angle ox oy).trace
      (E1M1DuplicateSuffix.tailCell nextCell) nextData start.flags after
    let call := E1M1FiringNextThings.called scan.1
    let out := OriginalThingEntry.result call.core
    (∃ steps≤502+281*(c.ids.length+nextCell.ids.tail.length)+230*nodes.length,
      X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] steps
        ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    call.core.regs 0=x.toBitVec ∧ call.core.regs 2=y.toBitVec ∧
    OriginalThingEntry.head (OriginalThingEntry.guarded (OriginalThingEntry.entry call.core)).core=nextHead ∧
    (nextHead=0 → out.core.regs 0=(1#32) ∧ out.core.regs 4=s.regs 4-(112#32) ∧ out.pc=0x2cab1) ∧
    (nextHead≠0 → out.pc=0x2c5d2 ∧ out.core.regs 2=nextHead ∧ out.core.regs 4=s.regs 4-(120#32) ∧
      load32 out.core.memory (out.core.regs 4)=(0x2c720#32)) ∧
    OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) scan.2.collected 0 ∧
    Represents out.core.memory lines (load32 s.memory 0x13580+1)
      (OriginalLineVisits.markPrefix
        (E1M1ScanContracts.candidates (path thing angle ox oy).trace lines nextCell.ids.tail nextData)
        nextCell.ids.tail.length 0 (seenAfter (path thing angle ox oy).trace lines c data)) ∧
    (∃ added : List Collision.Intercept, scan.2.collected.toList=after.collected.toList++added) := by
  obtain ⟨⟨n,hn,prior⟩,items,pc,sp,mem,cursor,⟨after,production,bound,tracked⟩,represented,ready⟩ :=
    E1M1FiringNextGeometry.execution gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d stamps epochBefore epochAfter stampSetup fresh epochTail stampTail room world dimension ids scene locals f globalsSafe imageSafe notEnd x y mapX mapY nextCell inMap valid selectedCell nextData nextInput traceSafe activeSafe
  have entry := E1M1NextCursor.firing_cursor gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene locals globalsSafe imageSafe x y mapX mapY nextCell inMap valid selectedCell
  have address : (E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core.regs 2=
      base+BitVec.ofNat 32 (2*(nextCell.offset+1)) := by
    rw [cursor,entry,E1M1NextCursor.tail_address]
  have capacity := E1M1CellCapacity.suffix_reserve _ _ _ _ (c.ids.length+nodes.length)
    nextCell.ids.tail.length tracked budget
  obtain ⟨⟨m,hm,scan⟩,runs,collected,visits,frame,ordered⟩ :=
    E1M1NextLineScan.execution _ (s.regs 4) _ lines objects (path thing angle ox oy).trace
      (E1M1DuplicateSuffix.tailCell nextCell) nextData sp address items
      (E1M1NextCursor.tail_ids nextCell words valid) ready nextLayout stamps _ after capacity
      (load32 s.memory 0x13580+1) (seenAfter (path thing angle ox oy).trace lines c data)
      (E1M1FiringLineVisits.seen_size _ _ _ _) represented
  change m≤281*nextCell.ids.tail.length+7 at hm
  rw [OriginalPathXStep.at_pc _ _ pc] at scan runs
  have saved := E1M1NextSavedFrame.saved_words gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene
  have flagValue := E1M1NextSavedFrame.flag_word gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene
  have ret := E1M1NextLineReturn.parent_return _ (s.regs 4) _ lines objects (path thing angle ox oy).trace (E1M1DuplicateSuffix.tailCell nextCell) nextData sp address items (E1M1NextCursor.tail_ids nextCell words valid) ready nextLayout returns (E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).flags after capacity
  have flagAfter := E1M1NextLineReturn.flag_word _ (s.regs 4) _ lines objects (path thing angle ox oy).trace (E1M1DuplicateSuffix.tailCell nextCell) nextData sp address items (E1M1NextCursor.tail_ids nextCell words valid) ready nextLayout flag (E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).flags after capacity (by rw [mem]; exact flagValue)
  rw [mem,saved.1,saved.2] at ret
  have returnedPC : (E1M1NextLineScan.result _ lines (path thing angle ox oy).trace
      (E1M1DuplicateSuffix.tailCell nextCell) nextData (E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).flags after).1.pc=0x2ca94 := ret.2.2.2
  obtain ⟨⟨k,hk,call⟩,stop,stack,argX,argY,callback,returnWord,kept,history⟩ :=
    E1M1FiringNextThings.enter _ (s.regs 4) lines (load32 s.memory 0x13580+1) objects _ _ returnedPC ret.1 ret.2.1 flagAfter collected visits
      (returns.array _ (by simp [E1M1ScanReturn.returnWords]))
      (epochTail.caller 116 (by simp))
      (fun j hj => (stampTail j (by simpa only [OriginalLineVisitedRun.mark_size,E1M1FiringLineVisits.seen_size] using hj)).caller 116 (by simp))
  let scanResult := E1M1NextLineScan.result (E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core lines (path thing angle ox oy).trace
    (E1M1DuplicateSuffix.tailCell nextCell) nextData (E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).flags after
  let callState := E1M1FiringNextThings.called scanResult.1
  have coords := E1M1NextCoordinates.suffix_coordinates gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene locals x y mapX mapY
  have coordinate (axis : Bool) := E1M1NextCoordinates.scan_coordinate _ (s.regs 4) _ lines objects (path thing angle ox oy).trace (E1M1DuplicateSuffix.tailCell nextCell) nextData sp address items (E1M1NextCursor.tail_ids nextCell words valid) ready nextLayout (E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).flags after capacity axis
  have cx : callState.core.regs 0=x.toBitVec := argX.trans ((coordinate true).trans coords.1)
  have cy : callState.core.regs 2=y.toBitVec := argY.trans ((coordinate false).trans coords.2)
  have callAddress : scanResult.1.core.regs 4-(4#32)=s.regs 4-(116#32) := by
    rw [ret.2.1]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have read (a : Word) (setup : E1M1PathMapFiring.Safe gun s a)
      (safe : E1M1FiringMapState.Safe (s.regs 4) lines a) :
      load32 callState.core.memory a=load32 s.memory a := by
    have scanRead := E1M1NextLineReturn.read_word _ (s.regs 4) _ lines objects (path thing angle ox oy).trace (E1M1DuplicateSuffix.tailCell nextCell) nextData sp address items (E1M1NextCursor.tail_ids nextCell words valid) ready nextLayout (E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).flags after capacity a safe.scan
    rw [mem] at scanRead
    exact (OriginalPathCell.call_frame false scanResult.1.core _ a (by
      change Apart a (scanResult.1.core.regs 4-(4#32))
      rw [callAddress]; exact safe.caller 116 (by simp))).trans
      (scanRead.trans (E1M1NextCallbackMemory.firing_frame gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links nodes lookupSafe global selected objects d room world dimension ids scene a setup safe))
  have entryAddress : callState.core.regs 4-(4#32)=s.regs 4-(120#32) := by
    rw [stack]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have encoding : OriginalThingEntry.Inputs callState.core x y w h := by
    refine ⟨cx,cy,?_,?_,input.map.widthBound,input.map.heightBound,?_⟩
    · exact (read _ (input.map.globalsSafe _ (by simp)) (globalsSafe _ (by simp))).trans input.map.width
    · exact (read _ (input.map.globalsSafe _ (by simp)) (globalsSafe _ (by simp))).trans input.map.height
    · intro a ha
      rw [entryAddress]
      exact (globalsSafe a (by simpa using List.mem_append_left [0x2c100,0x2c10c,0x2c120] ha)).caller 120 (by simp)
  obtain ⟨⟨j,hj,lookup⟩,head,empty,nonempty,hits,visits⟩ :=
    E1M1NextThingLookup.execution callState (s.regs 4) lines (load32 s.memory 0x13580+1) objects _ _
      x y w h links nextHead stop stack callback returnWord encoding inMap
      ((read _ (nextSetup _ (by simp)) (nextSafe _ (by simp))).trans global)
      ((read _ (nextSetup _ (by simp)) (nextSafe _ (by simp))).trans headValue)
      ((nextSafe _ (by simp)).caller 120 (by simp))
      ((nextSafe _ (by simp)).caller 120 (by simp)) kept history
      (returns.array _ (by simp [E1M1ScanReturn.returnWords]))
      (epochTail.caller 120 (by simp))
      (fun j hj => (stampTail j (by simpa only [OriginalLineVisitedRun.mark_size,E1M1FiringLineVisits.seen_size] using hj)).caller 120 (by simp))
  exact ⟨after,production,⟨n+m+k+j,by omega,E1M1PspriteStep.prefix_trans
    (E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans prior scan) call) lookup⟩,
    cx,cy,head,empty,nonempty,hits,visits,ordered⟩
end Firing
end Doom.Proofs.E1M1FiringNextLookup
