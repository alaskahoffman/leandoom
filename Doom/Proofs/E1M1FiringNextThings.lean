import Doom.Proofs.E1M1NextSavedFrame
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1FiringNextThings
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open E1M1ThingListInputs (before)
open E1M1FiringGridState (initial)
open E1M1FiringLineVisits (seenAfter)
open E1M1FiringVisitedNext (TailSafe)
open OriginalLineVisits (Represents stamp)
attribute [local irreducible] load32 Collision.pathFirstIntercept


def called (s : X86Control.State) := OriginalPathCell.called false s.core (OriginalPathCell.gateFlags false s.core)

/-- Execute the success test and enabled object CALL, retaining mixed hits and
visit stamps across the real return-address store. No object body runs here. -/
theorem enter (s : X86Control.State) (sp lines epoch : Word) (objects : Nat → Word)
    (hits : Array Collision.Intercept) (seen : Array Bool)
    (pc : s.pc=0x2ca94) (success : s.core.regs 0=(1#32))
    (stack : s.core.regs 4=sp-(112#32))
    (flag : load32 s.core.memory (E1M1ThingGate.flagWord sp)=(3#32))
    (tracked : OriginalLineCollection.Tracks s.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) hits 0)
    (represented : Represents s.core.memory lines epoch seen)
    (array : OriginalLineMixedInvariant.ArraySafe 0x2ba20 (sp-(116#32)))
    (epochSafe : Apart (0x13580#32) (sp-(116#32)))
    (stampSafe : ∀ j<seen.size, Apart (stamp lines j) (sp-(116#32))) :
    (∃ n≤8, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s (called s)) ∧
    (called s).pc=0x2c5a0 ∧ (called s).core.regs 4=sp-(116#32) ∧
    (called s).core.regs 0=s.core.regs 6 ∧ (called s).core.regs 2=s.core.regs 1 ∧
    (called s).core.regs 3=(0x2c720#32) ∧
    load32 (called s).core.memory ((called s).core.regs 4)=(0x2cab1#32) ∧
    OriginalLineCollection.Tracks (called s).core 0x2ba20 (E1M1ThingFinish.resolve lines objects) hits 0 ∧
    Represents (called s).core.memory lines epoch seen := by
  have contains (pc : Nat) (h : OriginalPathCell.program pc≠none) :
      E1M1FiringAdvance.program pc=OriginalPathCell.program pc := by
    have a := E1M1ScanReturn.contains_dispatch pc h
    exact (E1M1NextLineScan.contains_scan pc (by rw [a]; exact h)).trans a
  have resumed := (OriginalPathCell.resume_execution true s.core s.flags).transfer
    E1M1FiringAdvance.program [] contains (by simp)
  change X86Routine.Prefix _ [] 2 ⟨s.core,s.flags,0x2ca94⟩ _ at resumed
  rw [OriginalPathXStep.at_pc _ _ pc] at resumed
  have on : OriginalPathCell.enabled false s.core=true := by
    have byte := congrArg (fun v : Word => v.extractLsb' 0 8) flag
    rw [E1M1PathCell.low_byte] at byte
    unfold OriginalPathCell.enabled OriginalPathCell.optionBits
    rw [stack]
    have addr : sp-(112#32)+(64#32)=E1M1ThingGate.flagWord sp := by
      simp [E1M1ThingGate.flagWord,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    change (s.core.memory (sp-(112#32)+(64#32)) &&& (2#8) != 0)=true
    rw [addr,byte]; decide
  have stop : (OriginalPathCell.resumed true s.core).pc=0x2ca9c := by
    simp [OriginalPathCell.resumed,OriginalPathCell.skipPc,success]
  obtain ⟨n,hn,tail⟩ := OriginalPathCell.enter_execution false s.core (OriginalPathCell.resumed true s.core).flags
  simp only [OriginalPathCell.enter,on,↓reduceIte] at tail
  change X86Routine.Prefix _ [] n ⟨(OriginalPathCell.resumed true s.core).core,(OriginalPathCell.resumed true s.core).flags,0x2ca9c⟩ _ at tail
  rw [OriginalPathXStep.at_pc _ _ stop] at tail
  have addr : s.core.regs 4-(4#32)=sp-(116#32) := by rw [stack]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have obs := OriginalPathCell.call_inputs false s.core (OriginalPathCell.gateFlags false s.core)
  have keep (a : Word) (safe : Apart a (sp-(116#32))) : load32 (called s).core.memory a=load32 s.core.memory a :=
    OriginalPathCell.call_frame false s.core _ a (by change Apart a (s.core.regs 4-(4#32)); rw [addr]; exact safe)
  refine ⟨⟨2+n,by omega,E1M1PspriteStep.prefix_trans (X86CodeMemory.lift_success resumed FloorCaller.cm)
    (X86CodeMemory.lift_success (tail.transfer _ [] contains (by simp)) FloorCaller.cm)⟩,
    obs.2.2.2.2.2,obs.2.2.2.1.trans addr,obs.1,obs.2.1,obs.2.2.1,?_,
    E1M1ThingGate.call_collection s.core _ _ _ _ 0 tracked (by rw [addr]; exact array),?_⟩
  · change load32 (called s).core.memory ((called s).core.regs 4)=_
    unfold called
    rw [obs.2.2.2.1]; exact obs.2.2.2.2.1
  · exact ⟨(keep _ epochSafe).trans represented.1,fun j hj => by rw [keep _ (stampSafe j hj)]; exact represented.2 j hj⟩

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
/-- Continuous firing now returns from the second line list, passes the success
and enable tests, and enters the actual object iterator. Its table lookup and
callback body remain separate, as does identifying the retained coordinates. -/
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
    (budget : c.ids.length+nodes.length+nextCell.ids.tail.length≤128) :
    let start := E1M1FiringNextSuffix.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes
    ∃ after, E1M1FiringThings.sceneCell (path thing angle ox oy).trace world
      (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY
      (before gun s weapon actor thing angle ox oy xout yout base lines words c w h data input)=.ok after ∧
    let scan := E1M1NextLineScan.result start.core lines (path thing angle ox oy).trace
      (E1M1DuplicateSuffix.tailCell nextCell) nextData start.flags after
    let out := called scan.1
    (∃ steps≤482+281*(c.ids.length+nextCell.ids.tail.length)+230*nodes.length,
      X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] steps
        ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    scan.1.core.regs 0=(1#32) ∧ scan.1.pc=0x2ca94 ∧
    scan.1.core.regs 7=(E1M1NextCellMemory.advanced (E1M1FiringCellReturn.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input nodes).core).regs 7 ∧
    out.pc=0x2c5a0 ∧ out.core.regs 4=s.regs 4-(116#32) ∧
    out.core.regs 0=scan.1.core.regs 6 ∧ out.core.regs 2=scan.1.core.regs 1 ∧ out.core.regs 3=(0x2c720#32) ∧
    load32 out.core.memory (out.core.regs 4)=(0x2cab1#32) ∧
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
    enter _ (s.regs 4) lines (load32 s.memory 0x13580+1) objects _ _ returnedPC ret.1 ret.2.1 flagAfter collected visits
      (returns.array _ (by simp [E1M1ScanReturn.returnWords]))
      (epochTail.caller 116 (by simp))
      (fun j hj => (stampTail j (by simpa only [OriginalLineVisitedRun.mark_size,E1M1FiringLineVisits.seen_size] using hj)).caller 116 (by simp))
  exact ⟨after,production,⟨n+m+k,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans prior scan) call⟩,
    ret.1,returnedPC,ret.2.2.1,stop,stack,argX,argY,callback,returnWord,kept,history,ordered⟩
end Firing
end Doom.Proofs.E1M1FiringNextThings
