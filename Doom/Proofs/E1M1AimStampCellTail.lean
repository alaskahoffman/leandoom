import Doom.Proofs.E1M1AimStampNextScan
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimStampCellTail
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanContracts (LineData)
open OriginalLineVisits (Represents stamp)
open E1M1FiringVisitedNext (TailSafe)
attribute [local irreducible] load32

/-- Actual object selection and list traversal preserve any word protected
from their own writes. Mutable line stamps need no separation from line writes. -/
theorem object_run (s : X86Control.State) (sp base lines epoch : Word) (words : Array Nat) (w h : Nat)
    (objects : Nat → Word) (trace : Collision.Divline) (cell : E1M1PathMap.Cell)
    (data : Nat → LineData) (nodes : List E1M1ThingList.Node) (r : Collision.PathResult) (seen : Array Bool)
    (pc : s.pc=0x2ca94) (success : s.core.regs 0=(1#32)) (stack : s.core.regs 4=sp-(112#32))
    (maps : E1M1CellMapInvariant.Image s.core.memory sp base lines words w h)
    (mapLayout : E1M1CellMapInvariant.Layout sp base lines words)
    (payload : E1M1CellSceneInvariant.Image s.core.memory lines trace cell data nodes)
    (payloadSafe : E1M1CellSceneInvariant.Protected sp lines cell data nodes)
    (contracts : E1M1CellSceneInvariant.Contracts sp lines trace cell data objects nodes)
    (x y : Int32) (mapX : s.core.regs 6=x.toBitVec) (mapY : s.core.regs 1=y.toBitVec)
    (inMap : Collision.pathCellInside x y w h=true) (links : Word)
    (selection : E1M1CellObjectSelection.Image s.core.memory links x y w nodes)
    (selectionSafe : E1M1CellObjectSelection.Protected sp lines links x y w)
    (tracked : OriginalLineCollection.Tracks s.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) r.collected 0)
    (capacity : r.collected.size+nodes.length≤128)
    (represented : Represents s.core.memory lines epoch seen)
    (returns : E1M1ScanReturn.ReturnSafe sp lines)
    (epochSafe : TailSafe sp (0x13580#32)) (stampSafe : ∀ j<seen.size, TailSafe sp (stamp lines j))
    (locals : E1M1GridLocals.Safe sp lines) :
    let out := E1M1CellObjectRun.result s nodes
    (∃ n≤31+230*nodes.length, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
    out.core.regs 0=(1#32) ∧ out.core.regs 4=sp-(112#32) ∧ out.pc=0x2cab1 ∧
    E1M1PathAdvance.observe out.core=E1M1PathAdvance.observe s.core ∧
    (∃ after, E1M1ThingList.collect trace nodes r=.ok after ∧
      OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) after.collected 0 ∧
      after.collected.size≤r.collected.size+nodes.length) ∧
    Represents out.core.memory lines epoch seen ∧
    (∀ a, TailSafe sp a → load32 out.core.memory a=load32 s.core.memory a) := by
  obtain ⟨⟨n,hn,enter⟩,callPC,callSP,cx,cy,callback,returnWord,hits,visits⟩ :=
    E1M1FiringNextThings.enter s sp lines epoch objects r.collected seen pc success stack maps.options tracked represented
      (returns.array _ (by simp [E1M1ScanReturn.returnWords])) (epochSafe.caller 116 (by simp))
      (fun j hj => (stampSafe j hj).caller 116 (by simp))
  let call := E1M1FiringNextThings.called s
  have address : call.core.regs 4-(4#32)=sp-(120#32) := by
    rw [callSP]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have read (a : Word) (safe : E1M1FiringMapState.Safe sp lines a) :
      load32 call.core.memory a=load32 s.core.memory a := by
    apply OriginalPathCell.call_frame false s.core _ a
    rw [stack]
    simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe.caller 116 (by simp)
  have encoding : OriginalThingEntry.Inputs call.core x y w h := by
    refine ⟨cx.trans mapX,cy.trans mapY,
      (read _ (mapLayout.globals _ (by simp))).trans maps.width,
      (read _ (mapLayout.globals _ (by simp))).trans maps.height,maps.widthBound,maps.heightBound,?_⟩
    intro a ha
    rw [address]
    apply (mapLayout.globals a ?_).caller 120 (by simp)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl <;> simp
  obtain ⟨⟨m,hm,lookup⟩,_,empty,nonempty,collected,history⟩ :=
    E1M1NextThingLookup.execution call sp lines epoch objects r.collected seen x y w h links
      (E1M1ThingList.head nodes) callPC callSP callback returnWord encoding inMap
      ((read _ selectionSafe.global).trans selection.global)
      ((read _ selectionSafe.selected).trans selection.selected)
      (selectionSafe.global.caller 120 (by simp)) (selectionSafe.selected.caller 120 (by simp)) hits visits
      (returns.array _ (by simp [E1M1ScanReturn.returnWords])) (epochSafe.caller 120 (by simp))
      (fun j hj => (stampSafe j hj).caller 120 (by simp))
  let entry := E1M1CellObjectSelection.result s
  have frame := E1M1CellObjectSelection.frame s sp lines stack
  have retained := E1M1CellSceneInvariant.transport _ _ sp lines trace cell data nodes payload payloadSafe frame
  have caller := E1M1CellObjectSelection.caller_word s sp stack
  have ready (present : E1M1ThingList.head nodes≠0) :
      E1M1ThingList.Image entry.core.memory (entry.core.regs 4) trace nodes (0x2cab1#32) ∧
      E1M1ThingList.Layout (entry.core.regs 4) trace (E1M1ThingFinish.resolve lines objects) nodes :=
    E1M1CellSceneInvariant.objects_ready entry.core sp lines trace cell data objects nodes retained contracts
      (nonempty present).2.2.1 (nonempty present).2.2.2 caller
  obtain ⟨⟨k,hk,run⟩,outSuccess,outStack,outPC,⟨after,production,outHits⟩,outHistory⟩ :=
    E1M1NextObjectTraversal.execution entry sp lines epoch objects trace nodes r seen
      contracts.objects.nonzero empty nonempty ready collected capacity history epochSafe.objects
      (fun j hj => (stampSafe j hj).objects)
  have keep := E1M1ObjectBoundary.preserved entry sp lines objects trace nodes r
    contracts.objects.nonzero empty nonempty ready collected capacity
  have numeric := (E1M1ObjectBoundary.observe entry sp lines objects trace nodes r
    contracts.objects.nonzero empty nonempty ready collected capacity locals).trans
    (E1M1CellObjectSelection.observe s sp stack)
  exact ⟨⟨n+m+k,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans enter lookup) run⟩,
    outSuccess,outStack,outPC,numeric,⟨after,production,outHits,E1M1CellCapacity.collect_bound trace nodes r after production⟩,
    outHistory,fun a safe => (keep.2.2 a safe.objects).trans (E1M1CellObjectSelection.read_word s sp stack a
      (safe.caller 116 (by simp)) (safe.caller 120 (by simp)))⟩

/-- Join that exact frame to the numeric grid step and retain the stamp image. -/
theorem advance (s : X86Control.State) (sp base lines epoch : Word) (words : Array Nat) (w h : Nat)
    (objects : Nat → Word) (trace : Collision.Divline) (cell : E1M1PathMap.Cell)
    (data : Nat → LineData) (nodes : List E1M1ThingList.Node) (r : Collision.PathResult) (seen : Array Bool)
    (pc : s.pc=0x2ca94) (success : s.core.regs 0=(1#32)) (stack : s.core.regs 4=sp-(112#32))
    (maps : E1M1CellMapInvariant.Image s.core.memory sp base lines words w h)
    (mapLayout : E1M1CellMapInvariant.Layout sp base lines words)
    (payload : E1M1CellSceneInvariant.Image s.core.memory lines trace cell data nodes)
    (payloadSafe : E1M1CellSceneInvariant.Protected sp lines cell data nodes)
    (contracts : E1M1CellSceneInvariant.Contracts sp lines trace cell data objects nodes)
    (x y : Int32) (mapX : s.core.regs 6=x.toBitVec) (mapY : s.core.regs 1=y.toBitVec)
    (inMap : Collision.pathCellInside x y w h=true) (links : Word)
    (selection : E1M1CellObjectSelection.Image s.core.memory links x y w nodes)
    (selectionSafe : E1M1CellObjectSelection.Protected sp lines links x y w)
    (tracked : OriginalLineCollection.Tracks s.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) r.collected 0)
    (capacity : r.collected.size+nodes.length≤128)
    (represented : Represents s.core.memory lines epoch seen)
    (returns : E1M1ScanReturn.ReturnSafe sp lines)
    (epochSafe : TailSafe sp (0x13580#32)) (stampSafe : ∀ j<seen.size, TailSafe sp (stamp lines j))
    (locals : E1M1GridLocals.Safe sp lines)
    (world : Collision.Scene) (dimension : world.grid.width=w)
    (ids : world.links[Collision.pathCellIndex x y w]?=some (nodes.map E1M1ThingList.Node.id).toArray)
    (scene : ∀ node∈nodes, world.things[node.id]?=some node.target)
    (origin : Memory) (image : E1M1AimStampImage.Image origin s.core.memory lines epoch seen) :
    let out := E1M1CellObjectAdvance.result s nodes
    (∃ n≤52+230*nodes.length, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
    out.core.regs 4=sp-(112#32) ∧
    E1M1PathAdvance.observe out.core=E1M1PathAdvance.step (E1M1PathAdvance.observe s.core) ∧
    out.pc=E1M1PathAdvance.nextPc (E1M1PathAdvance.observe s.core) ∧
    (∃ after, E1M1FiringThings.sceneCell trace world x y r=.ok after ∧
      after.collected.size≤r.collected.size+nodes.length ∧
      OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1ThingFinish.resolve lines objects)
        after.collected (128-(r.collected.size+nodes.length))) ∧
    Represents out.core.memory lines epoch seen ∧
    E1M1CellMapInvariant.Image out.core.memory sp base lines words w h ∧
    E1M1CellSceneInvariant.Image out.core.memory lines trace cell data nodes ∧
    E1M1CellObjectSelection.Image out.core.memory links x y w nodes ∧
    E1M1CellMapInvariant.Frame sp lines s.core.memory out.core.memory ∧
    (∀ a, TailSafe sp a → load32 out.core.memory a=load32 s.core.memory a) ∧
    E1M1AimStampImage.Image origin out.core.memory lines epoch seen := by
  obtain ⟨⟨n,hn,run⟩,ok,sp',pc',numeric,⟨after,production,collected,bound⟩,history,tailFrame⟩ :=
    object_run s sp base lines epoch words w h objects trace cell data nodes r seen pc success stack maps mapLayout payload payloadSafe contracts x y mapX mapY inMap links selection selectionSafe tracked capacity represented returns epochSafe stampSafe locals
  obtain ⟨⟨k,hk,advance⟩,finalSP,obs,nextPC,hits,visits⟩ :=
    E1M1CellBoundaryAdvance.execution _ sp lines epoch objects (E1M1PathAdvance.observe s.core)
      after.collected seen ⟨pc',ok,sp',numeric,collected,history⟩ locals epochSafe.advance
      (fun j hj => (stampSafe j hj).advance)
  have exactFrame (a : Word) (safe : TailSafe sp a) :
      load32 (E1M1CellObjectAdvance.result s nodes).core.memory a=load32 s.core.memory a :=
    (E1M1CellBoundaryAdvance.frame _ sp sp' a safe.advance).trans (tailFrame a safe)
  have exactImage := E1M1AimStampImage.transport origin _ _ lines epoch seen image
    (exactFrame _ epochSafe) (fun j hj => exactFrame _ (stampSafe j hj))
  have complete : E1M1CellMapInvariant.Frame sp lines s.core.memory (E1M1CellObjectAdvance.result s nodes).core.memory :=
    fun a safe => exactFrame a ⟨safe.caller,safe.objects,safe.advance⟩
  have reserved := E1M1CellCapacity.reserve _ _ _ _ _ hits bound capacity
  refine ⟨⟨n+k,by omega,E1M1PspriteStep.prefix_trans run advance⟩,finalSP,obs,nextPC,
    ⟨after,?_,bound,reserved⟩,visits,
    E1M1CellMapInvariant.transport _ _ sp base lines words w h maps mapLayout complete,
    E1M1CellSceneInvariant.transport _ _ sp lines trace cell data nodes payload payloadSafe complete,
    E1M1CellObjectSelection.transport _ _ sp lines links x y w nodes selection selectionSafe complete,complete,exactFrame,exactImage⟩
  rw [E1M1FiringThings.scene_cell trace world x y w nodes r dimension ids,
    E1M1ThingTraversal.objectCell_collect trace world.things nodes r scene]
  exact production
end Doom.Proofs.E1M1AimStampCellTail
