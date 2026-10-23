import Doom.Proofs.E1M1CellObjectRun
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1CellObjectAdvance
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanContracts (LineData)
open OriginalLineVisits (Represents stamp)
open E1M1FiringVisitedNext (TailSafe)
attribute [local irreducible] load32

def result (s : X86Control.State) (nodes : List E1M1ThingList.Node) :=
  E1M1CellBoundaryAdvance.result (E1M1CellObjectRun.result s nodes)

/-- The reusable object half of a cell joins actual selection, full traversal,
caller success and the original numeric advance. Persistent images, mutable
history and the proved remaining reserve accompany the actual production hits.
The line phase and repeated-cell induction remain separate obligations. -/
theorem execution (s : X86Control.State) (sp base lines epoch : Word) (words : Array Nat) (w h : Nat)
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
    (scene : ∀ node∈nodes, world.things[node.id]?=some node.target) :
    let out := result s nodes
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
    E1M1CellMapInvariant.Frame sp lines s.core.memory out.core.memory := by
  obtain ⟨⟨n,hn,run⟩,ok,sp',pc',numeric,⟨after,production,collected,bound⟩,history,frame⟩ :=
    E1M1CellObjectRun.execution s sp base lines epoch words w h objects trace cell data nodes r seen pc success stack maps mapLayout payload payloadSafe contracts x y mapX mapY inMap links selection selectionSafe tracked capacity represented returns epochSafe stampSafe locals
  obtain ⟨⟨k,hk,advance⟩,finalSP,obs,nextPC,hits,visits⟩ :=
    E1M1CellBoundaryAdvance.execution _ sp lines epoch objects (E1M1PathAdvance.observe s.core)
      after.collected seen ⟨pc',ok,sp',numeric,collected,history⟩ locals epochSafe.advance
      (fun j hj => (stampSafe j hj).advance)
  have complete : E1M1CellMapInvariant.Frame sp lines s.core.memory (result s nodes).core.memory :=
    fun a safe => (E1M1CellBoundaryAdvance.frame _ sp sp' a safe.advance).trans (frame a safe)
  have reserved := E1M1CellCapacity.reserve _ _ _ _ _ hits bound capacity
  refine ⟨⟨n+k,by omega,E1M1PspriteStep.prefix_trans run advance⟩,finalSP,obs,nextPC,
    ⟨after,?_,bound,reserved⟩,visits,
    E1M1CellMapInvariant.transport _ _ sp base lines words w h maps mapLayout complete,
    E1M1CellSceneInvariant.transport _ _ sp lines trace cell data nodes payload payloadSafe complete,
    E1M1CellObjectSelection.transport _ _ sp lines links x y w nodes selection selectionSafe complete,complete⟩
  rw [E1M1FiringThings.scene_cell trace world x y w nodes r dimension ids,
    E1M1ThingTraversal.objectCell_collect trace world.things nodes r scene]
  exact production
end Doom.Proofs.E1M1CellObjectAdvance
