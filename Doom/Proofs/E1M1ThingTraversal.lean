import Doom.Proofs.E1M1ThingList
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.E1M1ThingTraversal
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ThingList (Node Layout Image head collect run)
abbrev program := E1M1ThingList.program

def result (s : X86Control.State) (count : Nat) := OriginalThingEntry.returned (run count s).core

theorem return_observe (s : X86Memory.State) :
    (OriginalThingEntry.returned s).core.memory=s.memory ∧
    (OriginalThingEntry.returned s).core.regs 0=(1#32) ∧
    (OriginalThingEntry.returned s).core.regs 4=s.regs 4+(8#32) ∧
    (OriginalThingEntry.returned s).pc=(load32 s.memory (s.regs 4+(4#32))).toNat := by
  simp [OriginalThingEntry.returned,OriginalThingEntry.r2,OriginalThingEntry.r1,put,write]

/-- Execute every node and the real iterator epilogue, returning success to the
saved caller address. Empty lists take the same three-instruction epilogue. -/
theorem execution (s : X86Control.State) (trace : Collision.Divline)
    (resolve : Collision.Intercept → Word) (nodes : List E1M1ThingList.Node) (ret : Word)
    (layout : Layout (s.core.regs 4) trace resolve nodes)
    (image : Image s.core.memory (s.core.regs 4) trace nodes ret)
    (cursor : s.core.regs 2=head nodes)
    (pc : s.pc=if head nodes=(0#32) then 0x2c5e2 else 0x2c5d2)
    (r : Collision.PathResult) (tracked : OriginalLineCollection.Tracks s.core 0x2ba20 resolve r.collected 0)
    (capacity : r.collected.size+nodes.length≤128) :
    let out := result s nodes.length
    (∃ n≤230*nodes.length+3, X86CodeMemory.Prefix FloorCaller.cm program [] n s out) ∧
    out.core.regs 0=(1#32) ∧ out.core.regs 4=s.core.regs 4+(8#32) ∧ out.pc=ret.toNat ∧
    (∃ after, collect trace nodes r=.ok after ∧ OriginalLineCollection.Tracks out.core 0x2ba20 resolve after.collected 0) := by
  obtain ⟨⟨n,hn,prior⟩,sp,_,atReturn,imageOut,after,production,trackedOut⟩ :=
    E1M1ThingList.execution s trace resolve nodes ret layout image cursor pc r tracked capacity
  have tail := OriginalThingEntry.return_execution (run nodes.length s).core (run nodes.length s).flags
  rw [OriginalPathXStep.at_pc _ _ atReturn] at tail
  have obs := return_observe (run nodes.length s).core
  refine ⟨⟨n+3,by omega,X86CodeMemory.lift_success
    (OriginalGroupBounds.prefix_join prior (tail.transfer program [] E1M1ThingVisit.contains_iterator (by simp))) FloorCaller.cm⟩,
    obs.2.1,obs.2.2.1.trans (by rw [sp]),?_,after,production,?_⟩
  · exact obs.2.2.2.trans (by rw [sp,imageOut.caller])
  · refine ⟨?_,?_,trackedOut.room⟩
    · change OriginalLineFinish.Encodes (OriginalThingEntry.returned (run nodes.length s).core).core.memory _ _ _
      rw [obs.1]; exact trackedOut.encoded
    · change load32 (OriginalThingEntry.returned (run nodes.length s).core).core.memory (0x2c028#32)=_
      rw [obs.1]; exact trackedOut.cursor

/-- The recursive collector is the ordinary monadic left fold: order is retained,
including equal-fraction hits. -/
theorem collect_fold (trace : Collision.Divline) (nodes : List E1M1ThingList.Node) (r : Collision.PathResult) :
    collect trace nodes r=nodes.foldlM (fun r node => E1M1ThingFinish.collect trace node.target node.id r) r := by
  induction nodes generalizing r with
  | nil => rfl
  | cons node rest ih =>
    simp only [collect,List.foldlM_cons]
    congr 1
    funext after
    exact ih after

/-- This loop uses the same object lookup, intersection and append operations as
Path.pathTraverse's object-cell loop. The outer cell walk is not proved here. -/
def objectCell (trace : Collision.Divline) (things : Array Collision.SolidThing)
    (ids : Array Nat) (r : Collision.PathResult) : Except String Collision.PathResult := do
  let mut result := r
  for id in ids do
    let some target := things[id]? | throw "path: invalid actor link"
    if let some frac ← Collision.thingIntercept trace target then
      result ← Collision.appendIntercept result ⟨frac,false,id⟩
  return result

theorem objectCell_collect (trace : Collision.Divline) (things : Array Collision.SolidThing)
    (nodes : List E1M1ThingList.Node) (r : Collision.PathResult)
    (lookup : ∀ node∈nodes, things[node.id]?=some node.target) :
    objectCell trace things (nodes.map E1M1ThingList.Node.id).toArray r=E1M1ThingList.collect trace nodes r := by
  unfold objectCell
  simp only [List.forIn_toArray,List.forIn_map,bind_pure]
  induction nodes generalizing r with
  | nil => rfl
  | cons node rest ih =>
    simp only [List.forIn_cons,E1M1ThingList.collect,lookup node (by simp)]
    unfold E1M1ThingFinish.collect
    cases hitEq : Collision.thingIntercept trace node.target with
    | error e => rfl
    | ok value =>
      cases value with
      | none => exact ih r (fun n hn => lookup n (by simp [hn]))
      | some frac =>
        simp only [Bind.bind,Except.bind]
        cases app : Collision.appendIntercept r ⟨frac,false,node.id⟩ with
        | error e => rfl
        | ok after => exact ih after (fun n hn => lookup n (by simp [hn]))

/-- The final collection agrees with the actual lookup/intersection/append loop,
under the scene-ID encoding. No sorting or deduplication is introduced. -/
theorem execution_cell (s : X86Control.State) (trace : Collision.Divline)
    (resolve : Collision.Intercept → Word) (nodes : List E1M1ThingList.Node) (ret : Word)
    (layout : Layout (s.core.regs 4) trace resolve nodes)
    (image : Image s.core.memory (s.core.regs 4) trace nodes ret)
    (cursor : s.core.regs 2=head nodes)
    (pc : s.pc=if head nodes=(0#32) then 0x2c5e2 else 0x2c5d2)
    (r : Collision.PathResult) (tracked : OriginalLineCollection.Tracks s.core 0x2ba20 resolve r.collected 0)
    (capacity : r.collected.size+nodes.length≤128)
    (things : Array Collision.SolidThing) (lookup : ∀ node∈nodes, things[node.id]?=some node.target) :
    let out := result s nodes.length
    (∃ n≤230*nodes.length+3, X86CodeMemory.Prefix FloorCaller.cm program [] n s out) ∧
    out.core.regs 0=(1#32) ∧ out.core.regs 4=s.core.regs 4+(8#32) ∧ out.pc=ret.toNat ∧
    (∃ after, objectCell trace things (nodes.map E1M1ThingList.Node.id).toArray r=.ok after ∧
      OriginalLineCollection.Tracks out.core 0x2ba20 resolve after.collected 0) := by
  rw [objectCell_collect trace things nodes r lookup]
  exact execution s trace resolve nodes ret layout image cursor pc r tracked capacity
end Doom.Proofs.E1M1ThingTraversal
