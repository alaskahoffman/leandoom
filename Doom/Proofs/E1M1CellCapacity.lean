import Doom.Proofs.E1M1DuplicateSuffix
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.E1M1CellCapacity
open Verification X86 X86Memory X86Control BlockSummary

/-- Count possible appends over the complete object list. Rejected intersections
consume no capacity; an error supplies no successful output to this theorem. -/
theorem collect_bound (trace : Collision.Divline) (nodes : List E1M1ThingList.Node)
    (r after : Collision.PathResult) (ok : E1M1ThingList.collect trace nodes r=.ok after) :
    after.collected.size≤r.collected.size+nodes.length := by
  induction nodes generalizing r with
  | nil =>
    change Except.ok r=Except.ok after at ok
    cases ok; simp
  | cons node rest ih =>
    cases next : E1M1ThingFinish.collect trace node.target node.id r with
    | error e => simp [E1M1ThingList.collect,next,Bind.bind,Except.bind] at ok
    | ok middle =>
      have tail : E1M1ThingList.collect trace rest middle=.ok after := by
        simpa [E1M1ThingList.collect,next,Bind.bind,Except.bind] using ok
      have one := E1M1ThingList.collect_size trace node.target node.id r middle next
      have more := ih middle tail
      simp only [List.length_cons]
      omega

/-- Relate the size bound to the scene-cell result already returned by the
continuous firing proof, with the original object-ID order. -/
theorem scene_bound (trace : Collision.Divline) (world : Collision.Scene) (x y : Int32)
    (width : Nat) (nodes : List E1M1ThingList.Node) (r after : Collision.PathResult)
    (dimension : world.grid.width=width)
    (ids : world.links[Collision.pathCellIndex x y width]?=some (nodes.map E1M1ThingList.Node.id).toArray)
    (scene : ∀ node∈nodes, world.things[node.id]?=some node.target)
    (ok : E1M1FiringThings.sceneCell trace world x y r=.ok after) :
    after.collected.size≤r.collected.size+nodes.length := by
  rw [E1M1FiringThings.scene_cell trace world x y width nodes r dimension ids,
    E1M1ThingTraversal.objectCell_collect trace world.things nodes r scene] at ok
  exact collect_bound trace nodes r after ok

/-- A proved upper bound supplies conservative remaining capacity. This does
not derive more room from a zero-reserve collection invariant alone. -/
theorem reserve (s : X86Memory.State) (base : Word) (resolve : Collision.Intercept → Word)
    (hits : Array Collision.Intercept) (limit : Nat)
    (tracked : OriginalLineCollection.Tracks s base resolve hits 0)
    (bound : hits.size≤limit) (room : limit≤128) :
    OriginalLineCollection.Tracks s base resolve hits (128-limit) := by
  exact ⟨tracked.encoded,tracked.cursor,by omega⟩

/-- A two-cell candidate budget is a sufficient initial condition for the
remaining next-cell line scan. It is not a traversal-wide capacity proof. -/
theorem suffix_reserve (s : X86Memory.State) (base : Word) (resolve : Collision.Intercept → Word)
    (hits : Array Collision.Intercept) (limit remaining : Nat)
    (tracked : OriginalLineCollection.Tracks s base resolve hits (128-limit))
    (budget : limit+remaining≤128) :
    OriginalLineCollection.Tracks s base resolve hits remaining := by
  exact ⟨tracked.encoded,tracked.cursor,by have := tracked.room; omega⟩
end Doom.Proofs.E1M1CellCapacity
