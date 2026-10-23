import Doom.Proofs.E1M1TraversalSource
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1TraversalLineJoin
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanContracts (LineData candidates)
open E1M1NextCallbackReady (Ready)
open OriginalLineVisits (Represents markPrefix)
attribute [local irreducible] load32
section Scan
variable (s : X86Memory.State) (sp cursor lines : Word) (objects : Nat → Word)
    (trace : Collision.Divline) (c : E1M1PathMap.Cell) (data : Nat → LineData)
    (stack : s.regs 4=sp-(124#32)) (list : s.regs 2=cursor)
    (items : E1M1PathMapLookup.ScanWords s lines c)
    (ids : ∀ i : Fin c.ids.length, c.ids[i.val]<475)
    (ready : Ready s lines trace c data)
    (layout : E1M1ScanContracts.Layout sp cursor lines c.ids.length (candidates trace lines c.ids data))
    (stamps : E1M1ScanContracts.Stamps sp lines) (f : Option Flags)
    (r : Collision.PathResult)
    (tracked : OriginalLineCollection.Tracks s 0x2ba20 (E1M1ThingFinish.resolve lines objects) r.collected c.ids.length)
    (epoch : Word) (seen : Array Bool) (size : seen.size=475)
    (represented : Represents s.memory lines epoch seen)
    (sceneLines : Array Collision.Line)
    (lookup : ∀ i : Fin c.ids.length, sceneLines[c.ids[i.val]]?=some (data i.val).line)
include stack list items ids ready layout stamps tracked size represented lookup

/-- Join the authenticated DOS scan to the callback interface of `live_aiming`.
The same source collector is now connected to the complete live traversal;
this remains a per-cell machine theorem, not a complete-query machine proof. -/
theorem execution :
    let out := E1M1NextLineScan.result s lines trace c data f r
    (∃ steps≤281*c.ids.length+7, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] steps
      ⟨s,f,0x2c57f⟩ out.1) ∧
    E1M1TraversalSource.aimingScan trace sceneLines c.ids.toArray seen r=.ok
      (none,out.2,markPrefix (candidates trace lines c.ids data) c.ids.length 0 seen) ∧
    OriginalLineCollection.Tracks out.1.core 0x2ba20 (E1M1ThingFinish.resolve lines objects) out.2.collected 0 ∧
    Represents out.1.core.memory lines epoch (markPrefix (candidates trace lines c.ids data) c.ids.length 0 seen) := by
  have joined := E1M1LineSourceScan.execution s sp cursor lines objects trace c data stack list items ids ready layout stamps f r tracked epoch seen size represented sceneLines lookup
  refine ⟨joined.1,?_,joined.2.2⟩
  unfold E1M1TraversalSource.aimingScan
  rw [joined.2.1]
  rfl
end Scan
end Doom.Proofs.E1M1TraversalLineJoin
