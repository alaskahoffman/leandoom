import Doom.Proofs.E1M1NextCallbackMemory
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1NextCallbackReady
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (Geometry SideSafe linePointer)
open E1M1ScanContracts (LineData candidate)
open OriginalLineMixedInvariant (atIndex)
attribute [local irreducible] load32

/-- Immutable line data and address separation at the original firing boundary.
Indices refer to the remaining list, after consuming the leading duplicate. -/
structure Data (gun : Fire.Gun) (s : X86Memory.State) (lines : Word)
    (trace : Collision.Divline) (c : E1M1PathMap.Cell) (data : Nat → LineData) : Prop where
  encoded : ∀ i : Fin c.ids.length, E1M1ScanMemory.LineWords s.memory (data i.val).line
    (linePointer lines c.ids[i.val]) (data i.val).v (data i.val).w
  setup : ∀ i : Fin c.ids.length, ∀ a∈E1M1ScanMemory.lineReads (linePointer lines c.ids[i.val]) (data i.val).v (data i.val).w,
    E1M1PathMapFiring.Safe gun s a
  safe : ∀ i : Fin c.ids.length, ∀ a∈E1M1ScanMemory.lineReads (linePointer lines c.ids[i.val]) (data i.val).v (data i.val).w,
    E1M1FiringMapState.Safe (s.regs 4) lines a
  back : ∀ i : Fin c.ids.length, load32 s.memory (linePointer lines c.ids[i.val]+50)=0 ↔ (data i.val).line.back.isNone=true
  backSetup : ∀ i : Fin c.ids.length, E1M1PathMapFiring.Safe gun s (linePointer lines c.ids[i.val]+50)
  backSafe : ∀ i : Fin c.ids.length, E1M1FiringMapState.Safe (s.regs 4) lines (linePointer lines c.ids[i.val]+50)
  callback : ∀ i : Fin c.ids.length, ∀ a∈OriginalLineSecondPoint.reads (linePointer lines c.ids[i.val]) (data i.val).v (data i.val).w,
    SideSafe (s.regs 4) a
  computed : ∀ i : Fin c.ids.length,
    OriginalLineSecondPoint.firstSide trace (data i.val).line≠OriginalLineSecondPoint.lastSide trace (data i.val).line →
    Collision.interceptVector trace ⟨(data i.val).line.x,(data i.val).line.y,(data i.val).line.dx,(data i.val).line.dy⟩=.ok (data i.val).frac

/-- Callback templates at the reached suffix. The scan invariant must still
transport them through earlier candidates before each actual callback runs. -/
structure Ready (s : X86Memory.State) (lines : Word) (trace : Collision.Divline)
    (c : E1M1PathMap.Cell) (data : Nat → LineData) : Prop where
  target : load32 s.memory (s.regs 4)=(0x2c5f0#32)
  active : load32 s.memory (0x2c024#32)=0
  geometry : ∀ i : Fin c.ids.length, Geometry (OriginalLineDispatch.view (atIndex s i.val))
    trace (data i.val).line (linePointer lines c.ids[i.val]) (data i.val).v (data i.val).w
  back : ∀ i : Fin c.ids.length, load32 s.memory (linePointer lines c.ids[i.val]+50)=0 ↔ (data i.val).line.back.isNone=true
  computed : ∀ i : Fin c.ids.length,
    OriginalLineSecondPoint.firstSide trace (data i.val).line≠OriginalLineSecondPoint.lastSide trace (data i.val).line →
    Collision.interceptVector trace ⟨(data i.val).line.x,(data i.val).line.y,(data i.val).line.dx,(data i.val).line.dy⟩=.ok (data i.val).frac
  storage : ∀ i : Fin c.ids.length, OriginalLineCollection.Layout (atIndex s i.val) 0x2ba20

/-- The same readiness supplies the original same-side rejection callback. -/
theorem rejection (s : X86Memory.State) (lines : Word) (trace : Collision.Divline)
    (c : E1M1PathMap.Cell) (data : Nat → LineData) (ready : Ready s lines trace c data)
    (i : Fin c.ids.length)
    (same : (candidate trace lines c.ids[i.val] (data i.val)).crosses=false) :
    OriginalLineReject.Inputs (OriginalLineDispatch.view (atIndex s i.val)) trace
      (data i.val).line (linePointer lines c.ids[i.val]) (data i.val).v (data i.val).w := by
  apply E1M1ScanGeometry.rejection_inputs _ _ _ _ _ _ (ready.geometry i)
  simpa [candidate] using same

/-- Crossings use the production fraction and the initialized autoaim flags. -/
theorem crossing (s : X86Memory.State) (lines : Word) (trace : Collision.Divline)
    (c : E1M1PathMap.Cell) (data : Nat → LineData) (ready : Ready s lines trace c data)
    (i : Fin c.ids.length)
    (crosses : (candidate trace lines c.ids[i.val] (data i.val)).crosses=true) :
    OriginalLineMixedInvariant.Crossing (atIndex s i.val) (candidate trace lines c.ids[i.val] (data i.val)) := by
  have ne : OriginalLineSecondPoint.firstSide trace (data i.val).line≠OriginalLineSecondPoint.lastSide trace (data i.val).line := by
    simpa [candidate] using crosses
  refine ⟨E1M1ScanGeometry.crossing_inputs _ _ _ _ _ _ (ready.geometry i) ne,ready.computed i ne,?_,ready.back i⟩
  change load32 s.memory (0x2c024#32)≠0 ↔ (3:Nat) &&& 4≠0
  rw [ready.active]; decide
end Doom.Proofs.E1M1NextCallbackReady
