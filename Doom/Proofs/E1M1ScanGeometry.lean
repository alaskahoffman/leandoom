import Doom.Proofs.OriginalLineVisits
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.E1M1ScanGeometry
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanMemory (firstScan LineWords lineReads)
open OriginalLineMixedInvariant (atIndex)

def path (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed) :=
  Collision.pathStart ox oy thing.x thing.y (thing.attackEndpoint angle (Fixed.ofInt 1024)).1
    (thing.attackEndpoint angle (Fixed.ofInt 1024)).2

def linePointer (lines : Word) (id : Nat) : Word := BitVec.ofNat 32 id*62+lines

theorem caller_stack (s : X86Memory.State) (x y : Int32) (w h : Nat)
    (dims : E1M1PathMapCaller.Dimensions s w h) (mapX : s.regs 6=x.toBitVec) (mapY : s.regs 1=y.toBitVec)
    (inside : Collision.pathCellInside x y w h=true) :
    (E1M1PathMapCaller.scan s).core.regs 4=s.regs 4-(12#32) := by
  have ins := (OriginalLineBounds.live_bounds _ x y w h
    (E1M1PathMapCaller.bounds_inputs s x y w h dims mapX mapY)).mpr inside
  change (OriginalLineCell.lookup (OriginalLineBounds.result (E1M1PathMapCaller.call s).core).core).core.regs 4=_
  rw [(OriginalLineCell.lookup_observe _).2.2.1,E1M1LineCell.inside_state _ ins]
  change (OriginalLineBounds.entry (E1M1PathMapCaller.call s).core).regs 4=_
  rw [(OriginalLineBounds.entry_coordinates _).2.2,E1M1PathMapCaller.call_stack]
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]

/-- Signed bounds and successful axis setup determine the actual scan frame.
All map/geometry premises are at the common post-sound firing boundary. -/
theorem firing_stack (gun : Fire.Gun) (s : X86Memory.State) (actor : Word)
    (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (geometry : E1M1FiringGeometry.Inputs gun s actor thing angle ox oy)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (path thing angle ox oy).xStep=.ok xout)
    (okY : (path thing angle ox oy).yStep=.ok yout)
    (base lines : Word) (words : Array Nat) (w h : Nat)
    (map : E1M1PathMapFiring.MapInputs gun s base lines words w h)
    (inside : Collision.pathCellInside (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY w h=true) :
    (firstScan gun s).core.regs 4=s.regs 4-(124#32) := by
  have geo := E1M1AimGeometry.path_inputs _ thing angle _ ox oy
    (E1M1FiringGeometry.query_geometry gun s actor thing angle ox oy geometry)
  have maps := E1M1PathMapSetup.map_at_grid _ ox oy _ _ _ _ geo base lines words w h
    (E1M1PathMapQuery.map_at_traversal _ base lines words w h
      (E1M1PathMapFiring.map_at_query gun s base lines words w h map))
  have grid := (E1M1PathGridSetup.grid_observation_from_init _ ox oy _ _ _ _ geo xout yout okX okY).2
  have stack := caller_stack _ _ _ w h maps.1 grid.mapX grid.mapY inside
  have sp := E1M1PathMapSetup.grid_stack _ ox oy _ _ _ _ geo
  change (firstScan gun s).core.regs 4=(E1M1PathMapSetup.grid (E1M1AimSetup.firstTraversal gun s).core).core.regs 4-(12#32) at stack
  change (E1M1PathMapSetup.grid (E1M1AimSetup.firstTraversal gun s).core).core.regs 4=
    (E1M1AimSetup.firstTraversal gun s).core.regs 4-(60#32) at sp
  rw [sp,E1M1ScanMemory.firing_stack] at stack
  simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using stack

/-- Layout contracts use the original SP, not reached-state memory. -/
def SideSafe (sp a : Word) : Prop :=
  ∀ off∈[(4#32),8,12,16,20,40,44,48,52,56], Apart a (sp-(128#32)-off)
def ScratchSafe (sp a : Word) : Prop :=
  ∀ off∈OriginalLineTail.stackOffsets, Apart a (sp-(128#32)-(36#32)+off)

theorem view_stack (s : X86Memory.State) (sp : Word) (stack : s.regs 4=sp-(124#32)) (i : Nat) :
    (OriginalLineDispatch.view (atIndex s i)).regs 4=sp-(128#32) := by
  change (OriginalLineDispatch.entry (atIndex s i)).core.regs 4=_
  rw [(OriginalLineDispatch.entry_regs _).2.2]
  change s.regs 4-(4#32)=_
  rw [stack]
  simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem side_safe (s : X86Memory.State) (sp : Word) (stack : s.regs 4=sp-(124#32))
    (i : Nat) (a : Word) (safe : SideSafe sp a) :
    OriginalLineCrossing.SideSafe (OriginalLineDispatch.view (atIndex s i)) a := by
  unfold OriginalLineCrossing.SideSafe
  rw [view_stack s sp stack i]
  exact safe

theorem scratch_safe (s : X86Memory.State) (sp : Word) (stack : s.regs 4=sp-(124#32))
    (i : Nat) (a : Word) (safe : ScratchSafe sp a) :
    OriginalLineCrossing.ScratchSafe (OriginalLineDispatch.view (atIndex s i)) a := by
  unfold OriginalLineCrossing.ScratchSafe
  rw [view_stack s sp stack i]
  exact safe

/-- Common callback geometry, before choosing same-side rejection or crossing. -/
structure Geometry (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line) (p v w : Word) : Prop where
  entry : OriginalLineInterceptEntry.Inputs s trace line p v
  data : E1M1LineSecondPoint.LineData s line p v w

theorem callback_geometry (s : X86Memory.State) (sp : Word) (stack : s.regs 4=sp-(124#32))
    (i : Nat) (trace : Collision.Divline) (line : Collision.Line) (p v w : Word)
    (pointer : OriginalLineDispatch.pointer (atIndex s i)=p)
    (traceWords : (load32 s.memory 0x2ba10,load32 s.memory 0x2ba14,load32 s.memory 0x2ba18,load32 s.memory 0x2ba1c)=
      (trace.x.raw.toBitVec,trace.y.raw.toBitVec,trace.dx.raw.toBitVec,trace.dy.raw.toBitVec))
    (encoded : LineWords s.memory line p v w)
    (safe : ∀ a∈OriginalLineSecondPoint.reads p v w, SideSafe sp a) :
    Geometry (OriginalLineDispatch.view (atIndex s i)) trace line p v w := by
  have protect (a : Word) (ha : a∈OriginalLineSecondPoint.reads p v w) :=
    side_safe s sp stack i a (safe a ha)
  refine ⟨⟨?_,?_,?_,?_,?_,encoded.vertex1,encoded.x1,encoded.y1,?_⟩,
    ⟨encoded.vertex2,encoded.x2,encoded.y2,encoded.dx,encoded.dy,protect⟩⟩
  · exact (OriginalLineDispatch.entry_regs _).1.trans pointer
  · exact congrArg (fun t => t.1) traceWords
  · exact congrArg (fun t => t.2.1) traceWords
  · exact congrArg (fun t => t.2.2.1) traceWords
  · exact congrArg (fun t => t.2.2.2) traceWords
  · intro a ha off ho
    apply protect a
    · simp only [OriginalLineInterceptEntry.reads,List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [OriginalLineSecondPoint.reads]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl|rfl|rfl|rfl|rfl <;> simp

theorem rejection_inputs (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line) (p v w : Word)
    (geometry : Geometry s trace line p v w)
    (same : OriginalLineSecondPoint.firstSide trace line=OriginalLineSecondPoint.lastSide trace line) :
    OriginalLineReject.Inputs s trace line p v w := ⟨geometry.entry,geometry.data,same⟩

theorem crossing_inputs (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line) (p v w : Word)
    (geometry : Geometry s trace line p v w)
    (crosses : OriginalLineSecondPoint.firstSide trace line≠OriginalLineSecondPoint.lastSide trace line) :
    OriginalLineCrossing.Inputs s trace line p v w := ⟨geometry.entry,geometry.data,crosses⟩

/-- Intercept storage is specified once using firing-entry SP, all E1M1 line
stamps, and the fixed 128-record array. No reached cursor value is assumed. -/
structure Storage (sp lines : Word) : Prop where
  stamps : ∀ k<128, ∀ off∈[(0#32),4,8], ∀ id<475,
    Apart (OriginalLineCollection.slot 0x2ba20 k off) (OriginalLineVisits.stamp lines id)
  call : ∀ k<128, ∀ off∈[(0#32),4,8], Apart (OriginalLineCollection.slot 0x2ba20 k off) (sp-(128#32))
  side : ∀ k<128, ∀ off∈[(0#32),4,8], SideSafe sp (OriginalLineCollection.slot 0x2ba20 k off)
  scratch : ∀ k<128, ∀ off∈[(0#32),4,8], ScratchSafe sp (OriginalLineCollection.slot 0x2ba20 k off)
  metadata : ∀ k<128, ∀ off∈[(0#32),4,8], Apart (OriginalLineCollection.slot 0x2ba20 k off) (0x2c028#32)

theorem storage_layout (s : X86Memory.State) (sp lines : Word) (stack : s.regs 4=sp-(124#32))
    (i id : Nat) (bound : id<475) (pointer : OriginalLineDispatch.pointer (atIndex s i)=linePointer lines id)
    (storage : Storage sp lines) : OriginalLineCollection.Layout (atIndex s i) 0x2ba20 := by
  refine ⟨?_,?_,?_,storage.metadata⟩
  · intro k hk off ho
    constructor
    · unfold OriginalLineDispatch.stamp
      rw [pointer]
      exact storage.stamps k hk off ho id bound
    · change Apart _ (s.regs 4-(4#32))
      rw [stack]
      simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using storage.call k hk off ho
  · intro k hk off ho
    exact side_safe s sp stack i _ (storage.side k hk off ho)
  · intro k hk off ho
    exact scratch_safe s sp stack i _ (storage.scratch k hk off ho)
/-- Both weapons reach the first scan and supply its indexed callback geometry
templates and intercept-storage layout from firing-entry contracts. The scan
invariant transports these templates to reached callbacks; this theorem alone
does not assert that every indexed candidate is executed. -/
theorem first_line_geometry (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (weapon : Weapon.Context) (input : E1M1DischargeSetters.Inputs gun s weapon)
    (actor : Word) (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (geometry : E1M1FiringGeometry.Inputs gun s actor thing angle ox oy)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (path thing angle ox oy).xStep=.ok xout)
    (okY : (path thing angle ox oy).yStep=.ok yout)
    (base lines : Word) (words : Array Nat) (c : E1M1PathMap.Cell) (w h : Nat)
    (map : E1M1PathMapFiring.MapInputs gun s base lines words w h)
    (cursorSafe : E1M1PathMapSetup.StackSafe (s.regs 4-(112#32)) (0x2c028#32))
    (inside : Collision.pathCellInside (path thing angle ox oy).startBlockX
      (path thing angle ox oy).startBlockY w h=true)
    (valid : c.Valid words)
    (selected : words[4+Collision.pathCellIndex (path thing angle ox oy).startBlockX
      (path thing angle ox oy).startBlockY w]?=some c.offset)
    (i : Fin c.ids.length) (line : Collision.Line) (v1 v2 : Word)
    (encoded : LineWords s.memory line (linePointer lines c.ids[i.val]) v1 v2)
    (lineSafe : ∀ a∈lineReads (linePointer lines c.ids[i.val]) v1 v2, E1M1PathMapFiring.Safe gun s a)
    (traceSafe : ∀ a∈[(0x2ba10#32),0x2ba14,0x2ba18,0x2ba1c], E1M1PathMapSetup.StackSafe (s.regs 4-(112#32)) a)
    (callbackSafe : ∀ a∈OriginalLineSecondPoint.reads (linePointer lines c.ids[i.val]) v1 v2, SideSafe (s.regs 4) a)
    (storage : Storage (s.regs 4) lines) :
    (∃ n≤368, X86CodeMemory.Prefix FloorCaller.cm E1M1PathMapCaller.firingProgram [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstScan gun s)) ∧
    E1M1PathMapLookup.ScanWords (firstScan gun s).core lines c ∧
    OriginalLineCollection.Tracks (firstScan gun s).core 0x2ba20 (E1M1PathMap.resolve lines) #[] c.ids.length ∧
    (firstScan gun s).core.regs 4=s.regs 4-(124#32) ∧
    Geometry (OriginalLineDispatch.view (atIndex (firstScan gun s).core i.val))
      (path thing angle ox oy).trace line (linePointer lines c.ids[i.val]) v1 v2 ∧
    OriginalLineCollection.Layout (atIndex (firstScan gun s).core i.val) 0x2ba20 := by
  have run := E1M1FiringGeometry.first_scan_execution gun s f weapon input actor thing angle ox oy geometry
    xout yout okX okY base lines words c w h map cursorSafe inside valid selected
  have sp := firing_stack gun s actor thing angle ox oy geometry xout yout okX okY base lines words w h map inside
  have pointer : OriginalLineDispatch.pointer (atIndex (firstScan gun s).core i.val)=linePointer lines c.ids[i.val] :=
    run.2.1.pointers i (Fixed.ofInt 0)
  have trace := E1M1ScanMemory.firing_trace gun s actor thing angle ox oy geometry traceSafe
  have loaded := E1M1ScanMemory.firing_line gun s actor thing angle ox oy geometry line _ v1 v2 encoded lineSafe
  exact ⟨run.1,run.2.1,run.2.2,sp,callback_geometry _ (s.regs 4) sp i.val _ line _ v1 v2 pointer trace loaded callbackSafe,
    storage_layout _ (s.regs 4) lines sp i.val c.ids[i.val] (valid.2.2.2.1 i).1 pointer storage⟩
end Doom.Proofs.E1M1ScanGeometry
