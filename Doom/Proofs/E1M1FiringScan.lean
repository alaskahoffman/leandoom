import Doom.Proofs.E1M1ScanContracts
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1FiringScan
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanMemory (firstScan)
open E1M1ScanGeometry (path linePointer)
open E1M1ScanContracts (LineData candidates)

/-- The iterator prologue saves the callback installed by the real caller. -/
theorem caller_target (s : X86Memory.State) (x y : Int32) (w h : Nat)
    (dims : E1M1PathMapCaller.Dimensions s w h)
    (mapX : s.regs 6=x.toBitVec) (mapY : s.regs 1=y.toBitVec)
    (inside : Collision.pathCellInside x y w h=true) :
    load32 (E1M1PathMapCaller.scan s).core.memory
      ((E1M1PathMapCaller.scan s).core.regs 4) = (0x2c5f0#32) := by
  have ins := (OriginalLineBounds.live_bounds _ x y w h
    (E1M1PathMapCaller.bounds_inputs s x y w h dims mapX mapY)).mpr inside
  change load32 (OriginalLineCell.lookup (OriginalLineBounds.result (E1M1PathMapCaller.call s).core).core).core.memory
    ((OriginalLineCell.lookup (OriginalLineBounds.result (E1M1PathMapCaller.call s).core).core).core.regs 4)=_
  rw [(OriginalLineCell.lookup_observe _).2.1,(OriginalLineCell.lookup_observe _).2.2.1,
    E1M1LineCell.inside_state _ ins]
  change load32 (store32 _ ((E1M1PathMapCaller.call s).core.regs 4-8)
    ((E1M1PathMapCaller.call s).core.regs 3)) ((E1M1PathMapCaller.call s).core.regs 4-8)=_
  rw [load_store]
  exact (OriginalPathCell.call_inputs true s (OriginalPathCell.gateFlags true s)).2.2.1

/-- The actual BLOCKMAP offset determines the scan cursor. -/
theorem caller_cursor (s : X86Memory.State) (base lines : Word) (words : Array Nat)
    (c : E1M1PathMap.Cell) (x y : Int32) (w h : Nat)
    (dims : E1M1PathMapCaller.Dimensions s w h)
    (mapX : s.regs 6=x.toBitVec) (mapY : s.regs 1=y.toBitVec)
    (globals : E1M1PathMapCaller.Globals s base lines)
    (inside : Collision.pathCellInside x y w h=true) (valid : c.Valid words)
    (image : E1M1PathMap.WordImage s.memory base words)
    (safe : E1M1PathMapCaller.ImageSafe s base words)
    (selected : words[4+Collision.pathCellIndex x y w]?=some c.offset) :
    (E1M1PathMapCaller.scan s).core.regs 2=base+BitVec.ofNat 32 (2*c.offset) := by
  have retained := E1M1PathMapCaller.image_at_call s base words image safe
  have context := E1M1PathMapBounds.lookup_context _ base lines x y w h
    (E1M1PathMapCaller.bounds_inputs s x y w h dims mapX mapY)
    (E1M1PathMapCaller.globals_at_call s base lines globals) inside
  exact (E1M1PathMapLookup.lookup_ready _ base words c x y w h context inside valid
    (E1M1PathMapBounds.image_preserved _ base words retained.1 retained.2) selected).1

/-- Data and separation at post-sound firing entry. No reached scan register,
callback address, geometry, or intercept cursor is an input field. -/
structure Inputs (gun : Fire.Gun) (s : X86Memory.State) (weapon : Weapon.Context)
    (actor : Word) (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (xout yout : Int32 × Fixed × Fixed) (base lines : Word) (words : Array Nat)
    (c : E1M1PathMap.Cell) (w h : Nat) (data : Nat → LineData) : Prop where
  firing : E1M1DischargeSetters.Inputs gun s weapon
  geometry : E1M1FiringGeometry.Inputs gun s actor thing angle ox oy
  okX : (path thing angle ox oy).xStep=.ok xout
  okY : (path thing angle ox oy).yStep=.ok yout
  map : E1M1PathMapFiring.MapInputs gun s base lines words w h
  cursorSafe : E1M1PathMapSetup.StackSafe (s.regs 4-(112#32)) (0x2c028#32)
  activeSafe : E1M1PathMapSetup.StackSafe (s.regs 4-(112#32)) (0x2c024#32)
  inside : Collision.pathCellInside (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY w h=true
  valid : c.Valid words
  selected : words[4+Collision.pathCellIndex (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY w]?=some c.offset
  encoded : ∀ i : Fin c.ids.length, E1M1ScanMemory.LineWords s.memory (data i.val).line
    (linePointer lines c.ids[i.val]) (data i.val).v (data i.val).w
  lineSafe : ∀ i : Fin c.ids.length, ∀ a∈E1M1ScanMemory.lineReads (linePointer lines c.ids[i.val]) (data i.val).v (data i.val).w,
    E1M1PathMapFiring.Safe gun s a
  traceSafe : ∀ a∈[(0x2ba10#32),0x2ba14,0x2ba18,0x2ba1c], E1M1PathMapSetup.StackSafe (s.regs 4-(112#32)) a
  computed : ∀ i : Fin c.ids.length,
    OriginalLineSecondPoint.firstSide (path thing angle ox oy).trace (data i.val).line≠OriginalLineSecondPoint.lastSide (path thing angle ox oy).trace (data i.val).line →
    Collision.interceptVector (path thing angle ox oy).trace ⟨(data i.val).line.x,(data i.val).line.y,(data i.val).line.dx,(data i.val).line.dy⟩=.ok (data i.val).frac
  back : ∀ i : Fin c.ids.length, load32 s.memory (linePointer lines c.ids[i.val]+50)=0 ↔ (data i.val).line.back.isNone=true
  backSafe : ∀ i : Fin c.ids.length, E1M1PathMapFiring.Safe gun s (linePointer lines c.ids[i.val]+50)
  layout : E1M1ScanContracts.Layout (s.regs 4) (base+BitVec.ofNat 32 (2*c.offset)) lines c.ids.length
    (candidates (path thing angle ox oy).trace lines c.ids data)

/-- The setup and scan use the same decoded instruction map. -/
theorem firing_program (pc : Nat) :
    E1M1PathMapCaller.firingProgram pc=E1M1LineCell.program pc := by
  unfold E1M1PathMapCaller.firingProgram E1M1LineCell.program E1M1PathCell.program
    E1M1PathMapCaller.program E1M1PathMapCaller.bytesProgram
    E1M1PathMapBounds.bytesProgram
  change (match E1M1PathGridSetup.program pc with
    | some op => some op
    | none => match OriginalPathCell.program pc with
      | some op => some op
      | none => match OriginalLineBounds.program pc with
        | some op => some op
        | none => OriginalLineCell.program pc)=_
  cases E1M1PathGridSetup.program pc <;> cases OriginalPathCell.program pc <;>
    cases OriginalLineBounds.program pc <;> rfl

theorem contains_firing (pc : Nat) (h : E1M1PathMapCaller.firingProgram pc≠none) :
    OriginalLineMixedInvariant.program pc=E1M1PathMapCaller.firingProgram pc := by
  rw [firing_program] at h ⊢
  exact E1M1LineCrossing.contains_cell pc h

section Firing
variable (gun : Fire.Gun) (s : X86Memory.State) (weapon : Weapon.Context)
    (actor : Word) (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (xout yout : Int32 × Fixed × Fixed) (base lines : Word) (words : Array Nat)
    (c : E1M1PathMap.Cell) (w h : Nat) (data : Nat → LineData)
    (input : Inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data)
include input

theorem boundary :
    (firstScan gun s).core.regs 2=base+BitVec.ofNat 32 (2*c.offset) ∧
    load32 (firstScan gun s).core.memory ((firstScan gun s).core.regs 4)=(0x2c5f0#32) ∧
    (firstScan gun s).pc=0x2c57f := by
  have geo := E1M1AimGeometry.path_inputs _ thing angle _ ox oy
    (E1M1FiringGeometry.query_geometry gun s actor thing angle ox oy input.geometry)
  have maps := E1M1PathMapSetup.map_at_grid _ ox oy _ _ _ _ geo base lines words w h
    (E1M1PathMapQuery.map_at_traversal _ base lines words w h
      (E1M1PathMapFiring.map_at_query gun s base lines words w h input.map))
  have grid := (E1M1PathGridSetup.grid_observation_from_init _ ox oy _ _ _ _ geo xout yout input.okX input.okY).2
  exact ⟨caller_cursor _ base lines words c _ _ w h maps.1 grid.mapX grid.mapY maps.2.1
      input.inside input.valid maps.2.2.1 maps.2.2.2 input.selected,
    caller_target _ _ _ w h maps.1 grid.mapX grid.mapY input.inside,
    (OriginalLineCell.lookup_observe _).2.2.2⟩

/-- Assemble the complete first-cell invariant from firing-entry memory. -/
def initial : OriginalLineMixedInvariant.Initial (firstScan gun s).core c.ids.length 0x2ba20 (E1M1PathMap.resolve lines) := by
  have run := E1M1FiringGeometry.first_scan_execution gun s none weapon input.firing actor thing angle ox oy input.geometry
    xout yout input.okX input.okY base lines words c w h input.map input.cursorSafe input.inside input.valid input.selected
  have sp := E1M1ScanGeometry.firing_stack gun s actor thing angle ox oy input.geometry xout yout input.okX input.okY
    base lines words w h input.map input.inside
  have entry := boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  apply E1M1ScanContracts.initial (firstScan gun s).core (s.regs 4) (base+BitVec.ofNat 32 (2*c.offset)) lines
    (path thing angle ox oy).trace c data sp entry.1 run.2.1 (fun i => (input.valid.2.2.2.1 i).1) entry.2.1
    (E1M1ScanContracts.firing_active gun s actor thing angle ox oy input.geometry input.activeSafe) _ input.computed _ input.layout
  · intro i
    apply E1M1ScanGeometry.callback_geometry _ (s.regs 4) sp i.val _ _ _ _ _
      (run.2.1.pointers i (Fixed.ofInt 0))
      (E1M1ScanMemory.firing_trace gun s actor thing angle ox oy input.geometry input.traceSafe)
      (E1M1ScanMemory.firing_line gun s actor thing angle ox oy input.geometry _ _ _ _ (input.encoded i) (input.lineSafe i))
    intro a ha
    apply (input.layout.words a (E1M1ScanContracts.read_member _ _ _ _ i.val i.isLt a ?_)).side
    simp only [candidates,E1M1ScanContracts.candidate,OriginalLineMixedInvariant.Candidate.reads,
      getElem!_pos c.ids i.val i.isLt]
    exact List.mem_append_left _ ha
  · intro i
    exact E1M1ScanContracts.firing_back gun s actor thing angle ox oy input.geometry _ _ (input.back i) (input.backSafe i)
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Collision.SolidThing.attackEndpoint
/-- Both branches reuse the same initialized empty intercept collection. -/
theorem scan_return (f : Option Flags) :
    let contract := initial gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
    let out := OriginalLineMixedInvariant.finished (firstScan gun s).core c.ids.length 0x2ba20
      (E1M1PathMap.resolve lines) contract (firstScan gun s).flags { trace := (path thing angle ox oy).trace }
    (∃ n≤368, X86CodeMemory.Prefix FloorCaller.cm E1M1PathMapCaller.firingProgram [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ (firstScan gun s)) ∧
    (∃ steps≤281*c.ids.length+7, X86Routine.Prefix OriginalLineMixedInvariant.program [] steps
      (firstScan gun s) out.1) ∧
    OriginalLineTraversal.Runs (firstScan gun s) out.1 c.ids.length ∧
    OriginalLineCollection.Tracks out.1.core 0x2ba20 (E1M1PathMap.resolve lines) out.2.collected 0 := by
  have run := E1M1FiringGeometry.first_scan_execution gun s f weapon input.firing actor thing angle ox oy input.geometry
    xout yout input.okX input.okY base lines words c w h input.map input.cursorSafe input.inside input.valid input.selected
  let contract := initial gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  have continues : ∀ i<c.ids.length, (contract.candidates i).crosses=true → (contract.candidates i).Continues := by
    intro i _ _
    dsimp only [contract,initial,E1M1ScanContracts.initial]
    exact E1M1ScanContracts.candidate_continues (path thing angle ox oy).trace lines c.ids[i]! (data i)
  have tail := OriginalLineMixedInvariant.through_sentinel (firstScan gun s).core c.ids.length 0x2ba20
    (E1M1PathMap.resolve lines) contract { trace := (path thing angle ox oy).trace } (firstScan gun s).flags run.2.2 continues run.2.1.sentinel
  have pc := (boundary gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).2.2
  rw [OriginalPathXStep.at_pc _ _ pc] at tail
  exact ⟨run.1,tail.1,tail.2.1,tail.2.2.1⟩
/-- One continuous original-instruction prefix from either weapon's post-sound
boundary through the complete first-cell line list and its sentinel return.
The initial geometry, successful computations and byte separation remain explicit. -/
theorem firing_through_sentinel (f : Option Flags) :
    let contract := initial gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
    let out := OriginalLineMixedInvariant.finished (firstScan gun s).core c.ids.length 0x2ba20
      (E1M1PathMap.resolve lines) contract (firstScan gun s).flags { trace := (path thing angle ox oy).trace }
    (∃ steps≤375+281*c.ids.length, X86CodeMemory.Prefix FloorCaller.cm OriginalLineMixedInvariant.program [] steps
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out.1) ∧
    OriginalLineTraversal.Runs (firstScan gun s) out.1 c.ids.length ∧
    OriginalLineCollection.Tracks out.1.core 0x2ba20 (E1M1PathMap.resolve lines) out.2.collected 0 := by
  obtain ⟨⟨n,hn,setup⟩,⟨m,hm,suffix⟩,runs,collected⟩ :=
    scan_return gun s weapon actor thing angle ox oy xout yout base lines words c w h data input f
  exact ⟨⟨n+m,by omega,E1M1PspriteStep.prefix_trans
    (setup.transfer OriginalLineMixedInvariant.program [] contains_firing (by simp))
    (X86CodeMemory.lift_success suffix FloorCaller.cm)⟩,runs,collected⟩
end Firing
end Doom.Proofs.E1M1FiringScan
