import Doom.Proofs.OriginalLineCoordinates
import Doom.Proofs.E1M1ThingGate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1ThingCoordinates
open Verification X86 X86Memory X86Control BlockSummary
open OriginalLineCoordinates (register)
open E1M1ScanMemory (firstScan)
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)

/-- CALL setup, iterator bounds, and BLOCKMAP lookup leave ECX/ESI intact. -/
theorem caller_coordinate (s : X86Memory.State) (x : Bool) :
    (E1M1PathMapCaller.scan s).core.regs (register x)=s.regs (register x) := by
  have guarded (t : X86Memory.State) :
      (OriginalLineBounds.guarded t).core.regs (register x)=t.regs (register x) := by
    unfold OriginalLineBounds.guarded
    split <;> (try split) <;> (try split) <;> cases x <;>
      simp [OriginalLineBounds.loaded,register,put,write]
  have returned (t : X86Memory.State) :
      (OriginalLineBounds.returned t).core.regs (register x)=t.regs (register x) := by
    cases x <;> simp [OriginalLineBounds.returned,OriginalLineBounds.r3,OriginalLineBounds.r2,
      OriginalLineBounds.r1,register,put,write]
  have bounds (t : X86Memory.State) :
      (OriginalLineBounds.result t).core.regs (register x)=t.regs (register x) := by
    unfold OriginalLineBounds.result
    split <;> (try rw [returned]) <;> rw [guarded] <;> cases x <;>
      simp [OriginalLineBounds.entry,OriginalLineBounds.e2,OriginalLineBounds.e1,
        X86Routine.pushWord,register,put,write]
  have lookup (t : X86Memory.State) :
      (OriginalLineCell.lookup t).core.regs (register x)=t.regs (register x) := by
    cases x <;> simp [OriginalLineCell.lookup,OriginalLineCell.l7,OriginalLineCell.l6,
      OriginalLineCell.l5,OriginalLineCell.l4,OriginalLineCell.l3,OriginalLineCell.l2,
      OriginalLineCell.l1,register,put,write]
  unfold E1M1PathMapCaller.scan E1M1PathMapBounds.scanStart
  rw [lookup,bounds]
  cases x <;> simp [E1M1PathMapCaller.call,OriginalPathCell.called,OriginalPathCell.c3,
    OriginalPathCell.c2,OriginalPathCell.c1,X86Routine.pushWord,register,put,write]

section Firing
variable (gun : Fire.Gun) (s : X86Memory.State) (weapon : Weapon.Context)
    (actor : Word) (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (xout yout : Int32 × Fixed × Fixed) (base lines : Word) (words : Array Nat)
    (c : E1M1PathMap.Cell) (w h : Nat) (data : Nat → LineData)
    (input : E1M1FiringScan.Inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data)
include input

/-- Numeric initialization supplies the production path's first block, including
its original fixed-point nudges at block boundaries. -/
theorem first_coordinates :
    (firstScan gun s).core.regs 6=(path thing angle ox oy).startBlockX.toBitVec ∧
    (firstScan gun s).core.regs 1=(path thing angle ox oy).startBlockY.toBitVec := by
  have geometry := E1M1AimGeometry.path_inputs _ thing angle _ ox oy
    (E1M1FiringGeometry.query_geometry gun s actor thing angle ox oy input.geometry)
  have grid := (E1M1PathGridSetup.grid_observation_from_init _ ox oy _ _ _ _ geometry
    xout yout input.okX input.okY).2
  exact ⟨(caller_coordinate (E1M1PathGridSetup.firstGrid gun s).core true).trans grid.mapX,
    (caller_coordinate (E1M1PathGridSetup.firstGrid gun s).core false).trans grid.mapY⟩

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Collision.SolidThing.attackEndpoint

/-- The existing complete scan contract also restores both coordinate registers;
there are no extra saved-register assumptions at reached callbacks. -/
theorem scan_coordinate (x : Bool) :
    (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).1.core.regs
      (register x)=(firstScan gun s).core.regs (register x) := by
  let contract := E1M1FiringScan.initial gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  have run := E1M1FiringGeometry.first_scan_execution gun s none weapon input.firing actor thing angle ox oy input.geometry
    xout yout input.okX input.okY base lines words c w h input.map input.cursorSafe input.inside input.valid input.selected
  have keeps : ∀ i<c.ids.length, (contract.candidates i).crosses=true → (contract.candidates i).Continues := by
    intro i _ _
    dsimp only [contract,E1M1FiringScan.initial,E1M1ScanContracts.initial]
    exact E1M1ScanContracts.candidate_continues (path thing angle ox oy).trace lines c.ids[i]! (data i)
  exact OriginalLineCoordinates.finished_coordinate (firstScan gun s).core c.ids.length 0x2ba20
    (E1M1PathMap.resolve lines) contract {trace := (path thing angle ox oy).trace} (firstScan gun s).flags run.2.2 keeps x

/-- The thing iterator receives the intended map-cell coordinates, rather than
merely unspecified register values at its CALL site. -/
theorem call_coordinates :
    let out := E1M1ThingGate.called gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
    out.core.regs 0=(path thing angle ox oy).startBlockX.toBitVec ∧
    out.core.regs 2=(path thing angle ox oy).startBlockY.toBitVec := by
  have args := OriginalPathCell.call_inputs false
    (E1M1ThingGate.gate gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core
    (OriginalPathCell.gateFlags false (E1M1ThingGate.gate gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core)
  have first := first_coordinates gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  exact ⟨args.1.trans ((scan_coordinate gun s weapon actor thing angle ox oy xout yout base lines words c w h data input true).trans first.1),
    args.2.1.trans ((scan_coordinate gun s weapon actor thing angle ox oy xout yout base lines words c w h data input false).trans first.2)⟩

/-- Continuous execution to the actual original thing-iterator entry, now with
correct coordinates, callback, stack, return word, and retained line intercepts. -/
theorem firing_call (returns : E1M1ScanReturn.ReturnSafe (s.regs 4) lines)
    (safe : E1M1ThingGate.FlagSafe (s.regs 4) lines) (f : Option Flags) :
    let out := E1M1ThingGate.called gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
    let hits := (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).2.collected
    (∃ steps≤383+281*c.ids.length, X86CodeMemory.Prefix FloorCaller.cm OriginalLineMixedInvariant.program [] steps
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    out.pc=0x2c5a0 ∧ out.core.regs 4=s.regs 4-(116#32) ∧
    out.core.regs 0=(path thing angle ox oy).startBlockX.toBitVec ∧
    out.core.regs 2=(path thing angle ox oy).startBlockY.toBitVec ∧
    out.core.regs 3=(0x2c720#32) ∧ load32 out.core.memory (out.core.regs 4)=(0x2cab1#32) ∧
    OriginalLineCollection.Tracks out.core 0x2ba20 (E1M1PathMap.resolve lines) hits 0 := by
  obtain ⟨execution,pc,sp,_,_,callback,ret,hits⟩ :=
    E1M1ThingGate.firing_call gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns safe f
  have coords := call_coordinates gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  exact ⟨execution,pc,sp,coords.1,coords.2,callback,ret,hits⟩
end Firing
end Doom.Proofs.E1M1ThingCoordinates
