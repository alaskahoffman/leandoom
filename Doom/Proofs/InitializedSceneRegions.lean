import Doom.Proofs.InitializedScene
import Doom.Proofs.E1M1AimCellEntry

namespace Doom.Proofs.InitializedSceneRegions
open Verification X86Memory Collision
open InitializedScene
open E1M1NoiseAllocation (Region)
open E1M1AimObjectRegions (Storage region)

def storageCheck (stack : Region) (p : Word) (bytes : Nat) : Bool :=
  decide (p.toNat+bytes≤2^32 ∧ (region p bytes).Disjoint stack ∧
    (region p bytes).Disjoint E1M1AimMapRegions.globalStores)

theorem storage (stack : Region) (p : Word) (bytes : Nat)
    (checked : storageCheck stack p bytes=true) : Storage stack p bytes := by
  obtain ⟨bound,stackApart,globalsApart⟩ := of_decide_eq_true checked
  exact ⟨bound,stackApart,globalsApart⟩

def cellCheck (stack : Region) (d : Input) (c : E1M1CellWalkInvariant.Cell) : Bool :=
  storageCheck stack d.lines (475*62) && storageCheck stack d.links 3312 &&
  decide ((region 0x2c0f8 4).Disjoint stack) &&
  (List.ofFn fun i : Fin c.cell.ids.length =>
    storageCheck stack (c.data i.val).v 8 && storageCheck stack (c.data i.val).w 8).all id &&
  c.nodes.all (fun n => storageCheck stack n.pointer 68)

def mapCheck (stack : Region) (d : Input) : Bool :=
  storageCheck stack d.base 6924 && decide (E1M1AimStaticRegions.globals.Disjoint stack)

def check (stack : Region) (m : Memory) (d : Input) (world : Scene) : Bool :=
  mapCheck stack d && (List.range 828).all fun i =>
    cellCheck stack d (cell m d world i (fun _ => Fixed.ofInt 0))

/-- All addresses come from the checked incoming scene. This theorem does not
identify the captured pre-tick ESP with any future aiming-call ESP. -/
theorem cell_layout (stack : Region) (m : Memory) (d : Input) (world : Scene)
    (index : Nat) (fraction : Nat → Fixed) (sp epoch : Word) (trace : Divline)
    (checked : cellCheck stack d (cell m d world index fraction)=true)
    (valid : (cell m d world index fraction).cell.Valid d.words)
    (inside : pathCellInside (cell m d world index fraction).x
      (cell m d world index fraction).y 36 23=true) :
    E1M1AimCellRegions.Layout stack (context d world sp epoch trace) (cell m d world index fraction) := by
  simp only [cellCheck,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨⟨lines,heads⟩,global⟩,vertices⟩,nodes⟩ := checked
  refine ⟨rfl,rfl,inside,storage stack _ _ lines,fun i => (valid.2.2.2.1 i).1,?_,?_,
    storage stack _ _ heads,of_decide_eq_true global⟩
  · intro i
    have hv := List.all_eq_true.mp vertices _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    change (_ && _) = true at hv
    simp only [Bool.and_eq_true] at hv
    exact ⟨storage stack _ _ hv.1,storage stack _ _ hv.2⟩
  · intro n hn
    exact storage stack _ _ (List.all_eq_true.mp nodes n hn)

theorem map_layout (stack : Region) (d : Input) (checked : mapCheck stack d=true) :
    E1M1AimMapRegions.Layout stack d.base := by
  simp only [mapCheck,Bool.and_eq_true] at checked
  have h := storage stack _ _ checked.1
  exact ⟨h.bound,h.stackApart,h.globalsApart,of_decide_eq_true checked.2⟩

/-- Finite placement checks remove every per-read payload protection premise.
Only the scalar reserve for the actual future call remains, deliberately. -/
theorem cell_safe (stack : Region) (raw : Memory) (s : X86Memory.State)
    (base extent : Nat) (d : Input) (world : Scene) (index : Nat) (hi : index<828)
    (fraction : Nat → Fixed) (sp epoch : Word) (trace : Divline)
    (sceneChecked : sceneCheck raw s.memory base extent world d=true)
    (placement : check stack s.memory d world=true)
    (reserve : E1M1AimSetupFootprint.Reserve stack s) :
    E1M1AimPreRayMemory.PayloadSafe s (context d world sp epoch trace) (cell s.memory d world index fraction) := by
  have facts := (scene_sound raw s.memory base extent world d sceneChecked).2.2 index hi fraction sp epoch trace
  simp only [check,Bool.and_eq_true] at placement
  have cp := List.all_eq_true.mp placement.2 index (List.mem_range.mpr hi)
  have cp' : cellCheck stack d (cell s.memory d world index fraction)=true := cp
  exact E1M1AimCellEntry.safe stack s _ _ reserve
    (cell_layout stack s.memory d world index fraction sp epoch trace cp' facts.2.2.1 facts.2.2.2.1)

theorem map_inputs (stack : Region) (raw : Memory) (s : X86Memory.State)
    (base extent : Nat) (d : Input) (world : Scene)
    (sceneChecked : sceneCheck raw s.memory base extent world d=true)
    (placement : check stack s.memory d world=true)
    (reserve : E1M1AimSetupFootprint.Reserve stack s) :
    E1M1PathMapQuery.MapInputs s d.base d.lines d.words 36 23 := by
  have values := (scene_sound raw s.memory base extent world d sceneChecked).2.1
  simp only [sceneCheck,Bool.and_eq_true] at sceneChecked
  have size := (of_decide_eq_true sceneChecked.1.1.2).2.1
  simp only [check,Bool.and_eq_true] at placement
  exact E1M1AimMapEntry.inputs stack s _ _ _ reserve (map_layout stack d placement.1) size values
end Doom.Proofs.InitializedSceneRegions
