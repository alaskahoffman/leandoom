import Doom.Engine
import Doom.Proofs.E1M1QuerySource
import Doom.Proofs.E1M1AimStampImage

set_option maxRecDepth 32768
namespace Doom.Proofs.InitializedE1M1
open Verification X86 X86Memory Collision

/-- The actual private Combat.combatScene expression, not an independent world. -/
def aimingScene (s : Engine.State) : Except String Scene :=
  s.game.player.syncScene s.game.map

/-- Finite data checks only: no path result, callback or preservation premise. -/
def stampCheck (values : Array Nat) (epoch : Nat) : Bool :=
  decide (values.size = 475 ∧ epoch < 2^32-2 ∧
    ∀ j : Fin values.size, values[j.val] ≤ epoch)

def shapeCheck (scene : Scene) : Bool :=
  decide (scene.grid.vanillaOffsets = true ∧ scene.grid.width = 36 ∧
    scene.grid.height = 23 ∧ scene.grid.cells.size = 828 ∧ scene.links.size = 828)

structure ActorWords where
  x : Word
  y : Word
  z : Word
  height : Word

def actorWords (m : Memory) (pointer : Word) : ActorWords :=
  ⟨load32 m (pointer+12),load32 m (pointer+16),load32 m (pointer+20),load32 m (pointer+68)⟩

def actorCheck (t : SolidThing) (w : ActorWords) : Bool :=
  decide (w.x=t.x.raw.toBitVec ∧ w.y=t.y.raw.toBitVec ∧
    w.z=t.z.raw.toBitVec ∧ w.height=t.height.raw.toBitVec)

def engineCheck (s : Engine.State) (w : ActorWords) : Bool :=
  match aimingScene s with
  | .error _ => false
  | .ok scene => match scene.things[0]? with
    | none => false
    | some thing => shapeCheck scene && actorCheck thing w

/-- Discharges the existing live-query profile, not a newly named copy of it. -/
theorem supported_of_check (scene : Scene) (h : shapeCheck scene = true) :
    E1M1QuerySource.supported scene = true := by
  obtain ⟨vanilla,width,height,cells,links⟩ := of_decide_eq_true h
  simp [E1M1QuerySource.supported,vanilla,width,height,cells,links]

/-- Derive two original aiming freshness premises from bounded captured stamps.
The memory decoding equality is explicit. It says nothing about future writes;
transport to a later BulletSlope entry remains a separate proof obligation. -/
theorem fresh_pair (values : Array Nat) (epoch : Nat) (m : Memory) (lines : Word)
    (checked : stampCheck values epoch = true)
    (decoded : ∀ j<475, load32 m (OriginalLineVisits.stamp lines j) =
      BitVec.ofNat 32 values[j]!) :
    E1M1AimStampImage.Fresh m lines (BitVec.ofNat 32 epoch+1) 475 ∧
    E1M1AimStampImage.Fresh m lines ((BitVec.ofNat 32 epoch+1)+1) 475 := by
  obtain ⟨size,noWrap,bounds⟩ := of_decide_eq_true checked
  have epochLt : epoch < 2^32 := by omega
  have epochVal : (BitVec.ofNat 32 epoch).toNat=epoch := by
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt epochLt]
  have bounded : ∀ j<475, (load32 m (OriginalLineVisits.stamp lines j)).toNat≤
      (BitVec.ofNat 32 epoch).toNat := by
    intro j hj
    have hj' : j<values.size := by omega
    have hv : values[j] ≤ epoch := bounds ⟨j,hj'⟩
    rw [decoded j hj,epochVal]
    simpa only [getElem!_pos values j hj',BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show values[j]<2^32 by omega)] using hv
  have nextVal : (BitVec.ofNat 32 epoch+1).toNat=epoch+1 := by
    simp only [BitVec.toNat_add,epochVal]
    change (epoch+1)%2^32=epoch+1
    exact Nat.mod_eq_of_lt (by omega)
  constructor
  · exact E1M1AimStampImage.bounded_fresh m lines _ 475 bounded (by rw [epochVal]; omega)
  · apply E1M1AimStampImage.bounded_fresh m lines _ 475
    · intro j hj
      have h := bounded j hj
      rw [epochVal] at h
      rw [nextVal]
      omega
    · rw [nextVal]; omega

/-- A successful data checker on the *production Engine.State projection*
provides the existing profile, actual shooter lookup, and four memory input
facts used by E1M1AimGeometry.Inputs. No full execution contract is an argument.
Initialization execution/provenance and all remaining aim contracts are separate. -/
theorem engine_inputs (s : Engine.State) (m : Memory) (pointer : Word)
    (checked : engineCheck s (actorWords m pointer) = true) :
    ∃ scene thing,
      aimingScene s = .ok scene ∧ scene.things[0]? = some thing ∧
      E1M1QuerySource.supported scene = true ∧
      load32 m (pointer+12)=thing.x.raw.toBitVec ∧
      load32 m (pointer+16)=thing.y.raw.toBitVec ∧
      load32 m (pointer+20)=thing.z.raw.toBitVec ∧
      load32 m (pointer+68)=thing.height.raw.toBitVec := by
  cases hv : aimingScene s with
  | error e => simp [engineCheck,hv] at checked
  | ok scene =>
    cases ht : scene.things[0]? with
    | none => simp [engineCheck,hv,ht] at checked
    | some thing =>
      simp only [engineCheck,hv,ht,Bool.and_eq_true] at checked
      exact ⟨scene,thing,rfl,ht,supported_of_check scene checked.1,
        of_decide_eq_true checked.2⟩
/-- The production initializer itself, including assets and optional DOS heap.
Reject initialization errors rather than supplying a successful spawn premise. -/
def startCheck (lumps : Array Lump) (w : ActorWords) : Bool :=
  match Engine.start lumps true false with
  | .error _ => false
  | .ok (_,state,_) => engineCheck state w

/-- Checked production initialization yields its actual retained state and aiming
inputs. Capture authenticity/decoding is external; success of later queries is
not assumed. No launch or DOS/VGA initialization proof is required here. -/
theorem started_inputs (lumps : Array Lump) (m : Memory) (pointer : Word)
    (checked : startCheck lumps (actorWords m pointer) = true) :
    ∃ ctx state events scene thing,
      Engine.start lumps true false = .ok (ctx,state,events) ∧
      aimingScene state = .ok scene ∧ scene.things[0]? = some thing ∧
      E1M1QuerySource.supported scene = true ∧
      load32 m (pointer+12)=thing.x.raw.toBitVec ∧
      load32 m (pointer+16)=thing.y.raw.toBitVec ∧
      load32 m (pointer+20)=thing.z.raw.toBitVec ∧
      load32 m (pointer+68)=thing.height.raw.toBitVec := by
  cases hs : Engine.start lumps true false with
  | error e => simp [startCheck,hs] at checked
  | ok result =>
    rcases result with ⟨ctx,state,events⟩
    have check : engineCheck state (actorWords m pointer)=true := by
      simpa only [startCheck,hs] using checked
    obtain ⟨scene,thing,inputs⟩ := engine_inputs state m pointer check
    exact ⟨ctx,state,events,scene,thing,rfl,inputs⟩

end Doom.Proofs.InitializedE1M1
